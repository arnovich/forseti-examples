"""Check every walkthrough against its original with Glitnir's walkthrough helper.

A walkthrough (``walkthroughs/<name>/``) explains an existing Lean project that
Glitnir cannot check. It is never compiled and has no results file. This
check is the only one it gets, and it compares text only:

* the helper's ``check OUTLINE --notebook NOTEBOOK`` must exit 0 with an
  ``ok:`` line, so each outline entry and each claim restates a declaration of
  the original at the outline's commit, word for word;
* ``map.html`` and ``assets/map.svg`` must be exactly what the helper's
  ``map --links public`` draws now, and name no local path;
* the folder holds one notebook and no ``.glitnir.json`` anywhere.

Run ``python3 scripts/fetch_originals.py`` first: it checks out the originals
and downloads the pinned helper, whose SHA-256 is verified again here.
"""

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

if __package__ in (None, ""):
    # Run as a file (`python scripts/check_walkthroughs.py`), like check_bundles.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.fetch_originals import (  # noqa: E402
    FetchError,
    checked_out_commit,
    checkout_directory,
    check_root,
    outlines,
    project_of,
    verified_helper,
)

RESULTS_SUFFIX = ".glitnir.json"
MAP_FILES = ("map.html", "assets/map.svg")
_LOCAL = re.compile(r"file://|vscode://|/Users/|/home/|_originals")
_TIMEOUT_SECONDS = 600


class WalkthroughError(ValueError):
    """A walkthrough does not match its original or its published files."""


def notebook_of(folder: Path) -> Path:
    """Return the folder's one notebook, refusing none or several."""
    notebooks = sorted(folder.glob("*.lean"))
    if len(notebooks) != 1:
        raise WalkthroughError(f"{folder.name}: needs exactly one .lean notebook")
    return notebooks[0]


def walkthroughs(root: Path) -> list[tuple[Path, Path]]:
    """Return each walkthrough's outline and notebook, with unique names.

    A walkthrough's notebook name may repeat neither another walkthrough's
    nor a gallery notebook's under ``examples/``.
    """
    found = [(outline, notebook_of(outline.parent)) for outline in outlines(root)]
    names = [notebook.stem for _, notebook in found]
    names += [path.stem for path in root.glob("examples/*/*.lean")]
    repeated = sorted({name for name in names if names.count(name) > 1})
    if repeated:
        raise WalkthroughError(f"Notebook names are not unique: {', '.join(repeated)}")
    return found


def _run(command: list[str]) -> subprocess.CompletedProcess[str]:
    """Run the helper isolated from this environment and without bytecode."""
    return subprocess.run(
        [sys.executable, "-I", "-B", *command],
        capture_output=True,
        text=True,
        check=False,
        timeout=_TIMEOUT_SECONDS,
    )


def check_walkthrough(root: Path, outline: Path, notebook: Path) -> str:
    """Check one walkthrough; return the helper's ``ok:`` line.

    Raises:
        WalkthroughError: The text check fails, the maps differ or name a
            local path, or the folder has a results file.
        FetchError: The original or the helper is missing or not as pinned.
    """
    folder = outline.parent
    name = folder.name
    results = sorted(p.relative_to(root).as_posix() for p in folder.rglob(f"*{RESULTS_SUFFIX}"))
    if results:
        raise WalkthroughError(
            f"{name}: walkthroughs are unchecked and have no results file: "
            + ", ".join(results)
        )
    project = project_of(outline)
    check_root(root, project)
    if checked_out_commit(checkout_directory(root, project)) != project.commit:
        raise FetchError(
            f"{name}: the original is not checked out at {project.commit}; "
            "run python3 scripts/fetch_originals.py"
        )
    helper = str(verified_helper(root))
    done = _run([helper, "check", str(outline), "--notebook", str(notebook)])
    output = (done.stdout + done.stderr).strip()
    ok = [line for line in output.splitlines() if line.startswith("ok:")]
    if done.returncode or not ok:
        raise WalkthroughError(f"{name}: walkthrough.py check failed:\n{output}")
    with tempfile.TemporaryDirectory(prefix="walkthrough-map-") as directory:
        drawn = Path(directory)
        done = _run([helper, "map", str(outline), "--links", "public", "--out", str(drawn)])
        if done.returncode:
            raise WalkthroughError(f"{name}: walkthrough.py map failed:\n{done.stdout}")
        for relative in MAP_FILES:
            committed = folder / relative
            if not committed.is_file() or committed.read_bytes() != (
                drawn / relative
            ).read_bytes():
                raise WalkthroughError(
                    f"{name}: {relative} is not what `walkthrough.py map --links public` "
                    "draws; draw it again"
                )
    local = _LOCAL.search((folder / "map.html").read_text(encoding="utf-8"))
    if local:
        raise WalkthroughError(f"{name}: map.html names a local location ({local[0]})")
    return ok[-1]


def check_all(root: Path) -> list[str]:
    """Check every walkthrough; return one line per walkthrough.

    Raises:
        WalkthroughError: Any walkthrough fails; every failure is named.
    """
    if sys.version_info < (3, 10):
        raise WalkthroughError("The walkthrough helper needs Python 3.10 or newer")
    lines, problems = [], []
    for outline, notebook in walkthroughs(root):
        try:
            ok = check_walkthrough(root, outline, notebook)
        except (WalkthroughError, FetchError) as error:
            problems.append(str(error))
        else:
            lines.append(f"{notebook.relative_to(root).as_posix()}: {ok}")
    if problems:
        raise WalkthroughError("\n".join(problems))
    return lines


def main() -> None:
    """Check this repository's walkthroughs."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        lines = check_all(root)
    except (WalkthroughError, FetchError, OSError) as error:
        parser.exit(1, f"Walkthrough check failed: {error}\n")
    for line in lines:
        print(line)
    print(
        f"{len(lines)} walkthroughs match their originals as text "
        "(unchecked: nothing was compiled)"
    )


if __name__ == "__main__":
    main()
