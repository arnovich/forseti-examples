"""Export every notebook through Glitnir from its saved results, checking nothing.

Each page is the snapshot Glitnir's static export (``SavedNotebook``) builds
from the saved notebook and its committed ``<Notebook>.glitnir.json``, rendered
and exported by Glitnir's renderer (``scripts/gallery/render.cjs``). No claim is
checked and no results file is written. Glitnir shows saved results as
recorded, compared only with the saved source; the bundle check also requires
each results file to be for this exact source.

Diagrams are drawn by the Forseti view provider in the notebook's own Lake
project, so its imports must be built first (see ``--list-diagram-imports``).
A diagram that cannot be drawn, or that Glitnir marks uncertain because a
dependency's state could not be read, fails the build and is never cached.
With ``--allow-diagram-errors`` the page shows a note in place of a missing
diagram, and an uncertain one with Glitnir's "May be out of date" note.
"""

import argparse
import base64
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any
from urllib.parse import quote

from scripts.check_bundles import check_bundles, check_results, notebook_paths

# Inputs a drawing depends on besides the notebook text before its directive.
DRAWING_INPUTS = (
    "scripts/gallery/requirements.txt",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)
TOOLCHAIN_LIBRARIES = {"Init", "Std", "Lean", "Lake"}


def inventory(root: Path, only: list[str] | None = None) -> list[Path]:
    """Validate saved results before selecting notebooks for publication."""
    count, _ = check_bundles(root, only)
    paths = sorted(
        path
        for path in root.glob("examples/*/*.lean")
        if only is None or path.stem in only
    )
    if len(paths) != count:
        raise ValueError("Every gallery notebook must be under examples/<topic>/")
    return paths


def notebook_hashes(root: Path) -> dict[str, str]:
    """Fingerprint sources, saved results and assets before and after export."""
    return {
        path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted((root / "examples").rglob("*"))
        if path.is_file()
    }


def source_url(repository: str, revision: str, relative: str) -> str:
    """Bind a source link to a GitHub repository and exact Git revision."""
    if not re.fullmatch(r"[\w-]+/[\w.-]+", repository) or not re.fullmatch(
        r"[0-9a-f]{40}", revision
    ):
        raise ValueError("Expected owner/repository and a full Git commit SHA")
    return f"https://github.com/{repository}/blob/{revision}/{quote(relative)}"


def saved_text(path: Path) -> str:
    """Read the saved notebook as Glitnir does: UTF-8 with CRLF read as LF."""
    return path.read_bytes().decode("utf-8").replace("\r\n", "\n")


def drawing_key(root: Path, text: str, view: dict[str, Any]) -> str:
    """Identify a drawing by everything Lean reads to draw it."""
    inputs = {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in DRAWING_INPUTS
    }
    prefix = "".join(line + "\n" for line in text.split("\n")[: view["line"] - 1])
    unit = {
        "inputs": inputs,
        "kind": view["kind"],
        "name": view["name"],
        "using": view["using"],
        "prefix_sha256": hashlib.sha256(prefix.encode("utf-8")).hexdigest(),
    }
    return hashlib.sha256(json.dumps(unit, sort_keys=True).encode()).hexdigest()


def diagram_note(error: str, root: Path) -> str:
    """Shorten a drawing failure to a stable, machine-independent sentence."""
    first = (error.strip().splitlines() or ["unknown error"])[0]
    first = first.replace(str(root), ".").replace(str(Path.home()), "~")
    return f"This diagram could not be drawn for the gallery build: {first[:300]}"


def drawable(drawing: dict[str, Any]) -> bool:
    """Whether Glitnir returned a drawing rather than a failure."""
    return not drawing.get("error") and bool(drawing.get("svg"))


def _saved_notebook(path: Path) -> Any:
    """Open a notebook through Glitnir's public static export."""
    from glitnir.service.static_export import SavedNotebook

    return SavedNotebook(path)


def saved_snapshot(notebook: Any, path: Path) -> dict[str, Any]:
    """Return Glitnir's snapshot of the saved notebook and its saved results.

    Glitnir shows each saved result as recorded, compared only with the saved
    source. Publishing also requires the whole results file to be for this
    exact source, which the bundle check and this comparison enforce.
    """
    records = check_results(path)
    snapshot: dict[str, Any] = notebook.snapshot()
    if snapshot["sha256"] != records["source_sha256"]:
        raise ValueError(f"{path.name}: saved results are for other source")
    if snapshot.get("error") or snapshot.get("metadata_error"):
        raise ValueError(f"{path.name}: {snapshot}")
    if snapshot["preview"].get("recorded") is not True:
        raise ValueError(f"{path.name}: snapshot is not shown as recorded")
    return snapshot


def diagram_imports(root: Path, paths: list[Path]) -> list[str]:
    """List the modules Lean must find built to draw every gallery diagram."""
    modules: set[str] = set()
    for path in paths:
        with _saved_notebook(path) as notebook:
            modules.update(notebook.view_imports())
    return sorted(m for m in modules if m.split(".")[0] not in TOOLCHAIN_LIBRARIES)


def prepare_notebook(
    path: Path, root: Path, cache: Path, allow_diagram_errors: bool = False
) -> dict[str, Any]:
    """Read saved results and draw diagrams through Glitnir's static export."""
    with _saved_notebook(path) as notebook:
        snapshot = saved_snapshot(notebook, path)
        text = saved_text(path)
        drawings: dict[str, Any] = {}
        diagram_errors: list[str] = []
        for view in snapshot["views"]:
            key = f"{view['cell']}:{view['line']}"
            if view["error"]:
                drawing = {"error": view["error"]}
            else:
                cached = cache / f"{drawing_key(root, text, view)}.json"
                if cached.is_file():
                    drawing = json.loads(cached.read_text())
                else:
                    print(f"Drawing {path.stem}: {view['kind']} {view['name']}", flush=True)
                    drawing = notebook.draw_view(view["cell"], view["line"])
                    # One drawn while a dependency's state was unknown is redrawn.
                    if drawable(drawing) and not drawing.get("uncertain"):
                        cached.write_text(json.dumps(drawing, sort_keys=True) + "\n")
            if drawable(drawing) and drawing.get("uncertain"):
                problem = "a dependency's state could not be read while drawing it"
                if not allow_diagram_errors:
                    raise ValueError(f"{path.name}: diagram {view['name']}: {problem}")
                # Kept: Glitnir's renderer marks it "May be out of date".
                print(f"Diagram uncertain: {path.stem}: {view['name']}: {problem}", flush=True)
            elif not drawable(drawing):
                error = str(drawing.get("error") or "no drawing returned")
                if not allow_diagram_errors:
                    raise ValueError(f"{path.name}: diagram {view['name']} unavailable: {error}")
                print(f"Diagram unavailable: {path.stem}: {view['name']}: {error}", flush=True)
                drawing = {"error": diagram_note(error, root)}
                diagram_errors.append(key)
            drawings[key] = drawing
        figures = {}
        for asset in snapshot["assets"]:
            if asset["status"] != "ok":
                raise ValueError(f"{path.name}: figure unavailable: {asset}")
            body, media_type = notebook.asset(asset["path"], asset["sha256"])
            figures[asset["path"]] = {
                "sha256": asset["sha256"],
                "url": f"data:{media_type};base64,{base64.b64encode(body).decode()}",
            }
        return {
            "path": path.relative_to(root).as_posix(),
            "html": path.relative_to(root / "examples").with_suffix(".html").as_posix(),
            "snapshot": snapshot,
            "drawings": drawings,
            "diagram_errors": diagram_errors,
            "figures": figures,
        }


def main() -> None:
    """Build a complete gallery into a new output directory, leaving inputs intact."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--output", type=Path, default=Path("_site"))
    parser.add_argument(
        "--repository",
        default=os.environ.get("GITHUB_REPOSITORY", "arnovich/glitnir-notebooks"),
    )
    parser.add_argument("--revision", default=os.environ.get("GITHUB_SHA"))
    parser.add_argument("--diagram-cache", type=Path, default=Path(".gallery-cache"))
    parser.add_argument(
        "--allow-diagram-errors",
        action="store_true",
        help="show a note for a diagram that cannot be drawn instead of failing",
    )
    parser.add_argument(
        "--only",
        action="append",
        metavar="NOTEBOOK",
        help="export only this notebook (repeatable); for local previews",
    )
    parser.add_argument(
        "--list-diagram-imports",
        action="store_true",
        help="print the modules to build before drawing diagrams, then exit",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    if args.list_diagram_imports:
        # Needs only the inventory: the build may come before results exist.
        paths = [
            path
            for path in notebook_paths(root)
            if path.parent.parent == root / "examples"
            and (args.only is None or path.stem in args.only)
        ]
        print(" ".join(diagram_imports(root, paths)))
        return
    paths = inventory(root, args.only)
    revision = args.revision or subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    source_url(args.repository, revision, "README.md")
    if args.output.exists():
        parser.error("Output already exists; choose a new directory")
    if subprocess.run(["git", "diff", "--quiet", revision, "--", "examples"], cwd=root).returncode:
        parser.error("Notebook inputs differ from the selected source revision")
    if subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard", "--", "examples"], cwd=root
    ).strip():
        parser.error("Untracked notebook inputs cannot be linked to a source revision")
    before = notebook_hashes(root)
    args.diagram_cache.mkdir(parents=True, exist_ok=True)

    from glitnir.preview.editor import renderer_directory
    from glitnir.service import static_export

    # Commit time makes rebuilds deterministic; export does not imply a new check.
    timestamp = subprocess.check_output(
        ["git", "show", "-s", "--format=%cI", revision], cwd=root, text=True
    ).strip()
    try:
        with tempfile.TemporaryDirectory(prefix="forseti-gallery-") as temporary:
            work = Path(temporary)
            notebooks = [
                prepare_notebook(p, root, args.diagram_cache, args.allow_diagram_errors)
                for p in paths
            ]
            for notebook in notebooks:
                notebook["source_url"] = source_url(args.repository, revision, notebook["path"])
            manifest = {
                "repository": args.repository,
                "revision": revision,
                "timestamp": timestamp,
                "notebooks": notebooks,
                "media": str(renderer_directory()),
                "css": static_export.export_styles(),
            }
            inputs = work / "inputs.json"
            inputs.write_text(json.dumps(manifest))
            site = work / "site"
            subprocess.run(
                ["node", str(root / "scripts/gallery/render.cjs"), str(inputs), str(site)],
                check=True, cwd=root, env={**os.environ, "TZ": "UTC"},
            )
            if before != notebook_hashes(root):
                raise ValueError("Export modified a notebook input")
            shutil.copytree(site, args.output)
    finally:
        if before != notebook_hashes(root):
            raise ValueError("Export modified a notebook input")
    failed = sum(len(notebook["diagram_errors"]) for notebook in notebooks)
    note = f"; {failed} diagrams shown as unavailable" if failed else ""
    print(
        f"Exported {len(paths)} notebooks to {args.output}{note}; "
        "sources and saved results unchanged."
    )


if __name__ == "__main__":
    main()
