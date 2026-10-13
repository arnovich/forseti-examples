"""Validate the Lake notebook inventory, dependency pins and retained artifacts."""

import argparse
import json
import re
import tomllib
from pathlib import Path


def _file(root: Path, relative: Path) -> Path:
    """Resolve an existing unlinked relative file inside the repository."""
    candidate = root / relative
    target = candidate.resolve()
    if (
        relative.is_absolute()
        or not target.is_relative_to(root)
        or not target.is_file()
    ):
        raise ValueError(f"Missing or escaping file: {relative}")
    if any(
        path.is_symlink()
        for path in (candidate, *candidate.parents)
        if path.is_relative_to(root) and path != root
    ):
        raise ValueError(f"Linked file or directory: {relative}")
    return target


def check_bundles(directory: Path) -> tuple[int, int]:
    """Return notebook/reference counts only if the whole corpus is valid."""
    root = directory.resolve()
    config = tomllib.loads((root / "lakefile.toml").read_text())
    configured = {}
    for library in config["lean_lib"]:
        name = library["name"]
        if name in configured:
            raise ValueError(f"Duplicate Lake library: {name}")
        configured[name] = _file(
            root, Path(library.get("srcDir", ".")) / f"{name}.lean"
        )
    notebooks = [*root.glob("*.lean"), *root.glob("examples/*/*.lean")]
    if (
        not notebooks
        or len(notebooks) != len(configured)
        or {p.resolve() for p in notebooks} != set(configured.values())
        or set(config["defaultTargets"]) != set(configured)
    ):
        raise ValueError("Notebook inventory does not match Lake libraries and targets")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    if manifest["packagesDir"] != ".lake/packages" or not all(
        package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"])
        for package in manifest["packages"]
    ):
        raise ValueError("Dependencies must use portable Git pins")
    references = 0
    for path in configured.values():
        metadata = _file(root, path.with_suffix(".forseti.json").relative_to(root))
        for run in json.loads(metadata.read_text()).get("runs", []):
            for kind in ("artifact", "goal"):
                relative = run.get("artifact", {}).get(kind)
                if relative:
                    _file(root, path.parent.relative_to(root) / relative)
                    references += 1
    return len(notebooks), references


def main() -> None:
    """Check a corpus root supplied on the command line or this repository."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory", nargs="?", type=Path, default=Path(__file__).resolve().parents[1]
    )
    args = parser.parse_args()
    try:
        notebooks, references = check_bundles(args.directory)
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"Bundle check failed: {error}\n")
    print(
        f"{notebooks} complete notebook bundles; {references} retained references; "
        "all dependency revisions pinned"
    )


if __name__ == "__main__":
    main()
