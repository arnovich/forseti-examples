"""Export every notebook through Glitnir without replaying or writing records."""

import argparse
import base64
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from functools import partial
from pathlib import Path
from typing import Any
from urllib.parse import quote

from scripts.check_bundles import check_bundles


def inventory(root: Path) -> list[Path]:
    """Validate complete bundles before selecting notebooks for publication."""
    count, _ = check_bundles(root)
    paths = sorted(root.glob("examples/*/*.lean"))
    if len(paths) != count:
        raise ValueError("Every gallery notebook must be under examples/<topic>/")
    return paths


def notebook_hashes(root: Path) -> dict[str, str]:
    """Fingerprint sources, records and hidden evidence before and after export."""
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


def prepare_notebook(
    path: Path, root: Path, project: Path, cache: Path, timeout_ms: int = 300_000
) -> dict[str, Any]:
    """Read observations and render diagrams using Glitnir's confined Lean session."""
    from gimle.forseti.lean.environment import MAX_OUTPUT_BYTES
    from gimle.forseti.lean.session import SessionLimits, SubprocessLeanSession
    from gimle.forseti.lean_release import RELEASE_SHA256
    from gimle.forseti.notebook import assets
    from gimle.forseti.notebook.linking import load_notebook
    from gimle.forseti.notebook.server import NotebookService
    from gimle.forseti.notebook.views import unit_digest, views

    # snapshot() is read-only. Never call serve(), replay(), _read() or simulate().
    service = NotebookService(
        path,
        session_factory=partial(SubprocessLeanSession, project),
        limits=SessionLimits(timeout_ms=timeout_ms, max_output_bytes=MAX_OUTPUT_BYTES),
    )
    try:
        snapshot = service.snapshot()
        if snapshot.get("error") or snapshot.get("metadata_error"):
            raise ValueError(f"{path.name}: {snapshot}")
        notebook = load_notebook(path)
        drawings = {}
        for view in views(notebook):
            key = f"{view.cell}:{view.line}"
            backend_pin = (root / "scripts/gallery/requirements.txt").read_bytes()
            digest = hashlib.sha256(
                backend_pin + f"{RELEASE_SHA256}:{unit_digest(notebook, view)}".encode()
            ).hexdigest()
            cached = cache / f"{digest}.json"
            if cached.is_file():
                drawing = json.loads(cached.read_text())
            else:
                print(f"Drawing {path.stem}: {view.name}", flush=True)
                drawing = service.view(view.cell, view.line)
                if drawing.get("error") or not drawing.get("svg"):
                    raise ValueError(f"{path.name}: diagram unavailable: {drawing}")
                cached.write_text(json.dumps(drawing) + "\n")
            if drawing.get("error") or not drawing.get("svg"):
                raise ValueError(f"{path.name}: invalid cached diagram")
            drawings[key] = drawing
        figures = {}
        for asset in snapshot["assets"]:
            if asset["status"] != "ok":
                raise ValueError(f"{path.name}: figure unavailable: {asset}")
            body, media_type = assets.read(path, notebook, asset["path"], asset["sha256"])
            figures[asset["path"]] = {
                "sha256": asset["sha256"],
                "url": f"data:{media_type};base64,{base64.b64encode(body).decode()}",
            }
        return {
            "path": path.relative_to(root).as_posix(),
            "html": path.relative_to(root / "examples").with_suffix(".html").as_posix(),
            "snapshot": snapshot,
            "drawings": drawings,
            "figures": figures,
        }
    finally:
        service.close()


def main() -> None:
    """Build a complete gallery into a new output directory, leaving inputs intact."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("_site"))
    parser.add_argument("--lean-project", type=Path, required=True)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", "arnovich/forseti-examples"))
    parser.add_argument("--revision", default=os.environ.get("GITHUB_SHA"))
    parser.add_argument("--diagram-cache", type=Path, default=Path(".gallery-cache"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    revision = args.revision or subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    source_url(args.repository, revision, "README.md")
    if args.output.exists():
        parser.error("Output already exists; choose a new directory")
    paths = inventory(root)
    if subprocess.run(["git", "diff", "--quiet", revision, "--", "examples"], cwd=root).returncode:
        parser.error("Notebook inputs differ from the selected source revision")
    if subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard", "--", "examples"], cwd=root
    ).strip():
        parser.error("Untracked notebook inputs cannot be linked to a source revision")
    before = notebook_hashes(root)
    args.diagram_cache.mkdir(parents=True, exist_ok=True)

    from gimle.forseti.lean_release import verify_project
    from gimle.forseti.notebook import static_export

    verify_project(args.lean_project)
    # Commit time makes rebuilds deterministic; export does not imply a new check.
    timestamp = subprocess.check_output(
        ["git", "show", "-s", "--format=%cI", revision], cwd=root, text=True
    ).strip()
    try:
        with tempfile.TemporaryDirectory(prefix="forseti-gallery-") as temporary:
            work = Path(temporary)
            notebooks = [prepare_notebook(p, root, args.lean_project, args.diagram_cache) for p in paths]
            for notebook in notebooks:
                notebook["source_url"] = source_url(args.repository, revision, notebook["path"])
            manifest = {
                "repository": args.repository,
                "revision": revision,
                "timestamp": timestamp,
                "notebooks": notebooks,
                "media": str(Path(static_export.__file__).parent / "app"),
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
    print(f"Exported {len(paths)} notebooks to {args.output}; source and records unchanged.")


if __name__ == "__main__":
    main()
