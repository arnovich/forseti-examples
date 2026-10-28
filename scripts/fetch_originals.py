"""Fetch what the walkthroughs' text check reads: the originals and the helper.

Each ``walkthroughs/<name>/outline.json`` names an existing Lean project by its
repository, commit and folder (``project.repository``, ``project.commit``,
``project.path``). This script checks out each distinct repository and commit
once, shallowly, at::

    walkthroughs/_originals/<first 12 hex digits of the commit>/<repository name>/

and requires the outline's ``project.root`` to name that checkout's project
folder, relative to the outline. Two walkthroughs of the same repository at
different commits therefore get separate checkouts. It also downloads Glitnir's
walkthrough helper (``walkthrough.py``) at the commit pinned in
``scripts/walkthrough-script.txt`` and keeps it only if its SHA-256 is the
pinned one.

Everything is written under ``walkthroughs/_originals/``, which git ignores. A
checkout already at its commit and a helper with the pinned hash are reused.
Any failure, a network failure included, is an error.

Usage::

    python3 scripts/fetch_originals.py
"""

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any

WALKTHROUGHS = "walkthroughs"
ORIGINALS = "_originals"
HELPER_PIN = Path("scripts/walkthrough-script.txt")
HELPER_URL = (
    "https://raw.githubusercontent.com/arnovich/glitnir/{commit}"
    "/skills/glitnir-notebooks/scripts/walkthrough.py"
)
_COMMIT = re.compile(r"[0-9a-f]{40}")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_TIMEOUT_SECONDS = 120


class FetchError(RuntimeError):
    """An original or the helper could not be fetched or verified."""


@dataclass(frozen=True)
class Project:
    """The original Lean project a walkthrough outline explains."""

    outline: Path
    repository: str
    commit: str
    path: str

    @property
    def name(self) -> str:
        """The repository's name, which is also its checkout folder's name."""
        return self.repository.rstrip("/").rsplit("/", 1)[-1].removesuffix(".git")


@dataclass(frozen=True)
class HelperPin:
    """The pinned Glitnir commit and SHA-256 of the walkthrough helper."""

    commit: str
    sha256: str


def outlines(root: Path) -> list[Path]:
    """Return every walkthrough's outline, sorted; ``_``-folders are not ones."""
    return sorted(
        path
        for path in (root / WALKTHROUGHS).glob("*/outline.json")
        if not path.parent.name.startswith("_")
    )


def load_outline(path: Path) -> dict[str, Any]:
    """Read an outline as a JSON object."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise FetchError(f"{path}: cannot read the outline: {error}") from None
    if not isinstance(data, dict) or not isinstance(data.get("project"), dict):
        raise FetchError(f"{path}: an outline is a JSON object with a project")
    return data


def project_of(path: Path) -> Project:
    """Read and validate the project an outline names."""
    project = load_outline(path)["project"]
    repository, commit = project.get("repository"), project.get("commit")
    folder = project.get("path")
    if not isinstance(repository, str) or not re.fullmatch(
        r"(https|file)://\S+", repository
    ):
        raise FetchError(f"{path}: project.repository must be an https:// or file:// URL")
    if not isinstance(commit, str) or not _COMMIT.fullmatch(commit):
        raise FetchError(f"{path}: project.commit must be a full 40-digit commit")
    if (
        not isinstance(folder, str)
        or not folder
        or Path(folder).is_absolute()
        or ".." in Path(folder).parts
    ):
        raise FetchError(f"{path}: project.path must be a folder in the repository")
    return Project(path, repository, commit, folder)


def checkout_directory(root: Path, project: Project) -> Path:
    """Return where the project's repository is checked out at its commit."""
    return root / WALKTHROUGHS / ORIGINALS / project.commit[:12] / project.name


def project_root(root: Path, project: Project) -> Path:
    """Return the project folder the outline's ``project.root`` must name."""
    return checkout_directory(root, project) / project.path


def check_root(root: Path, project: Project) -> None:
    """Require ``project.root`` to name the project folder in its checkout."""
    stated = load_outline(project.outline)["project"].get("root")
    expected = project_root(root, project)
    if not isinstance(stated, str) or (project.outline.parent / stated).resolve() != (
        expected.resolve()
    ):
        relative = Path("..") / expected.relative_to(root / WALKTHROUGHS)
        raise FetchError(
            f"{project.outline}: project.root must be {relative.as_posix()}"
        )


def _git(*args: str, cwd: Path | None = None) -> str:
    """Run git and return its output, raising FetchError when it fails."""
    command = ["git", "-c", "advice.detachedHead=false", *args]
    try:
        done = subprocess.run(
            command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
            timeout=_TIMEOUT_SECONDS * 5,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise FetchError(f"git {' '.join(args)}: {error}") from None
    if done.returncode:
        message = (done.stderr or done.stdout).strip().splitlines()
        raise FetchError(f"git {' '.join(args)}: {message[-1] if message else 'failed'}")
    return done.stdout.strip()


def checked_out_commit(directory: Path) -> str | None:
    """Return the commit checked out in ``directory``, or None if it is none."""
    if not (directory / ".git").exists():
        return None
    try:
        return _git("-C", str(directory), "rev-parse", "HEAD")
    except FetchError:
        return None


def fetch_checkout(root: Path, project: Project) -> Path:
    """Check out the project's repository at its commit unless already there."""
    directory = checkout_directory(root, project)
    present = checked_out_commit(directory)
    if present == project.commit:
        return directory
    if directory.exists():
        raise FetchError(
            f"{directory} exists but is not a checkout of {project.commit}; remove it"
        )
    partial = directory.with_name(directory.name + ".partial")
    shutil.rmtree(partial, ignore_errors=True)
    partial.mkdir(parents=True)
    try:
        _git("init", "-q", str(partial))
        _git("-C", str(partial), "remote", "add", "origin", project.repository)
        _git("-C", str(partial), "fetch", "-q", "--depth", "1", "origin", project.commit)
        _git("-C", str(partial), "checkout", "-q", "--detach", "FETCH_HEAD")
        if checked_out_commit(partial) != project.commit:
            raise FetchError(f"{project.repository} did not give {project.commit}")
        partial.rename(directory)
    finally:
        shutil.rmtree(partial, ignore_errors=True)
    return directory


def helper_pin(root: Path) -> HelperPin:
    """Read the pinned helper commit and SHA-256 (``key value`` lines)."""
    values: dict[str, str] = {}
    for line in (root / HELPER_PIN).read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.startswith("#"):
            key, _, value = line.partition(" ")
            values[key] = value.strip()
    commit, sha256 = values.get("commit", ""), values.get("sha256", "")
    if not _COMMIT.fullmatch(commit) or not _SHA256.fullmatch(sha256):
        raise FetchError(f"{HELPER_PIN}: needs a full commit and a SHA-256")
    return HelperPin(commit, sha256)


def helper_path(root: Path, pin: HelperPin) -> Path:
    """Return where the fetched helper of the pinned commit is kept."""
    return root / WALKTHROUGHS / ORIGINALS / f"walkthrough-{pin.commit[:12]}.py"


def verified_helper(root: Path) -> Path:
    """Return the fetched helper if its SHA-256 is the pinned one.

    Raises:
        FetchError: It was not fetched, or its bytes are not the pinned ones.
    """
    pin = helper_pin(root)
    path = helper_path(root, pin)
    if not path.is_file() or path.is_symlink():
        raise FetchError(f"{path} is missing; run python3 scripts/fetch_originals.py")
    if hashlib.sha256(path.read_bytes()).hexdigest() != pin.sha256:
        raise FetchError(f"{path} does not have the pinned SHA-256; fetch it again")
    return path


def fetch_helper(root: Path, url: str = HELPER_URL) -> Path:
    """Download the pinned helper unless it is present; verify its SHA-256."""
    pin = helper_pin(root)
    path = helper_path(root, pin)
    try:
        return verified_helper(root)
    except FetchError:
        pass
    source = url.format(commit=pin.commit)
    try:
        with urllib.request.urlopen(source, timeout=_TIMEOUT_SECONDS) as response:
            data = response.read()
    except OSError as error:
        raise FetchError(f"cannot download {source}: {error}") from None
    if hashlib.sha256(data).hexdigest() != pin.sha256:
        raise FetchError(f"{source} does not have the pinned SHA-256")
    path.parent.mkdir(parents=True, exist_ok=True)
    partial = path.with_name(path.name + ".partial")
    partial.write_bytes(data)
    partial.replace(path)
    return path


def fetch_all(root: Path, helper_url: str = HELPER_URL) -> list[Path]:
    """Fetch every walkthrough's original and the helper; return the checkouts."""
    projects = [project_of(path) for path in outlines(root)]
    for project in projects:
        check_root(root, project)
    checkouts: dict[tuple[str, str], Path] = {}
    for project in projects:
        key = (project.repository, project.commit)
        if key not in checkouts:
            checkouts[key] = fetch_checkout(root, project)
    fetch_helper(root, helper_url)
    return list(checkouts.values())


def main() -> None:
    """Fetch for this repository's walkthroughs."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        checkouts = fetch_all(root)
    except (FetchError, OSError) as error:
        parser.exit(1, f"Fetching the originals failed: {error}\n")
    for directory in checkouts:
        print(f"{directory.relative_to(root).as_posix()} at {checked_out_commit(directory)}")
    print(f"Helper {helper_path(root, helper_pin(root)).relative_to(root).as_posix()} verified")


if __name__ == "__main__":
    main()
