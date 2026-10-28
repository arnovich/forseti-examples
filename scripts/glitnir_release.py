"""Resolve a Glitnir release and write pip requirements hashed from its SHA256SUMS.

The gallery and the recheck install Glitnir's backend wheel and the Forseti
plugin wheel from one immutable GitHub release. This script names that release
at run time, the latest published one or the tag passed with ``--tag``, so the
repository carries no Glitnir version. The hashes come from the release's own
``SHA256SUMS``, and pip's ``--require-hashes`` still verifies every downloaded
wheel against them.

Usage::

    python -m scripts.glitnir_release --output requirements.txt [--tag v0.1.10]

The resolved tag is printed on stdout.
"""

import argparse
import json
import os
import re
import sys
import urllib.request
from collections.abc import Callable
from pathlib import Path

REPOSITORY = "arnovich/glitnir"
TAG = re.compile(r"v(\d+\.\d+\.\d+)")
SHA256 = re.compile(r"[0-9a-f]{64}")
#: (pip project, wheel file name) of the two wheels every release carries.
WHEELS = (
    ("glitnir", "glitnir-{version}-py3-none-any.whl"),
    ("glitnir-forseti", "glitnir_forseti-{version}-py3-none-any.whl"),
)

Fetch = Callable[[str], bytes]


def fetch(url: str) -> bytes:
    """Read a URL; a token in GH_TOKEN or GITHUB_TOKEN lifts the API rate limit."""
    request = urllib.request.Request(url, headers={"User-Agent": "glitnir-notebooks"})
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if token and url.startswith("https://api.github.com/"):
        request.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def latest_tag(repository: str, fetch: Fetch = fetch) -> str:
    """The tag of the latest published release: never a draft or a pre-release."""
    release = json.loads(fetch(f"https://api.github.com/repos/{repository}/releases/latest"))
    tag = release.get("tag_name") if isinstance(release, dict) else None
    if (
        not isinstance(tag, str)
        or not TAG.fullmatch(tag)
        or release.get("draft")
        or release.get("prerelease")
    ):
        raise ValueError(f"{repository} has no published release with a vX.Y.Z tag")
    return tag


def parse_sums(text: str) -> dict[str, str]:
    """Map each asset name in a SHA256SUMS file to its digest."""
    sums: dict[str, str] = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        digest, _, name = line.partition("  ")
        name = name.strip()
        if not SHA256.fullmatch(digest) or not name:
            raise ValueError(f"Malformed SHA256SUMS line: {line!r}")
        sums[name] = digest
    return sums


def requirements(repository: str, tag: str, sums: dict[str, str]) -> str:
    """Hashed requirements for the release's backend and plugin wheels."""
    match = TAG.fullmatch(tag)
    if not match:
        raise ValueError(f"Expected a vX.Y.Z release tag, got {tag!r}")
    version = match.group(1)
    lines = [f"# Glitnir release {tag}: its wheels, hashed from its SHA256SUMS."]
    for project, pattern in WHEELS:
        name = pattern.format(version=version)
        if name not in sums:
            raise ValueError(f"Release {tag} lists no {name} in SHA256SUMS")
        url = f"https://github.com/{repository}/releases/download/{tag}/{name}"
        lines.append(f"{project} @ {url} --hash=sha256:{sums[name]}")
    return "\n".join(lines) + "\n"


def resolve(repository: str, tag: str | None, fetch: Fetch = fetch) -> tuple[str, str]:
    """Return the release tag and the hashed requirements for its wheels."""
    tag = tag or latest_tag(repository, fetch)
    if not TAG.fullmatch(tag):
        raise ValueError(f"Expected a vX.Y.Z release tag, got {tag!r}")
    sums_url = f"https://github.com/{repository}/releases/download/{tag}/SHA256SUMS"
    return tag, requirements(repository, tag, parse_sums(fetch(sums_url).decode("utf-8")))


def main(argv: list[str] | None = None, fetch: Fetch = fetch) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument(
        "--tag", default="", help="release tag such as v0.1.10 (default: the latest published release)"
    )
    parser.add_argument("--output", required=True, help="requirements file to write")
    parser.add_argument("--repository", default=REPOSITORY, help="GitHub owner/repository")
    args = parser.parse_args(argv)
    tag, text = resolve(args.repository, args.tag.strip() or None, fetch)
    Path(args.output).write_text(text)
    print(tag)
    return 0


if __name__ == "__main__":
    sys.exit(main())
