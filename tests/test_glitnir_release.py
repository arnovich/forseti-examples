"""Resolve a Glitnir release at run time and hash its wheels from SHA256SUMS."""

import io
import json
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from scripts.glitnir_release import latest_tag, main, parse_sums, requirements, resolve

REPOSITORY = "example/glitnir"
SUMS = (
    "2d622bdb73f109017e53e5890d40313f35619d0a201509776ff6d4eb9ec7d99f  glitnir-0.1.9.vsix\n"
    "efffd277dbe4dc1eb46e7001534de3159d514d4a99b7e8a836cfd6b7b042b7b5  glitnir-0.1.9-py3-none-any.whl\n"
    "94a42379281d10b82df91650dc8430c4afe3eb88c051135a512ee799dc1fe058  glitnir_forseti-0.1.9-py3-none-any.whl\n"
    "43d13a81c978214a1f6d573e4002da5b99f81a678fe0048951b120d90d351fbf  INSTALL.md\n"
)


def fake_fetch(latest: dict, sums: str = SUMS):
    """A fetch that serves the release API and SHA256SUMS, remembering its calls."""
    calls: list[str] = []

    def fetch(url: str) -> bytes:
        calls.append(url)
        if url == f"https://api.github.com/repos/{REPOSITORY}/releases/latest":
            return json.dumps(latest).encode()
        if url == f"https://github.com/{REPOSITORY}/releases/download/v0.1.9/SHA256SUMS":
            return sums.encode()
        raise AssertionError(f"unexpected fetch of {url}")

    fetch.calls = calls  # type: ignore[attr-defined]
    return fetch


class ParseSumsTest(unittest.TestCase):
    def test_maps_asset_names_to_digests(self) -> None:
        sums = parse_sums(SUMS)
        self.assertEqual(sums["glitnir-0.1.9-py3-none-any.whl"][:8], "efffd277")
        self.assertEqual(len(sums), 4)

    def test_rejects_malformed_lines(self) -> None:
        with self.assertRaises(ValueError):
            parse_sums("notahash  glitnir-0.1.9-py3-none-any.whl\n")
        with self.assertRaises(ValueError):
            parse_sums("e" * 64 + "\n")


class RequirementsTest(unittest.TestCase):
    def test_pins_both_wheels_of_the_release_by_hash(self) -> None:
        text = requirements(REPOSITORY, "v0.1.9", parse_sums(SUMS))
        lines = [line for line in text.splitlines() if not line.startswith("#")]
        self.assertEqual(
            lines,
            [
                "glitnir @ https://github.com/example/glitnir/releases/download/v0.1.9/"
                "glitnir-0.1.9-py3-none-any.whl --hash=sha256:"
                "efffd277dbe4dc1eb46e7001534de3159d514d4a99b7e8a836cfd6b7b042b7b5",
                "glitnir-forseti @ https://github.com/example/glitnir/releases/download/v0.1.9/"
                "glitnir_forseti-0.1.9-py3-none-any.whl --hash=sha256:"
                "94a42379281d10b82df91650dc8430c4afe3eb88c051135a512ee799dc1fe058",
            ],
        )

    def test_requires_both_wheels_and_a_release_tag(self) -> None:
        sums = parse_sums(SUMS)
        del sums["glitnir_forseti-0.1.9-py3-none-any.whl"]
        with self.assertRaises(ValueError):
            requirements(REPOSITORY, "v0.1.9", sums)
        with self.assertRaises(ValueError):
            requirements(REPOSITORY, "0.1.9", parse_sums(SUMS))
        with self.assertRaises(ValueError):
            requirements(REPOSITORY, "v0.1.8", parse_sums(SUMS))


class LatestTagTest(unittest.TestCase):
    def test_takes_the_latest_published_release(self) -> None:
        fetch = fake_fetch({"tag_name": "v0.1.9", "draft": False, "prerelease": False})
        self.assertEqual(latest_tag(REPOSITORY, fetch), "v0.1.9")

    def test_rejects_drafts_prereleases_and_odd_tags(self) -> None:
        for latest in (
            {"tag_name": "v0.1.9", "draft": True, "prerelease": False},
            {"tag_name": "v0.1.9", "draft": False, "prerelease": True},
            {"tag_name": "nightly", "draft": False, "prerelease": False},
            {},
        ):
            with self.assertRaises(ValueError, msg=repr(latest)):
                latest_tag(REPOSITORY, fake_fetch(latest))


class ResolveTest(unittest.TestCase):
    def test_a_named_tag_skips_the_release_api(self) -> None:
        fetch = fake_fetch({"tag_name": "v9.9.9", "draft": False, "prerelease": False})
        tag, text = resolve(REPOSITORY, "v0.1.9", fetch)
        self.assertEqual(tag, "v0.1.9")
        self.assertIn("glitnir_forseti-0.1.9-py3-none-any.whl", text)
        self.assertEqual(len(fetch.calls), 1)
        self.assertTrue(fetch.calls[0].endswith("/v0.1.9/SHA256SUMS"))

    def test_main_writes_the_requirements_and_prints_the_tag(self) -> None:
        fetch = fake_fetch({"tag_name": "v0.1.9", "draft": False, "prerelease": False})
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "glitnir-requirements.txt"
            stdout = io.StringIO()
            with redirect_stdout(stdout):
                code = main(["--repository", REPOSITORY, "--output", str(output)], fetch)
            self.assertEqual(code, 0)
            self.assertEqual(stdout.getvalue().strip(), "v0.1.9")
            self.assertEqual(output.read_text(), requirements(REPOSITORY, "v0.1.9", parse_sums(SUMS)))
            self.assertEqual(len(fetch.calls), 2)


if __name__ == "__main__":
    unittest.main()
