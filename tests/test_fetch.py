"""Fetching originals and the helper, from local repositories and files only."""

import hashlib
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from conftest import git, make_original, outline_for

from scripts.fetch_originals import (
    ALLOW_FILE_REPOSITORIES,
    FetchError,
    checked_out_commit,
    checkout_directory,
    fetch_all,
    fetch_helper,
    helper_path,
    helper_pin,
    project_of,
    verified_helper,
)


class FetchTests(unittest.TestCase):
    """Check out each outline's commit once and pin the helper by its hash."""

    def setUp(self) -> None:
        """Create an original repository, a walkthrough of it and a helper."""
        # The local fixture repositories are file:// URLs, allowed for tests only.
        patcher = mock.patch.dict(os.environ, {ALLOW_FILE_REPOSITORIES: "1"})
        patcher.start()
        self.addCleanup(patcher.stop)
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        base = Path(directory.name)
        self.original, self.commit = make_original(base / "upstream/formal")
        self.repository = f"file://{self.original}"
        self.root = base / "repo"
        self.write_outline("one", self.repository, self.commit)
        self.helper = base / "served" / ("b" * 40) / "walkthrough.py"
        self.helper.parent.mkdir(parents=True)
        self.helper.write_text("print('ok: helper')\n")
        self.url = f"file://{base}/served/{{commit}}/walkthrough.py"
        self.pin(hashlib.sha256(self.helper.read_bytes()).hexdigest())

    def write_outline(self, name: str, repository: str, commit: str, **project: str) -> Path:
        """Write ``walkthroughs/<name>/outline.json``."""
        outline = outline_for(repository, commit)
        outline["project"].update(project)
        path = self.root / "walkthroughs" / name / "outline.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(outline))
        return path

    def pin(self, sha256: str) -> None:
        """Pin the helper at commit b…b with ``sha256``."""
        (self.root / "scripts").mkdir(exist_ok=True)
        (self.root / "scripts/walkthrough-script.txt").write_text(
            f"# comment\ncommit {'b' * 40}\nsha256 {sha256}\n"
        )

    def test_checks_out_the_outline_commit_and_reuses_it(self) -> None:
        """A shallow checkout at the commit, where project.root points."""
        checkouts = fetch_all(self.root, self.url)
        expected = self.root / "walkthroughs/_originals" / self.commit[:12] / "formal"
        self.assertEqual(checkouts, [expected])
        self.assertEqual(checked_out_commit(expected), self.commit)
        self.assertTrue((expected / "proj/Main.lean").is_file())
        self.assertEqual(git("-C", str(expected), "rev-list", "--count", "HEAD"), "1")
        # Present at its commit: reused without fetching again.
        (expected / "marker").write_text("kept")
        fetch_all(self.root, self.url)
        self.assertTrue((expected / "marker").exists())

    def test_one_checkout_per_distinct_commit(self) -> None:
        """Two walkthroughs of one commit share a checkout; another commit gets its own."""
        (self.original / "proj/Main.lean").write_text("-- changed\n")
        git("-C", str(self.original), "commit", "-q", "-am", "second")
        second = git("-C", str(self.original), "rev-parse", "HEAD")
        self.write_outline("two", self.repository, self.commit)
        self.write_outline("three", self.repository, second)
        checkouts = fetch_all(self.root, self.url)
        self.assertEqual(len(checkouts), 2)
        self.assertEqual({checked_out_commit(path) for path in checkouts}, {self.commit, second})
        for path in checkouts:
            self.assertEqual(git("-C", str(path), "rev-list", "--count", "HEAD"), "1")
        self.assertEqual(
            (checkout_directory(self.root, project_of(
                self.root / "walkthroughs/three/outline.json")) / "proj/Main.lean").read_text(),
            "-- changed\n",
        )

    def test_project_root_must_name_the_checkout(self) -> None:
        """An outline pointing elsewhere is refused before anything is fetched."""
        self.write_outline("one", self.repository, self.commit, root="../elsewhere/proj")
        with self.assertRaisesRegex(FetchError, "project.root must be"):
            fetch_all(self.root, self.url)
        self.assertFalse((self.root / "walkthroughs/_originals").exists())

    def test_unreachable_repository_is_an_error(self) -> None:
        """A failed fetch (the network, here a missing repository) is an error."""
        self.write_outline("one", self.repository + "-missing", self.commit)
        with self.assertRaises(FetchError):
            fetch_all(self.root, self.url)
        checkout = self.root / "walkthroughs/_originals" / self.commit[:12]
        self.assertEqual(list(checkout.iterdir()), [])

    def test_unknown_commit_is_an_error(self) -> None:
        """A commit the repository does not have is not silently replaced."""
        self.write_outline("one", self.repository, "c" * 40)
        with self.assertRaises(FetchError):
            fetch_all(self.root, self.url)

    def test_other_checkout_in_the_way_is_refused(self) -> None:
        """A folder at the checkout path that is not that commit is not reused."""
        project = project_of(self.root / "walkthroughs/one/outline.json")
        checkout_directory(self.root, project).mkdir(parents=True)
        with self.assertRaisesRegex(FetchError, "remove it"):
            fetch_all(self.root, self.url)

    def test_file_repositories_need_the_test_flag(self) -> None:
        """Outside tests, a repository must be an https:// URL."""
        with mock.patch.dict(os.environ, {ALLOW_FILE_REPOSITORIES: ""}):
            with self.assertRaisesRegex(FetchError, "https://"):
                fetch_all(self.root, self.url)
            self.write_outline("one", "https://example.invalid/formal", self.commit)
            self.assertEqual(
                project_of(self.root / "walkthroughs/one/outline.json").name, "formal"
            )

    def test_repository_name_is_a_plain_folder_name(self) -> None:
        """The checkout folder is the repository's name: no dots-only or odd names."""
        for repository in (
            "https://example.invalid/..",
            "https://example.invalid/.",
            "https://example.invalid/a%2Fb",
            "https://example.invalid/a b",
            "https://example.invalid/",
            "https://example.invalid/.git",
        ):
            with self.subTest(repository=repository):
                path = self.write_outline("one", repository, self.commit)
                with self.assertRaisesRegex(FetchError, "repository"):
                    project_of(path)

    def test_outline_needs_a_full_commit_and_url(self) -> None:
        """Abbreviated commits and other URL schemes are refused."""
        for project in ({"commit": self.commit[:7]}, {"repository": "ssh://host/repo"}):
            with self.subTest(project=project):
                outline = outline_for(self.repository, self.commit)
                outline["project"].update(project)
                path = self.root / "walkthroughs/one/outline.json"
                path.write_text(json.dumps(outline))
                with self.assertRaises(FetchError):
                    project_of(path)

    def test_helper_is_kept_only_with_the_pinned_hash(self) -> None:
        """The downloaded helper must have the pinned SHA-256."""
        with self.assertRaisesRegex(FetchError, "missing"):
            verified_helper(self.root)
        path = fetch_helper(self.root, self.url)
        self.assertEqual(path, helper_path(self.root, helper_pin(self.root)))
        self.assertEqual(verified_helper(self.root), path)
        path.write_text("tampered\n")
        with self.assertRaisesRegex(FetchError, "pinned SHA-256"):
            verified_helper(self.root)
        self.assertEqual(fetch_helper(self.root, self.url).read_bytes(), self.helper.read_bytes())
        self.pin("0" * 64)
        path.unlink()
        with self.assertRaisesRegex(FetchError, "pinned SHA-256"):
            fetch_helper(self.root, self.url)
        self.assertFalse(path.exists())

    def test_unreachable_helper_is_an_error(self) -> None:
        """A failed helper download is an error."""
        with self.assertRaisesRegex(FetchError, "cannot download"):
            fetch_helper(self.root, self.url.replace("served", "missing"))


if __name__ == "__main__":
    unittest.main()
