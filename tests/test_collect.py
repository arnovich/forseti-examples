"""Collecting results copies only valid results for this checkout's sources."""

import shutil
import tempfile
import unittest
from pathlib import Path

from conftest import make_corpus

from scripts.check_bundles import check_bundles
from scripts.collect_results import collect


class CollectTests(unittest.TestCase):
    """Copy matching results from another checkout and refuse the rest."""

    def setUp(self) -> None:
        """Create a checked source checkout and a target without results."""
        self.directory = tempfile.TemporaryDirectory()
        base = Path(self.directory.name)
        self.source, self.root = base / "checked", base / "target"
        self.notebook = make_corpus(self.source)
        shutil.copytree(self.source, self.root)
        self.target = self.root / "examples/basics/Example.glitnir.json"
        self.target.unlink()

    def tearDown(self) -> None:
        """Remove both checkouts."""
        self.directory.cleanup()

    def test_copies_matching_results(self) -> None:
        """Valid results for the same source are copied and then pass."""
        self.assertEqual(collect(self.source, self.root), (1, []))
        self.assertEqual(check_bundles(self.root), (1, 1))

    def test_dry_run_copies_nothing(self) -> None:
        """A dry run validates without writing."""
        self.assertEqual(collect(self.source, self.root, dry_run=True), (1, []))
        self.assertFalse(self.target.exists())

    def test_refuses_results_for_other_source(self) -> None:
        """Results of a differently edited notebook are not copied."""
        (self.root / "examples/basics/Example.lean").write_text("-- edited\n")
        copied, skipped = collect(self.source, self.root)
        self.assertEqual(copied, 0)
        self.assertIn("other source", skipped[0])
        self.assertFalse(self.target.exists())

    def test_reports_missing_and_linked_results(self) -> None:
        """Missing or linked results in the source checkout are named."""
        results = self.notebook.with_suffix(".glitnir.json")
        outside = Path(self.directory.name) / "outside.json"
        results.rename(outside)
        self.assertIn("missing", collect(self.source, self.root)[1][0])
        results.symlink_to(outside)
        copied, skipped = collect(self.source, self.root)
        self.assertEqual(copied, 0)
        self.assertIn("linked", skipped[0])

    def test_refuses_own_checkout(self) -> None:
        """Collecting from this checkout itself would be a no-op."""
        with self.assertRaises(ValueError):
            collect(self.root, self.root)


if __name__ == "__main__":
    unittest.main()
