"""Bundle validation must fail rather than silently lose corpus coverage."""

import json
import tempfile
import unittest
from pathlib import Path

from conftest import make_corpus

from scripts.check_bundles import check_bundles


class BundleTests(unittest.TestCase):
    """Validate complete nested bundles and reject missing or escaping inputs."""

    def test_nested_bundle(self) -> None:
        """Resolve retained paths relative to the notebook, not the repo root."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            self.assertEqual(check_bundles(root), (1, 1))

    def test_missing_metadata(self) -> None:
        """Every configured source needs its metadata."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root).with_suffix(".forseti.json").unlink()
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_unconfigured_source(self) -> None:
        """An omitted Lake target cannot silently reduce coverage."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            notebook.with_name("Omitted.lean").write_text("-- omitted\n")
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_duplicate_name(self) -> None:
        """Two topics cannot ambiguously identify one notebook."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            (root / notebook.name).write_bytes(notebook.read_bytes())
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_missing_artifact(self) -> None:
        """A broken retained artifact reference is an error."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            next(notebook.parent.glob(".Example.forseti/artifacts/*")).unlink()
            with self.assertRaises(ValueError):
                check_bundles(root)

    def test_artifact_cannot_escape(self) -> None:
        """Reject absolute paths, traversal and symlinks outside the corpus."""
        for mode in ("absolute", "traversal", "symlink"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                outside = Path(directory) / "secret.json"
                outside.write_text("{}")
                root = Path(directory) / "repo"
                notebook = make_corpus(root)
                relative = "../../../secret.json"
                if mode == "absolute":
                    relative = str(outside)
                elif mode == "symlink":
                    (notebook.parent / "escape.json").symlink_to(outside)
                    relative = "escape.json"
                notebook.with_suffix(".forseti.json").write_text(
                    json.dumps({"runs": [{"artifact": {"artifact": relative}}]})
                )
                with self.assertRaises(ValueError):
                    check_bundles(root)

    def test_build_dependencies_are_not_examples(self) -> None:
        """Do not discover dependency sources in .lake."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            dependency = root / ".lake/packages/Dependency.lean"
            dependency.parent.mkdir(parents=True)
            dependency.write_text("-- dependency\n")
            self.assertEqual(check_bundles(root), (1, 1))

    def test_internal_symlink_is_rejected(self) -> None:
        """Match the runtime's refusal of linked sources, even inside the repo."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            original = notebook.rename(notebook.with_suffix(".original"))
            notebook.symlink_to(original)
            with self.assertRaises(ValueError):
                check_bundles(root)


if __name__ == "__main__":
    unittest.main()
