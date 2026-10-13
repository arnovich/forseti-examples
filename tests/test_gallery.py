"""Guard complete, portable gallery inventories and unchanged notebook inputs."""

import tempfile
import unittest
from pathlib import Path

from conftest import make_corpus

from scripts.build_gallery import inventory, notebook_hashes, source_url


class GalleryTests(unittest.TestCase):
    """Catch omissions, unstable source links and accidental notebook writes."""

    def test_inventory_keeps_topic_and_validates_bundle(self) -> None:
        """An export keeps topic paths and cannot omit an unconfigured notebook."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            self.assertEqual(inventory(root), [notebook])
            notebook.with_name("Missing.lean").write_text("-- missing\n")
            with self.assertRaises(ValueError):
                inventory(root)

    def test_hashes_cover_metadata_and_hidden_artifacts(self) -> None:
        """The no-write guard covers more than Lean source alone."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            before = notebook_hashes(root)
            artifact = next(notebook.parent.glob(".Example.forseti/artifacts/*"))
            artifact.write_text('{"changed": true}')
            self.assertNotEqual(before, notebook_hashes(root))
            self.assertIn(notebook.with_suffix(".forseti.json").relative_to(root).as_posix(), before)

    def test_source_link_is_revision_bound(self) -> None:
        """Published pages point to the exact source that produced them."""
        self.assertEqual(
            source_url("owner/examples", "a" * 40, "examples/basics/My File.lean"),
            "https://github.com/owner/examples/blob/" + "a" * 40
            + "/examples/basics/My%20File.lean",
        )
        for repository, revision in (("../secret", "a" * 40), ("owner/repo", "main")):
            with self.assertRaises(ValueError):
                source_url(repository, revision, "examples/basics/Test.lean")


if __name__ == "__main__":
    unittest.main()
