"""Guard complete, portable gallery inventories and unchanged notebook inputs."""

import tempfile
import unittest
from pathlib import Path

from conftest import make_corpus

from scripts.build_gallery import (
    DRAWING_INPUTS,
    diagram_note,
    drawing_key,
    inventory,
    notebook_hashes,
    source_url,
)


class GalleryTests(unittest.TestCase):
    """Catch omissions, unstable source links and accidental notebook writes."""

    def test_inventory_keeps_topic_and_validates_bundle(self) -> None:
        """An export keeps topic paths and cannot omit an unconfigured notebook."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            self.assertEqual(inventory(root), [notebook])
            self.assertEqual(inventory(root, only=["Example"]), [notebook])
            notebook.with_name("Missing.lean").write_text("-- missing\n")
            with self.assertRaises(ValueError):
                inventory(root)

    def test_inventory_requires_saved_results(self) -> None:
        """A notebook without saved results cannot be published."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root).with_suffix(".glitnir.json").unlink()
            with self.assertRaisesRegex(ValueError, "missing Glitnir results"):
                inventory(root)

    def test_hashes_cover_saved_results(self) -> None:
        """The no-write guard covers more than Lean source alone."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            notebook = make_corpus(root)
            before = notebook_hashes(root)
            results = notebook.with_suffix(".glitnir.json")
            self.assertIn(results.relative_to(root).as_posix(), before)
            results.write_text('{"changed": true}')
            self.assertNotEqual(before, notebook_hashes(root))

    def test_drawing_key_follows_what_lean_reads(self) -> None:
        """Edits above a view or to pins redraw it; edits below it do not."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            make_corpus(root)
            for name in DRAWING_INPUTS:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                if not (root / name).exists():
                    (root / name).write_text(name)
            view = {"line": 2, "kind": "circuit", "name": "c", "using": []}
            text = "def c := 1\n-- @view circuit c\n"
            key = drawing_key(root, text, view)
            self.assertEqual(key, drawing_key(root, text + "-- below\n", view))
            self.assertNotEqual(key, drawing_key(root, "def c := 2\n" + text[11:], view))
            self.assertNotEqual(key, drawing_key(root, text, {**view, "using": ["d"]}))
            (root / "lake-manifest.json").write_text("{}")
            self.assertNotEqual(key, drawing_key(root, text, view))

    def test_diagram_note_is_machine_independent(self) -> None:
        """Unavailable-diagram notes do not leak local paths or long logs."""
        root = Path("/work/examples")
        note = diagram_note(f"Lean failed in {root}/examples/A.lean\nlong log", root)
        self.assertIn("./examples/A.lean", note)
        self.assertNotIn("/work", note)
        self.assertNotIn("long log", note)

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
