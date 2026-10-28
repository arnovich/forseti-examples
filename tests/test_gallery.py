"""Guard complete, portable gallery inventories and unchanged notebook inputs."""

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from conftest import make_corpus, make_original, make_walkthrough

from scripts.build_gallery import (
    DRAWING_INPUTS,
    diagram_note,
    drawing_key,
    inventory,
    notebook_hashes,
    prepare_notebook,
    prepare_walkthrough,
    source_url,
    unchecked_notice,
    walkthrough_inventory,
)


class FakeNotebook:
    """Stand in for Glitnir's SavedNotebook with one view and a fixed drawing."""

    def __init__(self, path: Path, drawing: dict) -> None:
        self.path, self.drawing, self.draws = path, drawing, 0

    def __enter__(self) -> "FakeNotebook":
        return self

    def __exit__(self, *_: object) -> None:
        pass

    def snapshot(self) -> dict:
        text = self.path.read_text()
        view = {"cell": 0, "line": 1, "kind": "circuit", "name": "c", "using": []}
        return {
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "preview": {"recorded": True},
            "views": [{**view, "error": ""}],
            "assets": [],
        }

    def draw_view(self, cell: int, line: int) -> dict:
        self.draws += 1
        return dict(self.drawing)


class FakeWalkthrough(FakeNotebook):
    """Stand in for SavedNotebook on a walkthrough: no results, claims or views."""

    def __init__(self, path: Path) -> None:
        super().__init__(path, {})

    def snapshot(self) -> dict:
        text = self.path.read_text()
        return {
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "preview": {"recorded": True, "notice": "Saved results, shown as recorded."},
            "project_claims": [],
            "views": [],
            "assets": [],
        }


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

    def _prepare(self, drawing: dict, allow: bool) -> tuple[dict, Path, FakeNotebook]:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        notebook = make_corpus(root)
        for name in DRAWING_INPUTS:
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            if not (root / name).exists():
                (root / name).write_text(name)
        cache = root / "cache"
        cache.mkdir()
        fake = FakeNotebook(notebook, drawing)
        with mock.patch("scripts.build_gallery._saved_notebook", return_value=fake):
            return prepare_notebook(notebook, root, cache, allow), cache, fake

    def test_certain_drawing_is_cached(self) -> None:
        """A drawing made in a known environment is reused by later builds."""
        entry, cache, _ = self._prepare({"svg": "<svg/>"}, allow=False)
        self.assertEqual(entry["drawings"]["0:1"], {"svg": "<svg/>"})
        self.assertEqual(len(list(cache.iterdir())), 1)

    def test_uncertain_drawing_fails_unless_allowed_and_is_never_cached(self) -> None:
        """Glitnir's uncertain drawings are not published silently."""
        drawing = {"svg": "<svg/>", "uncertain": True}
        with self.assertRaisesRegex(ValueError, "state could not be read"):
            self._prepare(drawing, allow=False)
        entry, cache, _ = self._prepare(drawing, allow=True)
        self.assertEqual(entry["drawings"]["0:1"], drawing)
        self.assertEqual(entry["diagram_errors"], [])
        self.assertEqual(list(cache.iterdir()), [])

    def test_failed_drawing_becomes_a_note_only_when_allowed(self) -> None:
        """A failure stops the build, or shows a stable note when allowed."""
        with self.assertRaisesRegex(ValueError, "unavailable: boom"):
            self._prepare({"error": "boom"}, allow=False)
        entry, cache, _ = self._prepare({"error": "boom"}, allow=True)
        self.assertEqual(entry["diagram_errors"], ["0:1"])
        self.assertIn("boom", entry["drawings"]["0:1"]["error"])
        self.assertEqual(list(cache.iterdir()), [])

    def _walkthrough(self) -> tuple[Path, Path]:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        base = Path(directory.name)
        root = base / "repo"
        make_corpus(root)
        original, commit = make_original(base / "upstream/formal")
        return root, make_walkthrough(root, original, commit)

    def test_walkthrough_is_shown_unchecked(self) -> None:
        """A walkthrough is exported with no results and an unchecked notice."""
        root, notebook = self._walkthrough()
        with mock.patch(
            "scripts.build_gallery._saved_notebook", return_value=FakeWalkthrough(notebook)
        ):
            entry = prepare_walkthrough(notebook, root)
        self.assertEqual(entry["html"], "walkthroughs/fixture/Fixture.html")
        self.assertEqual(entry["walkthrough"], {"name": "fixture", "map": "walkthroughs/fixture/map.html"})
        notice = entry["snapshot"]["preview"]["notice"]
        self.assertEqual(notice, unchecked_notice(notebook.parent / "outline.json"))
        self.assertTrue(notice.startswith("Unchecked walkthrough."))
        self.assertIn("example.invalid/formal (proj) at commit", notice)
        self.assertNotIn("shown as recorded", notice)
        self.assertEqual((entry["drawings"], entry["diagram_errors"]), ({}, []))

    def test_walkthrough_with_results_or_claims_is_refused(self) -> None:
        """A results file, a saved claim or a view is never published for one."""
        root, notebook = self._walkthrough()
        fake = FakeWalkthrough(notebook)
        for change in ("results", "claims", "views"):
            with self.subTest(change=change):
                snapshot = fake.snapshot()
                if change == "results":
                    notebook.with_suffix(".glitnir.json").write_text("{}")
                else:
                    snapshot[f"project_{change}" if change == "claims" else change] = [{}]
                with mock.patch.object(fake, "snapshot", return_value=snapshot), mock.patch(
                    "scripts.build_gallery._saved_notebook", return_value=fake
                ):
                    with self.assertRaises(ValueError):
                        prepare_walkthrough(notebook, root)
                if change == "results":
                    with self.assertRaisesRegex(ValueError, "no results"):
                        walkthrough_inventory(root)
                    notebook.with_suffix(".glitnir.json").unlink()
        self.assertEqual(walkthrough_inventory(root), [notebook])
        self.assertEqual(walkthrough_inventory(root, only=["Example"]), [])

    def test_hashes_cover_walkthroughs_but_not_fetched_originals(self) -> None:
        """The no-write guard covers walkthroughs; fetched originals are not inputs."""
        root, notebook = self._walkthrough()
        before = notebook_hashes(root)
        self.assertIn("walkthroughs/fixture/Fixture.lean", before)
        self.assertIn("walkthroughs/fixture/outline.json", before)
        self.assertFalse(any("_originals" in path for path in before))
        notebook.write_text(notebook.read_text() + "-- edited\n")
        self.assertNotEqual(before, notebook_hashes(root))

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
