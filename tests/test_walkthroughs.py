"""The walkthrough check: the helper's text check, the maps and no results file.

``StandInHelperTests`` run everywhere with a stand-in for Glitnir's helper.
``PinnedHelperTests`` run the real, pinned helper on a small project; it is
available after ``python3 scripts/fetch_originals.py``. They are skipped
without it, unless ``REQUIRE_WALKTHROUGH_HELPER=1`` (set in CI after the
fetch), where a missing helper fails them.
"""

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from conftest import make_corpus, make_original, make_walkthrough, pin_helper

from scripts.check_walkthroughs import WalkthroughError, check_all, walkthroughs
from scripts.fetch_originals import FetchError, verified_helper

REPOSITORY = Path(__file__).resolve().parents[1]

# Mimics the helper's interface: `check` fails on a claim of a * b = a * b.
STAND_IN = '''import sys
from pathlib import Path
args = sys.argv[1:]
if args[0] == "check":
    if "a * b = a * b" in Path(args[args.index("--notebook") + 1]).read_text():
        print("error: claim theorem1: statement differs")
        sys.exit(1)
    print("ok: 1 nodes, 1 Lean entries, 1 claims")
else:
    out = Path(args[args.index("--out") + 1])
    (out / "assets").mkdir(parents=True, exist_ok=True)
    (out / "assets/map.svg").write_text("<svg/>")
    (out / "map.html").write_text("<p>https://example.invalid/orig</p>")
'''


def _wrong_claim(notebook: Path) -> None:
    """Change the claim so it no longer restates the original's theorem."""
    text = notebook.read_text()
    notebook.write_text(text.replace("a * b = b * a := by", "a * b = a * b := by"))


class _Fixture(unittest.TestCase):
    """A repository with one walkthrough of a local original."""

    def setUp(self) -> None:
        """Create the original, the walkthrough and the pinned helper."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        base = Path(directory.name)
        self.root = base / "repo"
        original, commit = make_original(base / "upstream/formal")
        self.notebook = make_walkthrough(self.root, original, commit)
        self.folder = self.notebook.parent
        self.helper = pin_helper(self.root, self.helper_source(base))
        self.draw_maps()

    def helper_source(self, base: Path) -> Path:
        """Return the helper the fixture pins."""
        raise NotImplementedError

    def draw_maps(self) -> None:
        """Draw the committed maps with the pinned helper, as an author does."""
        subprocess.run(
            [sys.executable, "-I", "-B", str(self.helper), "map",
             str(self.folder / "outline.json"), "--links", "public", "--out", str(self.folder)],
            check=True, capture_output=True,
        )


class StandInHelperTests(_Fixture):
    """The check's own rules, with a stand-in for the helper."""

    def helper_source(self, base: Path) -> Path:
        """Write the stand-in helper."""
        path = base / "stand-in.py"
        path.write_text(STAND_IN)
        return path

    def test_matching_walkthrough_passes(self) -> None:
        """A walkthrough the helper accepts, with its current maps, passes."""
        self.assertEqual(
            check_all(self.root),
            ["walkthroughs/fixture/Fixture.lean: ok: 1 nodes, 1 Lean entries, 1 claims"],
        )

    def test_failing_text_check_fails(self) -> None:
        """The helper's error is reported with the walkthrough's name."""
        _wrong_claim(self.notebook)
        with self.assertRaisesRegex(WalkthroughError, "fixture: walkthrough.py check failed"):
            check_all(self.root)

    def test_outdated_or_missing_map_fails(self) -> None:
        """The maps must be exactly what the helper draws now."""
        for relative in ("map.html", "assets/map.svg"):
            with self.subTest(relative=relative):
                (self.folder / relative).write_text("stale")
                with self.assertRaisesRegex(WalkthroughError, f"{relative} is not what"):
                    check_all(self.root)
                (self.folder / relative).unlink()
                with self.assertRaisesRegex(WalkthroughError, f"{relative} is not what"):
                    check_all(self.root)
                self.draw_maps()

    def test_results_file_is_refused(self) -> None:
        """A walkthrough is unchecked: no results file, anywhere in its folder."""
        for relative in ("Fixture.glitnir.json", "assets/Other.glitnir.json"):
            with self.subTest(relative=relative):
                (self.folder / relative).write_text("{}")
                with self.assertRaisesRegex(WalkthroughError, "no results file"):
                    check_all(self.root)
                (self.folder / relative).unlink()

    def test_helper_must_have_the_pinned_hash(self) -> None:
        """A changed helper is never run."""
        self.helper.write_text(STAND_IN + "\n# changed\n")
        with self.assertRaisesRegex(WalkthroughError, "pinned SHA-256"):
            check_all(self.root)

    def test_original_must_be_at_its_commit(self) -> None:
        """A checkout moved off the outline's commit is refused."""
        checkout = next((self.root / "walkthroughs/_originals").glob("*/formal"))
        shutil.rmtree(checkout)
        with self.assertRaisesRegex(WalkthroughError, "fetch_originals"):
            check_all(self.root)

    def test_one_notebook_with_a_unique_name(self) -> None:
        """A folder needs one notebook, named unlike any other notebook."""
        make_corpus(self.root)
        (self.root / "examples/basics/Example.lean").rename(
            self.root / "examples/basics/Fixture.lean"
        )
        with self.assertRaisesRegex(WalkthroughError, "not unique: Fixture"):
            walkthroughs(self.root)
        shutil.rmtree(self.root / "examples")
        (self.folder / "Second.lean").write_text("-- second\n")
        with self.assertRaisesRegex(WalkthroughError, "exactly one"):
            walkthroughs(self.root)

    def test_local_location_in_map_is_refused(self) -> None:
        """A map drawn with local links names this machine; it is not published."""
        local = self.helper.with_name("local.py")
        local.write_text(STAND_IN.replace("https://example.invalid/orig", "vscode://file/x"))
        self.helper = pin_helper(self.root, local)
        self.draw_maps()
        with self.assertRaisesRegex(WalkthroughError, "local location"):
            check_all(self.root)


def _pinned_helper() -> Path | None:
    """Return this repository's fetched, verified helper, if there is one."""
    try:
        return verified_helper(REPOSITORY)
    except (FetchError, OSError):
        return None


@unittest.skipUnless(
    _pinned_helper() or os.environ.get("REQUIRE_WALKTHROUGH_HELPER") == "1",
    "the pinned walkthrough helper is not fetched; run scripts/fetch_originals.py",
)
class PinnedHelperTests(_Fixture):
    """Glitnir's pinned helper compares the claims with the original's source."""

    def helper_source(self, base: Path) -> Path:
        """Use the fetched helper; fail when it is required but missing."""
        helper = _pinned_helper()
        if helper is None:
            self.fail("REQUIRE_WALKTHROUGH_HELPER=1 but the helper is not fetched")
        return helper

    def test_matching_walkthrough_passes(self) -> None:
        """A claim restating the original's theorem word for word passes."""
        self.assertEqual(
            check_all(self.root),
            ["walkthroughs/fixture/Fixture.lean: ok: 1 nodes, 1 Lean entries, 1 claims"],
        )

    def test_wrong_claim_fails(self) -> None:
        """A claim whose statement differs from the original fails the check."""
        _wrong_claim(self.notebook)
        with self.assertRaisesRegex(WalkthroughError, "claim theorem1: statement"):
            check_all(self.root)


if __name__ == "__main__":
    unittest.main()
