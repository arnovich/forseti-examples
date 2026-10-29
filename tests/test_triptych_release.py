"""Release-matrix guards for the proved/refuted/unresolved triptych."""

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.check_triptych import ReleaseError, check_release


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class TriptychReleaseTests(unittest.TestCase):
    """A composite receipt binds directives, saved decisions and exact files."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "examples/dynamics").mkdir(parents=True)
        self.source = self.root / "examples/dynamics/Demo.lean"
        text = (
            "-- @decide proved : trajectory demo observe V always : V <= 2\n"
            "-- @decide refuted : trajectory demo observe V always : V <= 0\n"
            "-- @decide unresolved : trajectory demo observe V always : V <= 1\n"
        )
        self.source.write_text(text)
        key = lambda line: _sha(f"{line}\n0".encode())
        lines = text.splitlines()
        checked = {
            "status": "checked",
            "message": "checked",
            "axioms": ["propext"],
            "type": "True",
        }
        decisions = {
            key(lines[0]): self._entry("proven", "proved", checked),
            key(lines[1]): self._entry(
                "refuted",
                "refuted_refuted",
                {**checked, "type": "Not False"},
            ),
            key(lines[2]): self._entry("unknown", None, None),
        }
        results = {
            "format": "glitnir.project-checks/v2",
            "source_sha256": _sha(text.encode()),
            "environment": {"fingerprint": "f" * 64, "check": "c" * 64},
            "withheld": None,
            "claims": [],
            "decisions": decisions,
        }
        result_path = self.source.with_suffix(".glitnir.json")
        result_path.write_text(json.dumps(results, sort_keys=True))
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.1\n")
        (self.root / "lake-manifest.json").write_text(
            json.dumps(
                {
                    "packages": [
                        {"name": "forseti", "rev": "a" * 40},
                        {"name": "asgard", "rev": "b" * 40},
                    ]
                }
            )
        )
        self.manifest = self.root / "release.json"
        self.manifest.write_text(
            json.dumps(
                {
                    "format": "glitnir.triptych-release/v1",
                    "glitnir_tag": "v0.1.10",
                    "lean_toolchain": "leanprover/lean4:v4.32.1",
                    "lake_pins": {"forseti": "a" * 40, "asgard": "b" * 40},
                    "notebooks": [
                        {
                            "source": "examples/dynamics/Demo.lean",
                            "source_sha256": _sha(text.encode()),
                            "results_sha256": _sha(result_path.read_bytes()),
                            "environment": {"fingerprint": "f" * 64, "check": "c" * 64},
                            "model": "demo",
                            "observation": "V",
                            "decisions": [
                                self._decision("proved", lines[0], "proven", "True"),
                                self._decision("refuted", lines[1], "refuted", "Not False"),
                                self._decision("unresolved", lines[2], "unknown", None),
                            ],
                        }
                    ],
                },
                indent=2,
            )
            + "\n"
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def _entry(status: str, theorem: str | None, verification: dict | None) -> dict:
        block = None if theorem is None else f"theorem {theorem} : True := by trivial"
        return {
            "prefix_sha256": "p" * 64,
            "fingerprint": "f" * 64,
            "provider": "forseti",
            "created": "2026-10-29T08:00:00+00:00",
            "outcome": {
                "status": status,
                "reason": "bounded search completed",
                "stages": [["lane", status, "exact"]],
                "block": block,
                "theorem": theorem,
            },
            "verification": verification,
        }

    @staticmethod
    def _decision(name: str, directive: str, outcome: str, verification_type: str | None) -> dict:
        return {
            "name": name,
            "directive": directive,
            "outcome": outcome,
            "verification_type_sha256": (
                _sha(verification_type.encode()) if verification_type is not None else None
            ),
            "axioms": [] if outcome == "unknown" else ["propext"],
        }

    def test_accepts_exact_composite_receipt(self) -> None:
        self.assertEqual(check_release(self.root, self.manifest), 3)

    def test_rejects_missing_unknown_receipt(self) -> None:
        results = json.loads(self.source.with_suffix(".glitnir.json").read_text())
        results["decisions"].pop(next(reversed(results["decisions"])))
        self.source.with_suffix(".glitnir.json").write_text(json.dumps(results))
        with self.assertRaisesRegex(ReleaseError, "results SHA-256"):
            check_release(self.root, self.manifest)

    def test_rejects_sorry_in_refutation(self) -> None:
        results_path = self.source.with_suffix(".glitnir.json")
        results = json.loads(results_path.read_text())
        refuted = next(
            entry for entry in results["decisions"].values() if entry["outcome"]["status"] == "refuted"
        )
        refuted["verification"]["axioms"].append("sorryAx")
        results_path.write_text(json.dumps(results, sort_keys=True))
        manifest = json.loads(self.manifest.read_text())
        manifest["notebooks"][0]["results_sha256"] = _sha(results_path.read_bytes())
        manifest["notebooks"][0]["decisions"][1]["axioms"].append("sorryAx")
        self.manifest.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ReleaseError, "sorryAx"):
            check_release(self.root, self.manifest)


if __name__ == "__main__":
    unittest.main()
