"""Disposable notebook corpus fixtures for the standard-library test suite."""

import hashlib
import json
from pathlib import Path

SOURCE = "theorem example_claim : True := True.intro\n"


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def results_for(text: str) -> dict:
    """Return minimal Glitnir results recorded for the saved source ``text``."""
    return {
        "format": "glitnir.project-checks/v2",
        "source_sha256": _sha(text),
        "environment": {"fingerprint": "f" * 64, "check": "c" * 64},
        "withheld": None,
        "claims": [
            {
                "name": "example_claim",
                "status": "checked",
                "axioms": [],
                "start_line": 1,
                "end_line": 1,
                "declaration_sha256": _sha(text.rstrip("\n")),
                "prefix_sha256": _sha(text.rstrip("\n")),
                "proposition_sha256": "p" * 64,
            }
        ],
    }


def make_corpus(root: Path) -> Path:
    """Create one configured notebook with its saved Glitnir results."""
    directory = root / "examples/basics"
    directory.mkdir(parents=True)
    notebook = directory / "Example.lean"
    notebook.write_text(SOURCE)
    (root / "lakefile.toml").write_text(
        'name = "examples"\ndefaultTargets = ["Example"]\n'
        '[[lean_lib]]\nname = "Example"\nsrcDir = "examples/basics"\n'
    )
    (root / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packagesDir": ".lake/packages",
                "packages": [{"name": "forseti", "type": "git", "rev": "a" * 40}],
            }
        )
    )
    notebook.with_suffix(".glitnir.json").write_text(json.dumps(results_for(SOURCE)))
    return notebook


def add_certificate_library(root: Path, default: bool = False) -> Path:
    """Add an opt-in certificate library with a root and one submodule."""
    library = root / "certificates"
    (library / "Certified").mkdir(parents=True)
    (library / "Certified.lean").write_text("import Certified.Main\n")
    (library / "Certified/Main.lean").write_text(SOURCE)
    config = root / "lakefile.toml"
    text = config.read_text()
    if default:
        text = text.replace('defaultTargets = ["Example"]', 'defaultTargets = ["Example", "Certified"]')
    config.write_text(
        text + '[[lean_lib]]\nname = "Certified"\nsrcDir = "certificates"\n'
        'globs = ["Certified.*"]\n'
    )
    return library
