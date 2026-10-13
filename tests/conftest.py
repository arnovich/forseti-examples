"""Disposable notebook corpus fixtures for the standard-library test suite."""

import json
from pathlib import Path


def make_corpus(root: Path) -> Path:
    """Create one configured notebook with its metadata and retained artifact."""
    directory = root / "examples/basics"
    directory.mkdir(parents=True)
    notebook = directory / "Example.lean"
    notebook.write_text("theorem example_claim : True := True.intro\n")
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
    artifact = directory / ".Example.forseti/artifacts/test.artifact.json"
    artifact.parent.mkdir(parents=True)
    artifact.write_text("{}\n")
    notebook.with_suffix(".forseti.json").write_text(
        json.dumps(
            {"runs": [{"artifact": {"artifact": str(artifact.relative_to(directory))}}]}
        )
    )
    return notebook
