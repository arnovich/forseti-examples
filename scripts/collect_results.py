"""Copy saved Glitnir results from another checkout into this one's examples.

For each configured notebook, the ``<Notebook>.glitnir.json`` beside the same
path in ``SOURCE`` is copied only if it is valid and was recorded for this
checkout's saved notebook source. Nothing in ``SOURCE`` is written. The copied
results are then validated in place, and every notebook still without valid
results is named.

Usage::

    python3 -m scripts.collect_results /path/to/checked/checkout [--dry-run]
"""

import argparse
import shutil
from pathlib import Path

from scripts.check_bundles import (
    ResultsError,
    check_bundles,
    check_results,
    notebook_paths,
    results_path,
    validator,
)


def collect(source: Path, root: Path, dry_run: bool = False) -> tuple[int, list[str]]:
    """Copy every valid, matching results file from ``source`` into ``root``.

    Returns:
        How many files were copied (or would be, for a dry run) and why each
        other notebook's results were not.
    """
    source, root = source.resolve(), root.resolve()
    if source == root:
        raise ValueError("SOURCE is this checkout; nothing to collect")
    copied = 0
    skipped = []
    for notebook in notebook_paths(root):
        relative = results_path(notebook).relative_to(root)
        candidate = source / relative
        if not candidate.resolve().is_relative_to(source) or any(
            path.is_symlink() for path in (candidate, *candidate.parents)
            if path.is_relative_to(source) and path != source
        ):
            skipped.append(f"{relative.as_posix()}: linked or escaping path in SOURCE")
            continue
        try:
            check_results(notebook, candidate)
        except ResultsError as error:
            skipped.append(f"{relative.as_posix()}: {error}")
            continue
        if not dry_run:
            destination = root / relative
            if destination.is_symlink():
                raise ValueError(f"Refusing to replace linked {relative.as_posix()}")
            shutil.copyfile(candidate, destination)
            check_results(notebook)
        copied += 1
    return copied, skipped


def main() -> None:
    """Collect results from a checkout given on the command line."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("source", type=Path, help="checkout whose results to copy")
    parser.add_argument(
        "--dry-run", action="store_true", help="validate only; copy nothing"
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        copied, skipped = collect(args.source, root, args.dry_run)
    except (ValueError, OSError) as error:
        parser.exit(2, f"Collecting results failed: {error}\n")
    verb = "Would copy" if args.dry_run else "Copied"
    print(f"{verb} {copied} results files (validated with {validator()}).")
    for reason in skipped:
        print(f"Not copied: {reason}")
    if not args.dry_run:
        try:
            notebooks, claims = check_bundles(root)
        except (ValueError, OSError) as error:
            parser.exit(1, f"Bundle check failed: {error}\n")
        print(f"All {notebooks} notebooks have valid results ({claims} saved claims).")
    elif skipped:
        parser.exit(1)


if __name__ == "__main__":
    main()
