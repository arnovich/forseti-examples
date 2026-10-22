# Forseti examples

For notebook authoring, use Glitnir's `glitnir-notebooks` skill. Install it with
**Glitnir: Set Up Coding Agent**, as described in [getting started](README.md#getting-started).

Keep notebook names unique and update the Lake configuration and README catalog
when adding or moving examples.

Run the repository checks with Python 3.12 or newer:

```sh
python3 -m unittest discover -s tests -v
python3 scripts/check_bundles.py
```

Every notebook needs a committed `<Notebook>.glitnir.json` whose recorded
source SHA-256 matches the saved notebook. The bundle check validates it with
Glitnir's record loader when the Glitnir backend is importable, otherwise
structurally. After rechecking notebooks in another checkout, copy their results
here with `python3 -m scripts.collect_results /path/to/that/checkout` (add
`--dry-run` to validate only), then commit each results file by its path.

To recheck notebooks, use the `Notebook recheck` workflow. On pull requests it
rechecks only what changed: `scripts/select_recheck.py` takes
`git diff --name-only <base>...HEAD` and selects the notebooks whose `.lean`
source changed plus those that import them (through `import` lines and the
lakefile's libraries). A change to `lean-toolchain`, `lake-manifest.json`,
`lakefile.toml`, the gallery or recheck requirements, `scripts/recheck.py`,
`scripts/select_recheck.py` or the workflow rechecks all; results files and
docs recheck nothing, and the workflow's `.lean` paths filter does not even
start it for a pull request without `.lean` changes. When nothing is selected
the job succeeds with a summary line and builds no Lean. Manual dispatch takes
an optional `only` list (empty means all), on Linux with the gallery's pinned
Glitnir. Because the diff is against the pull request's base, a results commit
on top of a source change rechecks that notebook again. `python -m scripts.recheck` checks each notebook
through Glitnir's preview service, decides out-of-date decisions again
(replacing an earlier decision's block the way **Accept** inserts it), runs
out-of-date evidence again and draws every view so its drawing is saved. The
workflow never pushes: it uploads the results, `recheck.patch` and a
per-notebook report (`report.md`, also the job summary) that lists every claim
whose status changed. Review the report, apply the patch and commit each file
by its path. Results saved on one machine read as out of date in another
checkout: Glitnir's environment fingerprint includes Lake traces that name
each locally built module's absolute source path. The gallery and the bundle
check compare the saved source only, so they are unaffected.

For Lean source or Lake configuration changes, also run `lake build`. Bundle
checks and editor builds do not replay notebook claims. Use Glitnir's installed
skill for checking and metadata handling; preserve pinned dependencies unless
an upgrade is intentional.

## Gallery maintenance

The `Notebook gallery` workflow builds on main pushes, pull requests and manual
dispatch. It retains preview artifacts and deploys Pages only from public main.
To activate publication, set **Settings → Pages → Source → GitHub Actions** and
run the workflow. Restrict the `github-pages` environment to `main`. Update README
gallery/image URLs if the repository name or owner changes.

The gallery uses the Glitnir v0.1.5 backend and renderer and the Forseti view
provider, pinned by hash in `scripts/gallery/requirements.txt`. Use Python 3.12+,
Node 22.22.2, Lean 4.35.0 and a working sandbox (bubblewrap on Linux). Diagrams are
drawn in this project's own Lake environment, so first build the modules they
import, from this checkout:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install --require-hashes --only-binary=:all: -r scripts/gallery/requirements.txt
lake exe cache get
lake build $(.venv/bin/python -m scripts.build_gallery --list-diagram-imports)
npm ci --ignore-scripts
npx playwright install chromium
npm test
.venv/bin/python -m scripts.build_gallery
npm run gallery:check -- _site
```

Use a new output directory; for another build, pass `--output /path/to/new-site`
and check that same directory. Keep generated HTML and previews uncommitted.
Exports go through Glitnir's static export (`SavedNotebook`) and its renderer's
Export HTML, from the committed sources and saved results; they check no claim,
run no evidence or decision, and write nothing beside the notebooks. Pages show
Glitnir's "Saved results, shown as recorded" state, and each results file must
be for that exact source. A diagram that cannot be drawn, or that Glitnir drew
while a dependency's state could not be read ("uncertain"), fails the build
and is not cached; `--allow-diagram-errors` shows a note instead, and `--only NAME`
exports a subset for local previews. Verify pages offline and at desktop and
mobile widths. Upgrade the pinned Python, Node and Lean export dependencies
together and verify all exports when changing the renderer.
