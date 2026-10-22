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

The gallery uses the Glitnir v0.1.2 backend and renderer and the Forseti view
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
