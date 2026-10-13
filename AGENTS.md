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

Use Python 3.12+, Node 22.22.2 and a built Forseti Lean v1.30.0 checking
environment (Lean 4.32.1, with its pinned Asgard Lean v1.19.0 and Mathlib
dependencies). In that Forseti Lean checkout, run:

```sh
lake build Gimle.Forseti Gimle.Forseti.Examples Gimle.Asgard.Examples Gimle.Asgard.Visualization.Model
```

Then, from this examples checkout:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install --require-hashes --only-binary=:all: -r scripts/gallery/requirements.txt
npm ci --ignore-scripts
npx playwright install chromium
npm test
.venv/bin/python -m scripts.build_gallery --lean-project /absolute/path/to/forseti-lean
npm run gallery:check -- _site
```

Use a new output directory; for another build, pass `--output /path/to/new-site`
and check that same directory. Keep generated HTML and previews uncommitted.
Exports must preserve source/metadata hashes and include every claim, diagram
and retained figure. They read saved observations and draw diagrams without
replaying claims or running simulations. Verify pages offline and at desktop
and mobile widths. Upgrade the pinned Python, Node and Lean export dependencies
together and verify all exports when changing the renderer.
