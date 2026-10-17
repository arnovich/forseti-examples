# Forseti Examples

A collection of Lean notebooks exploring formal proofs of the properties of dynamical systems using the [Forseti](https://github.com/arnovich/forseti-lean) program logic and proof system for dynamical systems.

The notebooks are written in the [Glitnir](https://github.com/arnovich/glitnir) style for Lean notebooks, making them richer and easier to read than your standard Lean file.

In the [notebook gallery](https://arnovich.github.io/forseti-examples/) you can see rendered HTML snapshots of all the examples without installing Lean or Glitnir.

| A model in motion | How circuits compose |
| --- | --- |
| [![ThreeState notebook preview](https://arnovich.github.io/forseti-examples/previews/ThreeState.png)](https://arnovich.github.io/forseti-examples/basics/ThreeState.html) | [![CircuitProofs notebook preview](https://arnovich.github.io/forseti-examples/previews/CircuitProofs.png)](https://arnovich.github.io/forseti-examples/circuits/CircuitProofs.html) |

## Getting started

The best experience is to use [Glitnir](https://github.com/arnovich/glitnir) with VS Code
and Lean for VS Code, on local macOS or Linux. These steps use
[Glitnir v0.1.0](https://github.com/arnovich/glitnir/releases/tag/v0.1.0); take every
Glitnir file from that one release.

1. [Install VS Code](https://code.visualstudio.com/docs/getstarted/overview#install-vs-code),
   Python 3.12 or newer and [uv](https://docs.astral.sh/uv/getting-started/installation/).
2. [Install the Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
   and complete its setup guide, which installs elan and the Lean toolchain.
3. Download `glitnir-0.1.0.vsix` from the [release](https://github.com/arnovich/glitnir/releases/tag/v0.1.0)
   and run **Extensions: Install from VSIX…** in VS Code.
4. Clone this repository and build its Lean project once, from the repository root:

   ```sh
   lake exe cache get && lake build
   ```

   The first command downloads the prebuilt Mathlib files; the second builds
   Forseti, Asgard and the notebooks.
5. Open the folder in VS Code and a Lean file in a trusted workspace. Run
   **Glitnir: Set Up Environment → Install Backend with uv → Download matching backend**
   and confirm the location.
6. Install the Forseti plugin, which draws the diagrams and provides the
   evidence and decision cards. Download `glitnir_forseti-0.1.0-py3-none-any.whl`
   and `SHA256SUMS` from the same [release](https://github.com/arnovich/glitnir/releases/tag/v0.1.0),
   and verify the wheel in the download folder:

   ```sh
   shasum -a 256 -c --ignore-missing SHA256SUMS   # Linux: sha256sum -c --ignore-missing SHA256SUMS
   ```

   Then run **Glitnir: Install Extension Package…**, select the wheel, and
   choose the `z3` extra if you want to run decisions.
7. Open [ScalarDecay.lean](examples/basics/ScalarDecay.lean), run
   **Glitnir: Open in Glitnir**, then try [ThreeState](examples/basics/ThreeState.lean).
   Each notebook's saved check results are in `<Notebook>.glitnir.json` beside it;
   **Check saved file** checks it again.

For coding-agent assistance, run **Glitnir: Set Up Coding Agent**, select this
workspace and your agent, and install the bundled `glitnir-notebooks` skill.
Start a new agent session and ask it to use that skill. See
[Glitnir's agent setup](https://github.com/arnovich/glitnir#coding-agents) for details.

**Note:** Plan for several GB of free disk space: the Mathlib files and the
project build take several GB, and Glitnir keeps copies of the toolchain and
compiled imports it checks against in its own artifact store in your user cache
(`glitnir/artifacts`; delete it at any time to free the space). Full builds and
checks also need substantial memory; a measured K5 build used about 10 GB of RAM
in one process. The first check of a notebook replays Mathlib and Forseti once,
which takes about 18 minutes on a laptop; later checks take a few minutes.

## Examples

| Notebooks | Explore |
| --- | --- |
| [ScalarDecay](examples/basics/ScalarDecay.lean), [ThreeState](examples/basics/ThreeState.lean) | Basic claims, decisions and simulation |
| [CircuitProofs](examples/circuits/CircuitProofs.lean), [EnergyOptimization](examples/circuits/EnergyOptimization.lean) | Circuit contracts and rewrites |
| [Fibonacci](examples/circuits/LinearCircuitFibonacci.lean), [Jordan](examples/circuits/LinearCircuitJordan.lean) | Discrete linear circuits |
| [Lorenz](examples/dynamics/Lorenz.lean) | Continuous trajectories and bounds |
| [Laminar](examples/galerkin/NS_Laminar.lean), [T3](examples/galerkin/NS_T3.lean), [K5](examples/galerkin/NS_K5.lean), [B2](examples/galerkin/NS_B2.lean) | Finite-dimensional fluid models, energy and enstrophy |
| [Burgers](examples/pdes/Burgers.lean), [BurgersFronts](examples/pdes/BurgersFronts.lean), [Euler](examples/pdes/Euler.lean), [NavierStokes](examples/pdes/NavierStokes.lean) | Stream and PDE contracts |

Each [gallery entry](https://arnovich.github.io/forseti-examples/) links
to its rendered notebook and exact Lean source revision.

This repository is maintained by its authors and does not accept external contributions.
Licensed under the [MIT License](LICENSE).
