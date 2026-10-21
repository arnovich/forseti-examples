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
[Glitnir 0.1.2](https://github.com/arnovich/glitnir/releases/tag/v0.1.2) or newer.

1. [Install VS Code](https://code.visualstudio.com/docs/getstarted/overview#install-vs-code),
   Python 3.12 or newer and [uv](https://docs.astral.sh/uv/getting-started/installation/).
2. [Install the Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
   and complete its setup guide, which installs elan and the Lean toolchain.
3. Install **Glitnir — Lean Notebooks** from the
   [Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=gimle.glitnir):
   search for it in the Extensions view, or run `code --install-extension gimle.glitnir`.
4. Clone this repository and build its Lean project once, from the repository root:

   ```sh
   lake exe cache get && lake build
   ```

   The first command downloads the prebuilt Mathlib files; the second builds
   Forseti, Asgard and the notebooks. With less than about 32 GB of memory,
   first build the AntitheticFeedback notebook's certificate imports one at a
   time, since Lake would start them together:

   ```sh
   for module in AIFSafety.MeshGeometry AIFSafety.MeshBin{0..7} \
       AIFSafety.CandidateMesh AIFSafety.Cell AIFSafety.Cells.Bin3.Slab100 \
       Gimle.Forseti.Examples.AIFCertifiedCellData; do
     lake build "$module"
   done
   ```
5. Open the folder in VS Code and a Lean file in a trusted workspace. Run
   **Glitnir: Set Up Environment → Set Up**, which downloads, verifies and installs
   Glitnir's backend in one step.
6. Install the Forseti plugin, which draws the diagrams and provides the
   evidence and decision cards: run **Glitnir: Install Extension Package… →
   Forseti → Download from this release**, and answer yes to `z3` if you want to
   run decisions.
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
in one process, and AntitheticFeedback's imports include eight mesh modules of
4.3 to 4.6 GB each, a mesh geometry module of about 5.8 GB and two certificate
cells of about 7 GB. The first check of a
notebook replays Mathlib and Forseti once, which takes about 18 minutes on a
laptop; later checks take a few minutes.

## Examples

| Notebooks | Explore |
| --- | --- |
| [ScalarDecay](examples/basics/ScalarDecay.lean), [ThreeState](examples/basics/ThreeState.lean) | Basic claims, decisions and simulation |
| [AntitheticFeedback](examples/biochemistry/AntitheticFeedback.lean) | A biochemical controller that never overshoots by more than 60%: one certified cell checked, the full proof cited |
| [CircuitProofs](examples/circuits/CircuitProofs.lean), [EnergyOptimization](examples/circuits/EnergyOptimization.lean) | Circuit contracts and rewrites |
| [Fibonacci](examples/circuits/LinearCircuitFibonacci.lean), [Jordan](examples/circuits/LinearCircuitJordan.lean) | Discrete linear circuits |
| [Lorenz](examples/dynamics/Lorenz.lean) | Continuous trajectories and bounds |
| [HedgedSpread](examples/finance/HedgedSpread.lean) | A hedged book under every shock in a band |
| [Laminar](examples/galerkin/NS_Laminar.lean), [T3](examples/galerkin/NS_T3.lean), [K5](examples/galerkin/NS_K5.lean), [B2](examples/galerkin/NS_B2.lean) | Finite-dimensional fluid models, energy and enstrophy |
| [Burgers](examples/pdes/Burgers.lean), [BurgersFronts](examples/pdes/BurgersFronts.lean), [Euler](examples/pdes/Euler.lean), [NavierStokes](examples/pdes/NavierStokes.lean) | Stream and PDE contracts |

The AntitheticFeedback notebook checks the circuit, the composition rule and one
cell of a certified proof, and cites the rest. The full certificate (2,960 cells
and the theorem they assemble into) is the opt-in `AIFSafety` library under
[`certificates/`](certificates/). It is not a default target: `lake build
AIFSafety` takes about 40 hours of processor time, and each cell needs over
7 GB of memory, so build it in chunks, running no more modules at once than you
have about 8 GB of memory for.

Each [gallery entry](https://arnovich.github.io/forseti-examples/) links
to its rendered notebook and exact Lean source revision.

This repository is maintained by its authors and does not accept external contributions.
Licensed under the [MIT License](LICENSE).
