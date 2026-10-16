# Forseti Examples

A collection of Lean notebooks exploring formal proofs of the properties of dynamical systems using the [Forseti](https://github.com/arnovich/forseti-lean) program logic and proof system for dynamical systems.

The notebooks are written in the [Glitnir](https://github.com/arnovich/glitnir) style for Lean notebooks, making them richer and easier to read than your standard Lean file.

In the [notebook gallery](https://arnovich.github.io/forseti-examples/) you can see rendered HTML snapshots of all the examples without installing Lean or Glitnir.

| A model in motion | How circuits compose |
| --- | --- |
| [![ThreeState notebook preview](https://arnovich.github.io/forseti-examples/previews/ThreeState.png)](https://arnovich.github.io/forseti-examples/basics/ThreeState.html) | [![CircuitProofs notebook preview](https://arnovich.github.io/forseti-examples/previews/CircuitProofs.png)](https://arnovich.github.io/forseti-examples/circuits/CircuitProofs.html) |

## Getting started

The best experience is to use Glitnir combined with VS Code and Lean for VS Code:

1. [Install VS Code](https://code.visualstudio.com/docs/getstarted/overview#install-vs-code).
2. [Install the Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
   and complete its setup guide, which installs elan and the Lean toolchain.
3. [Install Glitnir](https://github.com/arnovich/glitnir#install).

4. Clone this repository and open the folder in VS Code.
5. Open a Lean file in a trusted workspace. Run **Glitnir: Set Up Environment →
   Install Backend with uv → Download matching backend** and confirm the location.
   Use the VSIX and backend from the same release.
6. Open [ScalarDecay.lean](examples/basics/ScalarDecay.lean), run
   **Glitnir: Open in Glitnir**, then try [ThreeState](examples/basics/ThreeState.lean).

For coding-agent assistance, run **Glitnir: Set Up Coding Agent**, select this
workspace and your agent, and install the bundled `glitnir-notebooks` skill.
Start a new agent session and ask it to use that skill. See
[Glitnir's agent setup](https://github.com/arnovich/glitnir#coding-agents) for details.

**Note:** Full Lean builds need substantial disk space and
memory; a measured K5 build used about 10 GB of RAM in one process.

## Examples

| Notebooks | Explore |
| --- | --- |
| [ScalarDecay](examples/basics/ScalarDecay.lean), [ThreeState](examples/basics/ThreeState.lean) | Basic claims, decisions and simulation |
| [CircuitProofs](examples/circuits/CircuitProofs.lean), [EnergyOptimization](examples/circuits/EnergyOptimization.lean) | Circuit contracts and rewrites |
| [Fibonacci](examples/circuits/LinearCircuitFibonacci.lean), [Jordan](examples/circuits/LinearCircuitJordan.lean) | Discrete linear circuits |
| [Lorenz](examples/dynamics/Lorenz.lean) | Continuous trajectories and bounds |
| [HedgedSpread](examples/finance/HedgedSpread.lean) | A hedged book under every shock in a band |
| [Laminar](examples/galerkin/NS_Laminar.lean), [T3](examples/galerkin/NS_T3.lean), [K5](examples/galerkin/NS_K5.lean), [B2](examples/galerkin/NS_B2.lean) | Finite-dimensional fluid models, energy and enstrophy |
| [Burgers](examples/pdes/Burgers.lean), [BurgersFronts](examples/pdes/BurgersFronts.lean), [Euler](examples/pdes/Euler.lean), [NavierStokes](examples/pdes/NavierStokes.lean) | Stream and PDE contracts |

Each [gallery entry](https://arnovich.github.io/forseti-examples/) links
to its rendered notebook and exact Lean source revision.

This repository is maintained by its authors and does not accept external contributions.
Licensed under the [MIT License](LICENSE).
