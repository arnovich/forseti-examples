import Gimle.Forseti
import Mathlib.Tactic.Linarith

/-!
# Following a proof through a circuit

Conditions belong to the wires. This circuit doubles a value, then triples it.
The three Hoare theorems identify what is known before, between and after those
components. Use **Conditions** to hide the labels, or select one triple to inspect
its component. Click a wire label to see the predicate and its theorem.
-/

namespace Notebook.CircuitProofs
open Gimle.Asgard Gimle.Forseti

def P : Predicate 1 := ⟨fun x => 0 ≤ x 0 ∧ x 0 ≤ 1⟩
def M : Predicate 1 := ⟨fun x => 0 ≤ x 0 ∧ x 0 ≤ 2⟩
def Q : Predicate 1 := ⟨fun x => 0 ≤ x 0 ∧ x 0 ≤ 6⟩
def double : Circuit 1 1 := .scalar 2
def triple : Circuit 1 1 := .scalar 3
def pipeline : Circuit 1 1 := .compose double triple

/-- Doubling maps the unit interval into the interval from zero to two. -/
theorem first : ExactHoare P double M := by
  intro x hx
  change 0 ≤ x 0 ∧ x 0 ≤ 1 at hx
  change 0 ≤ 2 * x 0 ∧ 2 * x 0 ≤ 2
  constructor <;> linarith [hx.1, hx.2]

/-- Tripling establishes the final bound from the intermediate bound. -/
theorem second : ExactHoare M triple Q := by
  intro x hx
  change 0 ≤ x 0 ∧ x 0 ≤ 2 at hx
  change 0 ≤ 3 * x 0 ∧ 3 * x 0 ≤ 6
  constructor <;> linarith [hx.1, hx.2]

/-- The intermediate condition connects the two checked component triples. -/
theorem whole : ExactHoare P pipeline Q := by
  exact exactHoareSequential first second

-- @view circuit pipeline using first, second, whole

/-!
## A condition on a bundle

The input condition below relates both coordinates. Its bracket spans both wires;
it is not a separate bound on either coordinate. Swapping the coordinates preserves
the same region.
-/

def unitDisk : Predicate 2 := ⟨fun x => x 0 * x 0 + x 1 * x 1 ≤ 1⟩
def exchange : Circuit 2 2 := .swap

/-- Exchanging coordinates preserves their joint quadratic bound. -/
theorem exchange_preserves : ExactHoare unitDisk exchange unitDisk := by
  intro x hx
  change x 0 * x 0 + x 1 * x 1 ≤ 1 at hx
  change x 1 * x 1 + x 0 * x 0 ≤ 1
  linarith

-- @view circuit exchange using exchange_preserves

end Notebook.CircuitProofs
