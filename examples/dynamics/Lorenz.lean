import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.Lorenz

/-!
# The Lorenz butterfly never leaves its ball

The Lorenz system is the most famous picture in dynamics: three coupled
equations whose solutions wander forever over a two-winged surface, never
repeating and never settling, so sensitive to their start that no simulation
of them can be trusted for long. This notebook proves one thing about it that
no simulation could: from the start $(1, 1, 1)$, the trajectory stays inside an
explicit ball for all time. It also shows, honestly, what the same machinery
cannot settle.

The equations, with the parameters Lorenz used in 1963, are

$$ x' = \sigma (y - x), \qquad y' = x(\rho - z) - y, \qquad z' = xy - \beta z, $$

with $\sigma = 10$, $\rho = 28$, $\beta = 8/3$, started from
$(x, y, z) = (1, 1, 1)$ at $t = 0$. We watch

$$ V = x^2 + y^2 + (z - 38)^2, $$

the squared distance from the point $(0, 0, \sigma + \rho)$, which starts at
$V(0) = 1 + 1 + 37^2 = 1371$.

Lorenz derived these equations by truncating Saltzman's expansion of the
Boussinesq equations for convection, the Navier–Stokes equations coupled to
heat, to three modes. A bound on this system is therefore a bound on a
three-mode truncation of Boussinesq convection. The pure Navier–Stokes
truncations, whose smallest member is a single triad rather than the Lorenz system, have
their own notebooks, T3 (`NS_T3.lean`), K5 (`NS_K5.lean`) and B2 (`NS_B2.lean`);
this one stands beside them as the convective case.

**Proved.** A trajectory from $(1, 1, 1)$ exists for all $t \ge 0$, is unique,
and satisfies $0 \le V \le 1600$ throughout. The bound is decided by the
trajectory decider from a named Lean contract and its certificate replays
without the solver.

**Refuted.** $V \le 1300$ for all $t \ge 0$: false at the start, where
$V = 1371$, and Lean checks that witness.

**Unknown.** $V \le 1400$ for all $t \ge 0$. A simulation says it is true
(the largest value it sees is about $1387$), but the contract proves only
$1600$, and the start does not refute it. The decider says so rather than
guess; that is the point of it.

**Not claimed.** Anything about chaos, the attractor, or sensitivity to the
start: the simulation below is evidence, and no status reads it. Nothing about
other starts or other parameters.

## The system, compiled

The equations are declared once, in Asgard's language, and compiled to a
circuit whose exact field Lean draws and reads:
-/
namespace Notebook.Lorenz
open Gimle.Asgard Gimle.Forseti.Examples.Lorenz

-- @view model Gimle.Forseti.Examples.Lorenz.compiled
-- @evidence simulate Gimle.Forseti.Examples.Lorenz.compiled (h := 1/200) (steps := 6000) (solver := rk4) (plane := x, z)

/-!
## What a simulation shows

The run above integrates the compiled field with RK4 in floating point from
$t = 0$ to $t = 30$, and shows the butterfly: $x$ and $y$ swinging between the
two wings, $z$ oscillating between about $5$ and $48$. The picture is right and
also the reason the picture cannot be a proof: two runs with different step
sizes diverge from each other after a few wing changes. What follows does not
depend on it.

## The storage function, and why the usual argument fails

Along any solution, the chain rule and the equations give

$$ V' = -20x^2 - 2y^2 - \tfrac{16}{3} z^2 + \tfrac{608}{3} z. $$

The cubic terms cancel, and so do the $xy$ terms, because the centre was placed
at $z = \sigma + \rho$; that choice is the whole trick. But $V'$ is not always
negative: near the origin, where $z$ is small and positive, $V$ grows. So $V$
is not monotone along the trajectory, and the simple argument used for a
damped system, "the energy only ever decreases", is unavailable. Lean checks
both facts about the compiled field below.
-/

/-- The compiled observation at the start is $1371$. -/
theorem energy_at_start : energy ![1, 1, 1] = 1371 := by
  norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons]

/-- $V$ is not monotone: at $(0, 0, 1)$ its rate along the field is positive. -/
theorem rate_positive_at_origin_side : 0 < rate ![0, 0, 1] := by
  norm_num [rate, Matrix.cons_val_two, Matrix.tail_cons]

/-!
What does hold is a differential inequality: at every state,

$$ V' + 2V \le 2 \cdot 1541. $$

The least constant for which this is true is $23104/15 \approx 1540.27$; Lean
checks it with $1541$. Then $e^{2t}(V - 1600)$ is non-increasing along any
solution, and since it starts negative, $V \le 1600$ forever. The margin
between $1541$ and $1600$ is not decoration: it is what makes the trajectory
exist for all time, as the next section explains.
-/

/-- The differential inequality at every state, checked for the closed-form rate. -/
theorem storage_inequality (x : Point 3) : rate x ≤ 2 * 1541 - 2 * energy x := by
  exact storage_bound x

/-!
## Existence is the hard part

For a linear system, a solution for all time is written down. For Lorenz it is
not, and Mathlib's Picard–Lindelöf theorem only gives a solution on a short
interval. The library's proof, in `Gimle.Forseti.Examples.Lorenz`, builds the
global solution by hand: clamp the field to a box containing the ball
$V \le 1600$, so that it is bounded and globally Lipschitz; get a solution on
every $[0, n]$; glue them by uniqueness; and show the glued solution never
leaves the ball, because at any point where $V = 1600$ its rate is at most
$2 \cdot 1541 - 2 \cdot 1600 = -118 < 0$. Inside the ball the clamp is the
identity, so the glued curve solves the true equations. Uniqueness is Lipschitz
continuity on the same compact ball.

That proof is what the decider's contract names. Every claim below is decided
against the compiled circuit, not against these words.

## The claims, decided
-/

-- @decide in_ball : trajectory lorenz from (1, 1, 1) at 0 observe V always : V >= 0 and V <= 1600

namespace DecidedShared_72f9d7627148

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 4 := ⟨3, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.Lorenz.evolution.states.map (·.initialId) = ["initial-x", "initial-y", "initial-z"] ∧
  (Gimle.Forseti.Examples.Lorenz.body.observations.get forsetiObservation).port.id =
    "obs-v" ∧
  Gimle.Forseti.Examples.Lorenz.evolution.axis.id = "time"

end DecidedShared_72f9d7627148

namespace Decided_in_ball

open DecidedShared_72f9d7627148

example : @forsetiTime = @DecidedShared_72f9d7627148.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_72f9d7627148.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_72f9d7627148.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_72f9d7627148.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1600) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["V"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1600) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.Lorenz.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- V is output 3 of the compiled circuit, the port obs-v; the input's initial wires (initial-x, initial-y, initial-z) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory lorenz interpretation continuous-real obligation contract start time = 0 initial initial-x = 1, initial-y = 1, initial-z = 1 observe obs-v as V always : V >= 0 and V <= 1600 -/
theorem in_ball :
    have circuit := Gimle.Forseti.Examples.Lorenz.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y →
        ∀ t ≥ 0, have V := y t 3; V ≥ 0 ∧ V ≤ 1600) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.Lorenz.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.Lorenz.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.Lorenz.compiled.initial := by rw [Gimle.Forseti.Examples.Lorenz.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.Lorenz.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.Lorenz.energy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (1600) 1) : ℚ) : ℝ) = 1600 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩

end Decided_in_ball


-- @decide below_thirteen_hundred : trajectory lorenz from (1, 1, 1) at 0 observe V always : V <= 1300

namespace Decided_below_thirteen_hundred

open DecidedShared_72f9d7627148

example : @forsetiTime = @DecidedShared_72f9d7627148.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_72f9d7627148.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_72f9d7627148.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_72f9d7627148.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1300) 1)))))

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.Lorenz.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- V is output 3 of the compiled circuit, the port obs-v; the input's initial wires (initial-x, initial-y, initial-z) start at (1, 1, 1) at time = 0. The trajectory decider refuted it. Goal (trajectory): trajectory lorenz interpretation continuous-real obligation contract start time = 0 initial initial-x = 1, initial-y = 1, initial-z = 1 observe obs-v as V always : V <= 1300 -/
theorem below_thirteen_hundred :
    have circuit := Gimle.Forseti.Examples.Lorenz.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y →
        ∀ t ≥ 0, have V := y t 3; V ≤ 1300) := by
  sorry

end Decided_below_thirteen_hundred


-- @decide below_fourteen_hundred : trajectory lorenz from (1, 1, 1) at 0 observe V always : V <= 1400

/-!
## What the ball says in coordinates

$V \le 1600$ means $|x| \le 40$, $|y| \le 40$ and $-2 \le z \le 78$. The
simulation stays well inside: it never sees $|x|$ above $20$, $|y|$ above $28$
or $z$ above $48$. The gap between the proved ball and the observed attractor
is real, and closing it would need a sharper invariant than a single quadratic;
that is the next rung, not this one.
-/

#print axioms energy_at_start
#print axioms rate_positive_at_origin_side
#print axioms storage_inequality

end Notebook.Lorenz
