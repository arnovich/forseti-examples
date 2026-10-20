import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.HedgedSpreadContract
import Gimle.Forseti.Examples.HedgedSpreadStepped
import Gimle.Forseti.Examples.HedgedSpread
import Gimle.Asgard.Compile.RationalInterchange
import Gimle.Asgard.Model.Continuous

/-!
# The odds of the stop, over every law in a class

The book is a pairs trade: long one leg, short the other, a position on the
spread between them, which the desk expects to revert to its mean. The desk
hedges it with a lag and runs it with a stop: if the exposure leaves its limit,
the position is cut. The first finance notebook, `HedgedSpread`, proved that no
continuous shock inside a band ever triggers the stop. Markets do not keep to
bands. Their shocks are random, and now and then large, and the desk's question
is one a band cannot answer: marked every trading day for a year, how likely is
the stop to be hit? And what must be known about the shocks before the answer
is a number?

This notebook answers from Lean, for the same book stepped once per mark, with
256 marks to the year, roughly one per trading day. Writing $s_n$ for the
exposure at mark $n$ in units of the limit (so the stop is hit when
$|s_n| > 1$), $h_n$ for the hedging flow still being put on and $d_n$ for the
shock,

$$ s_{n+1} = s_n + \Delta\,(-s_n - h_n + d_n), \qquad h_{n+1} = h_n + \Delta\,(s_n - h_n), \qquad \Delta = \tfrac{1}{256}, $$

from a flat book $s_0 = h_0 = 0$: one explicit Euler step of the first
notebook's equations per mark. The shocks $d_0, d_1, \ldots$ are independent
and all have the same law. That law is a hypothesis, never a fitted object: the
answers are bounds over a whole class of laws, and the class is the thing to
read first. Both classes below are set at the scale $64 = \sigma^2/\Delta$ with
$\sigma = 1/2$: a variance in the first, the variance of the comparison
Gaussian in the second. Under shocks of variance $64$ the year's summed shock
$\Delta(d_0 + \cdots + d_{255})$ has variance $\Delta^2 \cdot 256 \cdot 64 = 1/4$,
a standard deviation of half the limit.

**Proved.** For every centred shock law of variance $64$, whatever its shape —
fat tails and rare jumps included — the exposure leaves $|s| \le 1$ at some
mark of the year, $n \le 256$, with probability at most $1/4$; and the
expected gauge $V = s^2 + h^2$ is at most $32/255 \approx 0.1255$ at every
mark. For every shock law that is sub-Gaussian with proxy $64$ (its moment
generating function at most that of the Gaussian of variance $64$; defined
below), the exposure lies outside the limit on any one mark of the year,
chosen in advance, with probability at most $1/100$: the shape of a
value-at-risk statement, date by date, and not a statement about the year. The
mathematics is the library's (`HedgedSpreadStepped` in Forseti Lean:
`breach_within_year`, `expected_energy_le`, `exceeds_at_each_mark_year`).
Below, Forseti's decider decides the year's bound and the date-by-date bound
again, as this notebook's theorems `breach_within_year` and
`mark_on_any_date`, and with them `expected_gauge`: the expected gauge at the
year's end is at most $33/256$. The theorems written by hand are the pieces a
reader can check by eye: the one-step identity for $V$ read off the compiled
rows, the stationary constant $32/255$, which laws belong to which class, and
a lower bound on the breach probability of the rare-jump law below.

**Refuted.** Variance alone cannot bring the year's breach bound below about
$0.2198$. A law with mass $64/(2 \cdot 257^2)$ at each of $\pm 257$ and the rest
at $0$ is centred with variance $64$, and under it the stop is hit within the
year with probability at least $1 - (1 - 64/257^2)^{256} \approx 0.2198$; the
library turns that into the refutation of the bound $1/5$
(`breach_within_year_fifth_refuted`), and the decider below refutes $1/10$
with the same law (`tight_limit_refuted`). So the worst case over the class
lies between about $0.2198$ and $1/4$, and the distribution-free $1/4$ is at
most $1.14$ times the worst case it covers.

**Unknown.** Two things. Where between $1 - (1 - 64/257^2)^{256}$ and $1/4$ the
worst case over the variance-$64$ class lies: neither end is shown to be the
worst case. And the year as a whole under the sub-Gaussian hypothesis: the
date-by-date $1/100$ does not give a bound for the year (summed over the $256$
dates it is $2.56$, which bounds nothing), and no horizon bound under that
hypothesis is proved: the decision `breach_within_year_subgaussian` below, at
$1/50$, stays unknown.
Whether a horizon bound under thin tails exists, and whether it beats $1/4$,
is neither proved nor refuted here.

**Not claimed.** Continuous time: every statement is about the marks of the
stepped chain — the scheme a simulator runs — and nothing about the
continuous-time book of `HedgedSpread`, a stochastic differential equation, or
how close the chain comes to either. Markets: which class real shocks belong
to is not addressed; the law is an assumption of each bound. Dependence:
shocks that cluster, trend, or change law during the year are outside the
model. The probability under any one law: the bounds hold over each class, the
Gaussian's own breach probability is not computed in Lean (below it is
sampled, and at one date read off by hand), and the rare-jump law's is bounded
only from below. Nothing about profit and loss, other starting books or other
step sizes.

## The book, as Lean steps it

The library steps the compiled circuit of the first notebook, not a restatement
of its equations: `step x d` adds $\Delta$ times the compiled rates at
$[d, s, h]$ to the state $x = [s, h]$, with the shock in the driver slot, and
its two rows (`step_s`, `step_h`) are read off the compiled expressions. The
state at mark $n$ along a shock path $\omega$ is `run step compiled.initial ω n`,
from the flat book. The path is random: `pathMeasure law` makes its
coordinates independent, each distributed as `law`. A breach at mark $n$ is
`¬ exposureWithin 1 (run step compiled.initial ω n)`, that is $|s_n| > 1$,
strict as in the first notebook.

The two law classes, in words.

* `TwoMomentLaw law 64`: a probability law on the real line with mean $0$ and
  second moment $64$, and nothing else. Any shape is allowed, and any tail
  with that variance. It is what a desk that knows only the volatility of its
  shocks can assume.
* `SubGaussianLaw law 64`: a probability law whose moment generating function
  is at most $e^{64 t^2/2}$, that of the centred Gaussian of variance $64$. It
  is a different assumption, about the tail rather than the variance: it rules
  out jumps far beyond what that Gaussian produces, and as the classes are
  stated here neither contains the other (a law can be sub-Gaussian with proxy
  $64$ and have a smaller variance). It buys a sharper statement, but only date
  by date.

The expectation and the horizon bound both start from one identity. One step
moves the gauge to

$$ V(x_{n+1}) = \rho\, V(x_n) + 2\Delta\big((1 - \Delta)\, s_n - \Delta\, h_n\big)\, d_n + \Delta^2 d_n^2, \qquad \rho = (1 - \Delta)^2 + \Delta^2 = 1 - 2\Delta + 2\Delta^2. $$

As in continuous time, the cross terms between $s$ and $h$ cancel, because the
coupling is skew-symmetric; this is the discrete twin of the first notebook's
`budget_rate`. Without a shock the step shrinks $V$ by the factor $\rho < 1$.
The shock enters once linearly, with mean zero under a centred law, and once as
$\Delta^2 d_n^2$, whose mean is $\Delta^2$ times the variance. Lean checks the
identity against the two compiled rows.
-/
namespace Notebook.HedgedSpreadRisk
open MeasureTheory ProbabilityTheory Gimle.Asgard Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

/-- One Euler step of the compiled field moves the gauge `V = s² + h²` to
`ρ V + 2Δ((1 − Δ)s − Δh) d + Δ²d²`, at every state and every shock value: the
coupling terms cancel. -/
theorem energy_step_identity (x : Point states) (d : ℝ) :
    energy (step x d) = ρ * energy x
      + 2 * Δ * ((1 - Δ) * x (0 : Fin 2) - Δ * x (1 : Fin 2)) * d + Δ ^ 2 * d ^ 2 := by
  simp only [energy, step_s, step_h, ρ]
  push_cast
  ring

/-!
## The gauge in expectation

Take the expectation of the identity over the shock. Under a centred law of
variance $64$ the linear term vanishes and the last term contributes
$\Delta^2 \cdot 64$, so the expected gauge obeys
$\mathbb{E} V_{n+1} = \rho\, \mathbb{E} V_n + 64\,\Delta^2$ exactly, whatever the
law's shape: the library proves it for one step from any state
(`energy_step_eq`), and the independence of the shocks carries it along the
path. From the flat book, $\mathbb{E} V_n = 64\,\Delta^2 \sum_{k<n} \rho^k$
(`expected_energy_eq`), which rises toward the stationary value
$64\,\Delta^2/(1 - \rho)$ and is bounded by it at every mark
(`expected_energy_le`). The theorem below computes that constant.

In terms of $\sigma$ the constant is $\sigma^2 / (2(1 - \Delta))$, which tends
to $\sigma^2/2 = 1/8$ as the steps shrink. That reading is ours; the theorem is
the number.
-/

/-- The stationary expected gauge at variance `64`: `Δ² · 64 / (1 − ρ) = 32/255`,
about `0.1255`. It is the bound `expected_energy_le` gives at every mark. -/
theorem stationary_energy : (Δ : ℝ) ^ 2 * 64 / (1 - ρ) = 32 / 255 := by
  norm_num [Δ, ρ]

/-!
## Two laws with the same variance

A class is only as informative as the laws inside it, so here are two. The
first is the rare-jump law `threePoint ε 257` with $\varepsilon = 64/(2 \cdot 257^2)$:
the shock is $0$ with probability $1 - 2\varepsilon$, and $257$ or $-257$ with
probability $\varepsilon$ each, so a jump comes about once in a thousand marks.
It is centred and its variance is $2\varepsilon \cdot 257^2 = 64$, so it is in
the two-moment class. It is not in the sub-Gaussian class with proxy $64$ (the library's
`threePoint_not_subGaussian`): its variance sits in jumps far larger than a
Gaussian of the same variance would produce.
-/

/-- The rare-jump law, mass `64 / (2 · 257²)` at each of `±257` and the rest at
`0`, is centred with variance `64`: a member of the two-moment class. -/
theorem three_point_in_class : TwoMomentLaw (threePoint (64 / (2 * 257 ^ 2)) 257) 64 := by
  have hlaw := threePoint_twoMoment (ε := 64 / (2 * 257 ^ 2)) (L := 257) (by norm_num)
    (by norm_num)
  rwa [show 2 * (64 / (2 * 257 ^ 2) : ℝ) * 257 ^ 2 = 64 by norm_num] at hlaw

/-!
The second is the centred Gaussian of variance $64$, which is in both classes,
so both the horizon bound and the date-by-date bound apply to Gaussian shocks.
Neither computes the Gaussian's own breach probability; they bound it, along
with every other law in the class.
-/

/-- The centred Gaussian of variance `64` is a two-moment law of variance `64`
and a sub-Gaussian law with proxy `64`. -/
theorem gaussian_in_both :
    TwoMomentLaw (gaussianReal 0 64) 64 ∧ SubGaussianLaw (gaussianReal 0 64) 64 := by
  exact_mod_cast gaussian_in_both_classes 64

/-!
## Rare jumps

Under the rare-jump law the book does nothing until the first jump. A zero
shock leaves the flat book where it is (`step_zero_fixed`), and a single jump
of $\pm 257$ from the flat book moves the exposure to $\pm 257/256$, past the
limit (`step_big_breaches`). So the stop is hit at the first nonzero shock, and
the chance that one of the year's $256$ shocks is nonzero is
$1 - (1 - 2\varepsilon)^{256} \approx 0.2198$.

Lean proves that number as a lower bound on the breach probability, which is
the direction a refutation needs: no bound below it holds for every law of
variance $64$. That it is also the exact value, because a path without a jump
stays flat all year, is our reading and not a theorem here. Set beside the
proved $1/4$, it says the distribution-free bound is nearly attained, by a law
whose variance sits in rare one-step jumps. Equal volatility does not mean
equal risk of the stop: under the Gaussian of the same variance, a single
shock that large is a move of more than thirty-two standard deviations.
-/

/-- Under the rare-jump law of variance `64`, the exposure leaves `|s| ≤ 1` at
some mark of the year, `n ≤ 256`, with probability at least
`1 − (1 − 2ε)²⁵⁶ ≈ 0.2198`, where `2ε = 64/257²`: the three-point breach
probability, as a lower bound. -/
theorem three_point_breaches_often :
    ENNReal.ofReal (1 - (1 - 2 * (64 / (2 * 257 ^ 2 : ℝ))) ^ 256) ≤
      pathMeasure (threePoint (64 / (2 * 257 ^ 2)) 257)
        {ω | ∃ n ≤ 256, ¬ exposureWithin 1 (run step compiled.initial ω n)} := by
  exact breach_ge_threePoint (by norm_num) (by norm_num) step_zero_fixed
    (step_big_breaches 257 (by norm_num [Δ])) (step_big_breaches (-257) (by norm_num [Δ]))

/-!
## The claims, decided

Each claim below is a goal about the stepped book from the flat book, for every
shock law of the class it names, decided by Forseti's stepped decider. The
block that follows each directive is the decider's output, inserted as
proposed and checked by Lean as part of this file: the decider picks which of
the library's theorems to apply and with which constants, and a block whose
constants were wrong would fail to check. Two sampled cards sit among the
claims, each evidence about a single law, never a proof.

First, the year. For every centred shock law of variance $64$, the stop is hit
at some mark $n \le 256$ with probability at most $1/4$: the library's horizon
bound $N \Delta^2 v / B^2$ (`breach_within`) at $N = 256$, $v = 64$ and $B = 1$
is exactly $1/4$.
-/

-- @decide breach_within_year : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/4
namespace Decided_breach_within_year

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/4)

/-- For independent, identically distributed shocks drawn from any centred law with variance 64, the probability that the exposure s breaches 1 within 256 marks is at most 1/4. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0); `exposureWithin 1` is the band |s| ≤ 1. The stepped decider proved it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/4 -/
theorem breach_within_year :
    ∀ law : Measure ℝ, TwoMomentLaw law 64 →
      BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/4) := by
  have root : forsetiClaim := by
    unfold forsetiClaim
    exact fun law h => (breach_within h (by norm_num) 256).mono (by norm_num [Δ])
  refine (fun (bridge : _ ↔ forsetiClaim) => bridge.mpr root) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_breach_within_year

/-!
How far is that from one well-behaved law of the class? The card below samples
the book under Gaussian shocks of variance $64$: $4000$ shock paths of $256$
steps from seed $7$, run in float64, with eight paths of the exposure drawn
and, at each mark, the fraction of all paths that have hit the stop by then.
By the year's end that fraction is $0.007$, that is $0.7\,\%$, with a $95\,\%$
sampling interval of $0.004848$ to $0.0101$: far below the proved $1/4$, or
$25\,\%$. The gap is not slack in the argument. The bound is a statement about
every centred law of variance $64$, and the rare-jump law of the previous
section is one of them, with a breach probability of at least about $0.2198$;
a bound that covers both cannot sit near the Gaussian's fraction. That is the
price of knowing only the variance. The card is evidence about one law,
computed in floating point with sampling error; no claim's status depends on
it.
-/

-- @evidence sample Gimle.Forseti.Examples.HedgedSpread.compiled (law := gaussian) (variance := 64) (paths := 4000) (steps := 256) (seed := 7) (observe := s) (barrier := 1) (show := 8)

/-!
## Date by date, under thin tails

A value-at-risk statement fixes a date in advance and bounds the chance of a
breach on that date. Under shocks sub-Gaussian with proxy $64$, the exposure
at mark $n$ is sub-Gaussian too, with the proxy
$\Delta^2 \cdot 64 \sum_{k<n} w_k^2$, computed exactly over the rationals from
the weights $w_k$ with which the shocks reach it (the library's `proxy` and
`exceeds_at_proxy`); for Gaussian shocks of variance $64$ that proxy is the
variance of the exposure. It grows with the mark and is about $0.0913$ at the
year's end, and the tail bound it gives there is about $0.0084$, below the
claimed $1/100$. The theorem states $1/100$ at every mark $n \le 256$, each
mark taken separately.

For comparison, and as our reading rather than a theorem: under Gaussian
shocks of variance $64$ the exposure at the year's end is Gaussian with
variance about $0.0913$, so it lies outside the limit with probability about
$0.09\,\%$. The proved $1/100$ is roughly ten times that.
-/

-- @decide mark_on_any_date : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks subgaussian 64 at every mark within 256 observe s breach 1 probability <= 1/100
namespace Decided_mark_on_any_date

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, SubGaussianLaw law 64 →
    AtEveryMark step compiled.initial law 256 (exposureWithin 1) (1/100)

/-- For independent, identically distributed shocks drawn from any sub-Gaussian law with proxy 64, at each mark up to 256, taken separately, the probability that the exposure s breaches 1 is at most 1/100. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0); `exposureWithin 1` is the band |s| ≤ 1. The stepped decider proved it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks subgaussian 64 at every mark within 256 observe s breach 1 probability <= 1/100 -/
theorem mark_on_any_date :
    ∀ law : Measure ℝ, SubGaussianLaw law 64 →
      AtEveryMark step compiled.initial law 256 (exposureWithin 1) (1/100) := by
  have root : forsetiClaim := by
    unfold forsetiClaim
    intro law h
    have numeric : ∀ c : ℝ, 0 < c → c ≤ 18251/200000 → 2 * Real.exp (-1 ^ 2 / (2 * c)) ≤ 1/100 := by
      intro c h0 h1
      have hr : (100000/18251 : ℝ) ≤ 1 ^ 2 / (2 * c) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hexp : Real.exp (-1 ^ 2 / (2 * c)) ≤ Real.exp (-(100000/18251)) := by
        rw [Real.exp_le_exp, neg_div]
        exact neg_le_neg hr
      have hE := exp_ge_floor_cubic 5 (r := 100000/18251) (by norm_num)
      norm_num at hE
      have hq : 2 * Real.exp (-(100000/18251)) ≤ 1/100 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
        linarith
      linarith
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hempty : {ω : ℕ → ℝ | ¬ exposureWithin 1 (run step compiled.initial ω 0)} = ∅ := by
        ext ω
        norm_num [exposureWithin, initial_eq]
      refine ⟨h.prob, by norm_num, ?_⟩
      rw [hempty, measure_empty]
      exact zero_le
    · refine exceeds_at_proxy h (by norm_num) n ?_
      have hc : proxy 64 256 ≤ 18251/200000 := by
        rw [← proxyRec_eq]
        decide +kernel
      have hle : (proxy 64 n : ℝ) ≤ 18251/200000 := by
        have := Rat.cast_le (K := ℝ) |>.mpr ((proxy_mono 64 (by norm_num) hn).trans hc)
        push_cast at this
        exact this
      have hpos : (0 : ℝ) < proxy 64 n := by
        have h1 : (0 : ℚ) < proxy 64 1 := by
          rw [← proxyRec_eq]
          decide +kernel
        exact_mod_cast h1.trans_le (proxy_mono 64 (by norm_num) hn0)
      exact numeric _ hpos hle
  refine (fun (bridge : _ ↔ forsetiClaim) => bridge.mpr root) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_mark_on_any_date

/-!
## The gauge at the year's end

From the flat book the expected gauge is known exactly at every mark,
$\mathbb{E} V_n = 64\,\Delta^2 \sum_{k<n} \rho^k$ (`expected_energy_eq`), so a
claim about its value at the year's end is decided by exact arithmetic: about
$0.1085$ at $n = 256$, below the claimed $33/256 \approx 0.1289$. The claim
could not have failed: $33/256$ is above the stationary $32/255$ that bounds
every mark, and at the year's end the gauge is still short of that stationary
value. The stationary value is in turn just above $\sigma^2/2 = 32/256$, the
value it tends to as the steps shrink, on our reading above.
-/

-- @decide expected_gauge : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 observe V expected <= 33/256 at 256
namespace Decided_expected_gauge

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    ExpectedLe step compiled.initial law energy 256 (33/256)

/-- For independent, identically distributed shocks drawn from any centred law with variance 64, the expected energy V at mark 256 is at most 33/256. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0). The stepped decider proved it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 observe V expected <= 33/256 at 256 -/
theorem expected_gauge :
    ∀ law : Measure ℝ, TwoMomentLaw law 64 →
      ExpectedLe step compiled.initial law energy 256 (33/256) := by
  have root : forsetiClaim := by
    unfold forsetiClaim
    intro law h
    have hq : Δ ^ 2 * 64 * geomSum 256 ≤ 33/256 := by decide +kernel
    have hr := Rat.cast_le (K := ℝ) |>.mpr hq
    push_cast at hr
    refine ⟨h.prob, by norm_num, ?_⟩
    rw [expected_energy_eq h, ← geomSum_eq]
    exact ENNReal.ofReal_le_ofReal hr
  refine (fun (bridge : _ ↔ forsetiClaim) => bridge.mpr root) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_expected_gauge

/-!
## A tighter limit, refuted

Could a desk that knows only the volatility of its shocks promise $1/10$ for
the year? No. The decider refutes the claim with the rare-jump law: it is in
the class, and under it the stop is hit within the year with probability at
least $1 - (1 - 2\varepsilon)^{256} \approx 0.2198$, above $1/10$. The
theorem is the claim's negation: no bound of $1/10$ holds for every law of
variance $64$.
-/

-- @decide tight_limit : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/10
namespace Decided_tight_limit

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/10)

/-- For independent, identically distributed shocks drawn from any centred law with variance 64, the probability that the exposure s breaches 1 within 256 marks is at most 1/10. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0); `exposureWithin 1` is the band |s| ≤ 1. The stepped decider refuted it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/10 -/
theorem tight_limit_refuted : ¬ (∀ law : Measure ℝ, TwoMomentLaw law 64 →
      BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/10)) := by
  have refuted : ¬ forsetiClaim := by
    unfold forsetiClaim
    intro h
    have hlaw := threePoint_twoMoment (ε := 64 / (2 * 257 ^ 2)) (L := 257) (by norm_num) (by norm_num)
    rw [show 2 * (64 / (2 * 257 ^ 2) : ℝ) * 257 ^ 2 = 64 by norm_num] at hlaw
    exact not_breachWithin_threePoint (by norm_num) (by norm_num) step_zero_fixed (step_big_breaches 257 (by norm_num [Δ])) (step_big_breaches (-257) (by norm_num [Δ])) (by norm_num) (h _ hlaw)
  intro claim
  refine (fun (bridge : _ ↔ forsetiClaim) => refuted (bridge.mp claim)) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_tight_limit

/-!
The rare-jump law is a law of the class like any other, so it can be sampled
too. The card below runs the same plan, $4000$ paths of $256$ steps from seed
$7$, under the three-point law of variance $64$ (`threepoint`: jumps of
$\pm 257$, each with probability $64/(2 \cdot 257^2)$). By the year's end a
fraction $0.21875$ of the paths, about $22\,\%$, has hit the stop, with a
$95\,\%$ sampling interval of $0.2062$ to $0.2318$, against $0.007$ under the
Gaussian of the same variance. That is the fat-tail lesson: the same
volatility, a far likelier stop. The sampled fraction lies a little below the
lower bound $1 - (1 - 2\varepsilon)^{256} \approx 0.2198$ proved above, as a
sample may: the interval contains it. (That the bound is also the exact value
is our reading.) Set beside the proved $1/4$, the card shows in sampled paths
what that lower bound proves: the distribution-free bound is nearly tight over
its class.
-/

-- @evidence sample Gimle.Forseti.Examples.HedgedSpread.compiled (law := threepoint) (variance := 64) (paths := 4000) (steps := 256) (seed := 7) (observe := s) (barrier := 1) (show := 8)

/-!
## The year under thin tails

The last claim asks whether thin tails buy the year a much sharper bound: at
most $1/50$ for every shock law sub-Gaussian with proxy $64$. Neither side is
proved here. The horizon bound of the first claim is stated for laws of
variance $64$, which a law sub-Gaussian with proxy $64$ need not have, and
where it applies it gives $1/4$, not $1/50$; the date-by-date bound does not
add up over the year; and the rare-jump law that refutes $1/10$ is not in this
class (`threePoint_not_subGaussian`), so its refutation does not carry over.
The decider has no horizon theorem for the sub-Gaussian class, so it leaves
the claim unknown and no block follows. The Gaussian card above, one law of
the class, saw a fraction $0.007$ of its paths hit the stop within the year:
below $1/50$, and evidence about that one law, not a bound over the class.
-/

-- @decide breach_within_year_subgaussian : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks subgaussian 64 within 256 observe s breach 1 probability <= 1/50

/-!
## What is and is not in the picture

The horizon bound has the right shape, and a constant within a small factor of
the worst case in its class. The shape: it reads the shocks only through their
variance, as a bound over the class must, and it is, to first order, the
chance that the rare-jump law jumps at all within the year:
$2\varepsilon N = N v / L^2$ is the bound $N \Delta^2 v / B^2$ with the jump
$L$ in place of $B/\Delta$, $L$ being the smallest whole jump that clears the
limit in one step (that comparison is our reading). The constant: over the
variance-$64$ class the worst breach probability within the year lies between
about $0.2198$ and $1/4$, so $1/4$ is at most $1.14$ times it. The two cards
show both sides of that: one well-behaved law far below the bound, a sampled
$0.007$, and the rare-jump law near it, a sampled $0.21875$.

Not claimed: continuous time, since every statement is about the marks of the
stepped chain; markets, since the shock law is an assumption of each bound and
not a fit to prices; the Gaussian truth, since the Gaussian's own breach
probability, within the year or on one date, is sampled or read off by hand
here and never proved; and any horizon statement for sub-Gaussian shocks,
where the last decision stays unknown.
-/

#print axioms energy_step_identity
#print axioms stationary_energy
#print axioms three_point_in_class
#print axioms gaussian_in_both
#print axioms three_point_breaches_often

end Notebook.HedgedSpreadRisk
