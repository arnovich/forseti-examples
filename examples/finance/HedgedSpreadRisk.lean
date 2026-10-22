import Mathlib
-- Not used below: the two sample cards load it from this project's build, which this keeps built.
import Gimle.Asgard.Compile.RationalInterchange
import Gimle.Forseti.Examples.HedgedSpread
import Gimle.Forseti.Examples.HedgedSpreadContract
import Gimle.Forseti.Examples.HedgedSpreadStepped
import Gimle.Forseti.Stepped
import Gimle.Forseti.Syntax.Certificate

/-!
# The odds of the stop, over every law in a class

The book is a pairs trade: long one leg, short the other, a position on the
spread between them, which the desk expects to revert to its mean. The desk
hedges it with a lag and watches it against a stop on the gross exposure: the
stop is hit when the exposure leaves its limit, on either side. The first
finance notebook, `HedgedSpread`, proved that no continuous shock inside a band
ever hits the stop. Markets do not keep to bands. Their shocks are random, and
now and then large, and the desk's question is one a band cannot answer:
re-valued every trading day for a year, how likely is the stop to be hit? And
what must be known about the shocks before the answer is a number?

On $4000$ sampled paths each, the stop is hit within the first year from a
flat book on $0.70\,\%$ of the paths ($0.48\,\%$ to $1.01\,\%$) under Gaussian
shocks, and on $22\,\%$ ($20.6\,\%$ to $23.2\,\%$) under rare jumps of the
same variance: sampled fractions with their $95\,\%$ sampling intervals,
evidence and not proof. Lean proves that for every centred shock law (the law
being the probability distribution of one day's shock) of variance at most
$64$ the stop is hit within that year with probability at most $1/4$, and
refutes $1/5$: one law of variance $64$ breaks it. So no bound from the
variance alone can be $0.2197$ or lower: under that law the stop is hit with
probability above $0.2197$, also proved.

$$ \begin{array}{c|c|c} & \begin{gathered}\text{variance}\\ \le 64\end{gathered} & \begin{gathered}\text{sub-}\\ \text{Gaussian}\\ \text{proxy } 64\end{gathered} \\ \hline \begin{gathered}\text{one}\\ \text{date}\end{gathered} & \begin{gathered}\text{not}\\ \text{stated}\\ \text{here}\end{gathered} & \begin{gathered}\le 1/100\\ \text{proved}\end{gathered} \\ \hline \begin{gathered}\text{the}\\ \text{year}\end{gathered} & \begin{gathered}\le 1/4\\ \text{proved;}\\ \le 1/5\\ \text{refuted}\end{gathered} & \begin{gathered}\le 1/50\\ \text{unknown}\end{gathered} \end{array} $$

Sampled, not proved, on $4000$ paths each: $0.70\,\%$ within the year under
Gaussian shocks, $22\,\%$ under rare jumps.

- **Proved.** Shocks centred with variance at most $64$, of any shape and any
  tail with a finite second moment: the stop is hit within the first year with
  probability at most $1/4$ (`year_breach_bound`, decided at variance $64$;
  `year_bound_any_variance_le`, for any variance up to $64$).
- **Refuted.** Shocks centred with variance $64$: a year bound of $1/5$
  (`tight_limit_refuted`). Under the rare-jump law of that variance the stop is
  hit within the year with probability above $0.2197$
  (`three_point_breaches_often`, `three_point_lower_bound_decimal`).
- **Proved.** Shocks sub-Gaussian with proxy $64$, that is with tails no
  heavier than the Gaussian of variance $64$: on any one mark of the first
  year, chosen in advance, the exposure is outside its limit with probability
  at most $1/100$ (`mark_on_any_date`), a fixed-date quantile of limit
  utilisation and not a statement about the year.
- **Proved.** Shocks centred with variance $64$: the expected gauge, the
  squared distance of the book from flat, is at most $32/255$ at every mark
  (`expected_gauge_every_mark`) and at most $1086/10000$ at the first year's
  end (`expected_gauge`).
- **Unknown.** Shocks sub-Gaussian with proxy $64$: a year bound of $1/50$.
  Lean proves neither it nor its negation here
  (`breach_within_year_subgaussian`, the last section). Unknown too: where the
  worst case over the variance class lies, above $0.2197$ and at most $1/4$.
- **Not claimed.** The model is stylised: one hedged spread with a lag and a
  reversion, nothing fitted. The stop is observed, not modelled: the chain
  keeps stepping after a breach, so the year bounds count the first hit, while
  the date-by-date bound and the expected gauge describe a book that is never
  cut. No law without a finite second moment is covered. The Gaussian truth,
  the Gaussian's own breach probability within the year or on one date, is not
  proved: it is sampled, and read off by hand at one date. Continuous time:
  every statement is about the marks of the stepped chain, and nothing about
  the continuous-time book of `HedgedSpread`, a stochastic differential
  equation, or how close the chain comes to either. Markets: which class real
  shocks belong to is not addressed; the law is an assumption of each bound.
  Dependence: shocks that cluster, trend or change law are outside the model.
  No horizon statement for sub-Gaussian shocks is made. Nothing about profit
  and loss, other starting books or other step sizes.

## The book, as Lean steps it

A mark is one daily re-valuation of the book, and a year has $256$ of them.
Time is the book's own unit, read here as that year: the model is stylised,
so the hedge's lag and the spread's reversion are on the scale of a year too.
Writing $s_n$ for the exposure at mark $n$ in units of the limit (a breach,
the stop being hit, is $|s_n| > 1$), $h_n$ for the hedging flow still being
put on, $d_n$ for the day's shock and $\Delta = 1/256$ for the step,

$$ \begin{aligned} s_{n+1} &= s_n + \Delta\,(d_n - s_n - h_n) \\ h_{n+1} &= h_n + \Delta\,(s_n - h_n) \end{aligned} $$

from a flat book $s_0 = h_0 = 0$: one explicit Euler step of the first
notebook's equations per mark. The shocks $d_0, d_1, \ldots$ are independent
and all have the same law, the probability distribution of one day's shock.
That law is a hypothesis, never a fitted object: the answers are bounds over a
whole class of laws, and the class is the thing to read first. At variance
$64$, by arithmetic on that variance, a day's shock moves the exposure by
about $8/256$ of the limit, one standard deviation, and a year of them adds up
to about half the limit before the hedge and the reversion pull the exposure
back; the year bound $1/4$ below is that half, squared.

The library steps the compiled circuit of the first notebook, not a restatement
of its equations: `step x d` adds $\Delta$ times the compiled rates at
$[d, s, h]$ to the state $x = [s, h]$, with the shock in the driver slot, and
its two rows (`step_s`, `step_h`) are read off the compiled expressions. The
state at mark $n$ along a shock path $\omega$ is `run step compiled.initial ω n`,
from the flat book, and `pathMeasure law` makes the path's coordinates
independent, each distributed as `law`. A breach at mark $n$ is
`¬ exposureWithin 1 (run step compiled.initial ω n)`, strict as in the first
notebook.

The stop is observed, not modelled: `run` keeps stepping after a breach, as if
the position were never cut. A claim about a breach within the year
(`BreachWithin`) is not affected, since it asks only whether a first breach
happens; a claim at a fixed date (`AtEveryMark`) and the expected gauge
(`ExpectedLe`) describe the book as if it were never cut.

The two classes of laws:

- The variance class, `TwoMomentLaw law 64`: laws with mean $0$ and second
  moment exactly $64$, of any shape and with any tail that has that variance.
  The scale is $64 = \sigma^2/\Delta$, where $\sigma = 1/2$ is the shocks'
  standard deviation per unit of the book's time, the year. The class fixes
  the variance exactly; a desk that knows only a ceiling on the variance gets
  the year bound from `year_bound_any_variance_le`.
- The sub-Gaussian class, `SubGaussianLaw law 64`: laws whose moment
  generating function is at most $e^{64 t^2/2}$, that of the centred Gaussian
  of variance $64$, for every real $t$; $64$ is the class's proxy. Its tails
  are no heavier than that Gaussian's. **Our reading, not proved:** the bound
  forces mean $0$ and a variance of at most $64$; at variance $64$ it forces
  zero skew and kurtosis at most $3$, the Gaussian's, while a law of smaller
  variance may have relatively fatter tails and still qualify. So neither
  class contains the other: a sub-Gaussian law need not have variance exactly
  $64$ (a point mass at $0$ qualifies), and the rare-jump law below is in the
  variance class and not in this one, which is proved
  (`threePoint_not_subGaussian`).
-/
namespace Notebook.HedgedSpreadRisk
open MeasureTheory ProbabilityTheory Gimle.Asgard Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

/-!
## The year: at most 1 in 4 (proved)

The probability claims from here on (the year bounds, the refutation and the
one-date bound) and the year-end gauge are about the first year from the flat
book. Some claims are written by hand and are short and self-contained; the
others are decided by Forseti's stepped decider, and the block that follows
each `-- @decide` directive is its output, inserted as proposed and checked by
Lean as part of this file. The decider picks which theorems of the library,
Forseti Lean's `HedgedSpreadStepped`, to apply and with which constants, and a
block whose constants were wrong would fail to check.

The first claim is the horizon bound. For every centred shock law of variance
$v$ the exposure leaves $|s| \le B$ at some mark $n \le N$ with probability at
most $N \Delta^2 v / B^2$ (the library's `breach_within`), which at $N = 256$,
$v = 64$ and $B = 1$ is exactly $1/4$. The bound uses only the shock budget:
nothing in it depends on the hedge or the reversion, so it gives them no
credit.
**Our reading, not proved:** it is the classical bound for an unhedged random
walk with the same shocks. The rare-jump law below shows why the hedge earns
so little here: a one-day gap through the limit.
-/

-- @decide year_breach_bound : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/4
namespace Decided_year_breach_bound

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/4)

/-- For independent, identically distributed shocks drawn from any centred law with variance 64, the probability that the exposure s breaches 1 within 256 marks is at most 1/4. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0); `exposureWithin 1` is the band |s| ≤ 1. The stepped decider proved it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/4 -/
theorem year_breach_bound :
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

end Decided_year_breach_bound

/-!
The decided claim fixes the variance at $64$, as its class does. A desk that
knows only a ceiling on the variance gets the same bound, from the same
library theorem.
-/

/-- A ceiling on the variance is enough: for every `v ≤ 64` and every centred shock law
of second moment `v`, the stop is hit within the first year with probability at most
`1/4`. -/
theorem year_bound_any_variance_le {law : Measure ℝ} {v : ℝ} (hv : v ≤ 64)
    (h : TwoMomentLaw law v) :
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1 / 4) := by
  refine (breach_within h one_pos 256).mono ?_
  norm_num [Δ]
  linarith

/-!
## The year under Gaussian shocks (sampled)

The centred Gaussian of variance $64$ is in both classes, so the year bound and
the date-by-date bound both apply to it. Lean proves no year bound below $1/4$
for the Gaussian here: the bound covers it with every other law of the class,
and its own breach probability is not computed.
-/

/-- The centred Gaussian of variance `64` is in the variance class (`TwoMomentLaw`) at
variance `64` and is a sub-Gaussian law with proxy `64`. -/
theorem gaussian_in_both :
    TwoMomentLaw (gaussianReal 0 64) 64 ∧ SubGaussianLaw (gaussianReal 0 64) 64 := by
  -- The cast from `ℝ≥0` follows how the pinned library states its classes; a pin bump
  -- that changes it fails here loudly.
  exact_mod_cast gaussian_in_both_classes 64

/-!
What one law of the class does can be sampled. The first notebook drew no
paths, because one drawn path suggests itself as typical; here two laws of the
same variance are compared, and each card says it is evidence. The card below
draws $4000$ shock paths of $256$ marks from seed $7$, in float64, under
Gaussian shocks of variance $64$. Look at the eight paths drawn: they wander,
and none leaves $\pm 1$. The rising line is the fraction of all $4000$ paths
that has hit the stop by that mark; by the year's end it is $0.70\,\%$
($0.48\,\%$ to $1.01\,\%$), far below the proved $1/4$. Is $1/4$ just slack?
-/

-- @evidence sample Gimle.Forseti.Examples.HedgedSpread.compiled (law := gaussian) (variance := 64) (paths := 4000) (steps := 256) (seed := 7) (observe := s) (barrier := 1) (show := 8)

/-!
## The year under rare jumps (sampled)

No. The rare-jump law, `threePoint ε 257` in Lean with
$\varepsilon = 64/(2 \cdot 257^2)$, puts the shock at $0$ with probability
$1 - 2\varepsilon$ and at $257$ or $-257$ with probability $\varepsilon$ each.
It is centred with variance $2\varepsilon \cdot 257^2 = 64$, so it is in the
variance class, and it is not sub-Gaussian with proxy $64$
(`threePoint_not_subGaussian`).
-/

/-- The rare-jump law, mass `64 / (2 · 257²)` at each of `±257` and the rest at
`0`, is centred with variance `64`: a member of the variance class (`TwoMomentLaw`). -/
theorem three_point_in_class : TwoMomentLaw (threePoint (64 / (2 * 257 ^ 2)) 257) 64 := by
  have hlaw := threePoint_twoMoment (ε := 64 / (2 * 257 ^ 2)) (L := 257) (by norm_num)
    (by norm_num)
  -- The rewrite matches the cast form of the pinned library's statement; a pin bump that
  -- changes it fails here loudly.
  rwa [show 2 * (64 / (2 * 257 ^ 2) : ℝ) * 257 ^ 2 = 64 by norm_num] at hlaw

/-!
Under this law the book does nothing until the first jump: a zero shock leaves
the flat book where it is (`step_zero_fixed`), and one jump of $\pm 257$ moves
the exposure to $\pm 257/256$, through the limit in a single mark
(`step_big_breaches`). That is gap risk: a gap of the whole limit in one day,
which the hedge, following the exposure with a lag, cannot stop. In desk units,
by arithmetic on the law's parameters, a jump comes about once in a thousand
marks, roughly once in four years, and is a move of more than thirty-two
standard deviations of the Gaussian of the same variance. So the stop is hit
within the year with probability at least $1 - (1 - 2\varepsilon)^{256}$, the
chance that one of the year's $256$ shocks is a jump, and that number is above
$0.2197$, the decimal rounded down and checked by the kernel. **Our reading,
not proved:** it is also the exact breach probability, since a path without a
jump stays flat all year.
-/

/-- Under the rare-jump law of variance `64`, the exposure leaves `|s| ≤ 1` at
some mark of the year, `n ≤ 256`, with probability at least `1 − (1 − 2ε)²⁵⁶`,
where `2ε = 64/257²`: above `0.2197` (`three_point_lower_bound_decimal`). -/
theorem three_point_breaches_often :
    ENNReal.ofReal (1 - (1 - 2 * (64 / (2 * 257 ^ 2 : ℝ))) ^ 256) ≤
      pathMeasure (threePoint (64 / (2 * 257 ^ 2)) 257)
        {ω | ∃ n ≤ 256, ¬ exposureWithin 1 (run step compiled.initial ω n)} := by
  exact breach_ge_threePoint (by norm_num) (by norm_num) step_zero_fixed
    (step_big_breaches 257 (by norm_num [Δ])) (step_big_breaches (-257) (by norm_num [Δ]))

/-- The rare-jump law's lower bound as a decimal, rounded down:
`0.2197 < 1 − (1 − 64/257²)²⁵⁶`, the kernel evaluating the power. -/
theorem three_point_lower_bound_decimal :
    (2197 / 10000 : ℚ) < 1 - (1 - 64 / 257 ^ 2) ^ 256 := by
  decide +kernel

/-!
The card below has the same settings under this law: $4000$ paths of $256$
marks from seed $7$. The `rounded 32/66049` in its provenance names
$\varepsilon$ itself, a value float64 cannot hold exactly, which the sampler
rounded. Six of the eight drawn paths never move; the two that jump leave the
band in a single mark, and one of them jumps again later, because the stop is
observed, not modelled. By the year's end $22\,\%$ of the paths have hit the
stop: the card's $0.21875$ lies a little below the proved lower bound $0.2197$,
as a sample may, and its sampling interval, $20.6\,\%$ to $23.2\,\%$, contains
the bound. On the cards' sampled paths, equal volatility does not mean equal
risk of the stop: $0.70\,\%$ under the Gaussian against $22\,\%$ here. Lean
proves no year bound below $1/4$ for the Gaussian here, so that comparison is
the cards', not a theorem's.
-/

-- @evidence sample Gimle.Forseti.Examples.HedgedSpread.compiled (law := threepoint) (variance := 64) (paths := 4000) (steps := 256) (seed := 7) (observe := s) (barrier := 1) (show := 8)

/-!
## Tighter than 1 in 5: refuted

Could a desk that knows the shocks' variance promise $1/5$ for the year? No:
the bound fails for at least one law of the class, the rare-jump law, so it
does not hold over the class. The decider refutes it with the exact threshold:
the block's kernel step evaluates $(1 - 2\varepsilon)^{256}$ and confirms that
$1/5$ lies below $1 - (1 - 2\varepsilon)^{256}$, the route of the library's
`breach_within_year_fifth_refuted`. With `year_breach_bound`,
`three_point_in_class`, `three_point_breaches_often` and
`three_point_lower_bound_decimal`, the worst case over the variance class lies
above $0.2197$ and at most $1/4$, and $1/4$ is at most $1.14$ times it.
-/

-- @decide tight_limit : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/5
namespace Decided_tight_limit

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/5)

/-- For independent, identically distributed shocks drawn from any centred law with variance 64, the probability that the exposure s breaches 1 within 256 marks is at most 1/5. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0); `exposureWithin 1` is the band |s| ≤ 1. The stepped decider refuted it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 within 256 observe s breach 1 probability <= 1/5 -/
theorem tight_limit_refuted : ¬ (∀ law : Measure ℝ, TwoMomentLaw law 64 →
      BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/5)) := by
  have refuted : ¬ forsetiClaim := by
    unfold forsetiClaim
    intro h
    have hq : (1/5 : ℚ) < 1 - (1 - 2 * (64 / (2 * 257 ^ 2) : ℚ)) ^ 256 := by decide +kernel
    have hr := Rat.cast_lt (K := ℝ) |>.mpr hq
    push_cast at hr
    have hlaw := threePoint_twoMoment (ε := 64 / (2 * 257 ^ 2)) (L := 257) (by norm_num) (by norm_num)
    rw [show 2 * (64 / (2 * 257 ^ 2) : ℝ) * 257 ^ 2 = 64 by norm_num] at hlaw
    exact not_breachWithin_threePoint_exact (by norm_num) (by norm_num) step_zero_fixed (step_big_breaches 257 (by norm_num [Δ])) (step_big_breaches (-257) (by norm_num [Δ])) hr (h _ hlaw)
  intro claim
  refine (fun (bridge : _ ↔ forsetiClaim) => refuted (bridge.mp claim)) ?_
  constructor
  · intro claim
    exact claim
  · intro lane
    exact lane

end Decided_tight_limit

/-!
## One date at a time: at most 1 in 100 (proved)

A fixed-date quantile of limit utilisation picks a date in advance and bounds
the chance that the gross exposure is outside its limit on that date. Under
shocks sub-Gaussian with proxy $64$, the exposure at mark $n$ is sub-Gaussian
too, with its own proxy $\Delta^2 \cdot 64 \sum_{k<n} w_k^2$, computed exactly
over the rationals from the weights $w_k$ with which the shocks reach it (the
library's `proxy` and `exceeds_at_proxy`). It grows with the mark, and at the
year's end it is at most $913/10000$ (the library's `proxy_256_le`). The
decider's stage report puts it at about $0.0913$ and the tail bound it gives
at about $0.0084$, below the claimed $1/100$. What the block below certifies:
a `decide +kernel` step, of the same kind as `proxy_256_le`, shows that the
exposure's own proxy at mark $256$ is at most $18251/200000$; a cubic lower
bound on the exponential (`exp_ge_floor_cubic`) and linear arithmetic then
show $2 e^{-1/(2c)} \le 1/100$ for every proxy $c$ up to that. The theorem
states $1/100$ at every mark $n \le 256$, each mark taken separately.

**Our reading, not proved:** for Gaussian shocks of variance $64$ the
exposure's own proxy is its variance, so at the year's end the exposure is
Gaussian with variance about $0.0913$ and lies outside the limit with
probability about $0.09\,\%$; the proved $1/100$ is roughly ten times that.
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
        simp only [run_zero]
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
## Behind the bound: the gauge

The gauge $V = s^2 + h^2$ is the squared distance of the book from flat (the
library calls it `energy`). A breach forces $V > 1$, so the gauge is what the
year bound controls. One step moves it to

$$ \begin{aligned} V(x_{n+1}) &= \rho V(x_n) + 2\Delta c_n d_n \\ &\quad + \Delta^2 d_n^2, \\ c_n &= (1 - \Delta) s_n - \Delta h_n, \\ \rho &= (1 - \Delta)^2 + \Delta^2 \\ &= 1 - 2\Delta + 2\Delta^2. \end{aligned} $$

As in continuous time, the cross terms between $s$ and $h$ cancel, because the
coupling is skew-symmetric; this is the discrete twin of the first notebook's
`budget_rate`. Without a shock the step shrinks $V$ by the factor $\rho < 1$.
The shock enters once linearly, as $2\Delta c_n d_n$, with mean zero under a
centred law, and once as $\Delta^2 d_n^2$, whose mean is $\Delta^2$ times the
variance. Lean checks the identity against the two compiled rows.
-/

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
Taking the expectation over one shock, under a centred law of variance $64$,
gives $\rho\, V(x) + 64\,\Delta^2$ for one step from any fixed state $x$,
whatever the law's shape (`energy_step_eq`). Because the shocks are
independent this carries along the path,
$\mathbb{E} V_{n+1} = \rho\, \mathbb{E} V_n + 64\,\Delta^2$, and from the flat
book $\mathbb{E} V_n = 64\,\Delta^2 \sum_{k<n} \rho^k$ (`expected_energy_eq`).
It rises toward its long-run level $64\,\Delta^2/(1 - \rho) = 32/255$ and
stays below it at every mark (the library's `expected_energy_le`).
-/

/-- The long-run expected gauge at variance `64`: `Δ² · 64 / (1 − ρ) = 32/255`. -/
theorem stationary_energy : (Δ : ℝ) ^ 2 * 64 / (1 - ρ) = 32 / 255 := by
  norm_num [Δ, ρ]

/-- Under every centred shock law of variance `64`, the expected gauge is at most
`32/255` at every mark. -/
theorem expected_gauge_every_mark {law : Measure ℝ} (h : TwoMomentLaw law 64) :
    ∀ n, ExpectedLe step compiled.initial law energy n (32 / 255) := by
  intro n
  have bound := expected_energy_le h n
  rwa [stationary_energy] at bound

/-!
The year's end is still short of that level. The claim below puts the expected
gauge at the first year's end at most $1086/10000$, below $32/255$, as the
library's `expected_energy_year` does; the block writes the bound in lowest
terms, $543/5000$. Its kernel step evaluates the exact expectation
$64\,\Delta^2 \sum_{k<256} \rho^k$ and compares it with that bound. The
decider's stage report puts the exact value at about $0.1085$, so the claim
sits just above it.
-/

-- @decide expected_gauge : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 observe V expected <= 1086/10000 at 256
namespace Decided_expected_gauge

open MeasureTheory
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

def forsetiClaim : Prop :=
  ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    ExpectedLe step compiled.initial law energy 256 (543/5000)

/-- For independent, identically distributed shocks drawn from any centred law with variance 64, the expected energy V at mark 256 is at most 543/5000. `step` is the model's step of size 1/256 with the shock in its driver slot, from `compiled.initial` = (0, 0). The stepped decider proved it. Goal (stepped): stepped hedged-spread from (0, 0) at 0 step 1/256 shocks variance 64 observe V expected <= 543/5000 at 256 -/
theorem expected_gauge :
    ∀ law : Measure ℝ, TwoMomentLaw law 64 →
      ExpectedLe step compiled.initial law energy 256 (543/5000) := by
  have root : forsetiClaim := by
    unfold forsetiClaim
    intro law h
    have hq : Δ ^ 2 * 64 * geomSum 256 ≤ 543/5000 := by decide +kernel
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
## The year under thin tails: unknown

The last claim is $1/50$ for the year under shocks sub-Gaussian with proxy
$64$. Lean proves neither it nor its negation here: the library has no horizon
theorem for that class, the date-by-date $1/100$ does not add up over the year
(summed over the $256$ dates it is $2.56$, which bounds nothing), and the
rare-jump law that refutes $1/5$ is not in this class, so its refutation does
not carry over. The decider leaves the claim unknown and no block follows.
**Our reading, not proved:** a law sub-Gaussian with proxy $64$ has variance at
most $64$, so the year's $1/4$ would carry over through
`year_bound_any_variance_le`; whether thin tails buy anything below $1/4$ is
open here. The Gaussian card above, one law of this class, saw $0.70\,\%$ of
its paths hit the stop within the year: below $1/50$, and evidence about that
one law, not a bound over the class.
-/

-- @decide breach_within_year_subgaussian : stepped hedged-spread from (0, 0) at 0 step 1/256 shocks subgaussian 64 within 256 observe s breach 1 probability <= 1/50

/-!
## What is and is not in the picture

Variance alone buys a bound of 1 in 4 for the first year, giving the hedge no
credit, and that is nearly tight: one law of the class, gapping through the
limit in a day, comes within a factor of $1.14$ of it. Tails no heavier than a
Gaussian's buy 1 in 100, one date at a time. The year under thin tails is
unknown here. The grid at the top says which of these is proved, refuted or
unknown, and **Not claimed** there says what none of them covers.
-/

#print axioms year_bound_any_variance_le
#print axioms gaussian_in_both
#print axioms three_point_in_class
#print axioms three_point_breaches_often
#print axioms three_point_lower_bound_decimal
#print axioms energy_step_identity
#print axioms stationary_energy
#print axioms expected_gauge_every_mark

end Notebook.HedgedSpreadRisk
