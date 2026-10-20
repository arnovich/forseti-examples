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
This notebook's own theorems are the pieces a reader can check by eye: the
one-step identity for $V$ read off the compiled rows, the stationary constant
$32/255$, which laws belong to which class, and a lower bound on the breach
probability of the rare-jump law below.

**Refuted.** Variance alone cannot bring the year's breach bound below about
$0.2198$. A law with mass $64/(2 \cdot 257^2)$ at each of $\pm 257$ and the rest
at $0$ is centred with variance $64$, and under it the stop is hit within the
year with probability at least $1 - (1 - 64/257^2)^{256} \approx 0.2198$; the
library turns that into the refutation of the bound $1/5$
(`breach_within_year_fifth_refuted`). So the worst case over the class lies
between about $0.2198$ and $1/4$, and the distribution-free $1/4$ is at most
$1.14$ times the worst case it covers.

**Unknown.** Two things. Where between $1 - (1 - 64/257^2)^{256}$ and $1/4$ the
worst case over the variance-$64$ class lies: neither end is shown to be the
worst case. And the year as a whole under the sub-Gaussian hypothesis: the
date-by-date $1/100$ does not give a bound for the year (summed over the $256$
dates it is $2.56$, which bounds nothing), and no horizon bound under that
hypothesis is proved.
Whether a horizon bound under thin tails exists, and whether it beats $1/4$,
is neither proved nor refuted here.

**Not claimed.** Continuous time: every statement is about the marks of the
stepped chain — the scheme a simulator runs — and nothing about the
continuous-time book of `HedgedSpread`, a stochastic differential equation, or
how close the chain comes to either. Markets: which class real shocks belong
to is not addressed; the law is an assumption of each bound. Dependence:
shocks that cluster, trend, or change law during the year are outside the
model. The probability under any one law: the bounds hold over each class, the
Gaussian's own breach probability is not computed, and the rare-jump law's is
bounded only from below. Nothing about profit and loss, other starting books or
other step sizes.

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

#print axioms energy_step_identity
#print axioms stationary_energy
#print axioms three_point_in_class
#print axioms gaussian_in_both
#print axioms three_point_breaches_often

end Notebook.HedgedSpreadRisk
