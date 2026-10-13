import Mathlib
import Gimle.Forseti.Euler
import Gimle.Forseti.Examples.EulerContract
import Gimle.Asgard.Examples.EulerBand
import Gimle.Asgard.Streams.EulerRadius
import Gimle.Asgard.Streams.VorticityTable

/-!
# The Euler equations of a frictionless fluid, solved exactly as a power series in time: one solution, a certified radius, and how far it is from sharp

The equations that govern a frictionless fluid on a periodic square, solved as
a power series in time with exact rational coefficients. Lean checks the
coefficients, proves the series is the only one, proves it converges for
a short time — a very short time, with the gap to the true radius shown rather
than hidden — and proves that its sum solves the vorticity equation there.

Follow the argument from the formal recurrence, through exact coefficients
and a convergence certificate, to the classical vorticity solution. Generated
contracts and the separate viscous time-series question follow those steps.

The two-dimensional Euler equations for an incompressible fluid on the
$2\pi$-periodic square, written for the vorticity $\omega = \operatorname{curl} u$,

$$ \omega_t + u \cdot \nabla \omega = 0, \qquad u = \nabla^\perp \psi = (-\partial_y\psi,\ \partial_x\psi), \qquad \Delta \psi = \omega, $$

are the Navier–Stokes equations $\omega_t + u\cdot\nabla\omega = \nu\Delta\omega$
with the viscosity $\nu$ set to zero. The Galerkin notebooks on this shelf
study finite truncations of that equation — three, five or twelve Fourier
modes, an ordinary differential equation each. This notebook is about the
equation itself, as a **formal power series in time** whose coefficients are
trigonometric polynomials in space: $\omega = \sum_n \omega_n(x)\,t^n$, each
$\omega_n$ a finite sum of modes $e^{ik\cdot x}$ with exact rational
coefficients. It is the first page on the shelf about an incompressible fluid
in two space dimensions rather than a truncation of one;
[Burgers](Burgers.lean) did the same for the one-dimensional model.

The main example's initial vorticity is

$$ \omega_0 = \cos x + \cos(x+y) + \cos(2x+y), $$

the three modes of the `NS_T3` notebook's Galerkin member, each with amplitude
one.

**Proved.** The formal recurrence has a unique stream for each initial
vorticity. For the chosen start, Lean checks exact coefficients and persistent
mean-zero and even symmetries. The series converges and realizes the classical
vorticity equation on $|t|<1/648$. On $|t|\le1/6480$, the window through $t^2$
has error at most $1/100$, and the field stays within $1/50$ of its initial
value. These are certified local bounds, not the true convergence radius.

**Disproved and unresolved.** Two checked negations reject a wrong coefficient
and the assertion that viscosity leaves another coefficient unchanged. Six
stream-decider requests are checked; the upper bound $u\le3$ remains unknown
and emits no claim. No claim on this page has a recorded *refuted* status.

**Scope.** Uniqueness is among formal streams of trigonometric polynomials
with rational coefficients, not arbitrary classical solutions. The classical
result supplies the partial derivatives used in the vorticity equation;
pressure and the full velocity-pressure formulation are outside the claims.
The Fourier motivation is explained in **Read the recurrence and its carrier**.
The true radius beyond $1/648$, long-time behavior, global regularity and
three-dimensional flow are not established. For $\nu=1/10$, a factorial upper
bound certifies neither convergence nor divergence of the viscous time series.
The separate interaction expansion is explained in [Navier–Stokes](NavierStokes.lean).

## Construct the unique formal stream {fold}

The recurrence determines one formal stream from each initial vorticity.
For the chosen start, the circuit contract also packages the local bounds
and classical realization established below. Uniqueness here concerns formal
streams, not arbitrary classical solutions.

### Read the recurrence and its carrier {fold}

Each coefficient depends only on earlier time degrees. This makes the
formal construction causal; the carrier records exact rational Fourier
coefficients rather than sampled fields.

On the Fourier side the equation is explicit. With $\hat\omega_k$ the
coefficient of $e^{ik\cdot x}$, the transport $u\cdot\nabla\omega$ has
coefficient $\sum_{p+q=k} \frac{p \times q}{|p|^2}\,\hat\omega_p\,\hat\omega_q$:
the velocity of mode $p$ is $i\,p^\perp\hat\omega_p/(-|p|^2)$ with
$p^\perp = (-p_2, p_1)$, the gradient of mode $q$ is $i q\,\hat\omega_q$, and the
two factors of $i$ make the product rational. That this coupling is the
Fourier symbol of $u\cdot\nabla\omega$ is the motivation: the carrier of
trigonometric polynomials with rational coefficients has no derivative
operator (a single derivative multiplies by $ik_1$), so the library *defines*
the transport by the coupling; `Torus.transport_eq_jacobian` ties it to
$-(p\times q)$ against $\Delta^{-1}$ on the formal side, and the Jacobian
identity `Torus.field_transport` ties its field to
$\partial_1\psi\,\partial_2 q - \partial_2\psi\,\partial_1 q$ as real functions.
The coefficient of $t^{n+1}$ is

$$ (n+1)\,\omega_{n+1} = \nu\,\Delta\omega_n - \sum_{m \le n} B(\omega_m, \omega_{n-m}), $$

$$ B(P,Q)_k = \sum_{p+q=k} \frac{p\times q}{|p|^2}\,P_p\,Q_q, $$

and the right-hand side involves only $t$-degrees $\le n$: the equation is
**causal** in $t$. The library's formal existence-and-uniqueness lemma (the
formal half of Cauchy–Kowalevski: Picard iteration along $t$ builds a
solution, strong induction on the degree shows it is the only one) was proved
for streams of rational coefficients; for this page it was restated once for
any carrier with a graded notion of agreement, and the trigonometric streams
are its second instance.
-/
namespace Notebook.Euler

open Gimle.Asgard.Streams (TrigStream)
open Gimle.Asgard.Streams.Torus Gimle.Asgard.Streams.TrigStream Gimle.Asgard.Streams.NS
  Gimle.Asgard.Examples.EulerThreeMode Gimle.Asgard.Examples.EulerBand Real

/-!
A trigonometric polynomial is `TrigPoly`, a finitely supported function from
integer wavevectors `(ℤ × ℤ)` to `ℚ`; `cosine k` is `cos(k·x)`, half on `k`
and half on `−k`. A stream is `TrigStream := ℕ → TrigPoly`, and
`stream .ogf ν b` is the formal solution of the vorticity equation with
viscosity `ν` from the boundary stream `b`, of which only `b 0` is read. The
start `start` has `ω₀ = cosine (1, 0) + cosine (1, 1) + cosine (2, 1)` at
degree zero; `stream .ogf 0 start n k` is the coefficient of `tⁿ e^{ik·x}`.
`l1` is the ℓ¹ norm of a polynomial's coefficients; `analyticField ω t x` is
Lean's `∑'` of `field (ω n) x · tⁿ` with `field P x = Σ_k P_k cos(k·x)`, which
is `0` where the series does not converge — `converges` below is what makes
it the sum; and `windowField N` is the finite sum through `t`-degree `N − 1`.

### State the total circuit contract {fold}

The system is Asgard's typed Fourier feedback circuit `vorticityCircuit .ogf 0`:
it integrates the negative transport of its feedback state from the input's
initial slice. The input supplies only initial vorticity; the solution is the
output of the circuit. Forseti's `Fourier.Contract` proves existence, uniqueness
among formal circuit outputs, and a postcondition for every such output.

For the three-mode start, `certified` says that the output is the formal solution,
all its coefficients are even and mean zero, its window through `t²` is within
`1/100` on `|t| ≤ 1/6480`, its field stays within `1/50` of the initial field
there, and it is a classical vorticity solution on `|t| < 1/648`.
The supporting mathematical claims below explain these components; the system
claim is this contract over the circuit.

**What the workbench checks.** Every claim below is a theorem Lean re-checks
as part of this file. The library proves the general ones itself
(`NS.stream_pde`, `NS.stream_slice`, `NS.formal_unique`,
`NS.euler_l1_geometric`, `TrigStream.truncationBound`, `NS.euler_classical`,
`NS.gevrey_one`) and the example values (`EulerThreeMode.euler_t_x` and its
siblings, `EulerThreeMode.coeff_meanZero`, `coeff_isEven`, `EulerBand.euler_l1`,
`l1_one`, `l1_two`, `hasSum_field`, `truncation`, `band`, `classical`,
`vorticity_equation`, `laplacian_streamFunction`, `initial`, `viscous_gevrey`);
they are restated here so that the pinned library, under this notebook's own
check, carries them. Proved on this page: the two negations,
`discarded_mode` (the kernel evaluates the transport table here) and
`viscous_created_same`.
-/

/-- The Euler circuit has a unique formal output, with certified local bounds and PDE realization. -/
theorem circuit_contract :
    Gimle.Forseti.Fourier.Contract (vorticityCircuit .ogf 0)
      (fun input => input 0 0 = ω₀)
      Gimle.Forseti.Examples.EulerContract.certified := by
  exact Gimle.Forseti.Examples.EulerContract.euler_contract

/-!
### Establish formal existence and uniqueness {fold}

The library's stream solves the equation with the given start, and two formal
streams satisfying the Euler equation with the same initial vorticity are
equal. The claims are for `ν = 0`; the library's theorems are for every `ν`
and either basis.
-/

/-- The constructed stream satisfies the Euler equation and starts at `ω₀`. -/
theorem existence :
    derivative .ogf (stream .ogf 0 start) = rhs .ogf 0 (stream .ogf 0 start) ∧
      stream .ogf 0 start 0 = ω₀ := by
  exact ⟨stream_pde .ogf 0 start, stream_slice .ogf 0 start⟩

/-- Two formal Euler solutions with the same initial vorticity are the same stream. -/
theorem uniqueness (a b : TrigStream)
    (ha : derivative .ogf a = rhs .ogf 0 a) (hb : derivative .ogf b = rhs .ogf 0 b)
    (slice : a 0 = b 0) : a = b := by
  exact formal_unique .ogf 0 a b ha hb slice

/-!
## Inspect coefficients and preserved symmetries {fold}

Exact coefficients show which modes the equation creates, including one
absent from the three-mode truncation. Mean zero and evenness persist at every
degree. The wrong-coefficient claim is disproved by a checked negation.

### Compute the first coefficients {fold}

Each value is a rational the kernel computed in the library from the
recurrence on a table of `(mode, coefficient)` pairs — the Picard iteration
mirrored on finite lists, with a proved bridge to the exact stream
(`NS.stream_coeff`) — and the page restates the library's theorem.
-/

/-- The coefficient of $t\,e^{ix}$ is $-\tfrac{3}{40}$. -/
theorem coefficient_t_x : stream .ogf 0 start 1 (1, 0) = -3 / 40 := by
  exact euler_t_x

/-- The coefficient of $t\,e^{iy}$ is $\tfrac18$: a mode absent from the start,
which the three-mode Galerkin truncation discards and the equation creates at
the first step. -/
theorem coefficient_t_y : stream .ogf 0 start 1 (0, 1) = 1 / 8 := by
  exact euler_t_y

/-- At $t^2$: the coefficient of $e^{i(2x+2y)}$ is $\tfrac{11}{130}$ and of
$e^{i(x+y)}$ is $-\tfrac{49}{1300}$. -/
theorem coefficients_t2 :
    stream .ogf 0 start 2 (2, 2) = 11 / 130 ∧ stream .ogf 0 start 2 (1, 1) = -49 / 1300 := by
  exact ⟨euler_t2_2x2y, euler_t2_xy⟩

/-- At $t^3$: the coefficient of $e^{ix}$ is $\tfrac{27}{32000}$. -/
theorem coefficient_t3_x : stream .ogf 0 start 3 (1, 0) = 27 / 32000 := by
  exact euler_t3_x

/-- The transport of the start by itself lands on the discarded mode $(0, 1)$
with $-\tfrac18$: the same number as `coefficient_t_y` with the sign of the
recurrence, $\omega_1 = -B(\omega_0, \omega_0)$. Proved on this page through the
library's table mirror of the bilinear form, evaluated by the kernel here. -/
theorem discarded_mode : transport ω₀ ω₀ (0, 1) = -1 / 8 := by
  rw [ω₀_eq_table, ← Table.toTrig_transport, Table.toTrig_apply]
  decide +kernel

/-!
### Reject the wrong coefficient {fold}

From `coefficient_t_x` by arithmetic: the coefficient of $t\,e^{ix}$ is not
$-\tfrac18$. This is a theorem of the negation proved on this page, using the
page's own claim, so its status is checked, not refuted — only a decider
records refuted.
-/

/-- The coefficient of $t\,e^{ix}$ is not $-\tfrac18$. -/
theorem wrong_coefficient : stream .ogf 0 start 1 (1, 0) ≠ -1 / 8 := by
  rw [coefficient_t_x]
  norm_num

/-!
### Preserve mean zero and evenness {fold}

The start has no zero mode and even coefficients, and both propagate: the
transport has no zero mode at all ($p \times (-p) = 0$) and is even on even
data. Both are also what `NS.euler_classical` asks of the start; the reading of
the cosine field as the real part of $\sum_k \hat\omega_k e^{ik\cdot x}$ names
the coefficients and enters no theorem.
-/

/-- Every coefficient of the Euler stream has zero mean. -/
theorem mean_zero (n : ℕ) : stream .ogf 0 start n 0 = 0 := by
  exact coeff_meanZero 0 n

/-- Every coefficient of the Euler stream is even in the mode. -/
theorem even (n : ℕ) (k : Wave) : stream .ogf 0 start n (-k) = stream .ogf 0 start n k := by
  exact coeff_isEven 0 n k

/-!
## Certify convergence and finite-window bounds {fold}

For this start, $\|\omega_n\|_1 \le 9\cdot648^n$ certifies convergence for
$|t|<1/648$. On $|t|\le1/6480$, the window through $t^2$ has error at most
$1/100$. These are sufficient bounds, not a determination of the true radius.

### Explain the geometric certificate {fold}

The induction pays for each derivative by reducing the spatial analyticity
radius. Its constants give a time-convergence guarantee; the observed ratios
of finitely many coefficients do not prove a larger radius.

Each step of the recurrence costs one derivative: the coupling
$|p\times q|/|p|^2$ is at most $|q|_1 = |q_1| + |q_2|$, the size of the mode it
differentiates. A geometric bound on the coefficients cannot absorb a factor
that grows with the step, so the induction runs in a scale of norms
$\|P\|_\sigma = \sum_k |P_k|\,e^{\sigma|k|_1}$, $0 \le \sigma < \sigma_0$,
paying each derivative with a loss of radius $\sigma$ (Nagumo's estimate
$|k|\,e^{\sigma|k|} \le e^{\sigma'|k|}/(2(\sigma'-\sigma))$) and keeping the
losses summable with the weight $1/(n+1)^2$:

$$ \|\omega_n\|_\sigma \le M\Big(\frac{24M}{\sigma_0-\sigma}\Big)^n \frac{1}{(n+1)^2}, \qquad M \ge \|\omega_0\|_{\sigma_0}. $$

This is the classical argument of Nirenberg and Nishida, in its weighted form;
what is new is that it is in Lean, with rational constants. At $\sigma = 0$ it
is a geometric bound on the $\ell^1$ norms, and with $\sigma_0 = 1/K$ for a
start whose modes have size at most $K$ and $\ell^1$ norm at most $L$, every
constant is rational: $\|\omega_n\|_{\ell^1} \le 3L\,(72LK)^n$. Here $K = 3$ and
$L = 3$, hence $9\cdot 648^n$.

The radius this certifies is small. The constants are not sharp ($\tfrac12$
for $\tfrac1e$ in Nagumo, $3$ for $e$, $8$ for a convolution sum whose true
supremum is near $4.6$), the device is pessimistic by nature, and the exact
norms, computed off-line from the recurrence with exact rational arithmetic,
say so. The values below are rounded:

$$ \begin{array}{c|l} n & \|\omega_n\|_{\ell^1},\ \nu = 0 \\ \hline 0,\dots,4 & 3,\ 1.6,\ 0.858,\ 0.563,\ 0.348 \\ 5,\dots,8 & 0.235,\ 0.145,\ 0.085,\ 0.052 \\ 9,\dots,12 & 0.032,\ 0.018,\ 0.011,\ 0.0064 \end{array} $$

The ratios $\|\omega_{n+1}\|/\|\omega_n\|$ sit between $0.53$ and $0.68$ for
$n \le 11$, which is what a radius between $1.5$ and $1.7$ looks like, some
thousand times the certified $\tfrac{1}{648}$. That is evidence, not a
theorem: nothing on this page says anything about the series beyond
$|t| < \tfrac{1}{648}$. The first two norms, $\tfrac85$ and $\tfrac{223}{260}$,
are bounded above by the library's kernel-computed tables and restated below
(the bounds are in fact equalities; the equality is not a Lean statement); the
rest are not Lean statements.

### Bound the coefficients and the sum {fold}

The induction in a scale, specialised to this start: every coefficient's
ℓ¹ norm is at most $9 \cdot 648^n$, the series of the field sums for
$|t| < \tfrac{1}{648}$, and on $|t| \le \tfrac{1}{6480}$ the sum is within
$\tfrac{1}{100}$ of the finite sum through $t^2$ and within $\tfrac{1}{50}$ of
the initial vorticity's field. The band uses the ℓ¹ norms of the first two
coefficients, bounded by $\tfrac85$ and $\tfrac{223}{260}$ from the
kernel-computed tables.
-/

/-- $\|\omega_n\|_{\ell^1} \le 9 \cdot 648^n$, with the induction's slack constants. -/
theorem geometric_bound (n : ℕ) : l1 (stream .ogf 0 start n) ≤ 9 * 648 ^ n := by
  exact euler_l1 n

/-- The ℓ¹ norms of the first two coefficients are at most $\tfrac85$ and
$\tfrac{223}{260}$ (in fact equal; the equality is not a Lean statement). -/
theorem first_norms :
    l1 (stream .ogf 0 start 1) ≤ 8 / 5 ∧ l1 (stream .ogf 0 start 2) ≤ 223 / 260 := by
  exact ⟨l1_one, l1_two⟩

/-- The $t$-series of the field converges for $|t| < \tfrac{1}{648}$. -/
theorem converges {t : ℝ} (x : ℝ × ℝ) (ht : |t| < 1 / 648) :
    HasSum (seriesTerm (stream .ogf 0 start) t x) (analyticField (stream .ogf 0 start) t x) := by
  exact hasSum_field x ht

/-- On $|t| \le \tfrac{1}{6480}$ the sum is within $\tfrac{1}{100}$ of the finite
sum through $t^2$, at every point. -/
theorem truncation_through_t2 : TruncationBound (stream .ogf 0 start) (1 / 6480) 3 (1 / 100) := by
  exact truncation

/-- On $|t| \le \tfrac{1}{6480}$ the sum is within $\tfrac{1}{50}$ of
$\cos x + \cos(x+y) + \cos(2x+y)$, at every point. -/
theorem band_around_start {t : ℝ} (x : ℝ × ℝ) (ht : |t| ≤ 1 / 6480) :
    |analyticField (stream .ogf 0 start) t x -
      (cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2))| ≤ 1 / 50 := by
  exact band x ht

/-!
## Realize the classical vorticity solution {fold}

On $|t|<1/648$, the sum has the needed continuous derivatives and solves the
vorticity equation with the stated initial field. This establishes classical
realization, not uniqueness among all classical solutions.

The library proves that the sum of the series is a classical solution of the
vorticity equation on $|t| < \tfrac{1}{648}$ (`NS.euler_classical`): the field
$\omega$ and its stream function $\Psi$, the sum of the series of
$\Delta^{-1}\omega_n$, have every partial derivative that appears — $\omega$ in
$t$ and in each $x$ coordinate, $\Psi$ to second order — each the sum of the
termwise derivatives and continuous in $(t, x)$; $\Delta\Psi = \omega$; the
velocity $u = \nabla^\perp\Psi = (-\partial_2\Psi, \partial_1\Psi)$ is
divergence-free because the two mixed derivatives of $\Psi$ are one series; and
$\partial_t\omega + u\cdot\nabla\omega = 0$ at every point. The equation is the
Euler equation in vorticity form, read off the Jacobian identity
$\partial_1\Psi\,\partial_2\omega - \partial_2\Psi\,\partial_1\omega = u\cdot\nabla\omega$;
the velocity form and its pressure are not formed. At $t = 0$ the sum is the
start's field.
-/

/-- On $|t| < \tfrac{1}{648}$ the sum is a classical solution: every partial derivative
that appears exists and is continuous, $\Delta\Psi = \omega$, and the equation holds. -/
theorem classical_solution {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    IsClassicalSolution (stream .ogf 0 start) t x := by
  exact classical ht x

/-- $\partial_t\omega + u\cdot\nabla\omega = 0$ with $u = (-\partial_2\Psi, \partial_1\Psi)$. -/
theorem solves_vorticity_equation {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesDt (stream .ogf 0 start) t x +
      (-seriesD₂ (psi (stream .ogf 0 start)) t x * seriesD₁ (stream .ogf 0 start) t x +
        seriesD₁ (psi (stream .ogf 0 start)) t x * seriesD₂ (stream .ogf 0 start) t x) = 0 := by
  exact vorticity_equation ht x

/-- $\Delta\Psi = \omega$: the stream function's Laplacian is the vorticity. -/
theorem stream_function {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesD₁₁ (psi (stream .ogf 0 start)) t x + seriesD₂₂ (psi (stream .ogf 0 start)) t x =
      analyticField (stream .ogf 0 start) t x := by
  exact laplacian_streamFunction ht x

/-- At $t = 0$ the sum is $\cos x + \cos(x+y) + \cos(2x+y)$. -/
theorem initial_vorticity (x : ℝ × ℝ) :
    analyticField (stream .ogf 0 start) 0 x = cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2) := by
  exact initial x

/-!
## Inspect the generated circuit contracts {fold}

The six generated contracts certify bounds for the listed starts; the
`euler-*` readings additionally include classical realization. The request
$u\le3$ remains unknown and has no claim card. Checked-claim counts therefore
do not count every unresolved request.

### Certify bounds for the three-mode start {fold}

The `trig-*` contracts certify truncation error $1/100$ and the band
$[-31/10,31/10]$ on $|t|\le1/6480$. They do not include classical realization;
the tighter upper bound $3$ remains undecided.


The stream decider has a lane for this stream. A `@decide` directive names the
start as its six modes, the window, the radius and the error; the decider
recomputes $K = 3$, $L = 3$, $M = 3L = 9$, $\rho = 72LK = 648$ and the
certified bound $M(\rho r)^N/(1 - \rho r)$, writes the application of `euler_l1_geometric`
and `truncationBound_rat` with every side condition left to the kernel, and
the proof lifts these bounds through `Fourier.solution_contract` and
`Contract.consequence`. Each generated theorem is a total contract for
`vorticityCircuit .ogf 0`, with only the initial slice prescribed and convergence
and bounds on every circuit output. Lean checks that contract as part of this
file. These `trig-*` readings do not claim classical realization; that is included
in `circuit_contract` above and the `euler-*` section below. The first directive asks the bound
of `truncation_through_t2` and is checked, over the start spelled out as a
table of modes. The second asks a band on the sum itself rather than on its
distance from the start's field: the ℓ¹ norms $3, \tfrac85, \tfrac{223}{260}$
of the window through $t^2$, recomputed by the kernel from the Picard tables
(exact for these tables of distinct modes; the proof uses only
$\|\omega_n\|_{\ell^1} \le$ `Table.absSum`), plus the tail $\tfrac{1}{100}$
bound it by about $3.0102$ on
$|t| \le \tfrac{1}{6480}$, so $[-\tfrac{31}{10}, \tfrac{31}{10}]$ is
checked. The third asks $u \le 3$, the start's own ℓ¹ norm: no window's bound
separates it, and this lane evaluates the sum at no point, so it stays
undecided — exhausted, not refuted, and no claim is written. Whether the sum
ever exceeds $3$ is not settled here either way.
-/

-- @decide truncation_decided : stream vorticity viscosity 0 interpretation trig-truncation
--   basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2]
--   truncation u window 3 radius 1/6480 epsilon 1/100

namespace Decided_truncation_decided

def forsetiTable : Gimle.Asgard.Streams.Torus.Table :=
  [((1, 0), (mkRat (1) 2)), ((-1, 0), (mkRat (1) 2)), ((1, 1), (mkRat (1) 2)), ((-1, -1), (mkRat (1) 2)), ((2, 1), (mkRat (1) 2)), ((-2, -1), (mkRat (1) 2))]

noncomputable def forsetiStart : Gimle.Asgard.Streams.TrigStream :=
  fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop :=
  (∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (((mkRat (1) 6480) : ℚ) : ℝ) →
    HasSum (Gimle.Asgard.Streams.TrigStream.seriesTerm (output 0) t x)
      (Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x)) ∧
  Gimle.Asgard.Streams.TrigStream.TruncationBound (output 0) (((mkRat (1) 6480) : ℚ) : ℝ) 3 (((mkRat (1) 100) : ℚ) : ℝ)

def forsetiRoot : Prop :=
  Gimle.Forseti.Fourier.Contract
    (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf (mkRat (0) 1))
    (fun input => input 0 0 = forsetiStart 0) forsetiPost

/-- The Fourier feedback circuit (ν = 0; ν = 0 is the Euler equation) admits every input whose initial vorticity is Σ c·e^(i k·x) over the listed ((k₁, k₂), c); higher boundary coefficients are free. In basis ogf, a unique formal output exists and every output ω satisfies the bound: its series converges for |t| ≤ 1/6480, and the window through t^2 is within 1/100 of the sum there. This claim does not assert classical PDE realization; that theorem additionally needs an even, mean-zero start. The stream decider proved it. Goal (stream): stream vorticity viscosity 0 interpretation trig-truncation basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2] truncation u window 3 radius 1/6480 epsilon 1/100 -/
theorem truncation_decided :
    Gimle.Forseti.Fourier.Contract (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))])
      (fun output =>
        have ω := output 0;
        (∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (1/6480) →
          HasSum (Gimle.Asgard.Streams.TrigStream.seriesTerm ω t x)
            (Gimle.Asgard.Streams.TrigStream.analyticField ω t x)) ∧
        Gimle.Asgard.Streams.TrigStream.TruncationBound ω (1/6480) 3 (1/100)) := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    apply (Gimle.Forseti.Fourier.solution_contract .ogf (mkRat (0) 1) forsetiStart).consequence (fun _ h => h)
    intro output same
    subst output
    unfold forsetiPost
    simp only [Matrix.cons_val_zero]
    have geo : Gimle.Asgard.Streams.TrigStream.GeometricBound (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) (((mkRat (9) 1) : ℚ) : ℝ) (((mkRat (648) 1) : ℚ) : ℝ) := by
      intro n
      have h := Gimle.Asgard.Streams.NS.euler_l1_geometric forsetiStart (K := 3) (by decide) (Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (by decide)) (L := (mkRat (3) 1)) ((Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))) n
      have e : (3 * ((mkRat (3) 1) : ℚ) * (72 * (mkRat (3) 1) * ((3 : ℕ) : ℚ)) ^ n) = (mkRat (9) 1) * (mkRat (648) 1) ^ n := by norm_num [Rat.mkRat_eq_div]
      rw [e] at h
      have h' : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart n) : ℚ) : ℝ) ≤ (((mkRat (9) 1) * (mkRat (648) 1) ^ n : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    refine ⟨fun t x ht => ?_, ?_⟩
    · exact Gimle.Asgard.Streams.TrigStream.hasSum_analyticField geo (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) ht
    · refine (Gimle.Asgard.Streams.TrigStream.truncationBound_rat geo (by decide +kernel) (by decide +kernel) _).mono ?_
      exact_mod_cast (show Gimle.Asgard.Streams.TrigStream.tailBound (mkRat (9) 1) (mkRat (648) 1) (mkRat (1) 6480) 3 ≤ (mkRat (1) 100) by decide +kernel)
  have forsetiInitial : forsetiStart 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))] := by
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (0) 1) : ℚ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 6480) : ℚ) : ℝ) = (1/6480) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (1) 100) : ℚ) : ℝ) = (1/100) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1] at lane
    dsimp only
    exact lane

end Decided_truncation_decided




-- @decide band_decided : stream vorticity viscosity 0 interpretation trig-band
--   basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2]
--   band u radius 1/6480 : u >= -31/10 and u <= 31/10

namespace Decided_band_decided

def forsetiTable : Gimle.Asgard.Streams.Torus.Table :=
  [((1, 0), (mkRat (1) 2)), ((-1, 0), (mkRat (1) 2)), ((1, 1), (mkRat (1) 2)), ((-1, -1), (mkRat (1) 2)), ((2, 1), (mkRat (1) 2)), ((-2, -1), (mkRat (1) 2))]

noncomputable def forsetiStart : Gimle.Asgard.Streams.TrigStream :=
  fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop :=
  (∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (((mkRat (1) 6480) : ℚ) : ℝ) →
    HasSum (Gimle.Asgard.Streams.TrigStream.seriesTerm (output 0) t x)
      (Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x)) ∧
  ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (((mkRat (1) 6480) : ℚ) : ℝ) →
    (((mkRat (-31) 10) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x ∧ Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x ≤ (((mkRat (31) 10) : ℚ) : ℝ)

def forsetiRoot : Prop :=
  Gimle.Forseti.Fourier.Contract
    (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf (mkRat (0) 1))
    (fun input => input 0 0 = forsetiStart 0) forsetiPost

def forsetiBound : ℚ := (mkRat (32864382943) 10917504000)

/-- The Fourier feedback circuit (ν = 0; ν = 0 is the Euler equation) admits every input whose initial vorticity is Σ c·e^(i k·x) over the listed ((k₁, k₂), c); higher boundary coefficients are free. In basis ogf, a unique formal output exists and every output ω satisfies the bound: its series converges for |t| ≤ 1/6480, and its sum stays within the band there. This claim does not assert classical PDE realization; that theorem additionally needs an even, mean-zero start. The stream decider proved it. Goal (stream): stream vorticity viscosity 0 interpretation trig-band basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2] band u radius 1/6480 : u >= -31/10 and u <= 31/10 -/
theorem band_decided :
    Gimle.Forseti.Fourier.Contract (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))])
      (fun output =>
        have ω := output 0;
        (∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (1/6480) →
          HasSum (Gimle.Asgard.Streams.TrigStream.seriesTerm ω t x)
            (Gimle.Asgard.Streams.TrigStream.analyticField ω t x)) ∧
        ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (1/6480) →
          (-31/10) ≤ Gimle.Asgard.Streams.TrigStream.analyticField ω t x ∧ Gimle.Asgard.Streams.TrigStream.analyticField ω t x ≤ (31/10)) := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    apply (Gimle.Forseti.Fourier.solution_contract .ogf (mkRat (0) 1) forsetiStart).consequence (fun _ h => h)
    intro output same
    subst output
    unfold forsetiPost
    simp only [Matrix.cons_val_zero]
    have geo : Gimle.Asgard.Streams.TrigStream.GeometricBound (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) (((mkRat (9) 1) : ℚ) : ℝ) (((mkRat (648) 1) : ℚ) : ℝ) := by
      intro n
      have h := Gimle.Asgard.Streams.NS.euler_l1_geometric forsetiStart (K := 3) (by decide) (Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (by decide)) (L := (mkRat (3) 1)) ((Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))) n
      have e : (3 * ((mkRat (3) 1) : ℚ) * (72 * (mkRat (3) 1) * ((3 : ℕ) : ℚ)) ^ n) = (mkRat (9) 1) * (mkRat (648) 1) ^ n := by norm_num [Rat.mkRat_eq_div]
      rw [e] at h
      have h' : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart n) : ℚ) : ℝ) ≤ (((mkRat (9) 1) * (mkRat (648) 1) ^ n : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    refine ⟨fun t x ht => ?_, fun t x ht => ?_⟩
    · exact Gimle.Asgard.Streams.TrigStream.hasSum_analyticField geo (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) ht
    · have b := Gimle.Asgard.Streams.TrigStream.abs_analyticField_le (x := x) geo (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) ht 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b
      have h0 : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart 0) : ℚ) : ℝ) ≤ (((mkRat (3) 1) : ℚ) : ℝ) := by
        rw [Gimle.Asgard.Streams.NS.stream_eq_table (mkRat (0) 1) forsetiTable forsetiStart rfl]
        exact_mod_cast (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))
      have h1 : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart 1) : ℚ) : ℝ) ≤ (((mkRat (8) 5) : ℚ) : ℝ) := by
        rw [Gimle.Asgard.Streams.NS.stream_eq_table (mkRat (0) 1) forsetiTable forsetiStart rfl]
        exact_mod_cast (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))
      have h2 : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart 2) : ℚ) : ℝ) ≤ (((mkRat (223) 260) : ℚ) : ℝ) := by
        rw [Gimle.Asgard.Streams.NS.stream_eq_table (mkRat (0) 1) forsetiTable forsetiStart rfl]
        exact_mod_cast (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))
      have hB : |Gimle.Asgard.Streams.TrigStream.analyticField (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) t x| ≤ ((forsetiBound : ℚ) : ℝ) := by
        refine b.trans ?_
        norm_num [forsetiBound, Rat.mkRat_eq_div] at h0 h1 h2 ⊢
        linarith
      have hb := abs_le.mp hB
      norm_num [forsetiBound, Rat.mkRat_eq_div] at hb ⊢
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have forsetiInitial : forsetiStart 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))] := by
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (0) 1) : ℚ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 6480) : ℚ) : ℝ) = (1/6480) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (-31) 10) : ℚ) : ℝ) = (-31/10) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (31) 10) : ℚ) : ℝ) = (31/10) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2] at lane
    dsimp only
    exact lane

end Decided_band_decided




-- @decide band_tighter : stream vorticity viscosity 0 interpretation trig-band
--   basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2]
--   band u radius 1/6480 : u <= 3

/-!
### Include classical realization for a different start {fold}

For $\cos x+\tfrac12\cos(2y)$, the `euler-*` contracts include the classical
vorticity equation, error $1/100$ through $t^2$, and band $[-2,2]$ on
$|t|\le1/2160$. Uniqueness still concerns formal circuit outputs.


The preceding `trig-*` decisions certify convergence and quantitative bounds.
The explicit `euler-*` readings also certify the classical vorticity equation,
the initial field, and the mean-zero and even invariants of the actual circuit
output. Lean checks the symmetry and zero mean of the literal mode table.

For $\omega_0 = \cos x + \tfrac12\cos(2y)$, the initial norm is
$L=\tfrac32$ and the largest mode size is $K=2$. The certified open radius
is therefore $1/(72LK)=1/216$. On the smaller closed interval
$|t|\le 1/2160$, the window through $t^2$ has error at most $1/100$,
and the field stays in $[-2,2]$. These are total contracts on Asgard's
Fourier feedback circuit: only its input's initial slice is prescribed.
The uniqueness claim concerns formal streams.
-/

-- @decide classical_multimode_tail : stream vorticity viscosity 0 interpretation euler-truncation
--   basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [0, 2, 1/4], [0, -2, 1/4]
--   truncation u window 3 radius 1/2160 epsilon 1/100

namespace Decided_classical_multimode_tail

def forsetiTable : Gimle.Asgard.Streams.Torus.Table :=
  [((1, 0), (mkRat (1) 2)), ((-1, 0), (mkRat (1) 2)), ((0, 2), (mkRat (1) 4)), ((0, -2), (mkRat (1) 4))]

noncomputable def forsetiStart : Gimle.Asgard.Streams.TrigStream :=
  fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop :=
  Gimle.Forseti.Euler.Certified forsetiStart (((mkRat (1) 2160) : ℚ) : ℝ) output ∧
  Gimle.Asgard.Streams.TrigStream.TruncationBound (output 0) (((mkRat (1) 2160) : ℚ) : ℝ) 3 (((mkRat (1) 100) : ℚ) : ℝ)

def forsetiRoot : Prop :=
  Gimle.Forseti.Fourier.Contract
    (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf (mkRat (0) 1))
    (fun input => input 0 0 = forsetiStart 0) forsetiPost

/-- The Euler Fourier feedback circuit admits the listed initial modes, with higher boundary coefficients free. Its unique formal output has the prescribed initial field, mean-zero and even coefficients, and a convergent classical Euler field on the closed interval |t| ≤ 1/2160, including both endpoints. In addition, its series converges for |t| ≤ 1/2160, and the window through t^2 is within 1/100 of the sum there. Uniqueness concerns the formal stream; no classical uniqueness or maximal lifetime is claimed. The stream decider proved it. Goal (stream): stream vorticity viscosity 0 interpretation euler-truncation basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [0, 2, 1/4], [0, -2, 1/4] truncation u window 3 radius 1/2160 epsilon 1/100 -/
theorem classical_multimode_tail :
    Gimle.Forseti.Fourier.Contract (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))])
      (fun output =>
        have ω := output 0;
        Gimle.Forseti.Euler.Certified (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))]) (1/2160) output ∧
        Gimle.Asgard.Streams.TrigStream.TruncationBound ω (1/2160) 3 (1/100)) := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    apply (Gimle.Forseti.Fourier.solution_contract .ogf (mkRat (0) 1) forsetiStart).consequence (fun _ h => h)
    intro output same
    subst output
    unfold forsetiPost
    simp only [Matrix.cons_val_zero]
    have geo : Gimle.Asgard.Streams.TrigStream.GeometricBound (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) (((mkRat (9) 2) : ℚ) : ℝ) (((mkRat (216) 1) : ℚ) : ℝ) := by
      intro n
      have h := Gimle.Asgard.Streams.NS.euler_l1_geometric forsetiStart (K := 2) (by decide) (Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (by decide)) (L := (mkRat (3) 2)) ((Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))) n
      have e : (3 * ((mkRat (3) 2) : ℚ) * (72 * (mkRat (3) 2) * ((2 : ℕ) : ℚ)) ^ n) = (mkRat (9) 2) * (mkRat (216) 1) ^ n := by norm_num [Rat.mkRat_eq_div]
      rw [e] at h
      have h' : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart n) : ℚ) : ℝ) ≤ (((mkRat (9) 2) * (mkRat (216) 1) ^ n : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    refine ⟨?_, ?_⟩
    · exact Gimle.Forseti.Euler.certified forsetiStart
        (Gimle.Forseti.Euler.Table.meanZero (table := forsetiTable) (by decide +kernel))
        (Gimle.Forseti.Euler.Table.isEven (table := forsetiTable) (by decide +kernel))
        (Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (K := 2) (by decide)) geo
        (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div])
    · refine (Gimle.Asgard.Streams.TrigStream.truncationBound_rat geo (by decide +kernel) (by decide +kernel) _).mono ?_
      exact_mod_cast (show Gimle.Asgard.Streams.TrigStream.tailBound (mkRat (9) 2) (mkRat (216) 1) (mkRat (1) 2160) 3 ≤ (mkRat (1) 100) by decide +kernel)
  have forsetiInitial : forsetiStart 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))] := by
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (0) 1) : ℚ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 2160) : ℚ) : ℝ) = (1/2160) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (1) 100) : ℚ) : ℝ) = (1/100) := by norm_num [Rat.mkRat_eq_div]
  have forsetiBoundary : forsetiStart = (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))]) := by
    funext n
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiBoundary, Rat.cast_zero]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiBoundary, Rat.cast_zero] at lane
    dsimp only
    exact lane

end Decided_classical_multimode_tail


-- @decide classical_multimode_band : stream vorticity viscosity 0 interpretation euler-band
--   basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [0, 2, 1/4], [0, -2, 1/4]
--   band u radius 1/2160 : u >= -2 and u <= 2

namespace Decided_classical_multimode_band

def forsetiTable : Gimle.Asgard.Streams.Torus.Table :=
  [((1, 0), (mkRat (1) 2)), ((-1, 0), (mkRat (1) 2)), ((0, 2), (mkRat (1) 4)), ((0, -2), (mkRat (1) 4))]

noncomputable def forsetiStart : Gimle.Asgard.Streams.TrigStream :=
  fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop :=
  Gimle.Forseti.Euler.Certified forsetiStart (((mkRat (1) 2160) : ℚ) : ℝ) output ∧
  ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (((mkRat (1) 2160) : ℚ) : ℝ) →
    (((mkRat (-2) 1) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x ∧ Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x ≤ (((mkRat (2) 1) : ℚ) : ℝ)

def forsetiRoot : Prop :=
  Gimle.Forseti.Fourier.Contract
    (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf (mkRat (0) 1))
    (fun input => input 0 0 = forsetiStart 0) forsetiPost

def forsetiBound : ℚ := (mkRat (2) 1)

/-- The Euler Fourier feedback circuit admits the listed initial modes, with higher boundary coefficients free. Its unique formal output has the prescribed initial field, mean-zero and even coefficients, and a convergent classical Euler field on the closed interval |t| ≤ 1/2160, including both endpoints. In addition, its series converges for |t| ≤ 1/2160, and its sum stays within the band there. Uniqueness concerns the formal stream; no classical uniqueness or maximal lifetime is claimed. The stream decider proved it. Goal (stream): stream vorticity viscosity 0 interpretation euler-band basis ogf start modes [1, 0, 1/2], [-1, 0, 1/2], [0, 2, 1/4], [0, -2, 1/4] band u radius 1/2160 : u >= -2 and u <= 2 -/
theorem classical_multimode_band :
    Gimle.Forseti.Fourier.Contract (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))])
      (fun output =>
        have ω := output 0;
        Gimle.Forseti.Euler.Certified (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))]) (1/2160) output ∧
        ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (1/2160) →
          -2 ≤ Gimle.Asgard.Streams.TrigStream.analyticField ω t x ∧ Gimle.Asgard.Streams.TrigStream.analyticField ω t x ≤ 2) := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    apply (Gimle.Forseti.Fourier.solution_contract .ogf (mkRat (0) 1) forsetiStart).consequence (fun _ h => h)
    intro output same
    subst output
    unfold forsetiPost
    simp only [Matrix.cons_val_zero]
    have geo : Gimle.Asgard.Streams.TrigStream.GeometricBound (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) (((mkRat (9) 2) : ℚ) : ℝ) (((mkRat (216) 1) : ℚ) : ℝ) := by
      intro n
      have h := Gimle.Asgard.Streams.NS.euler_l1_geometric forsetiStart (K := 2) (by decide) (Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (by decide)) (L := (mkRat (3) 2)) ((Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))) n
      have e : (3 * ((mkRat (3) 2) : ℚ) * (72 * (mkRat (3) 2) * ((2 : ℕ) : ℚ)) ^ n) = (mkRat (9) 2) * (mkRat (216) 1) ^ n := by norm_num [Rat.mkRat_eq_div]
      rw [e] at h
      have h' : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart n) : ℚ) : ℝ) ≤ (((mkRat (9) 2) * (mkRat (216) 1) ^ n : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    refine ⟨?_, fun t x ht => ?_⟩
    · exact Gimle.Forseti.Euler.certified forsetiStart
        (Gimle.Forseti.Euler.Table.meanZero (table := forsetiTable) (by decide +kernel))
        (Gimle.Forseti.Euler.Table.isEven (table := forsetiTable) (by decide +kernel))
        (Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (K := 2) (by decide)) geo
        (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div])
    · have b := Gimle.Asgard.Streams.TrigStream.abs_analyticField_le (x := x) geo (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) ht 1
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b
      have h0 : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart 0) : ℚ) : ℝ) ≤ (((mkRat (3) 2) : ℚ) : ℝ) := by
        rw [Gimle.Asgard.Streams.NS.stream_eq_table (mkRat (0) 1) forsetiTable forsetiStart rfl]
        exact_mod_cast (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))
      have hB : |Gimle.Asgard.Streams.TrigStream.analyticField (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) t x| ≤ ((forsetiBound : ℚ) : ℝ) := by
        refine b.trans ?_
        norm_num [forsetiBound, Rat.mkRat_eq_div] at h0 ⊢
        linarith
      have hb := abs_le.mp hB
      norm_num [forsetiBound, Rat.mkRat_eq_div] at hb ⊢
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have forsetiInitial : forsetiStart 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))] := by
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (0) 1) : ℚ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 2160) : ℚ) : ℝ) = (1/2160) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (-2) 1) : ℚ) : ℝ) = -2 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (2) 1) : ℚ) : ℝ) = 2 := by norm_num [Rat.mkRat_eq_div]
  have forsetiBoundary : forsetiStart = (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((0, 2), (1/4)), ((0, -2), (1/4))]) := by
    funext n
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2, forsetiBoundary, Rat.cast_zero]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2, forsetiBoundary, Rat.cast_zero] at lane
    dsimp only
    exact lane

end Decided_classical_multimode_band


/-!
### Handle zero initial data exactly {fold}

The zero start gives the zero solution. Both contracts certify exact zero
bounds at radius one million, a special case that supplies no large-time
guarantee for nonzero starts.

Zero initial data give the zero solution at any finite radius. The next two
contracts use radius one million and exact zero bounds; this special case
does not require dividing by the vanishing geometric growth rate.
-/

-- @decide classical_zero_tail : stream vorticity viscosity 0 interpretation euler-truncation
--   basis ogf start modes [0, 0, 0]
--   truncation u window 1 radius 1000000 epsilon 0

namespace Decided_classical_zero_tail

def forsetiTable : Gimle.Asgard.Streams.Torus.Table :=
  [((0, 0), (mkRat (0) 1))]

noncomputable def forsetiStart : Gimle.Asgard.Streams.TrigStream :=
  fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop :=
  Gimle.Forseti.Euler.Certified forsetiStart (((mkRat (1000000) 1) : ℚ) : ℝ) output ∧
  Gimle.Asgard.Streams.TrigStream.TruncationBound (output 0) (((mkRat (1000000) 1) : ℚ) : ℝ) 1 (((mkRat (0) 1) : ℚ) : ℝ)

def forsetiRoot : Prop :=
  Gimle.Forseti.Fourier.Contract
    (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf (mkRat (0) 1))
    (fun input => input 0 0 = forsetiStart 0) forsetiPost

/-- The Euler Fourier feedback circuit admits the listed initial modes, with higher boundary coefficients free. Its unique formal output has the prescribed initial field, mean-zero and even coefficients, and a convergent classical Euler field on the closed interval |t| ≤ 1000000, including both endpoints. In addition, its series converges for |t| ≤ 1000000, and the window through t^0 is within 0 of the sum there. Uniqueness concerns the formal stream; no classical uniqueness or maximal lifetime is claimed. The stream decider proved it. Goal (stream): stream vorticity viscosity 0 interpretation euler-truncation basis ogf start modes [0, 0, 0] truncation u window 1 radius 1000000 epsilon 0 -/
theorem classical_zero_tail :
    Gimle.Forseti.Fourier.Contract (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)])
      (fun output =>
        have ω := output 0;
        Gimle.Forseti.Euler.Certified (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)]) 1000000 output ∧
        Gimle.Asgard.Streams.TrigStream.TruncationBound ω 1000000 1 0) := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    apply (Gimle.Forseti.Fourier.solution_contract .ogf (mkRat (0) 1) forsetiStart).consequence (fun _ h => h)
    intro output same
    subst output
    unfold forsetiPost
    simp only [Matrix.cons_val_zero]
    have zeroStart : forsetiStart 0 = 0 := Gimle.Forseti.Euler.Table.toTrig_zero (table := forsetiTable) (by decide +kernel)
    have geo : Gimle.Asgard.Streams.TrigStream.GeometricBound (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) (((mkRat (0) 1) : ℚ) : ℝ) (((mkRat (0) 1) : ℚ) : ℝ) := by
      simpa [Rat.mkRat_eq_div] using (Gimle.Forseti.Euler.zero_geometric forsetiStart zeroStart 0)
    refine ⟨?_, ?_⟩
    · have geoClassical := Gimle.Forseti.Euler.zero_geometric forsetiStart zeroStart (((mkRat (1) 1000001) : ℚ) : ℝ)
      exact Gimle.Forseti.Euler.certified forsetiStart
        (by simp [zeroStart, Gimle.Asgard.Streams.Torus.MeanZero])
        (by simp [zeroStart, Gimle.Asgard.Streams.Torus.IsEven])
        (by rw [zeroStart]; exact Gimle.Asgard.Streams.Torus.sizeLE_zero 1) geoClassical
        (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div])
    · refine (Gimle.Asgard.Streams.TrigStream.truncationBound_rat geo (by decide +kernel) (by decide +kernel) _).mono ?_
      exact_mod_cast (show Gimle.Asgard.Streams.TrigStream.tailBound (mkRat (0) 1) (mkRat (0) 1) (mkRat (1000000) 1) 1 ≤ (mkRat (0) 1) by decide +kernel)
  have forsetiInitial : forsetiStart 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)] := by
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (0) 1) : ℚ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1000000) 1) : ℚ) : ℝ) = 1000000 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiBoundary : forsetiStart = (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)]) := by
    funext n
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiBoundary, Rat.cast_zero]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiBoundary, Rat.cast_zero] at lane
    dsimp only
    exact lane

end Decided_classical_zero_tail


-- @decide classical_zero_band : stream vorticity viscosity 0 interpretation euler-band
--   basis ogf start modes [0, 0, 0]
--   band u radius 1000000 : u >= 0 and u <= 0

namespace Decided_classical_zero_band

def forsetiTable : Gimle.Asgard.Streams.Torus.Table :=
  [((0, 0), (mkRat (0) 1))]

noncomputable def forsetiStart : Gimle.Asgard.Streams.TrigStream :=
  fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop :=
  Gimle.Forseti.Euler.Certified forsetiStart (((mkRat (1000000) 1) : ℚ) : ℝ) output ∧
  ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ (((mkRat (1000000) 1) : ℚ) : ℝ) →
    (((mkRat (0) 1) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x ∧ Gimle.Asgard.Streams.TrigStream.analyticField (output 0) t x ≤ (((mkRat (0) 1) : ℚ) : ℝ)

def forsetiRoot : Prop :=
  Gimle.Forseti.Fourier.Contract
    (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf (mkRat (0) 1))
    (fun input => input 0 0 = forsetiStart 0) forsetiPost

def forsetiBound : ℚ := (mkRat (0) 1)

/-- The Euler Fourier feedback circuit admits the listed initial modes, with higher boundary coefficients free. Its unique formal output has the prescribed initial field, mean-zero and even coefficients, and a convergent classical Euler field on the closed interval |t| ≤ 1000000, including both endpoints. In addition, its series converges for |t| ≤ 1000000, and its sum stays within the band there. Uniqueness concerns the formal stream; no classical uniqueness or maximal lifetime is claimed. The stream decider proved it. Goal (stream): stream vorticity viscosity 0 interpretation euler-band basis ogf start modes [0, 0, 0] band u radius 1000000 : u >= 0 and u <= 0 -/
theorem classical_zero_band :
    Gimle.Forseti.Fourier.Contract (Gimle.Asgard.Streams.NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)])
      (fun output =>
        have ω := output 0;
        Gimle.Forseti.Euler.Certified (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)]) 1000000 output ∧
        ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ 1000000 →
          0 ≤ Gimle.Asgard.Streams.TrigStream.analyticField ω t x ∧ Gimle.Asgard.Streams.TrigStream.analyticField ω t x ≤ 0) := by
  have root : forsetiRoot := by
    unfold forsetiRoot
    apply (Gimle.Forseti.Fourier.solution_contract .ogf (mkRat (0) 1) forsetiStart).consequence (fun _ h => h)
    intro output same
    subst output
    unfold forsetiPost
    simp only [Matrix.cons_val_zero]
    have zeroStart : forsetiStart 0 = 0 := Gimle.Forseti.Euler.Table.toTrig_zero (table := forsetiTable) (by decide +kernel)
    have geo : Gimle.Asgard.Streams.TrigStream.GeometricBound (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) (((mkRat (0) 1) : ℚ) : ℝ) (((mkRat (0) 1) : ℚ) : ℝ) := by
      simpa [Rat.mkRat_eq_div] using (Gimle.Forseti.Euler.zero_geometric forsetiStart zeroStart 0)
    refine ⟨?_, fun t x ht => ?_⟩
    · have geoClassical := Gimle.Forseti.Euler.zero_geometric forsetiStart zeroStart (((mkRat (1) 1000001) : ℚ) : ℝ)
      exact Gimle.Forseti.Euler.certified forsetiStart
        (by simp [zeroStart, Gimle.Asgard.Streams.Torus.MeanZero])
        (by simp [zeroStart, Gimle.Asgard.Streams.Torus.IsEven])
        (by rw [zeroStart]; exact Gimle.Asgard.Streams.Torus.sizeLE_zero 1) geoClassical
        (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div])
    · have b := Gimle.Asgard.Streams.TrigStream.abs_analyticField_le (x := x) geo (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) ht 1
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at b
      have h0 : ((Gimle.Asgard.Streams.Torus.l1 (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart 0) : ℚ) : ℝ) ≤ (((mkRat (0) 1) : ℚ) : ℝ) := by
        rw [Gimle.Asgard.Streams.NS.stream_eq_table (mkRat (0) 1) forsetiTable forsetiStart rfl]
        exact_mod_cast (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))
      have hB : |Gimle.Asgard.Streams.TrigStream.analyticField (Gimle.Asgard.Streams.NS.stream .ogf (mkRat (0) 1) forsetiStart) t x| ≤ ((forsetiBound : ℚ) : ℝ) := by
        refine b.trans ?_
        norm_num [forsetiBound, Rat.mkRat_eq_div] at h0 ⊢
        linarith
      have hb := abs_le.mp hB
      norm_num [forsetiBound, Rat.mkRat_eq_div] at hb ⊢
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have forsetiInitial : forsetiStart 0 = Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)] := by
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (0) 1) : ℚ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1000000) 1) : ℚ) : ℝ) = 1000000 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiBoundary : forsetiStart = (fun _ => Gimle.Asgard.Streams.Torus.Table.toTrig [((0, 0), 0)]) := by
    funext n
    unfold forsetiStart forsetiTable
    norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    dsimp only at claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2, forsetiBoundary, Rat.cast_zero]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2, forsetiBoundary, Rat.cast_zero] at lane
    dsimp only
    exact lane

end Decided_classical_zero_band


/-!
## Separate the viscous time-series question {fold}

At $\nu=1/10$, a Gevrey-1 bound controls factorial coefficient growth but
certifies neither convergence nor divergence of this time series. The
[Navier–Stokes notebook](NavierStokes.lean) instead certifies a series in
interaction degree, with time-dependent heat and Duhamel terms.

### Understand the limit of the factorial bound {fold}

The Laplacian costs two derivatives in this time-series recurrence. The
resulting upper bound gives no positive convergence radius for the original
viscous series; finite coefficient samples do not settle the question.

With $\nu > 0$ the viscous term $\nu\Delta\omega_n$ costs two derivatives,
and the induction in a scale does not close. What a short induction gives is
Gevrey-1 growth of the formal series in $t$: the modes of $\omega_n$ have size
at most $(n+1)K$, so $\Delta$ costs $((n+1)K)^2$, each transport one factor,
and $\|\omega_n\|_{\ell^1} \le L\,(\nu K^2 + KL)^n\,n!$ — a radius for the
Borel transform of the series, not for the series. This factorial upper bound
alone proves neither convergence nor divergence of the original time series.
No positive radius is certified here for this viscous start. The same off-line
norms for $\nu = \tfrac{1}{10}$:

$$ \begin{array}{c|l} n & \|\omega_n\|_{\ell^1},\ \nu = \tfrac{1}{10} \\ \hline 0,\dots,4 & 3,\ 2,\ 1.383,\ 1.165,\ 0.858 \\ 5,\dots,8 & 0.749,\ 0.581,\ 0.496,\ 0.419 \\ 9,\dots,12 & 0.365,\ 0.362,\ 0.327,\ 0.389 \end{array} $$

The ratios drift upward — $0.67$, $0.69$, $0.84$, $0.74$, $0.87$, $0.78$,
$0.85$, $0.84$, $0.87$, $0.99$, $0.90$, $1.19$ — and cross $1$ at $n = 12$.
Twelve terms do not decide a radius. Coefficients proportional to $C^n n!$
would have ratios $C(n+1)$, but a Gevrey-1 upper bound does not require that
growth. These finite observations are consistent with either a positive
radius or none. They are evidence, never a status.

### Check the viscous coefficients and growth bound {fold}

The factorial bound and coefficient identities below are checked. Viscosity
changes the initial mode $(2,1)$ at first order, while the newly created mode
$(0,1)$ keeps its first coefficient.


With $\nu = \tfrac{1}{10}$ the same start gives
$\|\omega_n\|_{\ell^1} \le 3\cdot(\tfrac{99}{10})^n\,n!$, and no certified
radius. At $t^1$ the viscous coefficients are the inviscid ones plus the decay
$-\nu|k|^2\hat\omega_{0,k}$ of each initial mode: $e^{i(2x+y)}$ moves from
$-\tfrac18$ to $-\tfrac18 - \tfrac{1}{10}\cdot 5\cdot\tfrac12 = -\tfrac38$,
while the created mode $e^{iy}$, absent from the start, has nothing to decay
yet and keeps its $\tfrac18$. The first is a proved negation of "viscosity
changes nothing at $t^1$"; the second a checked equality, both from the
library's kernel-computed values.
-/

/-- Gevrey-1 growth in $t$ for the viscous stream. -/
theorem gevrey_viscous (n : ℕ) :
    (l1 (stream .ogf ν start n) : ℝ) ≤ 3 * (99 / 10) ^ n * n.factorial := by
  exact viscous_gevrey n

/-- Viscosity moves the coefficient of $t\,e^{i(2x+y)}$. -/
theorem viscous_differs : stream .ogf ν start 1 (2, 1) ≠ stream .ogf 0 start 1 (2, 1) := by
  rw [viscous_t_2xy, euler_t_2xy]
  norm_num

/-- Viscosity leaves the created mode's first coefficient alone. -/
theorem viscous_created_same : stream .ogf ν start 1 (0, 1) = stream .ogf 0 start 1 (0, 1) := by
  rw [viscous_t_y, euler_t_y]

/-!
## Scope and unresolved questions

The positive radius and classical realization above concern the inviscid
vorticity solution on its certified interval. Formal uniqueness does not
establish uniqueness among arbitrary classical solutions. The upper-bound
request $u\le3$ remains unknown, and the true radius beyond the certified
$1/648$ is not established here. The viscous time series has no certified
positive radius; its factorial bound is not a proof of divergence. Pressure,
global regularity and three-dimensional flow remain outside these claims.
-/

end Notebook.Euler
