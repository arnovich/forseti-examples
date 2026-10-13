import Mathlib
import Gimle.Forseti.MildVorticity
import Gimle.Forseti.Tests.MildStream
import Gimle.Asgard.Examples.MildBand

/-!
# Navier–Stokes through a typed mild circuit

The two-dimensional viscous vorticity equation on the periodic square is

$$ \partial_t\omega + \partial_1\psi\,\partial_2\omega - \partial_2\psi\,\partial_1\omega = \nu\Delta\omega, \qquad \Delta\psi = \omega. $$

This page starts from an **Asgard circuit** and proves **Forseti total Hoare
contracts** about every output related to an admitted input. Admission fixes
only the initial vorticity; all higher boundary slices are free. The contract
includes existence, uniqueness of the formal circuit output, convergence,
classical realization and spectral dissipation. Numerical bounds strengthen
that same postcondition.

The example is $\omega_0=\cos x+\cos(x+y)+\cos(2x+y)$, with viscosity
$\nu=1/10$. The circuit expands in **interaction degree**, using heat and
Duhamel gates. Its output is $\sum_n\omega_n(t,x)$, where

$$ \omega_0(t)=e^{\nu t\Delta}\omega_0, \qquad
   \omega_{n+1}(t)=-\int_0^t e^{\nu(t-s)\Delta}
     \sum_{j=0}^n B(\omega_j(s),\omega_{n-j}(s))\,ds. $$

Each coefficient is an exact exponential polynomial
$\sum c\,t^m e^{-\nu\lambda t}$, with rational $c$ and natural $m,\lambda$.
The window `4` means the sum of interaction terms **0, 1, 2, 3**.
Each term already depends on physical time: no extra factor $t^n$ is applied.
The `interaction` basis names this convention explicitly; Taylor-basis
spellings `ogf` and `egf` are rejected by the mild readings.

The proof has two alternative convergence certificates, followed by exact
coefficient checks and the classical and dissipation guarantees they support.
The automated tail and band requests are certified; the tighter band $[-3,3]$
remains unknown. Uniqueness is for formal circuit outputs, not arbitrary
classical solutions, and the guarantees apply on the certified time interval.

The [Euler notebook](Euler.lean) studies powers of physical time. Its viscous
factorial coefficient bound certifies no positive time-series radius. Here
heat evolution is kept inside each interaction term: convergence of this
series does not establish convergence of that viscous time series.

## Certify the mild circuit output {fold}

Two sufficient certificates give a unique formal circuit output and its
classical and spectral-dissipation guarantees. For the stated start and
$\nu=1/10$, contraction certifies $[0,1/5760]$; the Euler-scale route allows
any closed $[0,T]$ with $0\le T<1/648$, including at zero viscosity.

Both certificates assume a finite, even, mean-zero start with $\ell^1$ mass
at most $L$ and mode size at most $K$. Here $L=K=3$.

### Use viscous contraction {fold}

At $\nu=1/10$, $r=1/24$ gives $T=1/5760$ and contraction factor $1/2$.
The contract carries a four-term tail bound $21/1024$ and can be strengthened
to the field band $[-3.519,3.519]$ on that interval.

Choose $T\ge0$ and rational $r\ge0$ with $T\le\nu r^2$, $\nu>0$, and
$\theta=4rL<1$. Then $\|\omega_n(t)\|_1\le a_n=L(rL)^n C_n$,
where $C_n$ is Catalan. The tail after terms below $N$ is at most
$a_N/(1-\theta)$. After `circuit_contract`, the claims `truncation_contract`
and `band_contract` attach numerical bounds while retaining its other guarantees.
-/

namespace NavierStokes
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild
open Gimle.Asgard.Examples

/-- Every admitted input has a unique circuit output carrying the full guarantee. -/
theorem circuit_contract : Gimle.Forseti.Mild.Contract (mildCircuit (1 / 10))
    (fun input => input 0 0 = embed EulerThreeMode.ω₀)
    (Gimle.Forseti.MildVorticity.Certified (1 / 10) EulerThreeMode.ω₀ (1 / 5760)) := by
  have hg := wild_geometric (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Gimle.Forseti.MildVorticity.boundary EulerThreeMode.ω₀) EulerThreeMode.ω₀ rfl EulerBand.start_l1
  exact Gimle.Forseti.MildVorticity.contract (by norm_num) _
    EulerThreeMode.ω₀_meanZero EulerThreeMode.ω₀_isEven EulerBand.start_sizeLE
    (by norm_num) hg (by norm_num) (by norm_num)

/-- The four-term error is conjoined with the complete circuit postcondition. -/
theorem truncation_contract : Gimle.Forseti.Mild.Contract (mildCircuit (1 / 10))
    (fun input => input 0 0 = embed EulerThreeMode.ω₀)
    (fun output => Gimle.Forseti.MildVorticity.Certified (1 / 10) EulerThreeMode.ω₀ (1 / 5760) output ∧
      MildTruncationBound (1 / 10) (output 0) (1 / 5760) 4 (21 / 1024)) := by
  apply Gimle.Forseti.MildVorticity.contract_with _ circuit_contract
  exact MildBand.truncation

/-- The field band strengthens that same total contract. -/
theorem band_contract : Gimle.Forseti.Mild.Contract (mildCircuit (1 / 10))
    (fun input => input 0 0 = embed EulerThreeMode.ω₀)
    (fun output => Gimle.Forseti.MildVorticity.Certified (1 / 10) EulerThreeMode.ω₀ (1 / 5760) output ∧
      MildBandBound (1 / 10) (output 0) (1 / 5760) (3519 / 1000)) := by
  apply Gimle.Forseti.MildVorticity.contract_with _ circuit_contract
  exact MildBand.band

/-!
### Use the Euler-scale certificate {fold}

For every $\nu\ge0$, the same start has a certified circuit output on each
closed $[0,T]$ with $0\le T<1/648$. The four-term error bound is
$9(648T)^4/(1-648T)$. The strict endpoint is essential.

Require $q=72LKT<1$. Then $\|\omega_n(t)\|_1\le3Lq^n$ on $[0,T]$,
with tail $3Lq^N/(1-q)$. The initial heat term has the sharper bound $L$.
Neither $q=1$ nor $\theta=1$ proves convergence. Despite the name
"Euler scale", this certificate applies to the interaction series for all
nonnegative viscosities; it is not a viscous Taylor-series certificate.
-/

/-- The uniform Euler-scale interval is also a full circuit contract for ν ≥ 0. -/
theorem euler_scale_contract {ν : ℚ} {T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (ht : T < 1 / 648) : Gimle.Forseti.Mild.Contract (mildCircuit ν)
    (fun input => input 0 0 = embed EulerThreeMode.ω₀)
    (Gimle.Forseti.MildVorticity.Certified ν EulerThreeMode.ω₀ T) := by
  have hg := wild_euler_geometric hν (Gimle.Forseti.MildVorticity.boundary EulerThreeMode.ω₀)
    EulerThreeMode.ω₀ rfl (by norm_num : 1 ≤ 3) EulerBand.start_sizeLE EulerBand.start_l1 T
  exact Gimle.Forseti.MildVorticity.contract hν _ EulerThreeMode.ω₀_meanZero
    EulerThreeMode.ω₀_isEven EulerBand.start_sizeLE hT hg (by positivity) (by norm_num; linarith)

/-- Its four-term tail keeps all guarantees on every actual output. -/
theorem euler_tail_contract {ν T : ℚ} (hν : 0 ≤ ν) (hT : 0 ≤ T) (ht : T < 1 / 648) :
    Gimle.Forseti.Mild.Contract (mildCircuit ν)
    (fun input => input 0 0 = embed EulerThreeMode.ω₀)
    (fun output => Gimle.Forseti.MildVorticity.Certified ν EulerThreeMode.ω₀ T output ∧
      MildTruncationBound ν (output 0) T 4 (9 * (648 * (T : ℝ)) ^ 4 / (1 - 648 * T))) := by
  apply Gimle.Forseti.MildVorticity.contract_with _ (euler_scale_contract hν
    (by exact_mod_cast hT) (by
      have hh : (T : ℝ) < ((1 / 648 : ℚ) : ℝ) := by exact_mod_cast ht
      norm_num at hh
      exact hh))
  exact MildBand.euler_truncation hν hT ht

/-!
## Inspect exact terms and compare the certificates {fold}

The coefficient identities concern the actual circuit output. Cancellation
makes carrier coefficient sums poor bounds on the physical field. Comparing
the two certificates helps choose a bound; sampled values do not certify
longer time intervals.

### Identify the output and its first terms {fold}

The first three claims compute exact exponential-polynomial coefficients;
the fourth identifies their stream as an output of the circuit. The sampled
magnitudes below are numerical evidence, not certified suprema.

The first three coefficient claims below are identities in the exact carrier,
checked by Lean. They belong to the same output named by the circuit contract.
In particular, the first newly created $y$ mode is
$\frac58(e^{-t/10}-e^{-3t/10})$: its representation has substantial cancellation.
Absolute carrier coefficient sums are therefore poor physical bounds.

The following values were computed at 60 decimal digits on a 65-point grid
in $[0,1/5760]$. For each Fourier mode, take the largest sampled magnitude,
then sum across modes. **These sums of sampled mode maxima are numerical
evidence, not proofs or certified continuous suprema.** The coefficients and
the contracts have separate kernel proofs.

| interaction degree | carrier absolute sum | sum of sampled mode maxima | Catalan bound |
|---|---:|---:|---:|
| 0 | 3 | 3 | 3 |
| 1 | 10 | 2.778 × 10⁻⁴ | 0.375 |
| 2 | 47.85 | 2.585 × 10⁻⁸ | 0.09375 |
| 3 | 264.0 | 2.948 × 10⁻¹² | 0.02930 |

The gap suggests substantial room to improve these sufficient time bounds;
it does not establish a longer interval. The decider's compact report also
shows physical evaluations at $T$, explicitly as evidence. Its certificate
uses only the two proved majorants, never carrier coefficient norms.
-/

/-- The exact heat coefficient in the circuit's canonical output. -/
theorem heat_x : MildBand.ω (1 / 10) 0 (1, 0) = ExpPoly.Table.toExp [((1, 0), 1 / 2)] := by
  exact Gimle.Forseti.Tests.MildStream.heat_x

/-- The first created y mode contains two cancelling exponentials. -/
theorem first_y : MildBand.ω (1 / 10) 1 (0, 1) =
    ExpPoly.Table.toExp [((1, 0), 5 / 8), ((3, 0), -5 / 8)] := by
  exact Gimle.Forseti.Tests.MildStream.first_y

/-- The second interaction's exact coefficient includes a resonant t exponential. -/
theorem second_2x2y : MildBand.ω (1 / 10) 2 (2, 2) = ExpPoly.Table.toExp
    [((8, 0), -35 / 13), ((14, 0), 5 / 26), ((8, 1), -5 / 13), ((6, 0), 5 / 2)] := by
  exact Gimle.Forseti.Tests.MildStream.second_2x2y

/-- The stream whose coefficients were inspected is related to the actual circuit. -/
theorem inspected_output : (mildCircuit (1 / 10)).Rel ![MildBand.start] ![MildBand.ω (1 / 10)] := by
  exact MildBand.circuit_output _

/-!
### Compare the certified time intervals {fold}

At fixed $r=1/24$, the contraction threshold $\nu r^2$ exceeds the Euler-scale
threshold $1/648$ exactly when $\nu>8/9$. This compares sufficient time
bounds, not maximal solution lifetimes.

For $\nu=1/10$ and $T=1/5760$, the four-term Euler-scale tail is about
$0.001624$, smaller than $21/1024$, while contraction gives the tighter
field band. The Euler-scale interval has a strict upper threshold; its
certificate applies on each closed $[0,T]$ below that threshold.
-/

/-- The interval crossover is exact rational arithmetic. -/
theorem crossing (ν : ℚ) : 1 / 648 < ν * (1 / 24) ^ 2 ↔ 8 / 9 < ν := by
  exact MildBand.bound_crossing ν

/-!
## Read the classical and dissipation guarantees {fold}

Every admitted input has an actual output. Each such output realizes the
classical vorticity equation on the interval's interior and has nonincreasing
spectral energy and enstrophy on the closed interval. These guarantees do
not assert uniqueness among arbitrary classical solutions.

### Realize the classical vorticity equation {fold}

The contract supplies existence of an output and classical realization for
every admitted output. The PDE and time derivative hold in the interior;
a positive horizon also supplies a forward right derivative at zero.

The complete postcondition states that the physical sum has continuous
spatial derivatives and a continuous extension of the time derivative to the
closed interval. The time derivative and PDE hold on the interior; there is
no assertion of a two-sided time derivative at the upper endpoint. For a
positive horizon the sum also has the forward
right derivative at the initial time. The stream function satisfies
$\Delta\psi=\omega$; the mixed partials give divergence-free velocity.
The field is reconstructed from the absolutely summable Fourier coefficients
$W_k(t)=\sum_n\widehat\omega_{n,k}(t)$.
-/

/-- A concrete admitted input cannot satisfy a vacuous contract. -/
theorem exists_certified (input : Point 1) (hi : input 0 0 = embed EulerThreeMode.ω₀) :
    ∃ output, (mildCircuit (1 / 10)).Rel input output ∧
      Gimle.Forseti.MildVorticity.Certified (1 / 10) EulerThreeMode.ω₀ (1 / 5760) output := by
  exact circuit_contract.exists_safe input hi

/-- Every actual admitted output realizes the classical vorticity equation. -/
theorem classical_output (input output : Point 1) (hi : input 0 0 = embed EulerThreeMode.ω₀)
    (hr : (mildCircuit (1 / 10)).Rel input output) :
    IsMildClassicalSolution (1 / 10) (output 0) EulerThreeMode.ω₀ (1 / 5760) := by
  exact (circuit_contract.holds input hi output hr).classical

/-!
### Track spectral dissipation through the endpoints {fold}

The identities $Z'=-2\nu P$ and $E'=-2\nu Z$ hold in the interval's
interior. Monotonicity includes both endpoints; the final claim gives the
energy bound at $t=1/5760$. These quantities use spectral normalization.

The dissipation quantities are **spectral**, with the exact normalization

$$ Z=\sum_k W_k^2,\quad E=\sum_k |k|^{-2}W_k^2,\quad
   P=\sum_k |k|^2W_k^2,\qquad Z'=-2\nu P,\quad E'=-2\nu Z. $$

The zero inverse weight is defined as zero. There is no factor $1/2$ in
these definitions. Both identities hold on the interval's interior and both
quantities are nonincreasing on the closed interval, including its endpoints.
No Parseval identification with spatial integrals is asserted here.
-/

/-- The infinite Fourier enstrophy identity belongs to every actual circuit output. -/
theorem enstrophy_identity (input output : Point 1) (hi : input 0 0 = embed EulerThreeMode.ω₀)
    (hr : (mildCircuit (1 / 10)).Rel input output) (t : ℝ) (ht : t ∈ Set.Ioo 0 (1 / 5760)) :
    HasDerivAt (fun s => enstrophy (fourierCoeff (1 / 10) (output 0) s))
      (-2 * (1 / 10 : ℝ) * palinstrophy (fourierCoeff (1 / 10) (output 0) t)) t := by
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (circuit_contract.holds input hi output hr).dissipation.enstrophy_deriv t ht

/-- The infinite Fourier energy identity has the same circuit admission. -/
theorem energy_identity (input output : Point 1) (hi : input 0 0 = embed EulerThreeMode.ω₀)
    (hr : (mildCircuit (1 / 10)).Rel input output) (t : ℝ) (ht : t ∈ Set.Ioo 0 (1 / 5760)) :
    HasDerivAt (fun s => energy (fourierCoeff (1 / 10) (output 0) s))
      (-2 * (1 / 10 : ℝ) * enstrophy (fourierCoeff (1 / 10) (output 0) t)) t := by
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (circuit_contract.holds input hi output hr).dissipation.energy_deriv t ht

/-- The upper time endpoint is included in the energy control. -/
theorem energy_endpoint (input output : Point 1) (hi : input 0 0 = embed EulerThreeMode.ω₀)
    (hr : (mildCircuit (1 / 10)).Rel input output) :
    energy (fourierCoeff (1 / 10) (output 0) (1 / 5760)) ≤
      energy (fourierCoeff (1 / 10) (output 0) 0) := by
  exact (circuit_contract.holds input hi output hr).dissipation.energy_le_initial ⟨by norm_num, le_rfl⟩

/-!
## Inspect the automated contracts {fold}

The four-term tail request and band $[-3.519,3.519]$ are certified on
$[0,1/5760]$ for this start at $\nu=1/10$. The tighter band $[-3,3]$
remains unknown and has no claim card; the section's claim counts do not
include that unresolved request.


These directives select the better of the two proved bounds. The tail uses
the Euler scale; the band uses contraction. Each successful directive emits
the whole circuit contract, including the classical and dissipation guarantees.
The final band is deliberately tighter than either certificate supplies. It
stays **UNKNOWN**, which says nothing about whether the physical field actually
violates that band.
-/

/-!
### Inspect the certified tail {fold}

The decider uses the Euler-scale certificate to establish the requested
four-term error $21/1024$, together with the complete circuit postcondition.
The four terms already depend on physical time.
-/

-- @decide truncation_decided : stream vorticity viscosity 1/10 interpretation mild-truncation
--   basis interaction start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2]
--   truncation u window 4 time 1/5760 epsilon 21/1024

namespace Decided_truncation_decided

def forsetiTable : Gimle.Asgard.Streams.Torus.Table := [((1, 0), (mkRat (1) 2)), ((-1, 0), (mkRat (1) 2)), ((1, 1), (mkRat (1) 2)), ((-1, -1), (mkRat (1) 2)), ((2, 1), (mkRat (1) 2)), ((-2, -1), (mkRat (1) 2))]

noncomputable def forsetiP : Gimle.Asgard.Streams.Torus.TrigPoly := Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Mild.Point 1) : Prop :=
  Gimle.Forseti.MildVorticity.Certified (1 / 10 : ℚ) forsetiP (((mkRat (1) 5760) : ℚ) : ℝ) output ∧
  (Gimle.Asgard.Streams.Mild.MildTruncationBound (1 / 10 : ℚ) (output 0) (((mkRat (1) 5760) : ℚ) : ℝ) 4 (((mkRat (21) 1024) : ℚ) : ℝ))

def forsetiRoot : Prop :=
  Gimle.Forseti.Mild.Contract (Gimle.Asgard.Streams.Mild.mildCircuit (1 / 10 : ℚ))
    (fun input => input 0 0 = Gimle.Asgard.Streams.Mild.embed forsetiP) forsetiPost

/-- The typed mild feedback circuit at viscosity 1/10 admits every input with the listed even, mean-zero initial vorticity; higher boundary coefficients are free. A unique formal output exists. On 0 ≤ t ≤ 1/5760, every output has absolute convergence, Fourier reconstruction, continuous spatial derivatives, and nonincreasing spectral energy and enstrophy. The time derivative, classical PDE and dissipation derivative identities hold in the interval's interior; the time derivative extends continuously to its endpoints, and a positive horizon also gives a right derivative at zero. The first 4 physical interaction terms approximate the sum within 21/1024. The window counts interaction terms, each already a function of physical time. The stream decider proved it. Goal (stream): stream vorticity viscosity 1/10 interpretation mild-truncation basis interaction start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2] truncation u window 4 time 1/5760 epsilon 21/1024 -/
theorem truncation_decided :
    Gimle.Forseti.Mild.Contract (Gimle.Asgard.Streams.Mild.mildCircuit (1/10))
      (fun input => input 0 0 = Gimle.Asgard.Streams.Mild.embed (Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))]))
      (fun output => Gimle.Forseti.MildVorticity.Certified (1/10) (Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))]) (1/5760) output ∧
        (Gimle.Asgard.Streams.Mild.MildTruncationBound (1/10) (output 0) (1/5760) 4 (21/1024))) := by
  have root : forsetiRoot := by
    have hs : Gimle.Asgard.Streams.Torus.SizeLE 3 forsetiP := by
      exact Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (by decide +kernel : ∀ e ∈ forsetiTable, Gimle.Asgard.Streams.Torus.size e.1 ≤ 3)
    have hl : Gimle.Asgard.Streams.Torus.l1 forsetiP ≤ (mkRat (3) 1) := (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum forsetiTable).trans (by decide +kernel : Gimle.Asgard.Streams.Torus.Table.absSum forsetiTable ≤ (mkRat (3) 1))
    have hc : Gimle.Forseti.Mild.Contract (Gimle.Asgard.Streams.Mild.mildCircuit (1 / 10 : ℚ))
        (fun input => input 0 0 = Gimle.Asgard.Streams.Mild.embed forsetiP)
        (Gimle.Forseti.MildVorticity.Certified (1 / 10 : ℚ) forsetiP (((mkRat (1) 5760) : ℚ) : ℝ)) := by
      exact Gimle.Forseti.MildVorticity.Table.euler_contract forsetiTable (by decide +kernel) (by decide +kernel) (by norm_num [Rat.mkRat_eq_div]) (K := 3) (by decide +kernel) (by decide +kernel) (L := (mkRat (3) 1)) (by decide +kernel) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div])
    unfold forsetiRoot forsetiPost
    apply Gimle.Forseti.MildVorticity.contract_with forsetiP hc
    have h := Gimle.Asgard.Streams.Mild.wild_euler_truncation (ν := (1 / 10 : ℚ)) (T := (mkRat (1) 5760)) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) (Gimle.Forseti.MildVorticity.boundary forsetiP) forsetiP rfl (K := 3) (by decide +kernel) hs (L := (mkRat (3) 1)) hl (by norm_num [Rat.mkRat_eq_div]) 4
    apply h.mono
    exact_mod_cast (show Gimle.Asgard.Streams.Mild.eulerTail (mkRat (3) 1) 3 (mkRat (1) 5760) 4 ≤ (mkRat (21) 1024) by decide +kernel)
  have forsetiInitial : forsetiP = (Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))]) := by
    unfold forsetiP forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (1) 10) : ℚ) = (1/10) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 5760) : ℚ) : ℝ) = (1/5760) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (21) 1024) : ℚ) : ℝ) = (21/1024) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, Rat.cast_zero]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, Rat.cast_zero] at lane
    exact lane

/-!
### Inspect the certified band and the unresolved tighter band {fold}

Contraction certifies $[-3.519,3.519]$ with the full circuit guarantees.
The subsequent request for $[-3,3]$ remains unknown, which does not establish
that the physical field ever leaves that tighter band.
-/

end Decided_truncation_decided


-- @decide band_decided : stream vorticity viscosity 1/10 interpretation mild-band
--   basis interaction start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2]
--   band u time 1/5760 : u >= -3519/1000 and u <= 3519/1000

namespace Decided_band_decided

def forsetiTable : Gimle.Asgard.Streams.Torus.Table := [((1, 0), (mkRat (1) 2)), ((-1, 0), (mkRat (1) 2)), ((1, 1), (mkRat (1) 2)), ((-1, -1), (mkRat (1) 2)), ((2, 1), (mkRat (1) 2)), ((-2, -1), (mkRat (1) 2))]

noncomputable def forsetiP : Gimle.Asgard.Streams.Torus.TrigPoly := Gimle.Asgard.Streams.Torus.Table.toTrig forsetiTable

def forsetiPost (output : Gimle.Asgard.Streams.Mild.Point 1) : Prop :=
  Gimle.Forseti.MildVorticity.Certified (1 / 10 : ℚ) forsetiP (((mkRat (1) 5760) : ℚ) : ℝ) output ∧
  (∀ t ∈ Set.Icc 0 (((mkRat (1) 5760) : ℚ) : ℝ), ∀ x : ℝ × ℝ, (((mkRat (-3519) 1000) : ℚ) : ℝ) ≤ Gimle.Asgard.Streams.Mild.analyticField (1 / 10 : ℚ) (output 0) t x ∧ Gimle.Asgard.Streams.Mild.analyticField (1 / 10 : ℚ) (output 0) t x ≤ (((mkRat (3519) 1000) : ℚ) : ℝ))

def forsetiRoot : Prop :=
  Gimle.Forseti.Mild.Contract (Gimle.Asgard.Streams.Mild.mildCircuit (1 / 10 : ℚ))
    (fun input => input 0 0 = Gimle.Asgard.Streams.Mild.embed forsetiP) forsetiPost

/-- The typed mild feedback circuit at viscosity 1/10 admits every input with the listed even, mean-zero initial vorticity; higher boundary coefficients are free. A unique formal output exists. On 0 ≤ t ≤ 1/5760, every output has absolute convergence, Fourier reconstruction, continuous spatial derivatives, and nonincreasing spectral energy and enstrophy. The time derivative, classical PDE and dissipation derivative identities hold in the interval's interior; the time derivative extends continuously to its endpoints, and a positive horizon also gives a right derivative at zero. The physical field remains in the requested band. The window counts interaction terms, each already a function of physical time. The stream decider proved it. Goal (stream): stream vorticity viscosity 1/10 interpretation mild-band basis interaction start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2] band u time 1/5760 : u >= -3519/1000 and u <= 3519/1000 -/
theorem band_decided :
    Gimle.Forseti.Mild.Contract (Gimle.Asgard.Streams.Mild.mildCircuit (1/10))
      (fun input => input 0 0 = Gimle.Asgard.Streams.Mild.embed (Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))]))
      (fun output => Gimle.Forseti.MildVorticity.Certified (1/10) (Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))]) (1/5760) output ∧
        (∀ t ∈ Set.Icc 0 (1/5760), ∀ x : ℝ × ℝ, (-3519/1000) ≤ Gimle.Asgard.Streams.Mild.analyticField (1/10) (output 0) t x ∧ Gimle.Asgard.Streams.Mild.analyticField (1/10) (output 0) t x ≤ (3519/1000))) := by
  have root : forsetiRoot := by
    have hs : Gimle.Asgard.Streams.Torus.SizeLE 3 forsetiP := by
      exact Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig (by decide +kernel : ∀ e ∈ forsetiTable, Gimle.Asgard.Streams.Torus.size e.1 ≤ 3)
    have hl : Gimle.Asgard.Streams.Torus.l1 forsetiP ≤ (mkRat (3) 1) := (Gimle.Asgard.Streams.Torus.Table.l1_le_absSum forsetiTable).trans (by decide +kernel : Gimle.Asgard.Streams.Torus.Table.absSum forsetiTable ≤ (mkRat (3) 1))
    have hc : Gimle.Forseti.Mild.Contract (Gimle.Asgard.Streams.Mild.mildCircuit (1 / 10 : ℚ))
        (fun input => input 0 0 = Gimle.Asgard.Streams.Mild.embed forsetiP)
        (Gimle.Forseti.MildVorticity.Certified (1 / 10 : ℚ) forsetiP (((mkRat (1) 5760) : ℚ) : ℝ)) := by
      exact Gimle.Forseti.MildVorticity.Table.catalan_contract forsetiTable (by decide +kernel) (by decide +kernel) (r := (mkRat (1) 24)) (by norm_num [Rat.mkRat_eq_div]) (K := 3) (by decide +kernel) (L := (mkRat (3) 1)) (by decide +kernel) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div])
    unfold forsetiRoot forsetiPost
    apply Gimle.Forseti.MildVorticity.contract_with forsetiP hc
    have h := Gimle.Asgard.Streams.Mild.wild_catalan_band (ν := (1 / 10 : ℚ)) (r := (mkRat (1) 24)) (T := (((mkRat (1) 5760) : ℚ) : ℝ)) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) (by norm_num [Rat.mkRat_eq_div]) (Gimle.Forseti.MildVorticity.boundary forsetiP) forsetiP rfl (L := (mkRat (3) 1)) hl (by norm_num [Rat.mkRat_eq_div]) 8
    intro t ht x
    have hh := abs_le.mp (h t ht x)
    exact ⟨le_trans (by exact_mod_cast (show (mkRat (-3519) 1000) ≤ -(Gimle.Asgard.Streams.Mild.catalanBand (mkRat (3) 1) (mkRat (1) 24) 8) by decide +kernel)) hh.1, le_trans hh.2 (by exact_mod_cast (show Gimle.Asgard.Streams.Mild.catalanBand (mkRat (3) 1) (mkRat (1) 24) 8 ≤ (mkRat (3519) 1000) by decide +kernel))⟩
  have forsetiInitial : forsetiP = (Gimle.Asgard.Streams.Torus.Table.toTrig [((1, 0), (1/2)), ((-1, 0), (1/2)), ((1, 1), (1/2)), ((-1, -1), (1/2)), ((2, 1), (1/2)), ((-2, -1), (1/2))]) := by
    unfold forsetiP forsetiTable
    norm_num [Rat.mkRat_eq_div]
  have forsetiViscosity : ((mkRat (1) 10) : ℚ) = (1/10) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast0 : (((mkRat (1) 5760) : ℚ) : ℝ) = (1/5760) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (-3519) 1000) : ℚ) : ℝ) = (-3519/1000) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (3519) 1000) : ℚ) : ℝ) = (3519/1000) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiRoot) => bridge.mpr root) ?_
  constructor
  · intro claim
    unfold forsetiRoot forsetiPost
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2, Rat.cast_zero]
    exact claim
  · intro lane
    unfold forsetiRoot forsetiPost at lane
    set_option linter.unusedSimpArgs false in simp only [forsetiInitial, forsetiViscosity, forsetiCast0, forsetiCast1, forsetiCast2, Rat.cast_zero] at lane
    exact lane

end Decided_band_decided


-- @decide narrow_band : stream vorticity viscosity 1/10 interpretation mild-band
--   basis interaction start modes [1, 0, 1/2], [-1, 0, 1/2], [1, 1, 1/2], [-1, -1, 1/2], [2, 1, 1/2], [-2, -1, 1/2]
--   band u time 1/5760 : u >= -3 and u <= 3

/-!
## Scope and unresolved bounds

The uniqueness here is uniqueness of the formal circuit output for the
prescribed initial slice. This page does not prove uniqueness among arbitrary
classical solutions, continuation beyond the certified interval, global
2D regularity, a 3D result, or convergence as viscosity tends to zero.
The certified times are lower bounds. Pressure and the full velocity-pressure
formulation are outside these statements.

The band $[-3,3]$ remains unknown. Numerical samples and the absence of a
claim card do not settle it. The convergent interaction expansion above also
does not resolve the viscous time-series radius discussed in [Euler](Euler.lean).
-/

end NavierStokes
