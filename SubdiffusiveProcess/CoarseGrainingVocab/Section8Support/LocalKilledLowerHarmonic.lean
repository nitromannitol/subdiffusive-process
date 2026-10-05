module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOffDiagonal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerPotential

@[expose] public section

/-!
# Kernel oscillation from a bounded harmonic correction

The time derivative gives a bounded forcing. A continuous representative of its
zero-boundary Poisson solution has the maximum-principle bound, and subtracting it
from the kernel leaves a weakly harmonic function. The assumed oscillation
contraction then controls the oscillation of the kernel on the inner set.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-! ### Two facts about the oscillation -/

/-- A uniform bound on all differences bounds the oscillation. -/
theorem oscillation_le_ofReal {S : Set (Vec d)} {h : Vec d → ℝ} {b : ℝ}
    (hbd : ∀ x ∈ S, ∀ y ∈ S, |h x - h y| ≤ b) : oscillation S h ≤ ENNReal.ofReal b := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.oscillation
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal (hbd x hx y hy)

/-- A bounded oscillation bounds every absolute difference. -/
theorem abs_sub_le_of_oscillation_le {S : Set (Vec d)} {h : Vec d → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hosc : oscillation S h ≤ ENNReal.ofReal b) {x y : Vec d} (hx : x ∈ S) (hy : y ∈ S) :
    |h x - h y| ≤ b :=
  abs_sub_le_iff.mpr ⟨sub_le_of_oscillation_le hb hosc hx hy,
    sub_le_of_oscillation_le hb hosc hy hx⟩

/-! ### The harmonic approximation used by the oscillation argument -/

/-- A bounded Poisson correction leaves a weakly harmonic remainder. The correction
may be any continuous representative of the occupation solution; only its pointwise
bound and the harmonic remainder are consumed by the oscillation argument. -/
def KilledKernelHarmonicApproximation (kappa A gamma : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ, 2 ≤ d → ∀ c rho : Vec d → ℝ, ∀ law : Kernel (Vec d) (Path d),
      LocalDiffusion c rho law → ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
      CoefficientC11On U c → CoefficientC11On U rho →
      ∀ F : ℝ, 0 < F → ∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
      ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U) →
      0 < ((weightedMeasure rho) U).toReal →
      (∀ z ∈ U, meanExit law U z ≤ ENNReal.ofReal (A * F)) →
      (∀ t : ℝ, 0 < t → ∀ z ∈ U,
        p t z z ≤ A / ((weightedMeasure rho) U).toReal * (1 + F / t) ^ gamma) →
      ∀ t : ℝ, kappa * F / 8 ≤ t → t ≤ kappa * F / 4 → ∀ x ∈ U,
        ∀ outer : Set (Vec d), IsOpen outer → outer ⊆ U →
          ∀ E : ℝ, 0 ≤ E →
          (∀ z ∈ outer, meanExit law outer z ≤ ENNReal.ofReal E) →
          ∃ v : Vec d → ℝ,
            (∀ z ∈ outer, |v z| ≤ (C / (F * ((weightedMeasure rho) U).toReal)) * E) ∧
            WeakHarmonic c outer (fun y => p t x y - v y)

/-! ### The reduction -/

/-- A harmonic approximation gives kernel oscillation control: the correction is
bounded by `Cε/M`, the diagonal assumption bounds the whole kernel by
`A(1+8/κ)^γ/M`, and the local oscillation contraction closes the estimate. -/
theorem killedKernelOscillation_of_harmonicApproximation {kappa A gamma : ℝ}
    (hkappa : 0 < kappa) (hA : 0 < A) (hgamma : 0 < gamma)
    (hext : KilledKernelHarmonicApproximation kappa A gamma) :
    KilledKernelOscillation kappa A gamma := by
  obtain ⟨C, hC, hext⟩ := hext
  refine ⟨A * (1 + 8 / kappa) ^ gamma + 4 * C, by positivity, ?_⟩
  intro d hd c rho law hD U hU hUb hc11 hrho11 F hF p hp hpc hM hmean hdiag epsilon heps
    inner outer houter hinner hio hoU hoe hcontract t ht1 ht2 x hx
  set M := ((weightedMeasure rho) U).toReal with hMdef
  have : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hinnerU : inner ⊆ U := (subset_closure.trans hio).trans hoU
  -- the kernel at time `t` is bounded by `K` on the whole domain
  set K := A / M * (1 + 8 / kappa) ^ gamma with hKdef
  have hratio : F / t ≤ 8 / kappa := by
    rw [div_le_div_iff₀ htpos hkappa]
    nlinarith only [ht1, hkappa, hF]
  have hpow : (1 + F / t) ^ gamma ≤ (1 + 8 / kappa) ^ gamma :=
    Real.rpow_le_rpow (by positivity) (by linarith) hgamma.le
  have hdiagK : ∀ z ∈ U, p t z z ≤ K := by
    intro z hz
    refine (hdiag t htpos z hz).trans ?_
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hpK : ∀ y ∈ U, p t x y ≤ K :=
    fun y hy => density_le_of_diagonal_le hD hU hUb hp hpc htpos hdiagK hx hy
  have hpnn : ∀ y ∈ U, 0 ≤ p t x y := fun y hy => hp.2.1 t htpos x hx y hy
  have hKnn : 0 ≤ K := le_trans (hpnn x hx) (hpK x hx)
  -- the harmonic approximant and the maximum principle for the correction
  obtain ⟨v, hvc, hharm⟩ :=
    hext d hd c rho law hD U hU hUb hc11 hrho11 F hF p hp hpc hM hmean hdiag t ht1 ht2 x hx
      outer houter hoU (epsilon * F) (by positivity) hoe
  set cv := C * epsilon / M with hcvdef
  have hcvnn : 0 ≤ cv := by positivity
  have hvb : ∀ y ∈ outer, |v y| ≤ cv := by
    intro y hy
    refine (hvc y hy).trans_eq ?_
    rw [hcvdef]
    dsimp only [M]
    field_simp
  set h := fun y => p t x y - v y with hhdef
  -- the oscillation of the approximant on the outer set
  have hoscout : oscillation outer h ≤ ENNReal.ofReal (K + 2 * cv) := by
    refine oscillation_le_ofReal fun y hy z hz => ?_
    have h1 : |p t x y - p t x z| ≤ K := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [hpK y (hoU hy), hpnn z (hoU hz)]
      · linarith [hpK z (hoU hz), hpnn y (hoU hy)]
    have h2 := hvb y hy
    have h3 := hvb z hz
    have hrw : h y - h z = (p t x y - p t x z) - (v y - v z) := by rw [hhdef]; ring
    rw [hrw]
    calc |(p t x y - p t x z) - (v y - v z)|
        ≤ |p t x y - p t x z| + |v y - v z| := abs_sub _ _
      _ ≤ K + (|v y| + |v z|) := by gcongr; exact abs_sub _ _
      _ ≤ K + 2 * cv := by linarith
  -- the contraction on the inner set
  have hoscin : oscillation inner h ≤ ENNReal.ofReal (epsilon * (K + 2 * cv)) := by
    refine (hcontract h hharm).trans ?_
    rw [ENNReal.ofReal_mul heps.le]
    exact mul_le_mul' le_rfl hoscout
  have hstep : ∀ y ∈ inner, ∀ z ∈ inner,
      |p t x y - p t x z| ≤ epsilon * (K + 2 * cv) + 2 * cv := by
    intro y hy z hz
    have hy' : y ∈ outer := (subset_closure.trans hio) hy
    have hz' : z ∈ outer := (subset_closure.trans hio) hz
    have hh := abs_sub_le_of_oscillation_le (by positivity) hoscin hy hz
    have hrw : p t x y - p t x z = (h y - h z) + (v y - v z) := by rw [hhdef]; ring
    rw [hrw]
    calc |(h y - h z) + (v y - v z)| ≤ |h y - h z| + |v y - v z| := abs_add_le _ _
      _ ≤ epsilon * (K + 2 * cv) + (|v y| + |v z|) := by gcongr; exact abs_sub _ _
      _ ≤ epsilon * (K + 2 * cv) + 2 * cv := by linarith [hvb y hy', hvb z hz']
  have hG : (0 : ℝ) ≤ (1 + 8 / kappa) ^ gamma :=
    Real.rpow_nonneg (by positivity) _
  refine oscillation_le_ofReal fun y hy z hz => ?_
  rcases le_or_gt epsilon 1 with hle | hgt
  · refine (hstep y hy z hz).trans ?_
    rw [hKdef, hcvdef]
    have hid : (A * (1 + 8 / kappa) ^ gamma + 4 * C) * epsilon / M
        - (epsilon * (A / M * (1 + 8 / kappa) ^ gamma + 2 * (C * epsilon / M))
          + 2 * (C * epsilon / M))
        = 2 * C * epsilon * (1 - epsilon) / M := by
      field_simp
      ring
    have hnn : 0 ≤ 2 * C * epsilon * (1 - epsilon) / M :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) heps.le) (by linarith)) hM.le
    linarith
  · have h1 : |p t x y - p t x z| ≤ K := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · linarith [hpK y (hinnerU hy), hpnn z (hinnerU hz)]
      · linarith [hpK z (hinnerU hz), hpnn y (hinnerU hy)]
    refine h1.trans ?_
    rw [hKdef]
    have hid : (A * (1 + 8 / kappa) ^ gamma + 4 * C) * epsilon / M
        - A / M * (1 + 8 / kappa) ^ gamma
        = (A * (1 + 8 / kappa) ^ gamma * (epsilon - 1) + 4 * C * epsilon) / M := by
      field_simp
      ring
    have hnn : 0 ≤ (A * (1 + 8 / kappa) ^ gamma * (epsilon - 1) + 4 * C * epsilon) / M := by
      refine div_nonneg (add_nonneg ?_ ?_) hM.le
      · exact mul_nonneg (mul_nonneg hA.le hG) (by linarith)
      · positivity
    linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
