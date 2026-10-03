module

public import SubdiffusiveProcess.Assumptions
public import SubdiffusiveProcess.CoarseGrainingVocab.Defect
public import SubdiffusiveProcess.CoarseGrainingVocab.MeasurabilityProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import Homogenization.Book.Ch04.Theorems.Concentration
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

/-!
# Finite-cutoff spatial moments

This file supplies the two normalized spatial `L^p` cutoff-ratio estimates
from `e.am.Lp.moments` and `e.am.Lp.moments.inv`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book Homogenization.IndependentSums
open scoped BigOperators ENNReal NNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private abbrev Field (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField d

/-- A Chapter-2 domain, viewed with normalized Lebesgue measure. -/
noncomputable def domainNormalizedVolume {d : ℕ} (U : Ch02.Domain d) :
    Measure (Vec d) :=
  (U.isDomain.toBoundedMeasurableDomain U.nonempty).normalizedVolume

instance {d : ℕ} (U : Ch02.Domain d) :
    IsProbabilityMeasure (domainNormalizedVolume U) where
  measure_univ := by
    exact (U.isDomain.toBoundedMeasurableDomain U.nonempty).normalizedVolume_apply_univ

/-- The paper's normalized spatial `L^p` norm, kept in `ENNReal`. -/
noncomputable def cutoffSpatialLpNorm {d : ℕ} (U : Ch02.Domain d) (p : ℝ)
    (f : Vec d → ℝ) : ℝ≥0∞ :=
  SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p) (domainNormalizedVolume U)

/-- The unnormalized inverse ratio in `e.am.Lp.moments.inv`.  This is distinct
from the later Section-3 observable carrying an additional deterministic
normalization. -/
noncomputable def inverseCutoffRatioMinusOne {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) : ℝ :=
  aCutoffAtInt M n ω x / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x - 1

/-- Shell indices contributing to `a_m a_n⁻¹`, including the convention
`a_{-1}=1`. -/
def cutoffShellIndices (m : ℕ) (n : ℤ) : Finset ℕ :=
  Finset.Icc (n + 1).toNat m

/-- The centered random shell sum at a fixed spatial point. -/
def cutoffShellSum {d : ℕ} (m : ℕ) (n : ℤ) (x : Vec d) : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ :=
  fun omega => ∑ k ∈ cutoffShellIndices m n, omega k x

/-- Universal scale constant in the fixed-point shell-sum estimate. -/
noncomputable def cutoffGammaConst : ℝ :=
  Ch04.gammaSigmaIndependentSumConst 2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem cutoffGammaConst_pos : 0 < cutoffGammaConst := by
  have hsum : 0 < Ch04.gammaSigmaIndependentSumConst 2 := by
    dsimp [Ch04.gammaSigmaIndependentSumConst]
    simp only [show ¬(2 : ℝ) < 1 by norm_num, if_false]
    dsimp [Ch04.gammaSigmaExpRegimeEndpointConst,
      gammaSigmaExpRegimeEndpointConst]
    simp only [show (2 : ℝ) ≠ 1 by norm_num, if_false]
    apply mul_pos (by norm_num)
    dsimp [gammaSigmaExpRegimeConst]
    exact lt_of_lt_of_le
      (mul_pos (by positivity) (gammaMomentConst_pos (by norm_num)))
      (le_max_left _ _)
  exact mul_pos hsum (Real.rpow_pos_of_pos (by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith) _)

/-- One universal constant large enough for both source-shaped cutoff moment
estimates. -/
noncomputable def cutoffMomentConst : ℝ :=
  1 +
    2 * gammaMomentConst 2 * Real.sqrt 2 *
      (cutoffGammaConst + Real.log 2 / 2) +
    cutoffGammaConst ^ 2 + Real.log 2 / 2

theorem cutoffMomentConst_pos : 0 < cutoffMomentConst := by
  unfold cutoffMomentConst
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgamma : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsum : 0 < cutoffGammaConst + Real.log 2 / 2 :=
    add_pos cutoffGammaConst_pos (div_pos hlog (by norm_num))
  have hprod : 0 < 2 * gammaMomentConst 2 * Real.sqrt 2 *
      (cutoffGammaConst + Real.log 2 / 2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hgamma) hsqrt) hsum
  nlinarith [sq_nonneg cutoffGammaConst]

theorem self_le_exp_sq {r : ℝ} (hr : 0 ≤ r) :
    r ≤ Real.exp (r ^ 2) := by
  rcases le_or_gt r 1 with hr1 | hr1
  · exact hr1.trans (Real.one_le_exp (sq_nonneg r))
  · have hrsq : r ≤ r ^ 2 := by
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1.le)]
    exact hrsq.trans (le_trans (by linarith) (Real.add_one_le_exp (r ^ 2)))

/- The following layer-cake argument is adapted from
`Algsuperdiff/Section3/Provider/Orlicz/WeightedSubgaussian.lean`.  The factor
`3` (instead of `2`) fills the weak-tail convention's unregulated interval
`0 < s < 1`. -/

/-- An exponential tail above every positive threshold gives a square-
exponential moment. -/
private theorem integral_exp_smul_le_of_tail_three
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {W : Omega → ℝ}
    (hW_meas : AEMeasurable W mu) (hW_nn : 0 ≤ᵐ[mu] W)
    (hW_tail : ∀ s : ℝ, 0 < s →
      mu.real {ω | s < W ω} ≤ 3 * Real.exp (-s))
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) :
    Integrable (fun ω => Real.exp (l * W ω)) mu ∧
      ∫ ω, Real.exp (l * W ω) ∂mu ≤ 1 + 3 * l / (1 - l) := by
  have hposl : (0 : ℝ) < 1 - l := by linarith only [hl1]
  have hlne : l - 1 ≠ 0 := ne_of_lt (by linarith only [hl1])
  set g : ℝ → ℝ := fun s => l * Real.exp (l * s) with hg
  have hg_nn : ∀ t : ℝ, 0 ≤ g t := fun t =>
    mul_nonneg hl0 (Real.exp_pos _).le
  have hFTC : ∀ y : ℝ, ∫ s in (0 : ℝ)..y, g s = Real.exp (l * y) - 1 := by
    intro y
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) y,
        HasDerivAt (fun s => Real.exp (l * s)) (g s) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => l * s) l s := by
        simpa using (hasDerivAt_id s).const_mul l
      simpa [hg, mul_comm] using h1.exp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous g).intervalIntegrable 0 y)]
    simp
  have hsplit : (fun ω => ENNReal.ofReal (Real.exp (l * W ω))) =ᵐ[mu]
      (fun ω => ENNReal.ofReal (∫ s in (0 : ℝ)..(W ω), g s) + 1) := by
    filter_upwards [hW_nn] with ω hω
    have hge : (0 : ℝ) ≤ Real.exp (l * W ω) - 1 := by
      have h1 : (1 : ℝ) ≤ Real.exp (l * W ω) :=
        Real.one_le_exp (mul_nonneg hl0 hω)
      linarith only [h1]
    rw [hFTC (W ω), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add hge zero_le_one]
    congr 1
    ring
  have hg_intble : ∀ t > (0 : ℝ), IntervalIntegrable g volume 0 t :=
    fun t _ => (by fun_prop : Continuous g).intervalIntegrable 0 t
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul mu hW_nn hW_meas
    hg_intble (Filter.Eventually.of_forall hg_nn)
  have hRHS : ∫⁻ t in Set.Ioi (0 : ℝ),
      mu {a | t < W a} * ENNReal.ofReal (g t) ≤
        ENNReal.ofReal (3 * l / (1 - l)) := by
    have hbound : ∀ t : ℝ,
        mu {a | t < W a} * ENNReal.ofReal (g t) ≤
          ENNReal.ofReal (3 * l * Real.exp ((l - 1) * t)) := by
      intro t
      have hmeas_le : mu {a | t < W a} ≤
          ENNReal.ofReal (3 * Real.exp (-t)) := by
        rcases le_or_gt t 0 with ht | ht
        · refine le_trans
            (le_of_le_of_eq (measure_mono (Set.subset_univ _)) measure_univ) ?_
          rw [ENNReal.one_le_ofReal]
          have hexp : (1 : ℝ) ≤ Real.exp (-t) :=
            Real.one_le_exp (by linarith only [ht])
          nlinarith
        · rw [← ENNReal.ofReal_toReal (measure_ne_top mu _)]
          exact ENNReal.ofReal_le_ofReal (hW_tail t ht)
      calc
        mu {a | t < W a} * ENNReal.ofReal (g t) ≤
            ENNReal.ofReal (3 * Real.exp (-t)) * ENNReal.ofReal (g t) :=
          mul_le_mul_left hmeas_le _
        _ = ENNReal.ofReal (3 * Real.exp (-t) * g t) :=
          (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (3 * l * Real.exp ((l - 1) * t)) := by
          congr 1
          rw [hg, show (l - 1) * t = -t + l * t by ring, Real.exp_add]
          ring
    have hint : Integrable (fun t => 3 * l * Real.exp ((l - 1) * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (integrableOn_exp_mul_Ioi (show l - 1 < 0 by linarith only [hl1]) 0).const_mul
        (3 * l)
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t => 3 * l * Real.exp ((l - 1) * t)) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have heval : ∫ t in Set.Ioi (0 : ℝ),
        3 * l * Real.exp ((l - 1) * t) = 3 * l / (1 - l) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (show l - 1 < 0 by linarith only [hl1]) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp
      ring
    calc
      ∫⁻ t in Set.Ioi (0 : ℝ), mu {a | t < W a} * ENNReal.ofReal (g t) ≤
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (3 * l * Real.exp ((l - 1) * t)) :=
        lintegral_mono hbound
      _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ),
            3 * l * Real.exp ((l - 1) * t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ = ENNReal.ofReal (3 * l / (1 - l)) := by rw [heval]
  have hmain : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * W ω)) ∂mu ≤
      ENNReal.ofReal (1 + 3 * l / (1 - l)) := by
    rw [lintegral_congr_ae hsplit,
      lintegral_add_right _ measurable_const, lintegral_one, measure_univ, hlayer]
    have hsum : ENNReal.ofReal (1 + 3 * l / (1 - l)) =
        ENNReal.ofReal (3 * l / (1 - l)) + 1 := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by positivity) zero_le_one]
      congr 1
      ring
    rw [hsum]
    exact add_le_add hRHS le_rfl
  have hf_nn : 0 ≤ᵐ[mu] (fun ω => Real.exp (l * W ω)) :=
    Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
  have hf_meas : AEStronglyMeasurable (fun ω => Real.exp (l * W ω)) mu :=
    (Real.measurable_exp.comp_aemeasurable
      (hW_meas.const_mul l)).aestronglyMeasurable
  have hf_int : Integrable (fun ω => Real.exp (l * W ω)) mu := by
    refine ⟨hf_meas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hf_nn]
    exact lt_of_le_of_lt hmain ENNReal.ofReal_lt_top
  refine ⟨hf_int, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf_nn hf_meas]
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l * W ω)) ∂mu).toReal ≤
        (ENNReal.ofReal (1 + 3 * l / (1 - l))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = 1 + 3 * l / (1 - l) := ENNReal.toReal_ofReal (by positivity)

/-- A weak `Gamma_2` bound at an arbitrary positive scale retains that scale
inside a square-exponential moment. -/
private theorem integral_exp_half_normalized_sq_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * (A⁻¹ * |X ω|) ^ 2)) mu ∧
      ∫ ω, Real.exp ((1 / 2 : ℝ) * (A⁻¹ * |X ω|) ^ 2) ∂mu ≤ 4 := by
  let W : Omega → ℝ := fun ω => (A⁻¹ * |X ω|) ^ 2
  have hWm : AEMeasurable W mu := by
    simpa only [Real.norm_eq_abs] using (hXm.norm.const_mul A⁻¹).pow_const 2
  have hWnn : 0 ≤ᵐ[mu] W :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have htail : ∀ s : ℝ, 0 < s →
      mu.real {ω | s < W ω} ≤ 3 * Real.exp (-s) := by
    intro s hs
    rcases lt_or_ge s 1 with hs1 | hs1
    · calc
        mu.real {ω | s < W ω} ≤ 1 := measureReal_le_one
        _ ≤ 3 * Real.exp (-s) := by
          have hexp_lt : Real.exp s < 3 := by
            have h1 : Real.exp s < Real.exp 1 := Real.exp_lt_exp.mpr hs1
            have h2 := Real.exp_one_lt_d9
            linarith
          calc
            (1 : ℝ) = Real.exp s * Real.exp (-s) := by
              rw [← Real.exp_add]
              simp
            _ ≤ 3 * Real.exp (-s) :=
              mul_le_mul_of_nonneg_right hexp_lt.le (Real.exp_pos _).le
    · have hsqrt : 1 ≤ Real.sqrt s := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hs1
      have hsource :=
        (isBigO_gammaSigma_iff.mp hX) hsqrt
      have hsubset : {ω | s < W ω} ⊆
          absTailEvent X (A * Real.sqrt s) := by
        intro ω hω
        change s < (A⁻¹ * |X ω|) ^ 2 at hω
        change A * Real.sqrt s < |X ω|
        have hs0 : 0 ≤ s := hs.le
        have hsqrt0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
        have hscaled0 : 0 ≤ A⁻¹ * |X ω| :=
          mul_nonneg (inv_nonneg.mpr hA.le) (abs_nonneg _)
        have hsqrt_lt : Real.sqrt s < A⁻¹ * |X ω| := by
          rw [← sq_lt_sq₀ hsqrt0 hscaled0]
          simpa [Real.sq_sqrt hs0] using hω
        calc
          A * Real.sqrt s < A * (A⁻¹ * |X ω|) :=
            mul_lt_mul_of_pos_left hsqrt_lt hA
          _ = |X ω| := by field_simp
      calc
        mu.real {ω | s < W ω} ≤
            mu.real (absTailEvent X (A * Real.sqrt s)) := measureReal_mono hsubset
        _ ≤ Real.exp (-(Real.sqrt s ^ (2 : ℝ))) := hsource
        _ ≤ 3 * Real.exp (-s) := by
          rw [Real.rpow_two, Real.sq_sqrt hs.le]
          nlinarith [Real.exp_pos (-s)]
  have h := integral_exp_smul_le_of_tail_three hWm hWnn htail
    (l := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  constructor
  · simpa [W] using h.1
  · have hbound := h.2
    norm_num at hbound
    simpa [W] using hbound



theorem eLpNorm_le_of_isBigO_gammaTwo
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A p : ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    eLpNorm X (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt p * A) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : Integrable (fun ω => |X ω| ^ p) mu := by
    exact integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := fun ω => |X ω|) (K := A) (σ := 2) (p := p)
      (by norm_num) hA hp (fun ω => abs_nonneg (X ω))
      (hXm.norm) (by simpa [IsBigO] using hX)
  have hmem : MemLp X (ENNReal.ofReal p) mu := by
    apply (integrable_norm_rpow_iff hXm.aestronglyMeasurable
      (by positivity) ENNReal.ofReal_ne_top).1
    simpa [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hpow
  have hmoment := integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := mu) (X := X) (K := A) (σ := 2) (p := p)
    (by norm_num) hA hp hXm hX
  let B : ℝ := gammaMomentConst 2 * Real.sqrt p * A
  have hB : 0 < B := by
    exact mul_pos (mul_pos (gammaMomentConst_pos (by norm_num))
      (Real.sqrt_pos.mpr hp0)) hA
  have hroot : (∫ ω, |X ω| ^ p ∂mu) ^ p⁻¹ ≤ B := by
    have hint0 : 0 ≤ ∫ ω, |X ω| ^ p ∂mu :=
      integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    have h := Real.rpow_le_rpow hint0 hmoment (inv_nonneg.mpr hp0.le)
    calc
      (∫ ω, |X ω| ^ p ∂mu) ^ p⁻¹ ≤
          ((gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * A) ^ p) ^ p⁻¹ := h
      _ = B := by
        have hbase : gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * A = B := by
          dsimp [B]
          rw [Real.sqrt_eq_rpow]
          congr 2
          norm_num
        rw [hbase]
        rw [← Real.rpow_mul (le_of_lt hB)]
        rw [mul_inv_cancel₀ hp0.ne', Real.rpow_one]
  rw [hmem.eLpNorm_eq_integral_rpow_norm
    (by positivity) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal hroot

/-- Deterministic centering enlarges a weak-subgaussian scale by at most the
size of the center. -/
theorem isBigO_gammaTwo_sub_const
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {X : Omega → ℝ} {A b : ℝ}
    (hX : IsBigO mu (gammaSigma 2) X A) :
    IsBigO mu (gammaSigma 2) (fun ω => X ω - b) (A + |b|) := by
  rw [isBigO_gammaSigma_iff] at hX ⊢
  intro t ht
  refine (measureReal_mono ?_).trans (hX ht)
  intro ω hω
  change (A + |b|) * t < |X ω - b| at hω
  change A * t < |X ω|
  have htri : |X ω - b| ≤ |X ω| + |b| := abs_sub _ _
  have hbt : |b| ≤ |b| * t := by
    simpa using mul_le_mul_of_nonneg_left ht (abs_nonneg b)
  nlinarith

/-- Exponential absolute moments of a deterministically shifted weak
subgaussian variable.  The one-step weighted-energy comparison reuses this
estimate for the global Taylor envelope. -/
theorem integral_exp_abs_sub_const_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A q b : ℝ}
    (hA : 0 < A) (hq : 0 ≤ q) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    Integrable (fun ω => Real.exp (q * |X ω - b|)) mu ∧
      ∫ ω, Real.exp (q * |X ω - b|) ∂mu ≤
        4 * Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) := by
  have hsquare := integral_exp_half_normalized_sq_le hA hXm hX
  let majorant : Omega → ℝ := fun ω =>
    Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) *
      Real.exp ((1 / 2 : ℝ) * (A⁻¹ * |X ω|) ^ 2)
  have hmajorant : Integrable majorant mu := by
    exact hsquare.1.const_mul _
  have htargetMeas : AEStronglyMeasurable
      (fun ω => Real.exp (q * |X ω - b|)) mu := by
    exact (Real.measurable_exp.comp_aemeasurable
      ((hXm.sub_const b).norm.const_mul q)).aestronglyMeasurable
  have hpoint : ∀ ω, Real.exp (q * |X ω - b|) ≤ majorant ω := by
    intro ω
    have htri : |X ω - b| ≤ |X ω| + |b| := abs_sub _ _
    have hqtri : q * |X ω - b| ≤ q * |X ω| + q * |b| := by
      nlinarith
    have hyoung : q * |X ω| ≤
        q ^ 2 * A ^ 2 / 2 + (A⁻¹ * |X ω|) ^ 2 / 2 := by
      have hs : 0 ≤ (q * A - A⁻¹ * |X ω|) ^ 2 := sq_nonneg _
      field_simp [hA.ne'] at hs ⊢
      nlinarith
    change Real.exp (q * |X ω - b|) ≤
      Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) *
        Real.exp ((1 / 2 : ℝ) * (A⁻¹ * |X ω|) ^ 2)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hqtri, hyoung]
  have htarget : Integrable (fun ω => Real.exp (q * |X ω - b|)) mu := by
    refine hmajorant.mono' htargetMeas ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint ω
  refine ⟨htarget, ?_⟩
  calc
    ∫ ω, Real.exp (q * |X ω - b|) ∂mu ≤ ∫ ω, majorant ω ∂mu :=
      integral_mono htarget hmajorant hpoint
    _ = Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) *
        ∫ ω, Real.exp ((1 / 2 : ℝ) * (A⁻¹ * |X ω|) ^ 2) ∂mu := by
      rw [integral_const_mul]
    _ ≤ Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) * 4 :=
      mul_le_mul_of_nonneg_left hsquare.2 (Real.exp_pos _).le
    _ = 4 * Real.exp (q ^ 2 * A ^ 2 / 2 + q * |b|) := by ring

/-- Elementary multiplicative remainder bound for the exponential. -/
private theorem abs_exp_sub_one_le_mul (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht))]
    have hneg := Real.add_one_le_exp (-t)
    have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_pos t).le
    rw [Real.exp_neg, mul_add, mul_one,
      mul_inv_cancel₀ (Real.exp_ne_zero t)] at hmul
    nlinarith
  · have ht' : t ≤ 0 := ht.le
    rw [abs_of_neg ht, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht'))]
    have hlin := Real.add_one_le_exp t
    have hexp : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ -t)]

/-- A sharp-enough lognormal moment converter which retains the weak-tail
scale as a linear prefactor. -/
theorem integral_abs_exp_sub_const_sub_one_rpow_root_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A p b : ℝ}
    (hA : 0 < A) (hp : 1 ≤ p) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    Integrable (fun ω => |Real.exp (X ω - b) - 1| ^ p) mu ∧
      (∫ ω, |Real.exp (X ω - b) - 1| ^ p ∂mu) ^ p⁻¹ ≤
        2 * gammaMomentConst 2 * Real.sqrt (2 * p) * (A + |b|) *
          Real.exp (p * A ^ 2 + |b|) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h2p : 1 ≤ 2 * p := by nlinarith
  let T : Omega → ℝ := fun ω => X ω - b
  let f : Omega → ℝ := fun ω => |T ω| ^ p
  let g : Omega → ℝ := fun ω => Real.exp (p * |T ω|)
  have hTm : AEMeasurable T mu := hXm.sub_const b
  have hscale : 0 < A + |b| := add_pos_of_pos_of_nonneg hA (abs_nonneg b)
  have hTgamma : IsBigO mu (gammaSigma 2) T (A + |b|) := by
    simpa [T] using isBigO_gammaTwo_sub_const (b := b) hX
  have hTpow : Integrable (fun ω => |T ω| ^ (2 * p)) mu := by
    exact integrable_rpow_of_isBigOWith_gammaSigma
      (μ := mu) (Y := fun ω => |T ω|) (K := A + |b|)
      (σ := 2) (p := 2 * p) (by norm_num) hscale h2p
      (fun ω => abs_nonneg (T ω)) hTm.norm (by simpa [IsBigO] using hTgamma)
  have hTmoment : ∫ ω, |T ω| ^ (2 * p) ∂mu ≤
      (gammaMomentConst 2 * (2 * p) ^ (2 : ℝ)⁻¹ * (A + |b|)) ^ (2 * p) :=
    integral_abs_rpow_le_of_isBigO_gammaSigma
      (μ := mu) (X := T) (K := A + |b|) (σ := 2) (p := 2 * p)
      (by norm_num) hscale h2p hTm hTgamma
  have hExp := integral_exp_abs_sub_const_le
    (mu := mu) (X := X) (A := A) (q := 2 * p) (b := b)
    hA (by positivity) hXm hX
  have hfm : AEStronglyMeasurable f mu := by
    exact (hTm.norm.pow_const p).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g mu := by
    exact (Real.measurable_exp.comp_aemeasurable
      (hTm.norm.const_mul p)).aestronglyMeasurable
  have hf2 : MemLp f 2 mu := by
    apply (memLp_two_iff_integrable_sq hfm).2
    convert hTpow using 1
    funext ω
    dsimp [f]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (abs_nonneg (T ω))]
    congr 1
    ring
  have hg2 : MemLp g 2 mu := by
    apply (memLp_two_iff_integrable_sq hgm).2
    convert hExp.1 using 1
    funext ω
    dsimp [g, T]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfg : Integrable (fun ω => f ω * g ω) mu := by
    exact hf2.integrable_mul hg2
  have htargetMeas : AEStronglyMeasurable
      (fun ω => |Real.exp (T ω) - 1| ^ p) mu := by
    exact (((Real.measurable_exp.comp_aemeasurable hTm).sub
      measurable_const.aemeasurable).norm.pow_const p).aestronglyMeasurable
  have hpoint : ∀ ω, |Real.exp (T ω) - 1| ^ p ≤ f ω * g ω := by
    intro ω
    calc
      |Real.exp (T ω) - 1| ^ p ≤
          (|T ω| * Real.exp |T ω|) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) (abs_exp_sub_one_le_mul (T ω)) hp0.le
      _ = f ω * g ω := by
        rw [Real.mul_rpow (abs_nonneg _) (Real.exp_pos _).le]
        dsimp [f, g]
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 2
        ring
  have htarget : Integrable (fun ω => |Real.exp (T ω) - 1| ^ p) mu := by
    refine hfg.mono' htargetMeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hpoint ω
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hf2' : MemLp f (ENNReal.ofReal 2) mu := by simpa using hf2
  have hg2' : MemLp g (ENNReal.ofReal 2) mu := by simpa using hg2
  have hprod := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    (f := f) (g := g)
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hf2' hg2'
  have hintegral : ∫ ω, |Real.exp (T ω) - 1| ^ p ∂mu ≤
      (∫ ω, f ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        (∫ ω, g ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) := by
    exact (integral_mono htarget hfg hpoint).trans hprod
  -- The remaining calculation takes the two square roots and then the
  -- `p`-th root, preserving one power of the subgaussian scale.
  let K : ℝ := gammaMomentConst 2 * Real.sqrt (2 * p) * (A + |b|)
  let D : ℝ := (2 * p) ^ 2 * A ^ 2 / 2 + 2 * p * |b|
  have hK : 0 < K := by
    exact mul_pos (mul_pos (gammaMomentConst_pos (by norm_num))
      (Real.sqrt_pos.mpr (by positivity))) hscale
  have hfint : ∫ ω, f ω ^ (2 : ℝ) ∂mu ≤ K ^ (2 * p) := by
    calc
      ∫ ω, f ω ^ (2 : ℝ) ∂mu =
          ∫ ω, |T ω| ^ (2 * p) ∂mu := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [f]
        rw [← Real.rpow_mul (abs_nonneg (T ω))]
        congr 1
        ring
      _ ≤ (gammaMomentConst 2 * (2 * p) ^ (2 : ℝ)⁻¹ *
          (A + |b|)) ^ (2 * p) := hTmoment
      _ = K ^ (2 * p) := by
        congr 2
        rw [Real.sqrt_eq_rpow]
        congr 2
        norm_num
  have hgint : ∫ ω, g ω ^ (2 : ℝ) ∂mu ≤ 4 * Real.exp D := by
    calc
      ∫ ω, g ω ^ (2 : ℝ) ∂mu =
          ∫ ω, Real.exp (2 * p * |X ω - b|) ∂mu := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [g, T]
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      _ ≤ 4 * Real.exp ((2 * p) ^ 2 * A ^ 2 / 2 + 2 * p * |b|) := hExp.2
      _ = 4 * Real.exp D := by rfl
  have hfint0 : 0 ≤ ∫ ω, f ω ^ (2 : ℝ) ∂mu :=
    integral_nonneg (fun ω => Real.rpow_nonneg (Real.rpow_nonneg (abs_nonneg _) _) _)
  have hgint0 : 0 ≤ ∫ ω, g ω ^ (2 : ℝ) ∂mu :=
    integral_nonneg (fun ω => Real.rpow_nonneg (Real.exp_pos _).le _)
  have hfsqrt : (∫ ω, f ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) ≤ K ^ p := by
    calc
      (∫ ω, f ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) ≤
          (K ^ (2 * p)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hfint0 hfint (by norm_num)
      _ = K ^ p := by
        rw [← Real.rpow_mul hK.le]
        congr 1
        ring
  have hgsqrt : (∫ ω, g ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) ≤
      2 * Real.exp (D / 2) := by
    calc
      (∫ ω, g ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) ≤
          (4 * Real.exp D) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hgint0 hgint (by norm_num)
      _ = 2 * Real.exp (D / 2) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos _).le]
        norm_num
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
  have hI : ∫ ω, |Real.exp (T ω) - 1| ^ p ∂mu ≤
      2 * K ^ p * Real.exp (D / 2) := by
    calc
      ∫ ω, |Real.exp (T ω) - 1| ^ p ∂mu ≤
          (∫ ω, f ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
            (∫ ω, g ω ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) := hintegral
      _ ≤ K ^ p * (2 * Real.exp (D / 2)) :=
        mul_le_mul hfsqrt hgsqrt
          (Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg
            (Real.exp_pos _).le _) _)
          (Real.rpow_nonneg hK.le _)
      _ = 2 * K ^ p * Real.exp (D / 2) := by ring
  have hI0 : 0 ≤ ∫ ω, |Real.exp (T ω) - 1| ^ p ∂mu :=
    integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨by simpa [T] using htarget, ?_⟩
  calc
    (∫ ω, |Real.exp (X ω - b) - 1| ^ p ∂mu) ^ p⁻¹ =
        (∫ ω, |Real.exp (T ω) - 1| ^ p ∂mu) ^ p⁻¹ := by rfl
    _ ≤ (2 * K ^ p * Real.exp (D / 2)) ^ p⁻¹ :=
      Real.rpow_le_rpow hI0 hI (inv_nonneg.mpr hp0.le)
    _ = 2 ^ p⁻¹ * K * Real.exp (D / (2 * p)) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * K ^ p)
        (Real.exp_pos _).le]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg hK.le _)]
      rw [← Real.rpow_mul hK.le, mul_inv_cancel₀ hp0.ne', Real.rpow_one]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp [hp0.ne']
    _ ≤ 2 * K * Real.exp (p * A ^ 2 + |b|) := by
      have hpinv : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp
      have htwo : (2 : ℝ) ^ p⁻¹ ≤ 2 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) hpinv
      have hD : D / (2 * p) = p * A ^ 2 + |b| := by
        dsimp [D]
        field_simp [hp0.ne']
      rw [hD]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htwo hK.le) (Real.exp_pos _).le
    _ = 2 * gammaMomentConst 2 * Real.sqrt (2 * p) * (A + |b|) *
        Real.exp (p * A ^ 2 + |b|) := by
      dsimp [K]
      ring

/-- The shell interval has exactly `m-n` layers on the source range
`-1 ≤ n < m`. -/
theorem cutoffShellIndices_card (m : ℕ) (n : ℤ) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    (cutoffShellIndices m n).card = ((m : ℤ) - n).toNat := by
  rw [cutoffShellIndices, Nat.card_Icc]
  omega

/-- The difference of the two cutoff logarithms is the centered shell block. -/
theorem cutoff_log_ratio_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    (∑ k ∈ Finset.range (m + 1),
        (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) -
      (if n < 0 then 0 else
        ∑ k ∈ Finset.range (n.toNat + 1),
          (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
      cutoffShellSum m n x ω -
        (((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
  let F : ℕ → ℝ := fun k => ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hlower : (n + 1).toNat ≤ m + 1 := by omega
  have hinterval : Finset.Icc (n + 1).toNat m = Finset.Ico (n + 1).toNat (m + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hprefix :
      (if n < 0 then 0 else ∑ k ∈ Finset.range (n.toNat + 1), F k) =
        ∑ k ∈ Finset.range (n + 1).toNat, F k := by
    by_cases hnneg : n < 0
    · have hnval : n = -1 := by omega
      simp [hnval]
    · have hnat : (n + 1).toNat = n.toNat + 1 := by omega
      simp [hnneg, hnat]
  have hcentered : ∑ k ∈ cutoffShellIndices m n, F k =
      cutoffShellSum m n x ω -
        (((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [cutoffShellIndices_card m n hn hnm]
    have hdiff : 0 ≤ (m : ℤ) - n := by omega
    have hcast : ((((m : ℤ) - n).toNat : ℕ) : ℝ) =
        (((m : ℤ) - n : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hdiff
    rw [hcast]
    rfl
  change (∑ k ∈ Finset.range (m + 1), F k) -
      (if n < 0 then 0 else ∑ k ∈ Finset.range (n.toNat + 1), F k) = _
  rw [hprefix, ← Finset.sum_Ico_eq_sub F hlower, ← hinterval]
  exact hcentered

/-- Exact shell representation of the forward cutoff ratio. -/
theorem cutoffRatioMinusOne_eq_exp_shell {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    cutoffRatioMinusOne M m n ω x =
      Real.exp (cutoffShellSum m n x ω -
        (((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1 := by
  rw [cutoffRatioMinusOne, SubdiffusiveProcess.Frozen.Assumptions.aCutoff]
  by_cases hnneg : n < 0
  · have hnval : n = -1 := by omega
    simp only [aCutoffAtInt, hnneg, if_pos, div_one]
    rw [hnval] at hn hnm ⊢
    have hlog := cutoff_log_ratio_eq M m (-1) ω x hn hnm
    rw [if_pos (by omega)] at hlog
    exact congrArg (fun z : ℝ => Real.exp z - 1) (by linarith)
  · rw [aCutoffAtInt, if_neg hnneg, SubdiffusiveProcess.Frozen.Assumptions.aCutoff]
    rw [← Real.exp_sub]
    have hlog := cutoff_log_ratio_eq M m n ω x hn hnm
    rw [if_neg hnneg] at hlog
    exact congrArg (fun z : ℝ => Real.exp z - 1) hlog

/-- Exact shell representation of the inverse cutoff ratio. -/
theorem inverseCutoffRatioMinusOne_eq_exp_shell {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    inverseCutoffRatioMinusOne M m n ω x =
      Real.exp (-cutoffShellSum m n x ω +
        (((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1 := by
  rw [inverseCutoffRatioMinusOne, SubdiffusiveProcess.Frozen.Assumptions.aCutoff]
  by_cases hnneg : n < 0
  · have hnval : n = -1 := by omega
    simp only [aCutoffAtInt, hnneg, if_pos, one_div]
    rw [← Real.exp_neg]
    rw [hnval] at hnm ⊢
    have hlog := cutoff_log_ratio_eq M m (-1) ω x (by omega) hnm
    rw [if_pos (by omega)] at hlog
    exact congrArg (fun z : ℝ => Real.exp z - 1) (by linarith)
  · rw [aCutoffAtInt, if_neg hnneg, SubdiffusiveProcess.Frozen.Assumptions.aCutoff]
    rw [← Real.exp_sub]
    have hlog := cutoff_log_ratio_eq M m n ω x hn hnm
    rw [if_neg hnneg] at hlog
    exact congrArg (fun z : ℝ => Real.exp z - 1) (by linarith)

/-- The pushforward law of every shell evaluation is the zero-shell law at
the origin. -/
theorem map_potentialCoordinate_apply_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (x : Vec d) :
    Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k x) M.P.toMeasure =
      Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g 0)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
  let y : Vec d := (((3 : ℝ) ^ k)⁻¹) • x
  let evalX : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g x
  let evalY : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g y
  let eval0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g 0
  have hcoord := SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) k
  have hevalX := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x
  have hevalY := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval y
  have heval0 := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (0 : Vec d)
  calc
    Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k x) M.P.toMeasure =
        Measure.map evalX
          (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
      rw [SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw,
        ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map hevalX hcoord]
      rfl
    _ = Measure.map evalX
          (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by
      rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map]
    _ = Measure.map evalY
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [Measure.map_map hevalX
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)]
      congr 1
    _ = Measure.map eval0
          (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y)
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by
      rw [Measure.map_map heval0
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate y)]
      congr 1
      funext g
      simp [evalY]
    _ = Measure.map eval0
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [M.G1.stationary y]

/-- Assumption `(g2)` controls the absolute zero-shell value at the origin
with the same expectation-form `Gamma_2` scale. -/
theorem ogammaLE_abs_zeroPotential_at_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    SubdiffusiveProcess.OGammaLE
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure 2 M.delta
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => |g 0|) := by
  let E : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => |g 0|
  let ZE : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (E g) 0) ^ (2 : ℕ))
  let ZX : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (X g) 0) ^ (2 : ℕ))
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hzero_mem : (0 : Vec d) ∈ openCubeSet (originCube d 0) := by
    simp
  have hXE : ∀ g, X g ≤ E g := fun g =>
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.abs_apply_le_g2Observable g hzero_mem
  have hZXZE : ∀ g, ZX g ≤ ZE g := by
    intro g
    dsimp [ZX, ZE]
    apply Real.exp_le_exp.mpr
    have hmax : max (X g) 0 ≤ max (E g) 0 := max_le_max (hXE g) le_rfl
    have hmul : M.delta⁻¹ * max (X g) 0 ≤ M.delta⁻¹ * max (E g) 0 :=
      mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr hdelta.le)
    exact pow_le_pow_left₀
      (mul_nonneg (inv_nonneg.mpr hdelta.le) (le_max_right _ _)) hmul 2
  have hZEint : Integrable ZE
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    simpa [ZE, E, SubdiffusiveProcess.OGammaLE] using M.G2.regularity_expectation.1
  have hZXmeas : Measurable ZX := by
    dsimp [ZX, X]
    have habs : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => |g 0|) := by
      simpa only [Real.norm_eq_abs] using
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (0 : Vec d)).norm
    exact (measurable_const.mul (habs.max measurable_const)).pow_const 2 |>.exp
  have hZXint : Integrable ZX
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    refine hZEint.mono' hZXmeas.aestronglyMeasurable ?_
    filter_upwards with g
    calc
      ‖ZX g‖ = ZX g := Real.norm_of_nonneg (Real.exp_pos _).le
      _ ≤ ZE g := hZXZE g
  refine ⟨?_, ?_⟩
  · simpa [SubdiffusiveProcess.OGammaLE, ZX, X, Real.rpow_natCast] using hZXint
  · have hbound :
        ∫ g, ZX g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤ 2 := by
      calc
        ∫ g, ZX g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
          ∫ g, ZE g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
          integral_mono hZXint hZEint hZXZE
        _ ≤ 2 := by
          simpa [ZE, E, SubdiffusiveProcess.OGammaLE, Real.rpow_natCast] using
            M.G2.regularity_expectation.2
    simpa [ZX, X, Real.rpow_natCast] using hbound

/-- Every scaled shell evaluation inherits the same expectation-form
`Gamma_2` bound from `(g2)`, by marginal scaling and stationarity. -/
theorem ogammaLE_abs_potentialCoordinate_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (x : Vec d) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 M.delta
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => |omega k x|) := by
  let phi : ℝ → ℝ := fun z =>
    Real.exp ((M.delta⁻¹ * max |z| 0) ^ (2 : ℝ))
  let evalK : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega => omega k x
  let eval0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g 0
  have hphi : Measurable phi := by
    dsimp [phi]
    have habs : Measurable fun z : ℝ => |z| := by
      simpa only [Real.norm_eq_abs] using! measurable_id.norm
    exact (measurable_const.mul (habs.max measurable_const)).pow
      measurable_const |>.exp
  have hevalK : Measurable evalK :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) k)
  have heval0 : Measurable eval0 :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0
  have hmap : Measure.map evalK M.P.toMeasure =
      Measure.map eval0
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
    map_potentialCoordinate_apply_eq_zero M k x
  have hzero := ogammaLE_abs_zeroPotential_at_zero M
  have hzeroInt : Integrable (phi ∘ eval0)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    simpa [phi, eval0, Function.comp_def, SubdiffusiveProcess.OGammaLE] using hzero.1
  have hmapZeroInt : Integrable phi
      (Measure.map eval0
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) :=
    (integrable_map_measure hphi.aestronglyMeasurable heval0.aemeasurable).2 hzeroInt
  have hmapKInt : Integrable phi (Measure.map evalK M.P.toMeasure) := by
    rw [hmap]
    exact hmapZeroInt
  have hcompKInt : Integrable (phi ∘ evalK) M.P.toMeasure :=
    (integrable_map_measure hphi.aestronglyMeasurable hevalK.aemeasurable).1 hmapKInt
  refine ⟨?_, ?_⟩
  · simpa [phi, evalK, Function.comp_def, SubdiffusiveProcess.OGammaLE] using hcompKInt
  · calc
      ∫ omega, phi (evalK omega) ∂M.P.toMeasure =
          ∫ z, phi z ∂Measure.map evalK M.P.toMeasure := by
        exact (integral_map hevalK.aemeasurable hphi.aestronglyMeasurable).symm
      _ = ∫ z, phi z ∂Measure.map eval0
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by rw [hmap]
      _ = ∫ g, phi (eval0 g)
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
        exact integral_map heval0.aemeasurable hphi.aestronglyMeasurable
      _ ≤ 2 := by
        simpa [phi, eval0, SubdiffusiveProcess.OGammaLE] using hzero.2

/-- Fixed shell evaluations have symmetric `Gamma_2` tails at the scale
provided by `(g2)`. -/
theorem isBigO_gammaTwo_potentialCoordinate_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (x : Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k x)
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
  have h := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
    (μ := M.P.toMeasure) (σ := 2) (A := M.delta)
    (X := fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => |omega k x|)
    (by norm_num) M.shellPrefix.delta_pos (fun _ => abs_nonneg _)
    (ogammaLE_abs_potentialCoordinate_apply M k x)
  simpa [IsBigO] using h

/-- Negation symmetry `(g3)`, scaling, and stationarity center every shell
evaluation. -/
theorem integral_potentialCoordinate_apply_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (x : Vec d) :
    ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, omega k x ∂M.P.toMeasure = 0 := by
  let evalK : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega => omega k x
  let eval0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g 0
  let mu0 := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hevalK : Measurable evalK :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) k)
  have heval0 : Measurable eval0 :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0
  have hneg : Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0 = mu0 := by
    simpa [mu0] using congrArg ProbabilityMeasure.toMeasure M.G3.negation
  have hzero_neg : (∫ g, eval0 g ∂mu0) = ∫ g, -eval0 g ∂mu0 := by
    calc
      ∫ g, eval0 g ∂mu0 =
          ∫ g, eval0 g
            ∂Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0 := by
        rw [hneg]
      _ = ∫ g, eval0 (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate g) ∂mu0 := by
        exact integral_map
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_negate.aemeasurable
          heval0.aestronglyMeasurable
      _ = ∫ g, -eval0 g ∂mu0 := by
        apply integral_congr_ae
        filter_upwards with g
        simp [eval0]
  have hzero : ∫ g, eval0 g ∂mu0 = 0 := by
    rw [integral_neg] at hzero_neg
    linarith
  have hmap := map_potentialCoordinate_apply_eq_zero M k x
  calc
    ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, omega k x ∂M.P.toMeasure =
        ∫ z, z ∂Measure.map evalK M.P.toMeasure := by
      exact (integral_map hevalK.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ z, z ∂Measure.map eval0 mu0 := by rw [hmap]
    _ = ∫ g, eval0 g ∂mu0 := by
      exact integral_map heval0.aemeasurable measurable_id.aestronglyMeasurable
    _ = 0 := hzero

/-- The shell block between `n` and `m` has the central-limit `Gamma_2`
scale. -/
theorem isBigO_gammaTwo_cutoffShellSum {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) (x : Vec d)
    (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    IsBigO M.P.toMeasure (gammaSigma 2) (cutoffShellSum m n x)
      (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((cutoffShellIndices m n).card : ℝ) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
  let X : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun k omega => omega k x
  let s := cutoffShellIndices m n
  have hstart : (n + 1).toNat ≤ m := by
    omega
  have hs : s.Nonempty := by
    exact Finset.nonempty_Icc.mpr hstart
  have hIndep : iIndepFun X M.P.toMeasure := by
    simpa [X, Function.comp_def] using M.shellPrefix.independent.comp
      (fun _ g => g x)
      (fun _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x)
  have hMeas : ∀ k, Measurable (X k) := fun k =>
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) k)
  have hK : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
    exact mul_pos (Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos
  have hsum := Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := M.P.toMeasure) (X := X) (s := s) (σ := 2)
      (K := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)
      hIndep hMeas hs (by norm_num) (by norm_num) hK
      (fun k _ => isBigO_gammaTwo_potentialCoordinate_apply M k x)
      (fun k _ => integral_potentialCoordinate_apply_eq_zero M k x)
  simpa [cutoffShellSum, cutoffShellIndices, X, s] using! hsum

/-- Source-shaped central-limit scale for the shell sum. -/
theorem isBigO_gammaTwo_cutoffShellSum_sourceScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) (x : Vec d)
    (hn : -1 ≤ n) (hnm : n < (m : ℤ)) :
    IsBigO M.P.toMeasure (gammaSigma 2) (cutoffShellSum m n x)
      (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta) := by
  have hdiff : 0 ≤ (m : ℤ) - n := by omega
  have hcard := cutoffShellIndices_card m n hn hnm
  have hcast : ((cutoffShellIndices m n).card : ℝ) = ((m : ℤ) - n : ℤ) := by
    rw [hcard]
    exact_mod_cast Int.toNat_of_nonneg hdiff
  convert isBigO_gammaTwo_cutoffShellSum M m n x hn hnm using 1
  rw [hcast]
  unfold cutoffGammaConst
  ring

/-- The finite shell sum at one spatial point is measurable. -/
theorem measurable_cutoffShellSum {d : ℕ} (m : ℕ) (n : ℤ) (x : Vec d) :
    Measurable (cutoffShellSum (d := d) m n x) := by
  apply Finset.measurable_sum
  intro k _hk
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) k)

/-- Fixed-point moment estimate for the forward cutoff ratio, before the
universal constants are consolidated. -/
theorem integral_abs_cutoffRatioMinusOne_rpow_root_le_raw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (x : Vec d) (p : ℝ) (hp : 1 ≤ p) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => |cutoffRatioMinusOne M m n ω x| ^ p)
        M.P.toMeasure ∧
      (∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, |cutoffRatioMinusOne M m n ω x| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      2 * gammaMomentConst 2 * Real.sqrt (2 * p) *
        (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta +
          |(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) *
        Real.exp (p *
          (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta) ^ 2 +
          |(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := by
  let A := cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta
  let b := (((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hdiff : 0 < (((m : ℤ) - n : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hnm
  have hA : 0 < A := mul_pos (mul_pos cutoffGammaConst_pos
    (Real.sqrt_pos.mpr hdiff)) M.shellPrefix.delta_pos
  have h := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := cutoffShellSum m n x) (A := A) (p := p) (b := b)
    hA hp (measurable_cutoffShellSum m n x).aemeasurable
    (isBigO_gammaTwo_cutoffShellSum_sourceScale M m n x hn hnm)
  have heq : (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => |cutoffRatioMinusOne M m n ω x| ^ p) =
      fun ω => |Real.exp (cutoffShellSum m n x ω - b) - 1| ^ p := by
    funext ω
    rw [cutoffRatioMinusOne_eq_exp_shell M m n ω x hn hnm]
  rw [heq]
  simpa [A, b] using h

/-- Fixed-point moment estimate for the inverse cutoff ratio, before the
universal constants are consolidated. -/
theorem integral_abs_inverseCutoffRatioMinusOne_rpow_root_le_raw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (x : Vec d) (p : ℝ) (hp : 1 ≤ p) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    Integrable
        (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => |inverseCutoffRatioMinusOne M m n ω x| ^ p)
        M.P.toMeasure ∧
      (∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, |inverseCutoffRatioMinusOne M m n ω x| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      2 * gammaMomentConst 2 * Real.sqrt (2 * p) *
        (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta +
          |(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) *
        Real.exp (p *
          (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta) ^ 2 +
          |(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := by
  let A := cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta
  let b := -(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hdiff : 0 < (((m : ℤ) - n : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hnm
  have hA : 0 < A := mul_pos (mul_pos cutoffGammaConst_pos
    (Real.sqrt_pos.mpr hdiff)) M.shellPrefix.delta_pos
  have h := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := fun ω => -cutoffShellSum m n x ω)
    (A := A) (p := p) (b := b) hA hp
    (measurable_cutoffShellSum m n x).neg.aemeasurable
    (isBigO_gammaTwo_cutoffShellSum_sourceScale M m n x hn hnm).neg
  have heq :
      (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => |inverseCutoffRatioMinusOne M m n ω x| ^ p) =
        fun ω => |Real.exp (-cutoffShellSum m n x ω - b) - 1| ^ p := by
    funext ω
    rw [inverseCutoffRatioMinusOne_eq_exp_shell M m n ω x hn hnm]
    have hexponent : -cutoffShellSum m n x ω +
        (((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
        -cutoffShellSum m n x ω - b := by
      dsimp [b]
      ring
    rw [hexponent]
  rw [heq]
  simpa [A, b, abs_neg] using h

/-- Assumptions `(g2)` and `(g3)` give the sharp small-disorder exponential
moment bound at one point. -/
theorem integral_exp_zeroPotential_at_zero_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0)
        ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
      (2 : ℝ) ^ (M.delta ^ 2 / 2) := by
  let mu0 := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g 0
  let Z : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * |X g|) ^ (2 : ℕ))
  let r : ℝ := M.delta ^ 2 / 2
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    nlinarith [M.shellPrefix.delta_le_half, hdelta]
  have hZog := ogammaLE_abs_zeroPotential_at_zero M
  have hZint : Integrable Z mu0 := by
    simpa [Z, X, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left,
      Real.rpow_natCast] using hZog.1
  have hZle : ∫ g, Z g ∂mu0 ≤ 2 := by
    simpa [Z, X, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left,
      Real.rpow_natCast] using hZog.2
  have hZone : ∀ g, 1 ≤ Z g := by
    intro g
    exact Real.one_le_exp (sq_nonneg _)
  have hZr_le : ∀ g, Z g ^ r ≤ Z g := by
    intro g
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hZone g) hr1
  have hZr_meas : Measurable (fun g => Z g ^ r) := by
    have hZmeas : Measurable Z := by
      dsimp [Z, X]
      have habs : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => |g 0|) := by
        simpa only [Real.norm_eq_abs] using
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (0 : Vec d)).norm
      exact (measurable_const.mul habs).pow_const 2 |>.exp
    exact hZmeas.pow measurable_const
  have hZrint : Integrable (fun g => Z g ^ r) mu0 := by
    refine hZint.mono' hZr_meas.aestronglyMeasurable ?_
    filter_upwards with g
    calc
      ‖Z g ^ r‖ = Z g ^ r := Real.norm_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ ≤ Z g := hZr_le g
  have hJensen : ∫ g, Z g ^ r ∂mu0 ≤ (∫ g, Z g ∂mu0) ^ r := by
    exact (Real.concaveOn_rpow hr0 hr1).le_map_integral
      (Real.continuous_rpow_const hr0).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le)
      hZint hZrint
  have hIntZ_nonneg : 0 ≤ ∫ g, Z g ∂mu0 := integral_nonneg fun _ => (Real.exp_pos _).le
  have hJensenTwo : ∫ g, Z g ^ r ∂mu0 ≤ (2 : ℝ) ^ r := by
    exact hJensen.trans (Real.rpow_le_rpow hIntZ_nonneg hZle hr0)
  let expX : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (X g)
  let expNegX : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (-X g)
  have hexpXmeas : Measurable expX := by
    exact ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0).exp)
  have hexpXint : Integrable expX mu0 := by
    simpa [expX, X, mu0] using M.G4.exponential_integrable
  have hneg : Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0 = mu0 := by
    simpa [mu0] using congrArg ProbabilityMeasure.toMeasure M.G3.negation
  have hexpNegXint : Integrable expNegX mu0 := by
    have hmapInt : Integrable expX
        (Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0) := by
      rw [hneg]
      exact hexpXint
    have hcomp := (integrable_map_measure hexpXmeas.aestronglyMeasurable
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_negate.aemeasurable).1 hmapInt
    simpa [expX, expNegX, X, Function.comp_def] using hcomp
  have hexp_symm : ∫ g, expNegX g ∂mu0 = ∫ g, expX g ∂mu0 := by
    calc
      ∫ g, expNegX g ∂mu0 =
          ∫ g, expX (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate g) ∂mu0 := by
        apply integral_congr_ae
        filter_upwards with g
        simp [expNegX, expX, X]
      _ = ∫ z, expX z
          ∂Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0 := by
        exact (integral_map
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_negate.aemeasurable
          hexpXmeas.aestronglyMeasurable).symm
      _ = ∫ g, expX g ∂mu0 := by rw [hneg]
  have hcosh_int : Integrable (fun g => Real.cosh (X g)) mu0 := by
    have hadd := hexpXint.add hexpNegXint
    have hhalf := hadd.const_mul (2 : ℝ)⁻¹
    convert hhalf using 1
    funext g
    rw [Real.cosh_eq]
    dsimp [expX, expNegX]
    ring
  have hcosh_eq : ∫ g, Real.cosh (X g) ∂mu0 = ∫ g, expX g ∂mu0 := by
    calc
      ∫ g, Real.cosh (X g) ∂mu0 =
          (2 : ℝ)⁻¹ * (∫ g, expX g ∂mu0 + ∫ g, expNegX g ∂mu0) := by
        rw [← integral_add hexpXint hexpNegXint, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with g
        rw [Real.cosh_eq]
        simp [expX, expNegX, X]
        ring
      _ = ∫ g, expX g ∂mu0 := by rw [hexp_symm]; ring
  have hcosh_le : ∀ g, Real.cosh (X g) ≤ Z g ^ r := by
    intro g
    calc
      Real.cosh (X g) ≤ Real.exp ((X g) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = Z g ^ r := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        dsimp [Z, r]
        congr 1
        field_simp [hdelta.ne']
        rw [sq_abs]
  calc
    ∫ g, Real.exp (g 0) ∂mu0 = ∫ g, expX g ∂mu0 := by rfl
    _ = ∫ g, Real.cosh (X g) ∂mu0 := hcosh_eq.symm
    _ ≤ ∫ g, Z g ^ r ∂mu0 := integral_mono hcosh_int hZrint hcosh_le
    _ ≤ (2 : ℝ) ^ r := hJensenTwo

/-- The normalization exponent satisfies the source bound
`tauSq ≤ C delta²` with a universal constant. -/
theorem tauSq_le_delta_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (Real.log 2 / 2) * M.delta ^ 2 := by
  let I : ℝ := ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0)
    ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hIpos : 0 < I := by
    exact integral_exp_pos M.G4.exponential_integrable
  have hIle : I ≤ (2 : ℝ) ^ (M.delta ^ 2 / 2) := by
    exact integral_exp_zeroPotential_at_zero_le M
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  calc
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P = Real.log I := by
      rfl
    _ ≤ Real.log ((2 : ℝ) ^ (M.delta ^ 2 / 2)) :=
      Real.log_le_log hIpos hIle
    _ = (Real.log 2 / 2) * M.delta ^ 2 := by
      rw [Real.log_rpow htwo_pos]
      ring

/-- The raw fixed-point estimate is bounded by the paper's universal-constant
shape. -/
private theorem raw_cutoff_moment_bound_le_source {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (p : ℝ) (hp : 1 ≤ p) (hnm : n < (m : ℤ)) :
    2 * gammaMomentConst 2 * Real.sqrt (2 * p) *
        (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta +
          |(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) *
        Real.exp (p *
          (cutoffGammaConst * Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) * M.delta) ^ 2 +
          |(((m : ℤ) - n : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤
      cutoffMomentConst * Real.sqrt p * M.delta *
        Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
        Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
          (((m : ℤ) - n : ℤ) : ℝ)) := by
  let N : ℝ := (((m : ℤ) - n : ℤ) : ℝ)
  let R : ℝ := Real.sqrt N * M.delta
  let t : ℝ := Real.log 2 / 2
  let c : ℝ := cutoffGammaConst
  let G : ℝ := gammaMomentConst 2
  let C : ℝ := cutoffMomentConst
  let b : ℝ := N * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hN : 0 < N := by dsimp [N]; exact_mod_cast sub_pos.mpr hnm
  have hR : 0 < R := mul_pos (Real.sqrt_pos.mpr hN) M.shellPrefix.delta_pos
  have ht : 0 < t := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hc : 0 < c := cutoffGammaConst_pos
  have hG : 0 < G := gammaMomentConst_pos (by norm_num)
  have hC : 0 < C := cutoffMomentConst_pos
  have htau : 0 < SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := M.G4.tauSq_pos
  have hb0 : 0 ≤ b := mul_nonneg hN.le htau.le
  have hR2 : R ^ 2 = N * M.delta ^ 2 := by
    dsimp [R]
    rw [mul_pow, Real.sq_sqrt hN.le]
  have hb : b ≤ t * R ^ 2 := by
    dsimp [b, t]
    rw [hR2]
    calc
      N * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤
          N * ((Real.log 2 / 2) * M.delta ^ 2) :=
        mul_le_mul_of_nonneg_left (tauSq_le_delta_sq M) hN.le
      _ = (Real.log 2 / 2) * (N * M.delta ^ 2) := by ring
  have hRexp : R ≤ Real.exp (R ^ 2) := self_le_exp_sq hR.le
  have hexpone : 1 ≤ Real.exp (R ^ 2) := Real.one_le_exp (sq_nonneg R)
  have hlinear : c * R + b ≤
      (c + t) * R * Real.exp (R ^ 2) := by
    calc
      c * R + b ≤ c * R + t * R ^ 2 := add_le_add le_rfl hb
      _ = (c + t * R) * R := by ring
      _ ≤ (c + t * Real.exp (R ^ 2)) * R := by
        gcongr
      _ ≤ ((c + t) * Real.exp (R ^ 2)) * R := by
        gcongr
        nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hexpone)]
      _ = (c + t) * R * Real.exp (R ^ 2) := by ring
  have hsqrt : Real.sqrt (2 * p) = Real.sqrt 2 * Real.sqrt p := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hP : 2 * G * Real.sqrt 2 * (c + t) ≤ C := by
    dsimp [C, G, c, t, cutoffMomentConst]
    nlinarith [sq_nonneg cutoffGammaConst,
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have hE : R ^ 2 +
      (p * (c * R) ^ 2 + b) ≤ C * p * R ^ 2 := by
    have hcoef : 1 + c ^ 2 + t ≤ C := by
      dsimp [C, c, t, cutoffMomentConst]
      have hprod : 0 ≤ 2 * gammaMomentConst 2 * Real.sqrt 2 *
          (cutoffGammaConst + Real.log 2 / 2) := by positivity
      linarith
    calc
      R ^ 2 + (p * (c * R) ^ 2 + b) ≤
          R ^ 2 + (p * (c * R) ^ 2 + t * R ^ 2) := by linarith
      _ ≤ (1 + c ^ 2 + t) * p * R ^ 2 := by
        nlinarith [sq_nonneg R, sq_nonneg c,
          mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg R),
          mul_nonneg ht.le (mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg R))]
      _ ≤ C * p * R ^ 2 := by
        gcongr
  have hexp : Real.exp (R ^ 2) *
      Real.exp (p * (c * R) ^ 2 + b) ≤ Real.exp (C * p * R ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hE
  have hmain : 2 * G * Real.sqrt (2 * p) * (c * R + b) *
      Real.exp (p * (c * R) ^ 2 + b) ≤
      C * Real.sqrt p * R * Real.exp (C * p * R ^ 2) := by
    rw [hsqrt]
    calc
      2 * G * (Real.sqrt 2 * Real.sqrt p) * (c * R + b) *
          Real.exp (p * (c * R) ^ 2 + b) ≤
        2 * G * (Real.sqrt 2 * Real.sqrt p) *
            ((c + t) * R * Real.exp (R ^ 2)) *
              Real.exp (p * (c * R) ^ 2 + b) := by
        gcongr
      _ = (2 * G * Real.sqrt 2 * (c + t)) * Real.sqrt p * R *
          (Real.exp (R ^ 2) * Real.exp (p * (c * R) ^ 2 + b)) := by ring
      _ ≤ C * Real.sqrt p * R * Real.exp (C * p * R ^ 2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hP (Real.sqrt_nonneg p)) hR.le)
          hexp (by positivity) (by positivity)
  have habs : |(((m : ℤ) - n : ℤ) : ℝ) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P| = b := by
    dsimp [b, N] at hb0 ⊢
    exact abs_of_nonneg hb0
  rw [habs]
  have hNcast : 0 ≤ (((m : ℤ) - n : ℤ) : ℝ) := by
    exact_mod_cast (sub_pos.mpr hnm).le
  dsimp [N, R, t, c, G, C, b] at hmain ⊢
  simpa only [mul_pow,
    Real.sq_sqrt hNcast,
    mul_assoc, mul_left_comm, mul_comm] using hmain

/-- The forward fixed-point cutoff moment in the exact source shape. -/
theorem integral_abs_cutoffRatioMinusOne_rpow_root_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (x : Vec d) (p : ℝ) (hp : 1 ≤ p) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    (∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, |cutoffRatioMinusOne M m n ω x| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      cutoffMomentConst * Real.sqrt p * M.delta *
        Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
        Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
          (((m : ℤ) - n : ℤ) : ℝ)) :=
  (integral_abs_cutoffRatioMinusOne_rpow_root_le_raw M m n x p hp hn hnm).2.trans
    (raw_cutoff_moment_bound_le_source M m n p hp hnm)

/-- The inverse fixed-point cutoff moment in the exact source shape. -/
theorem integral_abs_inverseCutoffRatioMinusOne_rpow_root_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ)
    (x : Vec d) (p : ℝ) (hp : 1 ≤ p) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    (∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, |inverseCutoffRatioMinusOne M m n ω x| ^ p ∂M.P.toMeasure) ^ p⁻¹ ≤
      cutoffMomentConst * Real.sqrt p * M.delta *
        Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
        Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
          (((m : ℤ) - n : ℤ) : ℝ)) :=
  (integral_abs_inverseCutoffRatioMinusOne_rpow_root_le_raw
    M m n x p hp hn hnm).2.trans
    (raw_cutoff_moment_bound_le_source M m n p hp hnm)

/-- Tonelli packaging from uniform fixed-point `p`-moments to the paper's
normalized spatial `L^p` observable. -/
private theorem paperENNRealLpNorm_cutoffSpatialLpNorm_le
    {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (U : Ch02.Domain d)
    (F : Omega → Vec d → ℝ) (p B : ℝ) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hF : Measurable (Function.uncurry F))
    (hpoint : ∀ x, Integrable (fun ω => |F ω x| ^ p) mu ∧
      (∫ ω, |F ω x| ^ p ∂mu) ^ p⁻¹ ≤ B) :
    paperENNRealLpNorm mu p (fun ω => cutoffSpatialLpNorm U p (F ω)) ≤
      ENNReal.ofReal B := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let nu := domainNormalizedVolume U
  have hmoment : ∀ x, ∫ ω, |F ω x| ^ p ∂mu ≤ B ^ p := by
    intro x
    have hI0 : 0 ≤ ∫ ω, |F ω x| ^ p ∂mu :=
      integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    have h := Real.rpow_le_rpow
      (Real.rpow_nonneg hI0 p⁻¹) (hpoint x).2 hp0.le
    calc
      ∫ ω, |F ω x| ^ p ∂mu =
          ((∫ ω, |F ω x| ^ p ∂mu) ^ p⁻¹) ^ p := by
        rw [← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
      _ ≤ B ^ p := h
  have hinner : ∀ x,
      ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu =
        ENNReal.ofReal (∫ ω, |F ω x| ^ p ∂mu) := by
    intro x
    calc
      ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu =
          ∫⁻ ω, ENNReal.ofReal (|F ω x| ^ p) ∂mu := by
        apply lintegral_congr
        intro ω
        rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
        rw [← ofReal_norm_eq_enorm]
        simp only [Real.norm_eq_abs]
      _ = ENNReal.ofReal (∫ ω, |F ω x| ^ p ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal (hpoint x).1
          (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (abs_nonneg _) _)).symm
  have hinner_le : ∀ x, ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu ≤ ENNReal.ofReal (B ^ p) := by
    intro x
    rw [hinner x]
    exact ENNReal.ofReal_le_ofReal (hmoment x)
  have hmeas : Measurable (fun z : Omega × Vec d => ‖F z.1 z.2‖ₑ ^ p) := by
    exact hF.enorm.pow_const p
  have hdouble : ∫⁻ ω, ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu ∂mu ≤
      ENNReal.ofReal (B ^ p) := by
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc
      ∫⁻ x, ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu ∂nu ≤
          ∫⁻ _x, ENNReal.ofReal (B ^ p) ∂nu := lintegral_mono hinner_le
      _ = ENNReal.ofReal (B ^ p) := by simp [nu]
  have houter : paperENNRealLpNorm mu p
      (fun ω => cutoffSpatialLpNorm U p (F ω)) =
      (∫⁻ ω, ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu ∂mu) ^ p⁻¹ := by
    unfold paperENNRealLpNorm cutoffSpatialLpNorm
    congr 1
    apply lintegral_congr
    intro ω
    have hFω : AEStronglyMeasurable (F ω) (domainNormalizedVolume U) := by
      simpa only [Function.comp_def, Function.uncurry, id_eq] using!
        (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    change SubdiffusiveProcess.RawLp.eLpNorm (F ω) (ENNReal.ofReal p) (domainNormalizedVolume U) ^ p = _
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (p := ENNReal.ofReal p) (by positivity)
      ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hp0.le]
    rw [← ENNReal.rpow_mul]
    rw [one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  rw [houter]
  calc
    (∫⁻ ω, ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu ∂mu) ^ p⁻¹ ≤
        (ENNReal.ofReal (B ^ p)) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hdouble (inv_nonneg.mpr hp0.le)
    _ = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hB hp0.le]
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

/-- Joint measurability of the integer-indexed cutoff convention. -/
theorem measurable_aCutoffAtInt_uncurry {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℤ) :
    Measurable (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => aCutoffAtInt M n z.1 z.2) := by
  by_cases hn : n < 0
  · have heq : (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => aCutoffAtInt M n z.1 z.2) =
        fun _ => (1 : ℝ) := by
      funext z
      simp [aCutoffAtInt, hn]
    rw [heq]
    exact measurable_const
  · have heq : (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => aCutoffAtInt M n z.1 z.2) =
        fun z => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n.toNat z.1 z.2 := by
      funext z
      simp [aCutoffAtInt, hn]
    rw [heq]
    exact measurable_cutoff_uncurry M n.toNat

theorem measurable_cutoffRatioMinusOne_uncurry {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) :
    Measurable (Function.uncurry (cutoffRatioMinusOne M m n)) := by
  exact (measurable_cutoff_uncurry M m).div
    (measurable_aCutoffAtInt_uncurry M n) |>.sub measurable_const

theorem measurable_inverseCutoffRatioMinusOne_uncurry {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) :
    Measurable (Function.uncurry (inverseCutoffRatioMinusOne M m n)) := by
  exact (measurable_aCutoffAtInt_uncurry M n).div
    (measurable_cutoff_uncurry M m) |>.sub measurable_const

/-- `e.am.Lp.moments`: normalized spatial cutoff-ratio moments. -/
theorem cutoffRatio_spatialLp_moment {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (U : Ch02.Domain d)
    (m : ℕ) (n : ℤ) (p : ℝ) (hp : 1 ≤ p) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    paperENNRealLpNorm M.P.toMeasure p
        (fun ω => cutoffSpatialLpNorm U p (cutoffRatioMinusOne M m n ω)) ≤
      ENNReal.ofReal
        (cutoffMomentConst * Real.sqrt p * M.delta *
          Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
          Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
            (((m : ℤ) - n : ℤ) : ℝ))) := by
  let B := cutoffMomentConst * Real.sqrt p * M.delta *
    Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
    Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
      (((m : ℤ) - n : ℤ) : ℝ))
  have hdiff : 0 ≤ (((m : ℤ) - n : ℤ) : ℝ) := by
    exact_mod_cast (sub_pos.mpr hnm).le
  apply paperENNRealLpNorm_cutoffSpatialLpNorm_le
    M.P.toMeasure U (cutoffRatioMinusOne M m n) p B hp
    (by
      dsimp [B]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg p))
            M.shellPrefix.delta_pos.le)
          (Real.sqrt_nonneg _))
        (Real.exp_pos _).le)
    (measurable_cutoffRatioMinusOne_uncurry M m n)
  intro x
  exact ⟨(integral_abs_cutoffRatioMinusOne_rpow_root_le_raw
      M m n x p hp hn hnm).1,
    by simpa [B] using
      integral_abs_cutoffRatioMinusOne_rpow_root_le M m n x p hp hn hnm⟩

/-- `e.am.Lp.moments.inv`: normalized spatial inverse-cutoff moments. -/
theorem inverseCutoffRatio_spatialLp_moment {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (U : Ch02.Domain d)
    (m : ℕ) (n : ℤ) (p : ℝ) (hp : 1 ≤ p) (hn : -1 ≤ n)
    (hnm : n < (m : ℤ)) :
    paperENNRealLpNorm M.P.toMeasure p
        (fun ω => cutoffSpatialLpNorm U p (inverseCutoffRatioMinusOne M m n ω)) ≤
      ENNReal.ofReal
        (cutoffMomentConst * Real.sqrt p * M.delta *
          Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
          Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
            (((m : ℤ) - n : ℤ) : ℝ))) := by
  let B := cutoffMomentConst * Real.sqrt p * M.delta *
    Real.sqrt (((m : ℤ) - n : ℤ) : ℝ) *
    Real.exp (cutoffMomentConst * p * M.delta ^ 2 *
      (((m : ℤ) - n : ℤ) : ℝ))
  have hdiff : 0 ≤ (((m : ℤ) - n : ℤ) : ℝ) := by
    exact_mod_cast (sub_pos.mpr hnm).le
  apply paperENNRealLpNorm_cutoffSpatialLpNorm_le
    M.P.toMeasure U (inverseCutoffRatioMinusOne M m n) p B hp
    (by
      dsimp [B]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg p))
            M.shellPrefix.delta_pos.le)
          (Real.sqrt_nonneg _))
        (Real.exp_pos _).le)
    (measurable_inverseCutoffRatioMinusOne_uncurry M m n)
  intro x
  exact ⟨(integral_abs_inverseCutoffRatioMinusOne_rpow_root_le_raw
      M m n x p hp hn hnm).1,
    by simpa [B] using
      integral_abs_inverseCutoffRatioMinusOne_rpow_root_le M m n x p hp hn hnm⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab
