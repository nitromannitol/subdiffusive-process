import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseMeasureTheory
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.InductionHypothesis
import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Bad-event estimates for the Section 4 recursion

The first definition is deliberately a byte-level transcription of the
conclusion of the still-draft large-cube response anchor.  Keeping that result
as a premise avoids importing a draft Section 4 theorem.

PROVENANCE: the Markov/Cauchy--Schwarz split mirrors
`Algsuperdiff/Section3/Provider/Homogenization/CombineBadEvent.lean`; here the
paper's printed Cauchy--Schwarz route is retained.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem neZero_of_gmcModel {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩

/-- Exact conclusion shape of
`SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes`, copied here as a
hypothesis carrier so this module does not import the draft anchor. -/
def MultiscaleResponseLargeCubesConclusion (d : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (L m0 : ℕ) (s delta1 xi : ℝ),
      0 < s → s ≤ 1 → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
      L ≤ m0 →
      4 * (d : ℝ) * s⁻¹ ≤ xi →
      xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
      inductionHypothesis M m0 xi delta1 →
      ∀ K : ℕ, L ≤ K → ∀ z : PaperCubeTranslate d, ∀ r : ℕ,
        (r = 1 ∨ r = 2) →
        paperENNRealLpNorm M.P.toMeasure xi
            (translatedHomogenizationErrorRandom M L K z s r) ≤
          ENNReal.ofReal
            (C * Real.rpow s (-(1 / (r : ℝ))) * Real.sqrt delta1)

/-- Markov in the exact `paperENNRealLpNorm` convention. -/
theorem measure_le_ratio_rpow_of_paperENNRealLpNorm
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {xi t A : ℝ} (hxi : 0 < xi) (ht : 0 < t)
    {X : Omega → ℝ≥0∞} (hX : Measurable X)
    (hnorm : paperENNRealLpNorm mu xi X ≤ ENNReal.ofReal A)
    {B : Set Omega} (hB : B ⊆ {omega | ENNReal.ofReal t ≤ X omega}) :
    mu B ≤ (ENNReal.ofReal A / ENNReal.ofReal t) ^ xi := by
  let I : ℝ≥0∞ := ∫⁻ omega, X omega ^ xi ∂mu
  have hroot : I ^ xi⁻¹ ≤ ENNReal.ofReal A := by
    simpa [paperENNRealLpNorm, I] using hnorm
  have hI : I ≤ (ENNReal.ofReal A) ^ xi := by
    calc
      I = (I ^ xi⁻¹) ^ xi := by
        rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hxi.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal A) ^ xi := ENNReal.rpow_le_rpow hroot hxi.le
  have ht0 : ENNReal.ofReal t ≠ 0 := by
    positivity
  have httop : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  have htail : mu {omega | ENNReal.ofReal t ≤ X omega} ≤
      I / (ENNReal.ofReal t) ^ xi := by
    have hpowMeas : AEMeasurable (fun omega => X omega ^ xi) mu :=
      (ENNReal.continuous_rpow_const.measurable.comp hX).aemeasurable
    have hmarkov := meas_ge_le_lintegral_div hpowMeas
      (show (ENNReal.ofReal t) ^ xi ≠ 0 by positivity)
      (ENNReal.rpow_ne_top_of_nonneg hxi.le httop)
    have hsets : {omega | (ENNReal.ofReal t) ^ xi ≤ X omega ^ xi} =
        {omega | ENNReal.ofReal t ≤ X omega} := by
      ext omega
      exact ENNReal.rpow_le_rpow_iff hxi
    simpa [I, hsets] using hmarkov
  calc
    mu B ≤ mu {omega | ENNReal.ofReal t ≤ X omega} := measure_mono hB
    _ ≤ I / (ENNReal.ofReal t) ^ xi := htail
    _ ≤ (ENNReal.ofReal A) ^ xi / (ENNReal.ofReal t) ^ xi :=
      ENNReal.div_le_div_right hI _
    _ = (ENNReal.ofReal A / ENNReal.ofReal t) ^ xi := by
      rw [ENNReal.div_rpow_of_nonneg _ _ hxi.le]

/-- The concrete `s = 1/4`, `r = 1`, threshold `1/5` Markov extraction used
in the printed bad-event step.  The measurable-error hypothesis is explicit:
the draft large-cube conclusion only bounds a lower integral and does not
itself assert measurability of its pointwise error carrier. -/
theorem badEvent_measure_le_of_multiscaleResponseLargeCubes
    {d : ℕ} (hLarge : MultiscaleResponseLargeCubesConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m0 m : ℕ)
        (delta1 xi : ℝ),
        M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 → L ≤ m →
        16 * (d : ℝ) ≤ xi →
        xi ≤ c * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 xi delta1 →
        ∀ B : Set (Sample d),
          Measurable (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) →
          B ⊆ {omega | ENNReal.ofReal (1 / 5 : ℝ) ≤
            translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega} →
          M.P.toMeasure B ≤
            (ENNReal.ofReal
              (C * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) *
                Real.sqrt delta1) / ENNReal.ofReal (1 / 5 : ℝ)) ^ xi := by
  rcases hLarge with ⟨c, C, hc, hC, hlarge⟩
  refine ⟨c, C, hc, hC, ?_⟩
  intro M L m0 m delta1 xi hdelta hdelta1 hLm0 hLm hxi hxic hS B hmeas hB
  have hscaleXi : 4 * (d : ℝ) * (1 / 4 : ℝ)⁻¹ ≤ xi := by
    convert hxi using 1
    norm_num
    ring
  have hnorm := hlarge M L m0 (1 / 4) delta1 xi (by norm_num) (by norm_num)
    hdelta hdelta1 hLm0 hscaleXi hxic hS m hLm 0 (1 : ℕ) (Or.inl rfl)
  have hdeltaNonneg : 0 ≤ delta1 := (sq_nonneg M.delta).trans hdelta
  have hdPos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  have hxiPos : 0 < xi := by nlinarith [hxi]
  have hraw := measure_le_ratio_rpow_of_paperENNRealLpNorm
    (mu := M.P.toMeasure) (xi := xi) (t := (1 / 5 : ℝ))
    (A := C * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) * Real.sqrt delta1)
    hxiPos (by norm_num)
    hmeas (by simpa using hnorm) hB
  exact hraw

/-- Real-valued manuscript form of
`badEvent_measure_le_of_multiscaleResponseLargeCubes`.  The dimensional
constant emitted by Markov is explicitly `400 * C²`. -/
theorem badEvent_probability_le_of_multiscaleResponseLargeCubes
    {d : ℕ} (hLarge : MultiscaleResponseLargeCubesConclusion d) :
    ∃ c CB : ℝ, 0 < c ∧ 0 < CB ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m0 m : ℕ)
        (delta1 xi : ℝ),
        M.delta ^ 2 ≤ delta1 → delta1 < 1 → L ≤ m0 → L ≤ m →
        16 * (d : ℝ) ≤ xi →
        xi ≤ c * (1 / 4 : ℝ) * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 xi delta1 →
        ∀ B : Set (Sample d),
          Measurable (translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1) →
          B ⊆ {omega | ENNReal.ofReal (1 / 5 : ℝ) ≤
            translatedHomogenizationErrorRandom M L m 0 (1 / 4) 1 omega} →
          M.P.toMeasure.real B ≤ Real.rpow (CB * delta1) (xi / 2) := by
  rcases badEvent_measure_le_of_multiscaleResponseLargeCubes hLarge with
    ⟨c, C, hc, hC, hmarkov⟩
  refine ⟨c, 400 * C ^ 2, hc, by positivity, ?_⟩
  intro M L m0 m delta1 xi hdelta hdelta1 hLm0 hLm hxi hxic hS B hmeas hB
  have hENN := hmarkov M L m0 m delta1 xi hdelta hdelta1 hLm0 hLm
    hxi hxic hS B hmeas hB
  have hdeltaNonneg : 0 ≤ delta1 := (sq_nonneg M.delta).trans hdelta
  let A : ℝ := C * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) *
    Real.sqrt delta1
  let R : ℝ≥0∞ := ENNReal.ofReal A / ENNReal.ofReal (1 / 5 : ℝ)
  have hRtop : R ^ xi ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by
      have hdPos : 0 < (d : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
      nlinarith [hxi])
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by positivity)
  have hreal : M.P.toMeasure.real B ≤ (R ^ xi).toReal := by
    rw [measureReal_def]
    exact ENNReal.toReal_mono hRtop (by simpa [R, A] using hENN)
  have hA : A = 4 * C * Real.sqrt delta1 := by
    calc
      A = C * 4 * Real.sqrt delta1 := by
        dsimp [A]
        rw [show -(1 / (1 : ℝ)) = (-1 : ℝ) by norm_num,
          Real.rpow_neg_one]
        norm_num
      _ = 4 * C * Real.sqrt delta1 := by ring
  have hR : R.toReal = 20 * C * Real.sqrt delta1 := by
    dsimp [R]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal]
    · rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 5), hA]
      norm_num
      ring
    · rw [hA]
      positivity
  have hbase : 0 ≤ 20 * C * Real.sqrt delta1 := by positivity
  have halgebra : Real.rpow (20 * C * Real.sqrt delta1) xi =
      Real.rpow ((400 * C ^ 2) * delta1) (xi / 2) := by
    calc
      Real.rpow (20 * C * Real.sqrt delta1) xi =
          Real.rpow (20 * C * Real.sqrt delta1) (2 * (xi / 2)) := by
        congr 1
        ring
      _ = Real.rpow ((20 * C * Real.sqrt delta1) ^ 2) (xi / 2) :=
        Real.rpow_mul hbase 2 (xi / 2)
      _ = Real.rpow ((400 * C ^ 2) * delta1) (xi / 2) := by
        rw [Real.rpow_two]
        congr 1
        calc
          (20 * C * Real.sqrt delta1) ^ 2 =
              400 * C ^ 2 * (Real.sqrt delta1) ^ 2 := by ring
          _ = 400 * C ^ 2 * delta1 := by rw [Real.sq_sqrt hdeltaNonneg]
  calc
    M.P.toMeasure.real B ≤ (R ^ xi).toReal := hreal
    _ = Real.rpow R.toReal xi := (ENNReal.toReal_rpow R xi).symm
    _ = Real.rpow (20 * C * Real.sqrt delta1) xi := by rw [hR]
    _ = Real.rpow ((400 * C ^ 2) * delta1) (xi / 2) := halgebra

/-- Cauchy--Schwarz for a nonnegative response restricted to a measurable
event, in the exact form used at manuscript lines 4710--4716. -/
theorem integral_indicator_le_sqrt_sq_mul_sqrt_measureReal
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {B : Set Omega} (hB : MeasurableSet B)
    {J : Omega → ℝ} (hJ : AEStronglyMeasurable J mu)
    (hJnonneg : 0 ≤ᵐ[mu] J) (hJsq : Integrable (fun omega => J omega ^ 2) mu) :
    ∫ omega in B, J omega ∂mu ≤
      Real.sqrt (∫ omega, J omega ^ 2 ∂mu) * Real.sqrt (mu.real B) := by
  let oneB : Omega → ℝ := B.indicator fun _ => 1
  have hJmem : MemLp J (ENNReal.ofReal 2) mu := by
    simpa only [ENNReal.ofReal_ofNat] using
      (memLp_two_iff_integrable_sq hJ).2 hJsq
  have hOneBmem : MemLp oneB (ENNReal.ofReal 2) mu := by
    exact (memLp_const (1 : ℝ)).indicator hB
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) (f := J) (g := oneB) Real.HolderConjugate.two_two
    hJnonneg (Filter.Eventually.of_forall fun omega => Set.indicator_nonneg
      (fun _ _ => zero_le_one) omega) hJmem hOneBmem
  have hleft : ∫ omega, J omega * oneB omega ∂mu = ∫ omega in B, J omega ∂mu := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards with omega
    by_cases homega : omega ∈ B <;> simp [oneB, homega]
  have hone : ∫ omega, oneB omega ^ (2 : ℝ) ∂mu = mu.real B := by
    calc
      ∫ omega, oneB omega ^ (2 : ℝ) ∂mu =
          ∫ omega in B, (1 : ℝ) ∂mu := by
        rw [← integral_indicator hB]
        apply integral_congr_ae
        filter_upwards with omega
        by_cases homega : omega ∈ B <;> simp [oneB, homega]
      _ = mu.real B := by simp
  rw [hleft, hone] at hcs
  simpa [Real.sqrt_eq_rpow] using hcs

/-- Scalar close of Steps 7--8.  If the response second moment is
`C² delta₁²` and the bad-event probability is at most
`(C_B delta₁)^(xi/2)`, then `xi ≥ 4` and `C_B delta₁ ≤ 1` give the
printed dimension-only constant times `delta₁²` contribution. -/
theorem badEvent_response_le_delta_sq
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {B : Set Omega} (hB : MeasurableSet B)
    {J : Omega → ℝ} (hJ : AEStronglyMeasurable J mu)
    (hJnonneg : 0 ≤ᵐ[mu] J) {C CB delta1 xi : ℝ}
    (hC : 0 ≤ C) (hCB : 0 ≤ CB) (hdelta : 0 ≤ delta1)
    (hxi : 4 ≤ xi) (hsmall : CB * delta1 ≤ 1)
    (hJsq : Integrable (fun omega => J omega ^ 2) mu)
    (hJsqBound : ∫ omega, J omega ^ 2 ∂mu ≤ C ^ 2 * delta1 ^ 2)
    (hprob : mu.real B ≤ Real.rpow (CB * delta1) (xi / 2)) :
    ∫ omega in B, J omega ∂mu ≤ C * CB * delta1 ^ 2 := by
  have hbase : 0 ≤ CB * delta1 := mul_nonneg hCB hdelta
  have hsqNonneg : 0 ≤ ∫ omega, J omega ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  have hcs := integral_indicator_le_sqrt_sq_mul_sqrt_measureReal
    hB hJ hJnonneg hJsq
  have hrootJ : Real.sqrt (∫ omega, J omega ^ 2 ∂mu) ≤ C * delta1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨mul_nonneg hC hdelta, by nlinarith⟩
  have hrootP : Real.sqrt (mu.real B) ≤ Real.rpow (CB * delta1) (xi / 4) := by
    have hprobNonneg : 0 ≤ mu.real B := measureReal_nonneg
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (mu.real B) (1 / 2 : ℝ) ≤
          Real.rpow (Real.rpow (CB * delta1) (xi / 2)) (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hprobNonneg hprob (by norm_num)
      _ = Real.rpow (CB * delta1) (xi / 4) := by
        calc
          Real.rpow (Real.rpow (CB * delta1) (xi / 2)) (1 / 2) =
              Real.rpow (CB * delta1) ((xi / 2) * (1 / 2)) :=
            (Real.rpow_mul hbase (xi / 2) (1 / 2)).symm
          _ = Real.rpow (CB * delta1) (xi / 4) := by
            congr 1
            ring
  have hpow : Real.rpow (CB * delta1) (xi / 4) ≤ CB * delta1 := by
    by_cases hzero : CB * delta1 = 0
    · rw [hzero]
      exact (Real.zero_rpow (by nlinarith : xi / 4 ≠ 0)).le
    · have hbasePos : 0 < CB * delta1 := lt_of_le_of_ne hbase (Ne.symm hzero)
      have hexp : 1 ≤ xi / 4 := by linarith
      calc
        Real.rpow (CB * delta1) (xi / 4) ≤
            Real.rpow (CB * delta1) 1 :=
          Real.rpow_le_rpow_of_exponent_ge hbasePos hsmall hexp
        _ = CB * delta1 := Real.rpow_one _
  calc
    ∫ omega in B, J omega ∂mu ≤
        Real.sqrt (∫ omega, J omega ^ 2 ∂mu) * Real.sqrt (mu.real B) := hcs
    _ ≤ (C * delta1) * Real.rpow (CB * delta1) (xi / 4) :=
      mul_le_mul hrootJ hrootP (Real.sqrt_nonneg _) (mul_nonneg hC hdelta)
    _ ≤ C * CB * delta1 ^ 2 := by
      calc
        (C * delta1) * Real.rpow (CB * delta1) (xi / 4) ≤
            (C * delta1) * (CB * delta1) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hdelta)
        _ = C * CB * delta1 ^ 2 := by ring

/-- Step 8 specialized to the measurable coarse-ellipticity bad event and the
actual cutoff response.  The second-moment budget and the Step-7 probability
estimate remain explicit, exactly at the payload boundary of the recursion. -/
theorem coarseEllipticityBadEvent_response_le_delta_sq
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (p q : Vec d) {C CB delta1 xi : ℝ}
    (hC : 0 ≤ C) (hCB : 0 ≤ CB) (hdelta : 0 ≤ delta1)
    (hxi : 4 ≤ xi) (hsmall : CB * delta1 ≤ 1)
    (hJsq : Integrable (fun omega : Sample d =>
      J (Ch02.cubeDomain (originCube d (m : ℤ)))
        (aCutoffCoeffOnData M L omega
          (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn p q ^ 2)
        M.P.toMeasure)
    (hJsqBound :
      ∫ omega : Sample d,
          J (Ch02.cubeDomain (originCube d (m : ℤ)))
            (aCutoffCoeffOnData M L omega
              (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn p q ^ 2
            ∂M.P.toMeasure ≤ C ^ 2 * delta1 ^ 2)
    (hprob : M.P.toMeasure.real
        (coarseEllipticityGoodEvent M L m)ᶜ ≤
      Real.rpow (CB * delta1) (xi / 2)) :
    ∫ omega : Sample d in (coarseEllipticityGoodEvent M L m)ᶜ,
        J (Ch02.cubeDomain (originCube d (m : ℤ)))
          (aCutoffCoeffOnData M L omega
            (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn p q
        ∂M.P.toMeasure ≤ C * CB * delta1 ^ 2 := by
  letI : NeZero d := neZero_of_gmcModel M
  apply badEvent_response_le_delta_sq
    (measurableSet_coarseEllipticityGoodEvent M L m).compl
    (measurable_cutoff_responseJ M L
      (Ch02.cubeDomain (originCube d (m : ℤ))) p q).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => Ch02.responseJ_nonneg _ _ _ _)
    hC hCB hdelta hxi hsmall hJsq hJsqBound hprob

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
