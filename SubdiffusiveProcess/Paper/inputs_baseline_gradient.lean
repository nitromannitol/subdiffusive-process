module

public import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.ExtendedSupremum
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness

@[expose] public section

open MeasureTheory
open Homogenization hiding Vec
open scoped ENNReal BigOperators
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem aux_inputs_baseline_gradient_translatedCube_subset_closedBall
    {d : ℕ} (k : ℤ) (z : Vec d) :
    translatedCube d k z ⊆ Metric.closedBall z
      (cubeRadius (originCube d k)) := by
  rintro x ⟨u, hu, rfl⟩
  have huball : u ∈ Metric.ball (cubeCenter (originCube d k))
      (cubeRadius (originCube d k)) := by
    rw [ball_cubeCenter_eq_openCubeSet]
    exact hu
  apply Metric.ball_subset_closedBall
  rw [Metric.mem_ball] at huball ⊢
  have hcenter : cubeCenter (originCube d k) = (0 : Vec d) := by
    ext i
    simp [cubeCenter, originCube]
  simpa [dist_eq_norm, hcenter] using huball

/-- The literal ENNReal cube supremum is the real vector supremum after
extending the latter to `ENNReal`. -/
private theorem aux_inputs_baseline_gradient_cube_sup
    {d : ℕ} (k : ℕ) (z : Vec d) (g : PotentialField d) :
    sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) z ∧
      u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient g x)|} =
      ENNReal.ofReal (vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient g)) := by
  let S : Set ℝ := {r : ℝ | ∃ x : Vec d,
    x ∈ translatedCube d (k : ℤ) z ∧
      r = Homogenization.euclideanNorm (shellGradient g x)}
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x, hx⟩ := SubdiffusiveProcess.CoarseGrainingVocab.translatedCube_nonempty
      (d := d) (k : ℤ) z
    exact ⟨Homogenization.euclideanNorm (shellGradient g x), x, hx, rfl⟩
  have hcont : Continuous
      (fun x : Vec d => Homogenization.euclideanNorm (shellGradient g x)) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.comp
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellGradient g)
  have hS_bdd : BddAbove S := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall z
      (cubeRadius (originCube d (k : ℤ)))).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨B, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hB' := hB x
      (aux_inputs_baseline_gradient_translatedCube_subset_closedBall
        (k := (k : ℤ)) z hx)
    have hnonneg : 0 ≤ Homogenization.euclideanNorm (shellGradient g x) :=
      Homogenization.euclideanNorm_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hB'
  have himage :
      {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) z ∧
        u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient g x)|} =
      ENNReal.ofReal '' S := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Homogenization.euclideanNorm (shellGradient g x), ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · rw [abs_of_nonneg (Homogenization.euclideanNorm_nonneg _)]
    · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by rw [abs_of_nonneg (Homogenization.euclideanNorm_nonneg _)]⟩
  rw [himage]
  unfold S vectorSupNormOn
  exact SubdiffusiveProcess.CoarseGrainingVocab.extended_sup_eq_of_bddAbove hS_nonempty hS_bdd

private theorem aux_inputs_baseline_gradient_summand_eq
    {d : ℕ} (k j : ℕ) (z : Vec d) (omega : PotentialSample d) :
    (if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) z ∧
        u = ENNReal.ofReal |Homogenization.euclideanNorm
          (shellGradient (omega j) x)|} else 0) =
    ENNReal.ofReal (if k ≤ j then (3 : ℝ) ^ k *
      vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega j)) else 0) := by
  by_cases hkj : k ≤ j
  · simp only [ite_eq_left hkj]
    rw [aux_inputs_baseline_gradient_cube_sup]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ k)]
  · simp [hkj]

private theorem aux_inputs_baseline_gradient_term_eq_of_summable
    {d : ℕ} (k : ℕ) (z : Vec d) (omega : PotentialSample d)
    (hsum : Summable (fun j : ℕ => if k ≤ j then
      (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega j)) else 0)) :
    (∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) z ∧
        u = ENNReal.ofReal |Homogenization.euclideanNorm
          (shellGradient (omega j) x)|} else 0) =
    ENNReal.ofReal (∑' j : ℕ, if k ≤ j then (3 : ℝ) ^ k *
      vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega j)) else 0) := by
  have hnonneg : ∀ j : ℕ, 0 ≤ if k ≤ j then
      (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega j)) else 0 := by
    intro j
    by_cases hkj : k ≤ j
    · simp only [ite_eq_left hkj]
      exact mul_nonneg (by positivity)
        (SubdiffusiveProcess.CoarseGrainingVocab.vectorSupNormOn_shellGradient_nonneg
          j k hkj z omega)
    · simp only [ite_eq_right hkj]
      exact le_rfl
  have hfun :
      (fun j : ℕ => if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
        sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) z ∧
          u = ENNReal.ofReal |Homogenization.euclideanNorm
            (shellGradient (omega j) x)|} else 0) =
      fun j => ENNReal.ofReal (if k ≤ j then (3 : ℝ) ^ k *
        vectorSupNormOn (translatedCube d (k : ℤ) z)
          (shellGradient (omega j)) else 0) := by
    funext j
    exact aux_inputs_baseline_gradient_summand_eq k j z omega
  rw [hfun, ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]

private theorem aux_inputs_baseline_gradient_suffix_nonneg
    {d : ℕ} (k : ℕ) (z : Vec d) (omega : PotentialSample d) :
    0 ≤ ∑' j : ℕ, if k ≤ j then (3 : ℝ) ^ k *
      vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega j)) else 0 := by
  apply tsum_nonneg
  intro j
  by_cases hkj : k ≤ j
  · simp only [ite_eq_left hkj]
    exact mul_nonneg (by positivity)
      (SubdiffusiveProcess.CoarseGrainingVocab.vectorSupNormOn_shellGradient_nonneg
        j k hkj z omega)
  · simp only [ite_eq_right hkj]
    exact le_rfl

/-- The gradient term of the literal four-term accumulated-error score. -/
theorem inputs_baseline_gradient (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ min 1 delta0 →
        ∀ (k : ℕ) (z : Vec d),
          let term : PotentialSample d → ENNReal := fun omega =>
            ∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
          else 0
          (∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞) ∧
          MemLp (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun omega => (term omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
  let C : ℝ := Homogenization.IndependentSums.gammaMomentConst 2 *
    Real.sqrt q * SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.holderErrorGradientEnvelopeCoeff d
  have _hs := hs
  have hCoeff : 0 <
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.holderErrorGradientEnvelopeCoeff d := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.holderErrorGradientEnvelopeCoeff
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have htri : 0 < Homogenization.IndependentSums.gammaTriangleConst 2 :=
      Homogenization.IndependentSums.gammaTriangleConst_pos
    have hlog : 0 < 1 + Real.log 2 := by
      have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_pos (mul_pos (mul_pos hdpos htri) (by norm_num))
      (Real.rpow_pos_of_pos hlog _)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num))
        (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hq))) hCoeff
  refine ⟨C, 1, hC, by norm_num, ?_⟩
  intro M hM k z
  let suffix : PotentialSample d → ℝ := fun omega =>
    ∑' j : ℕ, if k ≤ j then (3 : ℝ) ^ k *
      vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega j)) else 0
  let env : PotentialSample d → ℝ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelope k z
  have hδle1 : M.delta ≤ 1 := (le_min_iff.mp hM).1
  have hApos :
      0 < SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.gradientEnvelopeScale_eq_coeff_mul]
    exact mul_pos hCoeff M.shellPrefix.delta_pos
  have hEnvNonneg : ∀ omega, 0 ≤ env omega := by
    intro omega
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelope_nonneg
      k z omega
  have hEnvMeas : AEMeasurable env M.P.toMeasure := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.aemeasurable_accumulatedGradientEnvelope
      M k z
  have hEnvBig : Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) env
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M) := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.isBigOWith_gammaTwo_accumulatedGradientEnvelope
      M k z
  have hDom : ∀ᵐ omega ∂M.P.toMeasure, suffix omega ≤ env omega := by
    simpa [suffix, env] using
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ae_accumulatedGradientSuffix_le_envelope
        M k z
  have hSuffixNonneg : ∀ omega, 0 ≤ suffix omega := by
    intro omega
    exact aux_inputs_baseline_gradient_suffix_nonneg k z omega
  have hSuffixMeas : Measurable suffix := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_accumulatedErrorTailTerm
      k z
  have hSuffixBigWith : Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) suffix
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M) := by
    intro t ht
    have hsubset :
        Homogenization.IndependentSums.upperTailEvent suffix
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M * t) ≤ᵐ[M.P.toMeasure]
        Homogenization.IndependentSums.upperTailEvent env
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M * t) := by
      filter_upwards [hDom] with omega hω
      intro htail
      exact lt_of_lt_of_le htail hω
    have hmeas := measure_mono_ae hsubset
    have hreal :
        (M.P.toMeasure
          (Homogenization.IndependentSums.upperTailEvent suffix
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M * t))).toReal ≤
        (M.P.toMeasure
          (Homogenization.IndependentSums.upperTailEvent env
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M * t))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hmeas
    exact hreal.trans (hEnvBig ht)
  have hSuffixBig : Homogenization.Book.Ch04.IsBigO M.P.toMeasure
      (Homogenization.Book.Ch04.gammaSigma 2) suffix
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M) := by
    change Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) suffix
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M)
    rw [Homogenization.IndependentSums.IsBigO]
    have habs : (fun omega => |suffix omega|) = suffix := by
      funext omega
      exact abs_of_nonneg (hSuffixNonneg omega)
    rw [habs]
    exact hSuffixBigWith
  have hSuffixPow : Integrable (fun omega => suffix omega ^ q) M.P.toMeasure := by
    exact Homogenization.IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (μ := M.P.toMeasure) (Y := suffix)
      (K := SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M)
      (σ := 2) (p := q) (by norm_num) hApos hq hSuffixNonneg
      hSuffixMeas.aemeasurable hSuffixBigWith
  have hSuffixMem : MemLp suffix (ENNReal.ofReal q) M.P.toMeasure := by
    apply (integrable_norm_rpow_iff hSuffixMeas.aestronglyMeasurable
      (by positivity) ENNReal.ofReal_ne_top).1
    have hAbsPow : Integrable (fun omega => |suffix omega| ^ q) M.P.toMeasure := by
      convert hSuffixPow using 1
      funext omega
      rw [abs_of_nonneg (hSuffixNonneg omega)]
    simpa [ENNReal.toReal_ofReal (lt_of_lt_of_le zero_lt_one hq).le,
      Real.norm_eq_abs] using hAbsPow
  have hSuffixMoment := SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
    (mu := M.P.toMeasure) (X := suffix)
    (A := SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M)
    (p := q) hApos hq hSuffixMeas.aemeasurable hSuffixBig
  have hScaleEq :
      Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt q *
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M =
        C * M.delta := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.gradientEnvelopeScale_eq_coeff_mul]
    dsimp [C]
    ring
  have hδsqrt : M.delta ≤ M.delta ^ (1 / 2 : ℝ) := by
    have hδsq : M.delta ^ 2 ≤ M.delta := by
      have hprod := mul_nonneg M.shellPrefix.delta_pos.le (sub_nonneg.mpr hδle1)
      nlinarith [hprod]
    have hsqrt : M.delta ≤ Real.sqrt M.delta := by
      have hsqsqrt := Real.sq_sqrt (le_of_lt M.shellPrefix.delta_pos)
      have hsqrt0 := Real.sqrt_nonneg M.delta
      nlinarith
    simpa [Real.sqrt_eq_rpow] using hsqrt
  have hCδ : C * M.delta ≤ C * M.delta ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hδsqrt hC.le
  have hSuffixMoment' : eLpNorm suffix (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
    apply hSuffixMoment.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt q *
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.accumulatedGradientEnvelopeScale M =
        C * M.delta := hScaleEq
      _ ≤ C * M.delta ^ (1 / 2 : ℝ) := hCδ
  have hsumAE := SubdiffusiveProcess.CoarseGrainingVocab.ae_summable_translatedCube_gradient_tail M k z
  let term := fun omega : PotentialSample d =>
    ∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
    else 0
  have hTermReadout : ∀ᵐ omega ∂M.P.toMeasure,
      term omega = ENNReal.ofReal (suffix omega) := by
    filter_upwards [hsumAE] with omega hsum
    have h := aux_inputs_baseline_gradient_term_eq_of_summable k z omega hsum
    simpa [term, suffix] using h
  have hTermFinite : ∀ᵐ omega ∂M.P.toMeasure, term omega ≠ ∞ := by
    filter_upwards [hTermReadout] with omega hω
    rw [hω]
    exact ENNReal.ofReal_ne_top
  have hTermToReal : ∀ᵐ omega ∂M.P.toMeasure, (term omega).toReal = suffix omega := by
    filter_upwards [hTermReadout] with omega hω
    rw [hω, ENNReal.toReal_ofReal (hSuffixNonneg omega)]
  have hTermEq : suffix =ᵐ[M.P.toMeasure] (fun omega => (term omega).toReal) := by
    filter_upwards [hTermToReal] with omega hω
    exact hω.symm
  have hTermAEStrong : AEStronglyMeasurable
      (fun omega => (term omega).toReal) M.P.toMeasure :=
    hSuffixMeas.aestronglyMeasurable.congr hTermEq
  have hTermMem : MemLp (fun omega => (term omega).toReal)
      (ENNReal.ofReal q) M.P.toMeasure := by
    apply hSuffixMem.congr_norm hTermAEStrong
    filter_upwards [hTermToReal] with omega hω
    rw [hω]
  have hTermNorm : eLpNorm (fun omega => (term omega).toReal)
      (ENNReal.ofReal q) M.P.toMeasure ≤ eLpNorm suffix
        (ENNReal.ofReal q) M.P.toMeasure := by
    apply eLpNorm_mono_ae hTermAEStrong
    filter_upwards [hTermToReal] with omega hω
    rw [hω]
  refine ⟨hTermFinite, hTermMem, ?_⟩
  exact hTermNorm.trans hSuffixMoment'

end SubdiffusiveProcess.Paper

