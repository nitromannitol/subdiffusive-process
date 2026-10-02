import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellGauge
import SubdiffusiveProcess.Frozen.Assumptions.G2Observable
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpMeanWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Convergence
import Mathlib.Topology.Algebra.InfiniteSum.Order
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.OGammaSummable
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SampleLawBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredGrowth
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.SharedStoppingFailures




set_option autoImplicit false
open Homogenization SubdiffusiveProcess.Frozen.Assumptions MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC (anchoredC11SampleLaw_preimage)
open SubdiffusiveProcess.CoarseGrainingVocab.OGamma (measureReal_ge_le_of_ogammaLE)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity (ogammaLE_mono_observable)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance (potentialField_deriv_translate)
open ProbabilityTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput (IsGridCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

variable {d : ℕ}

theorem smul_mem_openUnitCube {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) : r • x ∈ openCubeSet (originCube d 0) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hxi := hx i
  have hsm : (r • x) i = r * x i := rfl
  rw [hsm]
  constructor
  · nlinarith [hxi.1, hxi.2]
  · nlinarith [hxi.1, hxi.2]

/-- The gradient supremum on the unit cube scales by `r` under `x ↦ g (r x)`, for `0 < r ≤ 1`:
the rescaled cube sits inside the unit cube, and the chain rule contributes the factor `r`. -/
theorem unitCubeDerivNorm_spatialScale_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (g : PotentialField d) :
    PotentialField.unitCubeDerivNorm (PotentialField.spatialScale r g) ≤
      r * PotentialField.unitCubeDerivNorm g := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact mul_nonneg hr0.le (PotentialField.unitCubeDerivNorm_nonneg g)
  | some x =>
      have hmem : r • x.1 ∈ openCubeSet (originCube d 0) :=
        smul_mem_openUnitCube hr0 hr1 x.2
      have hchain : PotentialField.deriv (PotentialField.spatialScale r g) x.1 =
          r • PotentialField.deriv g (r • x.1) := deriv_spatialScale r g x.1
      show ‖PotentialField.deriv (PotentialField.spatialScale r g) x.1‖ ≤ _
      rw [hchain, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      exact mul_le_mul_of_nonneg_left
        (PotentialField.norm_deriv_le_unitCubeDerivNorm g hmem) hr0.le

/-- The gradient Lipschitz seminorm on the unit cube scales by `r ^ 2`: one factor from the
chain rule, one from the shortened distance. -/
theorem unitCubeDerivLipschitzSeminorm_spatialScale_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (g : PotentialField d) :
    PotentialField.unitCubeDerivLipschitzSeminorm (PotentialField.spatialScale r g) ≤
      r ^ 2 * PotentialField.unitCubeDerivLipschitzSeminorm g := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact mul_nonneg (by positivity)
        (PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g)
  | some p =>
      have hne : p.val.fst.val ≠ p.val.snd.val := fun hEq => p.property (Subtype.ext hEq)
      have hdist : 0 < dist p.val.fst.val p.val.snd.val := dist_pos.mpr hne
      have hmem1 : r • p.val.fst.val ∈ openCubeSet (originCube d 0) :=
        smul_mem_openUnitCube hr0 hr1 p.val.fst.2
      have hmem2 : r • p.val.snd.val ∈ openCubeSet (originCube d 0) :=
        smul_mem_openUnitCube hr0 hr1 p.val.snd.2
      have hlip := PotentialField.dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul g hmem1 hmem2
      have hsmulV : ∀ u v : Vec d, dist (r • u) (r • v) = r * dist u v := by
        intro u v
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0]
      have hsmulD : ∀ u v : Vec d →L[ℝ] ℝ, dist (r • u) (r • v) = r * dist u v := by
        intro u v
        rw [dist_eq_norm, dist_eq_norm, show r • u - r • v = r • (u - v) by
          rw [smul_sub], norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      have hsmul : dist (r • p.val.fst.val) (r • p.val.snd.val) =
          r * dist p.val.fst.val p.val.snd.val := hsmulV _ _
      show dist (PotentialField.deriv (PotentialField.spatialScale r g) p.val.fst.val)
          (PotentialField.deriv (PotentialField.spatialScale r g) p.val.snd.val) /
          dist p.val.fst.val p.val.snd.val ≤ _
      rw [deriv_spatialScale r g p.val.fst.val, deriv_spatialScale r g p.val.snd.val,
        hsmulD, div_le_iff₀ hdist]
      rw [hsmul] at hlip
      nlinarith [hlip, hdist, hr0,
        PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g]

/-! ### The triadic layers -/

/-- Layer `k` of the potential has the law of `g (3 ^ (-k) x)`, so its unit-cube gradient
supremum carries the factor `3 ^ (-k)`.  This is the source's `sum 3^{-k} <= 3/2`. -/
theorem unitCubeDerivNorm_triadicScale_le (k : ℕ) (g : PotentialField d) :
    PotentialField.unitCubeDerivNorm (PotentialField.triadicScale k g) ≤
      ((3 : ℝ) ^ k)⁻¹ * PotentialField.unitCubeDerivNorm g := by
  have h3 : (0:ℝ) < (3 : ℝ) ^ k := by positivity
  have h1 : (1:ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  exact unitCubeDerivNorm_spatialScale_le (inv_pos.mpr h3)
    ((inv_le_one₀ h3).mpr h1) g

/-- The gradient Lipschitz seminorm of layer `k` carries `3 ^ (-2k)`. -/
theorem unitCubeDerivLipschitzSeminorm_triadicScale_le (k : ℕ) (g : PotentialField d) :
    PotentialField.unitCubeDerivLipschitzSeminorm (PotentialField.triadicScale k g) ≤
      (((3 : ℝ) ^ k)⁻¹) ^ 2 * PotentialField.unitCubeDerivLipschitzSeminorm g := by
  have h3 : (0:ℝ) < (3 : ℝ) ^ k := by positivity
  have h1 : (1:ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  exact unitCubeDerivLipschitzSeminorm_spatialScale_le (inv_pos.mpr h3)
    ((inv_le_one₀ h3).mpr h1) g

theorem tsum_three_inv_pow : ∑' k : ℕ, ((3 : ℝ) ^ k)⁻¹ = 3 / 2 := by
  have h : ∑' k : ℕ, ((3 : ℝ)⁻¹) ^ k = (1 - (3 : ℝ)⁻¹)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  simp only [← inv_pow] at h ⊢
  rw [h]
  norm_num

/-! ### Change of variables along a pushforward -/

/-- Change of variables for `SubdiffusiveProcess.OGammaLE` along a pushforward between different spaces.
`OGammaSplit.ogammaLE_comp_measurePreserving` is the special case of an endomorphism of one
space; the layer transfer of assumption (g2) needs this form, because
`ShellLawPrefix.marginal_scaling` identifies the law of layer `k` as the pushforward of the
level-zero law along `PotentialField.triadicScale k`, and `ShellLawG1.stationary` identifies
the level-zero law as its own pushforward along `PotentialField.translate z`. -/
theorem ogammaLE_map_iff {Omega Omega' : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Omega'] {mu : Measure Omega} {T : Omega → Omega'} (hT : AEMeasurable T mu)
    {sigma A : ℝ} {X : Omega' → ℝ} (hX : AEMeasurable X (Measure.map T mu)) :
    SubdiffusiveProcess.OGammaLE (Measure.map T mu) sigma A X ↔
      SubdiffusiveProcess.OGammaLE mu sigma A (fun omega => X (T omega)) := by
  have hmeas : AEStronglyMeasurable
      (fun z => Real.exp ((A⁻¹ * max (X z) 0) ^ sigma)) (Measure.map T mu) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.aemeasurable_integrand sigma A hX).aestronglyMeasurable
  constructor
  · rintro ⟨hi, hb⟩
    exact ⟨(integrable_map_measure hmeas hT).mp hi, by rwa [← integral_map hT hmeas]⟩
  · rintro ⟨hi, hb⟩
    exact ⟨(integrable_map_measure hmeas hT).mpr hi, by rwa [integral_map hT hmeas]⟩

/-! ### A `Γ₂` observable squares to a `Γ₁` one -/

/-- `X ≤ O_{Γ₂}(A)` gives `X ^ 2 ≤ O_{Γ₁}(A ^ 2)` for a nonnegative `X`: the two Orlicz
integrands are literally the same function.  This is what turns the `Γ₂` gradient bound into
the `Γ₁` bound on `‖∇ log a‖ ^ 2` that the derivative display needs. -/
theorem ogammaLE_one_sq_of_ogammaLE_two {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A : ℝ} (hA : 0 < A) {X : Omega → ℝ} (hX : ∀ omega, 0 ≤ X omega)
    (h : SubdiffusiveProcess.OGammaLE mu 2 A X) :
    SubdiffusiveProcess.OGammaLE mu 1 (A ^ 2) (fun omega => X omega ^ 2) := by
  have hfun : (fun omega => Real.exp ((((A ^ 2)⁻¹ * max (X omega ^ 2) 0)) ^ (1:ℝ)))
      = fun omega => Real.exp ((A⁻¹ * max (X omega) 0) ^ (2:ℝ)) := by
    funext omega
    rw [Real.rpow_one, max_eq_left (by positivity), max_eq_left (hX omega),
      show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 1
    field_simp
  obtain ⟨hint, hbd⟩ := h
  refine ⟨?_, ?_⟩
  · show Integrable (fun omega => Real.exp ((((A ^ 2)⁻¹ * max (X omega ^ 2) 0)) ^ (1:ℝ))) mu
    rw [hfun]; exact hint
  · show ∫ omega, Real.exp ((((A ^ 2)⁻¹ * max (X omega ^ 2) 0)) ^ (1:ℝ)) ∂mu ≤ 2
    rw [hfun]; exact hbd

/-! ### Link 1: the layer bound at a translated site -/

/-- The translated layer observable, with the layer factor `3 ^ (-k)` extracted and the
translation pulled back to the layer's own scale. -/
theorem unitCubeDerivNorm_translate_triadicScale_le (k : ℕ) (y : Vec d)
    (g : PotentialField d) :
    PotentialField.unitCubeDerivNorm
        (PotentialField.translate y (PotentialField.triadicScale k g)) ≤
      ((3:ℝ) ^ k)⁻¹ * PotentialField.unitCubeDerivNorm
        (PotentialField.translate (((3:ℝ) ^ k)⁻¹ • y) g) := by
  have h3 : (0:ℝ) < (3:ℝ) ^ k := by positivity
  have h1 : (1:ℝ) ≤ (3:ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hr0 : (0:ℝ) < ((3:ℝ) ^ k)⁻¹ := inv_pos.mpr h3
  have hr1 : ((3:ℝ) ^ k)⁻¹ ≤ 1 := (inv_le_one₀ h3).mpr h1
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact mul_nonneg hr0.le (PotentialField.unitCubeDerivNorm_nonneg _)
  | some x =>
      have hmem : ((3:ℝ) ^ k)⁻¹ • x.1 ∈ openCubeSet (originCube d 0) :=
        smul_mem_openUnitCube hr0 hr1 x.2
      show ‖PotentialField.deriv
        (PotentialField.translate y (PotentialField.triadicScale k g)) x.1‖ ≤ _
      rw [potentialField_deriv_translate, PotentialField.triadicScale,
        deriv_spatialScale, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, smul_add,
        ← potentialField_deriv_translate]
      exact mul_le_mul_of_nonneg_left
        (PotentialField.norm_deriv_le_unitCubeDerivNorm _ hmem) hr0.le

/-- **Link 1: the layer bound at a translated site.**  Assumption (g2) on the level-zero law,
carried to layer `k` at the unit cube around `y` by `ShellLawPrefix.marginal_scaling`,
`ShellLawG1.stationary` and the layer scaling. -/
theorem ogammaLE_unitCubeDerivNorm_layer (M : GMCModel d) (k : ℕ) (y : Vec d) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (((3:ℝ) ^ k)⁻¹ * M.delta)
      (fun omega : PotentialSample d =>
        PotentialField.unitCubeDerivNorm (PotentialField.translate y (omega k))) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have h3 : (0:ℝ) < (3:ℝ) ^ k := by positivity
  have hr0 : (0:ℝ) < ((3:ℝ) ^ k)⁻¹ := inv_pos.mpr h3
  set r : ℝ := ((3:ℝ) ^ k)⁻¹ with hrdef
  -- (g2) on the level-zero law, restricted to the gradient observable
  have hDN : SubdiffusiveProcess.OGammaLE (zeroPotentialLaw M.P).toMeasure 2 M.delta
      PotentialField.unitCubeDerivNorm :=
    ogammaLE_mono_observable two_pos hdelta PotentialField.unitCubeDerivNorm_measurable
      (Filter.Eventually.of_forall fun g => PotentialField.unitCubeDerivNorm_le_g2Observable g)
      M.G2.regularity_expectation
  -- stationarity moves the unit cube to the layer's own translate
  have hTrans : SubdiffusiveProcess.OGammaLE (zeroPotentialLaw M.P).toMeasure 2 M.delta
      (fun g => PotentialField.unitCubeDerivNorm (PotentialField.translate (r • y) g)) := by
    refine SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_comp_measurePreserving
      ⟨PotentialField.measurable_translate (r • y), M.G1.stationary (r • y)⟩
      PotentialField.unitCubeDerivNorm_measurable.aemeasurable hDN
  -- the layer factor
  have hScaled : SubdiffusiveProcess.OGammaLE (zeroPotentialLaw M.P).toMeasure 2 (r * M.delta)
      (fun g => PotentialField.unitCubeDerivNorm
        (PotentialField.translate y (PotentialField.triadicScale k g))) := by
    refine ogammaLE_mono_observable two_pos (by positivity)
      ((PotentialField.unitCubeDerivNorm_measurable.comp
        (PotentialField.measurable_translate y)).comp
        (PotentialField.measurable_triadicScale k))
      (Filter.Eventually.of_forall fun g =>
        unitCubeDerivNorm_translate_triadicScale_le k y g)
      (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_const_mul hdelta hr0 hTrans)
  -- push forward along the layer scaling, then along the coordinate map
  have hmapScale : (potentialMarginalLaw M.P k).toMeasure =
      Measure.map (PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure := by
    rw [M.shellPrefix.marginal_scaling k,
      ProbabilityMeasure.toMeasure_map _ (PotentialField.measurable_triadicScale k).aemeasurable]
  have hmapCoord : Measure.map (fun omega : PotentialSample d => omega k) M.P.toMeasure =
      (potentialMarginalLaw M.P k).toMeasure := by
    rw [potentialMarginalLaw,
      ProbabilityMeasure.toMeasure_map _ (measurable_potentialCoordinate k).aemeasurable]
  have hmid : SubdiffusiveProcess.OGammaLE (potentialMarginalLaw M.P k).toMeasure 2 (r * M.delta)
      (fun g => PotentialField.unitCubeDerivNorm (PotentialField.translate y g)) := by
    rw [hmapScale]
    refine (ogammaLE_map_iff (PotentialField.measurable_triadicScale k).aemeasurable ?_).mpr
      hScaled
    rw [← hmapScale]
    exact (PotentialField.unitCubeDerivNorm_measurable.comp
      (PotentialField.measurable_translate y)).aemeasurable
  refine (ogammaLE_map_iff (T := fun omega : PotentialSample d => omega k)
    (X := fun g => PotentialField.unitCubeDerivNorm (PotentialField.translate y g))
    (measurable_potentialCoordinate k).aemeasurable ?_).mp ?_
  · rw [hmapCoord]
    exact (PotentialField.unitCubeDerivNorm_measurable.comp
      (PotentialField.measurable_translate y)).aemeasurable
  · rw [hmapCoord]; exact hmid

/-! ### Link 3: the layer bounds pass to the anchored limit -/

/-- **Link 3 (gradient): the layer bounds pass to the anchored limit.** -/
theorem norm_deriv_anchoredLog_le {omega : AnchoredC11Sample d} {G : ℕ → ℝ} {x : Vec d}
    (hG : ∀ k, ‖PotentialField.deriv (omega.val k) x‖ ≤ G k) (hsum : Summable G) :
    ‖PotentialField.deriv (anchoredLog omega) x‖ ≤ ∑' k, G k := by
  have hG0 : ∀ k, 0 ≤ G k := fun k => le_trans (norm_nonneg _) (hG k)
  have hlim := ((anchoredLog_spec omega).deriv_tendsto {x} isCompact_singleton).tendsto_at
    (Set.mem_singleton x)
  have hbd : ∀ L : ℕ,
      ‖PotentialField.deriv (anchoredPartialSumField omega.val L) x‖ ≤ ∑' k, G k := by
    intro L
    rw [deriv_anchoredPartialSumField]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hG k) ?_
    exact hsum.sum_le_tsum _ fun k _ => hG0 k
  exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hbd)

/-- **Link 3 (Lipschitz seminorm): the layer bounds pass to the anchored limit.** -/
theorem norm_deriv_sub_deriv_anchoredLog_le {omega : AnchoredC11Sample d} {K : ℕ → ℝ}
    {x y : Vec d} (hK0 : ∀ k, 0 ≤ K k)
    (hK : ∀ k, ‖PotentialField.deriv (omega.val k) x -
      PotentialField.deriv (omega.val k) y‖ ≤ K k * ‖x - y‖)
    (hsum : Summable K) :
    ‖PotentialField.deriv (anchoredLog omega) x -
        PotentialField.deriv (anchoredLog omega) y‖ ≤ (∑' k, K k) * ‖x - y‖ := by
  have hlimx := ((anchoredLog_spec omega).deriv_tendsto {x} isCompact_singleton).tendsto_at
    (Set.mem_singleton x)
  have hlimy := ((anchoredLog_spec omega).deriv_tendsto {y} isCompact_singleton).tendsto_at
    (Set.mem_singleton y)
  have hbd : ∀ L : ℕ,
      ‖PotentialField.deriv (anchoredPartialSumField omega.val L) x -
        PotentialField.deriv (anchoredPartialSumField omega.val L) y‖ ≤
        (∑' k, K k) * ‖x - y‖ := by
    intro L
    rw [deriv_anchoredPartialSumField, deriv_anchoredPartialSumField, ← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun k _ => hK k) ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hsum.sum_le_tsum _ fun k _ => hK0 k) (norm_nonneg _)
  exact le_of_tendsto (hlimx.sub hlimy).norm (Filter.Eventually.of_forall hbd)

/-! ### Link 4: the layer sums, and the tail of the anchored unit-cube gradient -/

/-- The translated layer Lipschitz seminorm, with the layer factor `3 ^ (-2k)` extracted. -/
theorem unitCubeDerivLipschitzSeminorm_translate_triadicScale_le (k : ℕ) (y : Vec d)
    (g : PotentialField d) :
    PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y (PotentialField.triadicScale k g)) ≤
      (((3:ℝ) ^ k)⁻¹) ^ 2 * PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate (((3:ℝ) ^ k)⁻¹ • y) g) := by
  have h3 : (0:ℝ) < (3:ℝ) ^ k := by positivity
  have h1 : (1:ℝ) ≤ (3:ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hr0 : (0:ℝ) < ((3:ℝ) ^ k)⁻¹ := inv_pos.mpr h3
  have hr1 : ((3:ℝ) ^ k)⁻¹ ≤ 1 := (inv_le_one₀ h3).mpr h1
  set r : ℝ := ((3:ℝ) ^ k)⁻¹ with hrdef
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact mul_nonneg (by positivity)
        (PotentialField.unitCubeDerivLipschitzSeminorm_nonneg _)
  | some p =>
      have hne : p.val.fst.val ≠ p.val.snd.val := fun hEq => p.property (Subtype.ext hEq)
      have hdist : 0 < dist p.val.fst.val p.val.snd.val := dist_pos.mpr hne
      have hmem1 : r • p.val.fst.val ∈ openCubeSet (originCube d 0) :=
        smul_mem_openUnitCube hr0 hr1 p.val.fst.2
      have hmem2 : r • p.val.snd.val ∈ openCubeSet (originCube d 0) :=
        smul_mem_openUnitCube hr0 hr1 p.val.snd.2
      have hlip := PotentialField.dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul
        (PotentialField.translate (r • y) g) hmem1 hmem2
      have hsmulV : ∀ u v : Vec d, dist (r • u) (r • v) = r * dist u v := by
        intro u v
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0]
      have hsmulD : ∀ u v : Vec d →L[ℝ] ℝ, dist (r • u) (r • v) = r * dist u v := by
        intro u v
        rw [dist_eq_norm, dist_eq_norm, show r • u - r • v = r • (u - v) by
          rw [smul_sub], norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      rw [hsmulV] at hlip
      show dist (PotentialField.deriv
          (PotentialField.translate y (PotentialField.triadicScale k g)) p.val.fst.val)
          (PotentialField.deriv
          (PotentialField.translate y (PotentialField.triadicScale k g)) p.val.snd.val) /
          dist p.val.fst.val p.val.snd.val ≤ _
      rw [potentialField_deriv_translate, potentialField_deriv_translate,
        PotentialField.triadicScale, deriv_spatialScale, deriv_spatialScale,
        smul_add, smul_add, ← potentialField_deriv_translate, ← potentialField_deriv_translate,
        hsmulD, div_le_iff₀ hdist]
      nlinarith [hlip, hdist, hr0,
        PotentialField.unitCubeDerivLipschitzSeminorm_nonneg
          (PotentialField.translate (r • y) g)]

/-- The partial layer sum of unit-cube gradient observables at a site. -/
def layerDerivSum (y : Vec d) (L : ℕ) (omega : PotentialSample d) : ℝ :=
  ∑ k ∈ Finset.range (L + 1),
    PotentialField.unitCubeDerivNorm (PotentialField.translate y (omega k))

theorem layerDerivSum_nonneg (y : Vec d) (L : ℕ) (omega : PotentialSample d) :
    0 ≤ layerDerivSum y L omega :=
  Finset.sum_nonneg fun _ _ => PotentialField.unitCubeDerivNorm_nonneg _

theorem layerDerivSum_mono (y : Vec d) {L L' : ℕ} (hL : L ≤ L') (omega : PotentialSample d) :
    layerDerivSum y L omega ≤ layerDerivSum y L' omega := by
  have hsub : Finset.range (L + 1) ⊆ Finset.range (L' + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro k _ _
  exact PotentialField.unitCubeDerivNorm_nonneg _

theorem measurable_layerDerivSum (y : Vec d) (L : ℕ) :
    Measurable (layerDerivSum (d := d) y L) :=
  Finset.measurable_sum _ fun k _ =>
    (PotentialField.unitCubeDerivNorm_measurable.comp
      (PotentialField.measurable_translate y)).comp (measurable_potentialCoordinate k)

theorem summable_three_inv_pow : Summable (fun k : ℕ => ((3:ℝ) ^ k)⁻¹) := by
  simp only [← inv_pow]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem sum_three_inv_pow_le (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), ((3:ℝ) ^ k)⁻¹ ≤ 3 / 2 := by
  rw [← tsum_three_inv_pow]
  exact summable_three_inv_pow.sum_le_tsum _ fun k _ => by positivity

/-- **Every partial layer sum is `O_{Γ₂}((3/2) δ)`**, uniformly in `L`. -/
theorem ogammaLE_layerDerivSum (M : GMCModel d) (y : Vec d) (L : ℕ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (3 / 2 * M.delta) (layerDerivSum y L) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hne : (Finset.range (L + 1)).Nonempty := Finset.nonempty_range_add_one
  have hA : ∀ k : ℕ, (0:ℝ) < ((3:ℝ) ^ k)⁻¹ * M.delta := by
    intro k; positivity
  have hbase := ogammaLE_two_finset_sum (mu := M.P.toMeasure)
    (X := fun k omega => PotentialField.unitCubeDerivNorm
      (PotentialField.translate y (omega k)))
    (A := fun k => ((3:ℝ) ^ k)⁻¹ * M.delta) hA
    (fun k => ((PotentialField.unitCubeDerivNorm_measurable.comp
      (PotentialField.measurable_translate y)).comp
      (measurable_potentialCoordinate k)).aemeasurable)
    (fun k omega => PotentialField.unitCubeDerivNorm_nonneg _)
    (fun k => ogammaLE_unitCubeDerivNorm_layer M k y) hne
  refine SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ogammaLE_mono_scale'
    two_pos (Finset.sum_pos (fun k _ => hA k) hne) ?_ hbase
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_three_inv_pow_le L) hdelta.le

/-- The partial-sum field's unit-cube gradient is bounded by the layer sum. -/
theorem unitCubeDerivNorm_translate_anchoredPartialSum_le (omega : PotentialSample d)
    (y : Vec d) (L : ℕ) :
    PotentialField.unitCubeDerivNorm
        (PotentialField.translate y (anchoredPartialSumField omega L)) ≤
      ∑ k ∈ Finset.range (L + 1),
        PotentialField.unitCubeDerivNorm (PotentialField.translate y (omega k)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact Finset.sum_nonneg fun k _ => PotentialField.unitCubeDerivNorm_nonneg _
  | some x =>
      show ‖PotentialField.deriv
        (PotentialField.translate y (anchoredPartialSumField omega L)) x.1‖ ≤ _
      rw [potentialField_deriv_translate, deriv_anchoredPartialSumField]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [← potentialField_deriv_translate]
      exact PotentialField.norm_deriv_le_unitCubeDerivNorm _ x.2

/-- A uniform bound on the partial sums passes to the anchored limit. -/
theorem unitCubeDerivNorm_translate_anchoredLog_le (omega : AnchoredC11Sample d)
    (y : Vec d) {c : ℝ}
    (hc : ∀ L : ℕ, PotentialField.unitCubeDerivNorm
      (PotentialField.translate y (anchoredPartialSumField omega.val L)) ≤ c) :
    PotentialField.unitCubeDerivNorm
        (PotentialField.translate y (anchoredLog omega)) ≤ c := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact le_trans (PotentialField.unitCubeDerivNorm_nonneg _) (hc 0)
  | some x =>
      have hlim := ((anchoredLog_spec omega).deriv_tendsto {x.1 + y}
        isCompact_singleton).tendsto_at (Set.mem_singleton _)
      show ‖PotentialField.deriv (PotentialField.translate y (anchoredLog omega)) x.1‖ ≤ c
      rw [potentialField_deriv_translate]
      refine le_of_tendsto hlim.norm (Filter.Eventually.of_forall fun L => ?_)
      rw [← potentialField_deriv_translate]
      exact le_trans (PotentialField.norm_deriv_le_unitCubeDerivNorm _ x.2) (hc L)

/-! ### The tail of the anchored unit-cube gradient at a site -/

/-- **The unit-cube gradient of the anchored log has a Gaussian tail at scale `(3/2) δ`.**
No summability of the layer observables is needed: the partial sums are increasing, so the
event that the limit exceeds `c` is the increasing union of the events that some partial sum
does, and each of those is controlled by `ogammaLE_layerDerivSum` and Markov. -/
theorem measureReal_unitCubeDerivNorm_anchoredLog_gt (M : GMCModel d) (y : Vec d) {c : ℝ}
    (hc : 0 ≤ c) :
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
        {s : AnchoredC11Sample d | c < PotentialField.unitCubeDerivNorm
          (PotentialField.translate y (anchoredLog s))} ≤
      2 * Real.exp (-(((3 / 2 * M.delta)⁻¹ * c) ^ (2:ℝ))) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : (0:ℝ) < 3 / 2 * M.delta := by positivity
  set B : ℝ := 2 * Real.exp (-(((3 / 2 * M.delta)⁻¹ * c) ^ (2:ℝ))) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set E : ℕ → Set (PotentialSample d) :=
    fun L => {omega | c < layerDerivSum y L omega} with hEdef
  have hEmono : Monotone E := by
    intro L L' hL omega homega
    exact lt_of_lt_of_le homega (layerDerivSum_mono y hL omega)
  have hEmeas : ∀ L, MeasurableSet (E L) := fun L =>
    measurableSet_lt measurable_const (measurable_layerDerivSum y L)
  -- each level, by Markov
  have hEbound : ∀ L, M.P.toMeasure (E L) ≤ ENNReal.ofReal B := by
    intro L
    have hmark := measureReal_ge_le_of_ogammaLE (ogammaLE_layerDerivSum M y L) hA
      (by norm_num) hc
    have hsub : E L ⊆ {omega | c ≤ layerDerivSum y L omega} := by
      intro omega homega
      have h' : c < layerDerivSum y L omega := homega
      exact le_of_lt h' 
    have hle : M.P.toMeasure.real (E L) ≤ B :=
      le_trans (measureReal_mono hsub (measure_ne_top _ _)) hmark
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB0).mpr hle
  -- the increasing union
  have hunion : M.P.toMeasure (⋃ L, E L) ≤ ENNReal.ofReal B := by
    rw [hEmono.measure_iUnion]
    exact iSup_le hEbound
  -- the anchored event sits inside the preimage of that union
  have hinc : {s : AnchoredC11Sample d | c < PotentialField.unitCubeDerivNorm
        (PotentialField.translate y (anchoredLog s))} ⊆
      Subtype.val ⁻¹' (⋃ L, E L) := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    by_contra hcon
    simp only [Set.mem_preimage, Set.mem_iUnion, not_exists, hEdef, Set.mem_setOf_eq,
      not_lt] at hcon
    have hbd : ∀ L : ℕ, PotentialField.unitCubeDerivNorm
        (PotentialField.translate y (anchoredPartialSumField s.val L)) ≤ c := fun L =>
      le_trans (unitCubeDerivNorm_translate_anchoredPartialSum_le s.val y L) (hcon L)
    exact absurd (unitCubeDerivNorm_translate_anchoredLog_le s y hbd) (not_le.mpr hs)
  refine le_trans (measureReal_mono hinc (measure_ne_top _ _)) ?_
  have heq : (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure (Subtype.val ⁻¹' (⋃ L, E L)) =
      M.P.toMeasure (⋃ L, E L) :=
    anchoredC11SampleLaw_preimage M _ _ _
  unfold Measure.real
  rw [heq]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB0).mp hunion

/-! ### The Lipschitz half of links 1 and 4 -/

/-- **Link 1, Lipschitz half.** -/
theorem ogammaLE_unitCubeDerivLipschitzSeminorm_layer (M : GMCModel d) (k : ℕ) (y : Vec d) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 ((((3:ℝ) ^ k)⁻¹) ^ 2 * M.delta)
      (fun omega : PotentialSample d =>
        PotentialField.unitCubeDerivLipschitzSeminorm
          (PotentialField.translate y (omega k))) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have h3 : (0:ℝ) < (3:ℝ) ^ k := by positivity
  have hr0 : (0:ℝ) < ((3:ℝ) ^ k)⁻¹ := inv_pos.mpr h3
  set r : ℝ := ((3:ℝ) ^ k)⁻¹ with hrdef
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have hDN : SubdiffusiveProcess.OGammaLE (zeroPotentialLaw M.P).toMeasure 2 M.delta
      PotentialField.unitCubeDerivLipschitzSeminorm :=
    ogammaLE_mono_observable two_pos hdelta
      PotentialField.unitCubeDerivLipschitzSeminorm_measurable
      (Filter.Eventually.of_forall fun g =>
        PotentialField.unitCubeDerivLipschitzSeminorm_le_g2Observable g)
      M.G2.regularity_expectation
  have hTrans : SubdiffusiveProcess.OGammaLE (zeroPotentialLaw M.P).toMeasure 2 M.delta
      (fun g => PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate (r • y) g)) := by
    refine SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_comp_measurePreserving
      ⟨PotentialField.measurable_translate (r • y), M.G1.stationary (r • y)⟩
      PotentialField.unitCubeDerivLipschitzSeminorm_measurable.aemeasurable hDN
  have hScaled : SubdiffusiveProcess.OGammaLE (zeroPotentialLaw M.P).toMeasure 2 (r ^ 2 * M.delta)
      (fun g => PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y (PotentialField.triadicScale k g))) := by
    refine ogammaLE_mono_observable two_pos (by positivity)
      ((PotentialField.unitCubeDerivLipschitzSeminorm_measurable.comp
        (PotentialField.measurable_translate y)).comp
        (PotentialField.measurable_triadicScale k))
      (Filter.Eventually.of_forall fun g =>
        unitCubeDerivLipschitzSeminorm_translate_triadicScale_le k y g)
      (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_const_mul hdelta hr2 hTrans)
  have hmapScale : (potentialMarginalLaw M.P k).toMeasure =
      Measure.map (PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure := by
    rw [M.shellPrefix.marginal_scaling k,
      ProbabilityMeasure.toMeasure_map _ (PotentialField.measurable_triadicScale k).aemeasurable]
  have hmapCoord : Measure.map (fun omega : PotentialSample d => omega k) M.P.toMeasure =
      (potentialMarginalLaw M.P k).toMeasure := by
    rw [potentialMarginalLaw,
      ProbabilityMeasure.toMeasure_map _ (measurable_potentialCoordinate k).aemeasurable]
  have hmid : SubdiffusiveProcess.OGammaLE (potentialMarginalLaw M.P k).toMeasure 2 (r ^ 2 * M.delta)
      (fun g => PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y g)) := by
    rw [hmapScale]
    refine (ogammaLE_map_iff (PotentialField.measurable_triadicScale k).aemeasurable ?_).mpr
      hScaled
    rw [← hmapScale]
    exact (PotentialField.unitCubeDerivLipschitzSeminorm_measurable.comp
      (PotentialField.measurable_translate y)).aemeasurable
  refine (ogammaLE_map_iff (T := fun omega : PotentialSample d => omega k)
    (X := fun g => PotentialField.unitCubeDerivLipschitzSeminorm
      (PotentialField.translate y g))
    (measurable_potentialCoordinate k).aemeasurable ?_).mp ?_
  · rw [hmapCoord]
    exact (PotentialField.unitCubeDerivLipschitzSeminorm_measurable.comp
      (PotentialField.measurable_translate y)).aemeasurable
  · rw [hmapCoord]; exact hmid

/-- The partial layer sum of unit-cube gradient Lipschitz seminorms at a site. -/
def layerLipSum (y : Vec d) (L : ℕ) (omega : PotentialSample d) : ℝ :=
  ∑ k ∈ Finset.range (L + 1),
    PotentialField.unitCubeDerivLipschitzSeminorm (PotentialField.translate y (omega k))

theorem layerLipSum_nonneg (y : Vec d) (L : ℕ) (omega : PotentialSample d) :
    0 ≤ layerLipSum y L omega :=
  Finset.sum_nonneg fun _ _ => PotentialField.unitCubeDerivLipschitzSeminorm_nonneg _

theorem layerLipSum_mono (y : Vec d) {L L' : ℕ} (hL : L ≤ L') (omega : PotentialSample d) :
    layerLipSum y L omega ≤ layerLipSum y L' omega := by
  have hsub : Finset.range (L + 1) ⊆ Finset.range (L' + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro k _ _
  exact PotentialField.unitCubeDerivLipschitzSeminorm_nonneg _

theorem measurable_layerLipSum (y : Vec d) (L : ℕ) :
    Measurable (layerLipSum (d := d) y L) :=
  Finset.measurable_sum _ fun k _ =>
    (PotentialField.unitCubeDerivLipschitzSeminorm_measurable.comp
      (PotentialField.measurable_translate y)).comp (measurable_potentialCoordinate k)

theorem summable_three_inv_pow_sq : Summable (fun k : ℕ => (((3:ℝ) ^ k)⁻¹) ^ 2) := by
  have hrw : (fun k : ℕ => (((3:ℝ) ^ k)⁻¹) ^ 2) = fun k : ℕ => ((9:ℝ)⁻¹) ^ k := by
    funext k
    rw [← inv_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [hrw]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem tsum_three_inv_pow_sq : ∑' k : ℕ, (((3:ℝ) ^ k)⁻¹) ^ 2 = 9 / 8 := by
  have hrw : (fun k : ℕ => (((3:ℝ) ^ k)⁻¹) ^ 2) = fun k : ℕ => ((9:ℝ)⁻¹) ^ k := by
    funext k
    rw [← inv_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [hrw, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem sum_three_inv_pow_sq_le (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), (((3:ℝ) ^ k)⁻¹) ^ 2 ≤ 9 / 8 := by
  rw [← tsum_three_inv_pow_sq]
  exact summable_three_inv_pow_sq.sum_le_tsum _ fun k _ => by positivity

/-- **Every partial Lipschitz layer sum is `O_{Γ₂}((9/8) δ)`**, uniformly in `L`. -/
theorem ogammaLE_layerLipSum (M : GMCModel d) (y : Vec d) (L : ℕ) :
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (9 / 8 * M.delta) (layerLipSum y L) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hne : (Finset.range (L + 1)).Nonempty := Finset.nonempty_range_add_one
  have hA : ∀ k : ℕ, (0:ℝ) < (((3:ℝ) ^ k)⁻¹) ^ 2 * M.delta := by
    intro k; positivity
  have hbase := ogammaLE_two_finset_sum (mu := M.P.toMeasure)
    (X := fun k omega => PotentialField.unitCubeDerivLipschitzSeminorm
      (PotentialField.translate y (omega k)))
    (A := fun k => (((3:ℝ) ^ k)⁻¹) ^ 2 * M.delta) hA
    (fun k => ((PotentialField.unitCubeDerivLipschitzSeminorm_measurable.comp
      (PotentialField.measurable_translate y)).comp
      (measurable_potentialCoordinate k)).aemeasurable)
    (fun k omega => PotentialField.unitCubeDerivLipschitzSeminorm_nonneg _)
    (fun k => ogammaLE_unitCubeDerivLipschitzSeminorm_layer M k y) hne
  refine SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ogammaLE_mono_scale'
    two_pos (Finset.sum_pos (fun k _ => hA k) hne) ?_ hbase
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_three_inv_pow_sq_le L) hdelta.le

/-- The partial-sum field's unit-cube gradient Lipschitz seminorm, bounded by the layer sum. -/
theorem unitCubeDerivLipschitzSeminorm_translate_anchoredPartialSum_le
    (omega : PotentialSample d) (y : Vec d) (L : ℕ) :
    PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y (anchoredPartialSumField omega L)) ≤
      layerLipSum y L omega := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none => exact layerLipSum_nonneg y L omega
  | some p =>
      have hne : p.val.fst.val ≠ p.val.snd.val := fun hEq => p.property (Subtype.ext hEq)
      have hdist : 0 < dist p.val.fst.val p.val.snd.val := dist_pos.mpr hne
      show dist (PotentialField.deriv
          (PotentialField.translate y (anchoredPartialSumField omega L)) p.val.fst.val)
          (PotentialField.deriv
          (PotentialField.translate y (anchoredPartialSumField omega L)) p.val.snd.val) /
          dist p.val.fst.val p.val.snd.val ≤ _
      rw [div_le_iff₀ hdist, potentialField_deriv_translate, potentialField_deriv_translate,
        deriv_anchoredPartialSumField, deriv_anchoredPartialSumField, dist_eq_norm,
        ← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) ?_
      rw [layerLipSum, Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← dist_eq_norm, ← potentialField_deriv_translate, ← potentialField_deriv_translate]
      exact PotentialField.dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul _ p.val.fst.2
        p.val.snd.2

/-- A uniform bound on the partial sums passes to the anchored limit. -/
theorem unitCubeDerivLipschitzSeminorm_translate_anchoredLog_le (omega : AnchoredC11Sample d)
    (y : Vec d) {c : ℝ}
    (hc : ∀ L : ℕ, PotentialField.unitCubeDerivLipschitzSeminorm
      (PotentialField.translate y (anchoredPartialSumField omega.val L)) ≤ c) :
    PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y (anchoredLog omega)) ≤ c := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none =>
      exact le_trans (PotentialField.unitCubeDerivLipschitzSeminorm_nonneg _) (hc 0)
  | some p =>
      have hne : p.val.fst.val ≠ p.val.snd.val := fun hEq => p.property (Subtype.ext hEq)
      have hdist : 0 < dist p.val.fst.val p.val.snd.val := dist_pos.mpr hne
      have hlim1 := ((anchoredLog_spec omega).deriv_tendsto {p.val.fst.val + y}
        isCompact_singleton).tendsto_at (Set.mem_singleton _)
      have hlim2 := ((anchoredLog_spec omega).deriv_tendsto {p.val.snd.val + y}
        isCompact_singleton).tendsto_at (Set.mem_singleton _)
      show dist (PotentialField.deriv
          (PotentialField.translate y (anchoredLog omega)) p.val.fst.val)
          (PotentialField.deriv
          (PotentialField.translate y (anchoredLog omega)) p.val.snd.val) /
          dist p.val.fst.val p.val.snd.val ≤ c
      rw [div_le_iff₀ hdist, potentialField_deriv_translate, potentialField_deriv_translate,
        dist_eq_norm]
      refine le_of_tendsto (hlim1.sub hlim2).norm (Filter.Eventually.of_forall fun L => ?_)
      rw [← dist_eq_norm, ← potentialField_deriv_translate, ← potentialField_deriv_translate]
      exact le_trans (PotentialField.dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul _
        p.val.fst.2 p.val.snd.2)
        (mul_le_mul_of_nonneg_right (hc L) (dist_nonneg))

/-- **The unit-cube gradient Lipschitz seminorm of the anchored log has a Gaussian tail at
scale `(9/8) δ`.**  Same increasing-union argument as the gradient case. -/
theorem measureReal_unitCubeDerivLipschitzSeminorm_anchoredLog_gt (M : GMCModel d) (y : Vec d)
    {c : ℝ} (hc : 0 ≤ c) :
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
        {s : AnchoredC11Sample d | c < PotentialField.unitCubeDerivLipschitzSeminorm
          (PotentialField.translate y (anchoredLog s))} ≤
      2 * Real.exp (-(((9 / 8 * M.delta)⁻¹ * c) ^ (2:ℝ))) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : (0:ℝ) < 9 / 8 * M.delta := by positivity
  set B : ℝ := 2 * Real.exp (-(((9 / 8 * M.delta)⁻¹ * c) ^ (2:ℝ))) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set E : ℕ → Set (PotentialSample d) :=
    fun L => {omega | c < layerLipSum y L omega} with hEdef
  have hEmono : Monotone E := by
    intro L L' hL omega homega
    exact lt_of_lt_of_le homega (layerLipSum_mono y hL omega)
  have hEbound : ∀ L, M.P.toMeasure (E L) ≤ ENNReal.ofReal B := by
    intro L
    have hmark := measureReal_ge_le_of_ogammaLE (ogammaLE_layerLipSum M y L) hA
      (by norm_num) hc
    have hsub : E L ⊆ {omega | c ≤ layerLipSum y L omega} := by
      intro omega homega
      have h' : c < layerLipSum y L omega := homega
      exact le_of_lt h'
    have hle : M.P.toMeasure.real (E L) ≤ B :=
      le_trans (measureReal_mono hsub (measure_ne_top _ _)) hmark
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB0).mpr hle
  have hunion : M.P.toMeasure (⋃ L, E L) ≤ ENNReal.ofReal B := by
    rw [hEmono.measure_iUnion]
    exact iSup_le hEbound
  have hinc : {s : AnchoredC11Sample d | c < PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y (anchoredLog s))} ⊆
      Subtype.val ⁻¹' (⋃ L, E L) := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    by_contra hcon
    simp only [Set.mem_preimage, Set.mem_iUnion, not_exists, hEdef, Set.mem_setOf_eq,
      not_lt] at hcon
    have hbd : ∀ L : ℕ, PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate y (anchoredPartialSumField s.val L)) ≤ c := fun L =>
      le_trans (unitCubeDerivLipschitzSeminorm_translate_anchoredPartialSum_le s.val y L)
        (hcon L)
    exact absurd (unitCubeDerivLipschitzSeminorm_translate_anchoredLog_le s y hbd)
      (not_le.mpr hs)
  refine le_trans (measureReal_mono hinc (measure_ne_top _ _)) ?_
  have heq : (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure (Subtype.val ⁻¹' (⋃ L, E L)) =
      M.P.toMeasure (⋃ L, E L) :=
    anchoredC11SampleLaw_preimage M _ _ _
  unfold Measure.real
  rw [heq]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB0).mp hunion




theorem log_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d) (w : Vec d) :
    Real.log (aAnchored M omega w) = anchoredLog omega w := by
  rw [aAnchored, Real.log_exp]

theorem euclideanGradient_potentialField (g : PotentialField d) (x : Vec d) :
    euclideanGradient (fun y : Vec d => (g : Vec d → ℝ) y) x = shellGradient g x := by
  funext i
  show euclideanCoordDeriv i (fun y : Vec d => (g : Vec d → ℝ) y) x = _
  rw [euclideanCoordDeriv, (g.hasFDerivAt x).fderiv]
  rfl

theorem euclideanGradient_log_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d)
    (x : Vec d) :
    euclideanGradient (fun w => Real.log (aAnchored M omega w)) x =
      shellGradient (anchoredLog omega) x := by
  have hfun : (fun w => Real.log (aAnchored M omega w))
      = fun w : Vec d => (anchoredLog omega : Vec d → ℝ) w := by
    funext w; exact log_aAnchored M omega w
  rw [hfun]
  exact euclideanGradient_potentialField (anchoredLog omega) x

/-- The Euclidean gradient of `log a` is controlled by the stored derivative of the anchored
log, with the dimensional constant of `euclideanNorm_le_dim_mul_norm`. -/
theorem euclideanNorm_euclideanGradient_log_aAnchored_le (M : GMCModel d)
    (omega : AnchoredC11Sample d) (x : Vec d) :
    euclideanNorm (euclideanGradient (fun w => Real.log (aAnchored M omega w)) x) ≤
      (d : ℝ) * ‖PotentialField.deriv (anchoredLog omega) x‖ := by
  rw [euclideanGradient_log_aAnchored]
  exact euclideanNorm_shellGradient_le (anchoredLog omega) x

/-- The same for an increment, which is what `HolderSeminormBoundOn` reads. -/
theorem euclideanNorm_euclideanGradient_log_aAnchored_sub_le (M : GMCModel d)
    (omega : AnchoredC11Sample d) (x y : Vec d) :
    euclideanNorm (euclideanGradient (fun w => Real.log (aAnchored M omega w)) x -
        euclideanGradient (fun w => Real.log (aAnchored M omega w)) y) ≤
      (d : ℝ) * ‖PotentialField.deriv (anchoredLog omega) x -
        PotentialField.deriv (anchoredLog omega) y‖ := by
  rw [euclideanGradient_log_aAnchored, euclideanGradient_log_aAnchored,
    shellGradient_eq_gradOfCLM, shellGradient_eq_gradOfCLM, ← gradOfCLM_sub]
  refine le_trans (euclideanNorm_le_dim_mul_norm _) ?_
  exact mul_le_mul_of_nonneg_left (norm_gradOfCLM_le _) (Nat.cast_nonneg d)

/-! ### Link 4's geometry: the side-`C` cube, and the failure event -/

theorem euclideanNorm_sum_le {iota : Type*} (s : Finset iota) (f : iota → Vec d) :
    euclideanNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, euclideanNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have htri : euclideanNorm (f a + ∑ i ∈ t, f i) ≤
          euclideanNorm (f a) + euclideanNorm (∑ i ∈ t, f i) := by
        rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
          euclideanNorm_eq_norm_ofVec]
        exact norm_add_le _ _
      linarith

theorem abs_apply_le_euclideanNorm (u : Vec d) (i : Fin d) : |u i| ≤ euclideanNorm u := by
  have h := sq_apply_le_vecNormSq u i
  have h0 : (0:ℝ) ≤ vecNormSq u := vecNormSq_nonneg u
  have hsq : euclideanNorm u ^ (2:ℕ) = vecNormSq u := euclideanNorm_sq u
  nlinarith [abs_nonneg (u i), sq_abs (u i), euclideanNorm_nonneg u]

theorem norm_le_euclideanNorm (u : Vec d) : ‖u‖ ≤ euclideanNorm u := by
  refine (pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg u)).2 fun i => ?_
  simpa only [Real.norm_eq_abs] using abs_apply_le_euclideanNorm u i

/-- The half-integer lattice point nearest a given vector, coordinatewise. -/
def unitCoverShift (u : Vec d) : Vec d := fun i => (round (2 * u i) : ℝ) / 2

theorem unitCoverShift_halfInteger (u : Vec d) (i : Fin d) :
    ∃ n : ℤ, unitCoverShift u i = (n : ℝ) / 2 := ⟨round (2 * u i), rfl⟩

theorem abs_sub_unitCoverShift (u : Vec d) (i : Fin d) :
    |u i - unitCoverShift u i| ≤ 1 / 4 := by
  have h := abs_sub_round (2 * u i)
  have hrw : u i - unitCoverShift u i = (2 * u i - (round (2 * u i) : ℝ)) / 2 := by
    unfold unitCoverShift; ring
  rw [hrw, abs_div]
  have : |(2:ℝ)| = 2 := by norm_num
  rw [this]
  linarith

/-- Every point of the side-`C` cube at `y` sits in the open unit cube around a half-integer
shift of `y`, and that shift is within `C/2 + 1/4` of the origin. -/
theorem exists_unitCoverShift {C : ℝ} (y z : Vec d) (hz : z ∈ centeredAxisCube y C) :
    (∀ i, ∃ n : ℤ, unitCoverShift (z - y) i = (n : ℝ) / 2) ∧
      (∀ i, |unitCoverShift (z - y) i| ≤ C / 2 + 1 / 4) ∧
      z - (y + unitCoverShift (z - y)) ∈ openCubeSet (originCube d 0) := by
  refine ⟨fun i => unitCoverShift_halfInteger _ i, ?_, ?_⟩
  · intro i
    have h1 := abs_sub_unitCoverShift (z - y) i
    have h2 := (Section9Support.mem_centeredAxisCube.mp hz) i
    have hzy : (z - y) i = z i - y i := rfl
    rw [hzy] at h1
    rw [abs_le] at h1 ⊢
    rw [abs_lt] at h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have h1 := abs_sub_unitCoverShift (z - y) i
    have hzy : (z - y) i = z i - y i := rfl
    rw [hzy] at h1
    have hcoord : (z - (y + unitCoverShift (z - y))) i =
        z i - y i - unitCoverShift (z - y) i := by
      show z i - (y i + unitCoverShift (z - y) i) = _
      ring
    rw [abs_le] at h1
    rw [hcoord]
    norm_num
    constructor <;> linarith [h1.1, h1.2]

/-- The stored derivative at a point of the big cube is read off the unit cube around the
covering shift. -/
theorem norm_deriv_le_of_unitCoverShift (g : PotentialField d) {C : ℝ} (y z : Vec d)
    (hz : z ∈ centeredAxisCube y C) :
    ‖PotentialField.deriv g z‖ ≤ PotentialField.unitCubeDerivNorm
      (PotentialField.translate (y + unitCoverShift (z - y)) g) := by
  obtain ⟨_, _, hmem⟩ := exists_unitCoverShift y z hz
  have hrw : PotentialField.deriv
      (PotentialField.translate (y + unitCoverShift (z - y)) g)
      (z - (y + unitCoverShift (z - y))) = PotentialField.deriv g z := by
    rw [potentialField_deriv_translate, sub_add_cancel]
  rw [← hrw]
  exact PotentialField.norm_deriv_le_unitCubeDerivNorm _ hmem

/-- **The gradient supremum on the side-`C` cube, from the unit-cube observables.** -/
theorem euclideanNorm_gradient_le_of_unitBounds (M : GMCModel d)
    (omega : AnchoredC11Sample d) {C G0 : ℝ} (y : Vec d)
    (hG : ∀ v : Vec d, (∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) → (∀ i, |v i| ≤ C / 2 + 1 / 4) →
      PotentialField.unitCubeDerivNorm
        (PotentialField.translate (y + v) (anchoredLog omega)) ≤ G0)
    {z : Vec d} (hz : z ∈ centeredAxisCube y C) :
    euclideanNorm (euclideanGradient (fun w => Real.log (aAnchored M omega w)) z) ≤
      (d : ℝ) * G0 := by
  obtain ⟨hhalf, hball, _⟩ := exists_unitCoverShift y z hz
  refine le_trans (euclideanNorm_euclideanGradient_log_aAnchored_le M omega z) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
  exact le_trans (norm_deriv_le_of_unitCoverShift (anchoredLog omega) y z hz)
    (hG _ hhalf hball)

/-- **The gradient Lipschitz seminorm on the side-`C` cube, from the unit-cube observables.**
The cube is convex, so the segment between two of its points stays inside; cutting it into
equal pieces of length at most `1/8` puts each consecutive pair inside one covering unit cube,
and the pieces are collinear, so their lengths sum exactly to the endpoint distance and no
chaining constant appears. -/
theorem holderSeminormBoundOn_of_unitBounds (M : GMCModel d) (omega : AnchoredC11Sample d)
    {C K0 : ℝ} (y : Vec d) (hK0 : 0 ≤ K0)
    (hK : ∀ v : Vec d, (∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) → (∀ i, |v i| ≤ C / 2 + 1 / 4) →
      PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate (y + v) (anchoredLog omega)) ≤ K0) :
    HolderSeminormBoundOn (centeredAxisCube y C) 1 ((d : ℝ) * K0)
      (euclideanGradient (fun w => Real.log (aAnchored M omega w))) := by
  classical
  set F : Vec d → Vec d := euclideanGradient (fun w => Real.log (aAnchored M omega w)) with hF
  intro p hp q hq
  rw [Real.rpow_one]
  set r : ℝ := euclideanNorm (p - q) with hr
  have hr0 : 0 ≤ r := euclideanNorm_nonneg _
  rcases eq_or_lt_of_le hr0 with hrz | hrpos
  · -- degenerate: the two points coincide
    have hpq : p - q = 0 := euclideanNorm_eq_zero_iff.mp hrz.symm
    have : p = q := by
      have := sub_eq_zero.mp hpq
      exact this
    rw [this, sub_self]
    simp only [euclideanNorm_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hK0) hr0
  -- the partition
  set n : ℕ := ⌈8 * r⌉₊ + 1 with hn
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hstep : r / (n : ℝ) ≤ 1 / 8 := by
    have hceil : (8 : ℝ) * r ≤ (⌈8 * r⌉₊ : ℝ) := Nat.le_ceil _
    have : (8 : ℝ) * r ≤ (n : ℝ) := by
      rw [hn]; push_cast; linarith
    rw [div_le_div_iff₀ hnR (by norm_num : (0:ℝ) < 8)]
    linarith
  set P : ℕ → Vec d := fun i => p + ((i : ℝ) / (n : ℝ)) • (q - p) with hP
  have hP0 : P 0 = p := by simp [hP]
  have hPn : P n = q := by
    simp only [hP]
    rw [div_self (ne_of_gt hnR), one_smul]
    abel
  have hmem : ∀ i : ℕ, i ≤ n → P i ∈ centeredAxisCube y C := by
    intro i hi
    have ht0 : (0:ℝ) ≤ (i : ℝ) / (n : ℝ) := by positivity
    have ht1 : (i : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]; exact_mod_cast hi
    rw [Section9Support.mem_centeredAxisCube]
    intro j
    have hpj := (Section9Support.mem_centeredAxisCube.mp hp) j
    have hqj := (Section9Support.mem_centeredAxisCube.mp hq) j
    have hcoord : P i j - y j =
        (1 - (i : ℝ) / (n : ℝ)) * (p j - y j) + ((i : ℝ) / (n : ℝ)) * (q j - y j) := by
      show p j + ((i : ℝ) / (n : ℝ)) * (q j - p j) - y j = _
      ring
    rw [hcoord]
    rw [abs_lt] at hpj hqj ⊢
    rcases le_total ((i : ℝ) / (n : ℝ)) (1 / 2) with hcase | hcase
    · exact ⟨by nlinarith [hpj.1, hqj.1, ht0, ht1, hcase],
        by nlinarith [hpj.2, hqj.2, ht0, ht1, hcase]⟩
    · exact ⟨by nlinarith [hpj.1, hqj.1, ht0, ht1, hcase],
        by nlinarith [hpj.2, hqj.2, ht0, ht1, hcase]⟩
  have hdiff : ∀ i : ℕ, P i - P (i + 1) = (-(1 / (n : ℝ))) • (q - p) := by
    intro i
    simp only [hP]
    push_cast
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    field_simp
    ring
  have hdiffnorm : ∀ i : ℕ, euclideanNorm (P i - P (i + 1)) = r / (n : ℝ) := by
    intro i
    rw [hdiff i, euclideanNorm_smul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / (n:ℝ))]
    have hqp : euclideanNorm (q - p) = r := by
      rw [hr, ← euclideanNorm_neg (p - q)]
      congr 1
      abel
    rw [hqp]
    ring
  -- the per-step estimate
  have hpiece : ∀ i : ℕ, i < n →
      euclideanNorm (F (P i) - F (P (i + 1))) ≤ (d : ℝ) * K0 * (r / (n : ℝ)) := by
    intro i hi
    obtain ⟨hhalf, hball, hmem1⟩ := exists_unitCoverShift y (P i) (hmem i (by omega))
    set v : Vec d := unitCoverShift (P i - y) with hv
    have hmem2 : P (i + 1) - (y + v) ∈ openCubeSet (originCube d 0) := by
      rw [mem_openCubeSet_originCube_iff]
      intro j
      have h1 : |P i j - y j - v j| ≤ 1 / 4 := by
        have := abs_sub_unitCoverShift (P i - y) j
        have hcast : (P i - y) j = P i j - y j := rfl
        rwa [hcast] at this
      have h2 : |P (i + 1) j - P i j| ≤ r / (n : ℝ) := by
        have hle := abs_apply_le_euclideanNorm (P (i + 1) - P i) j
        have hco : (P (i + 1) - P i) j = P (i + 1) j - P i j := rfl
        rw [hco] at hle
        refine le_trans hle (le_of_eq ?_)
        have : euclideanNorm (P (i + 1) - P i) = euclideanNorm (P i - P (i + 1)) := by
          rw [← euclideanNorm_neg (P i - P (i + 1))]
          congr 1
          abel
        rw [this, hdiffnorm i]
      have hcoord : (P (i + 1) - (y + v)) j = P (i + 1) j - y j - v j := by
        show P (i + 1) j - (y j + v j) = _
        ring
      rw [hcoord]
      rw [abs_le] at h1 h2
      norm_num
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hstep]
    have hT1 : PotentialField.deriv (PotentialField.translate (y + v) (anchoredLog omega))
        (P i - (y + v)) = PotentialField.deriv (anchoredLog omega) (P i) := by
      rw [potentialField_deriv_translate, sub_add_cancel]
    have hT2 : PotentialField.deriv (PotentialField.translate (y + v) (anchoredLog omega))
        (P (i + 1) - (y + v)) = PotentialField.deriv (anchoredLog omega) (P (i + 1)) := by
      rw [potentialField_deriv_translate, sub_add_cancel]
    have hlip := PotentialField.dist_deriv_le_unitCubeDerivLipschitzSeminorm_mul
      (PotentialField.translate (y + v) (anchoredLog omega)) hmem1 hmem2
    rw [hT1, hT2] at hlip
    have hdistrw : dist (P i - (y + v)) (P (i + 1) - (y + v)) = dist (P i) (P (i + 1)) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [hdistrw] at hlip
    have hdle : dist (P i) (P (i + 1)) ≤ r / (n : ℝ) := by
      rw [dist_eq_norm]
      exact le_trans (norm_le_euclideanNorm _) (le_of_eq (hdiffnorm i))
    have hbridge := euclideanNorm_euclideanGradient_log_aAnchored_sub_le M omega (P i) (P (i + 1))
    have hKap := hK v hhalf hball
    have hdistnn : (0:ℝ) ≤ dist (P i) (P (i + 1)) := dist_nonneg
    have hnorm : ‖PotentialField.deriv (anchoredLog omega) (P i) -
        PotentialField.deriv (anchoredLog omega) (P (i + 1))‖ ≤ K0 * (r / (n : ℝ)) := by
      rw [← dist_eq_norm]
      refine le_trans hlip ?_
      have hKapnn : (0:ℝ) ≤ PotentialField.unitCubeDerivLipschitzSeminorm
          (PotentialField.translate (y + v) (anchoredLog omega)) :=
        PotentialField.unitCubeDerivLipschitzSeminorm_nonneg _
      nlinarith [hKap, hdle, hdistnn, hKapnn]
    calc euclideanNorm (F (P i) - F (P (i + 1)))
        ≤ (d : ℝ) * ‖PotentialField.deriv (anchoredLog omega) (P i) -
            PotentialField.deriv (anchoredLog omega) (P (i + 1))‖ := hbridge
      _ ≤ (d : ℝ) * (K0 * (r / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg d)
      _ = (d : ℝ) * K0 * (r / (n : ℝ)) := by ring
  -- telescope
  have htel : F p - F q = ∑ i ∈ Finset.range n, (F (P i) - F (P (i + 1))) := by
    rw [Finset.sum_range_sub' (fun i => F (P i)) n, hP0, hPn]
  rw [htel]
  refine le_trans (euclideanNorm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.mp hi)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [mul_comm ((d:ℝ) * K0) r]
  field_simp
  ring_nf
  rfl

/-- **The side-`C` derivative bound from the unit-cube observables.**  This is the geometric
half of link 4: everything proved probabilistically about the unit cube now produces the
predicate `StoppingDerivativeBoundAt` that Step 2's requirement negates. -/
theorem stoppingDerivativeBoundAt_of_unitBounds (M : GMCModel d) (omega : AnchoredC11Sample d)
    {C G0 K0 B : ℝ} (y : Vec d) (hK0 : 0 ≤ K0) (hG0 : 0 ≤ G0)
    (hG : ∀ v : Vec d, (∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) → (∀ i, |v i| ≤ C / 2 + 1 / 4) →
      PotentialField.unitCubeDerivNorm
        (PotentialField.translate (y + v) (anchoredLog omega)) ≤ G0)
    (hK : ∀ v : Vec d, (∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) → (∀ i, |v i| ≤ C / 2 + 1 / 4) →
      PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate (y + v) (anchoredLog omega)) ≤ K0)
    (hB : 1 + ((d : ℝ) * G0) ^ 2 + (d : ℝ) * K0 ≤ B) :
    StoppingDerivativeBoundAt M omega C y B := by
  refine ⟨(d : ℝ) * G0, (d : ℝ) * K0, by positivity, by positivity, ?_, ?_, hB⟩
  · intro z hz
    exact euclideanNorm_gradient_le_of_unitBounds M omega y hG hz
  · exact holderSeminormBoundOn_of_unitBounds M omega y hK0 hK

/-- **Link 4, assembled.**  The failure of the unit-scale derivative requirement is covered by
the finitely many unit-cube events at the sites `S`, which the caller supplies together with the
guarantee that `S` contains every `y + v` the requirement can read: `y` a unit grid cube centre
within `C R_{a,j,0}` of `x`, and `v` a half-integer shift within `C/2 + 1/4` of the origin. -/
theorem measureReal_stoppingDerivativeFailure_le
    (mu : MeasureTheory.Measure (AnchoredC11Sample d)) [MeasureTheory.IsFiniteMeasure mu]
    (M : GMCModel d) (grid : Finset (Vec d)) (B C : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ)
    (S : Finset (Vec d)) {G0 K0 : ℝ} (hG0 : 0 ≤ G0) (hK0 : 0 ≤ K0)
    (hS : ∀ y : Vec d, IsGridCube grid y 1 →
      euclideanNorm (y - x) ≤ C * stoppingTestRadius m h a j 0 →
      ∀ v : Vec d, (∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) → (∀ i, |v i| ≤ C / 2 + 1 / 4) →
        y + v ∈ S)
    (hB : 1 + ((d : ℝ) * G0) ^ 2 + (d : ℝ) * K0 ≤ B * stoppingTestHeight h a j)
    {p1 p2 : ℝ}
    (hp1 : ∀ w ∈ S, mu.real {s : AnchoredC11Sample d | G0 < PotentialField.unitCubeDerivNorm
      (PotentialField.translate w (anchoredLog s))} ≤ p1)
    (hp2 : ∀ w ∈ S, mu.real {s : AnchoredC11Sample d |
      K0 < PotentialField.unitCubeDerivLipschitzSeminorm
      (PotentialField.translate w (anchoredLog s))} ≤ p2) :
    mu.real (stoppingDerivativeFailure M grid B C m h x a j) ≤ (S.card : ℝ) * (p1 + p2) := by
  classical
  set E : Vec d → Set (AnchoredC11Sample d) := fun w =>
    {s | G0 < PotentialField.unitCubeDerivNorm (PotentialField.translate w (anchoredLog s))} ∪
      {s | K0 < PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate w (anchoredLog s))} with hEdef
  have hinc : stoppingDerivativeFailure M grid B C m h x a j ⊆ ⋃ w ∈ S, E w := by
    intro s hs
    obtain ⟨y, hgrid, hdist, hfail⟩ := hs
    by_contra hcon
    simp only [Set.mem_iUnion, exists_prop, not_exists, not_and, hEdef, Set.mem_union,
      Set.mem_setOf_eq, not_or, not_lt] at hcon
    refine hfail (stoppingDerivativeBoundAt_of_unitBounds M s y hK0 hG0 ?_ ?_ hB)
    · intro v hhalf hball
      exact (hcon (y + v) (hS y hgrid hdist v hhalf hball)).1
    · intro v hhalf hball
      exact (hcon (y + v) (hS y hgrid hdist v hhalf hball)).2
  refine le_trans (MeasureTheory.measureReal_mono hinc (MeasureTheory.measure_ne_top _ _)) ?_
  refine SubdiffusiveProcess.CoarseGrainingVocab.OGamma.measureReal_biUnion_finset_le S ?_
  intro w hw
  refine le_trans (MeasureTheory.measureReal_union_le _ _) ?_
  exact add_le_add (hp1 w hw) (hp2 w hw)

/-- **Link 4 in the `K2` slot.**  The unit-scale derivative requirement fails with probability
`4 exp(-c B H_{a,j}/delta^2) exp(-(a+1)-j)`.  The thresholds are chosen so that the Gaussian
tail of the gradient — which enters squared — is already linear in `B H_{a,j}`:
`G0 = sqrt(B H)/(2d)` gives `(G0/((3/2) delta))^2 = B H/(9 d^2 delta^2)`, and
`K0 = B H/(4d)` gives a quadratic exponent, stronger still.  The site count and the reserve
`-(a+1)-j` are paid by `hreserve`, which is the source's "the entropy is absorbed by the same
lower bound on `h`". -/
theorem measureReal_stoppingDerivativeFailure_exp_le (M : GMCModel d)
    (grid : Finset (Vec d)) (B C : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ)
    (S : Finset (Vec d)) (Ccount : ℝ)
    (hS : ∀ y : Vec d, IsGridCube grid y 1 →
      euclideanNorm (y - x) ≤ C * stoppingTestRadius m h a j 0 →
      ∀ v : Vec d, (∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) → (∀ i, |v i| ≤ C / 2 + 1 / 4) →
        y + v ∈ S)
    (hd : 0 < d)
    (hBH : 9 / 4 ≤ B * (stoppingTestHeight h a j : ℝ))
    (hcount : (S.card : ℝ) ≤ Real.exp (Ccount * stoppingTestEntropy m h a j))
    (hreserve : Ccount * stoppingTestEntropy m h a j + ((a : ℝ) + 1) + (j : ℝ) ≤
      B * (stoppingTestHeight h a j : ℝ) / (18 * (d : ℝ) ^ 2 * M.delta ^ 2)) :
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
        (stoppingDerivativeFailure M grid B C m h x a j) ≤
      4 * Real.exp (-(B * (stoppingTestHeight h a j : ℝ) /
        (18 * (d : ℝ) ^ 2 * M.delta ^ 2))) * Real.exp (-((a : ℝ) + 1) - (j : ℝ)) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  set T : ℝ := B * (stoppingTestHeight h a j : ℝ) with hT
  have hT0 : (0:ℝ) < T := by linarith
  set G0 : ℝ := Real.sqrt T / (2 * (d : ℝ)) with hG0def
  set K0 : ℝ := T / (4 * (d : ℝ)) with hK0def
  have hG0 : 0 ≤ G0 := by rw [hG0def]; positivity
  have hK0 : 0 ≤ K0 := by rw [hK0def]; positivity
  have hsqrtT : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0.le
  -- the admissibility condition
  have hB : 1 + ((d : ℝ) * G0) ^ 2 + (d : ℝ) * K0 ≤ T := by
    have h1 : ((d : ℝ) * G0) ^ 2 = T / 4 := by
      rw [hG0def]
      field_simp
      rw [hsqrtT]
      ring
    have h2 : (d : ℝ) * K0 = T / 4 := by
      rw [hK0def]; field_simp
    rw [h1, h2]; linarith
  -- the two per-site tails
  have hp1 : ∀ w ∈ S, (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
      {s : AnchoredC11Sample d | G0 < PotentialField.unitCubeDerivNorm
        (PotentialField.translate w (anchoredLog s))} ≤
      2 * Real.exp (-(((3 / 2 * M.delta)⁻¹ * G0) ^ (2:ℝ))) := fun w _ =>
    measureReal_unitCubeDerivNorm_anchoredLog_gt M w hG0
  have hp2 : ∀ w ∈ S, (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
      {s : AnchoredC11Sample d | K0 < PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate w (anchoredLog s))} ≤
      2 * Real.exp (-(((9 / 8 * M.delta)⁻¹ * K0) ^ (2:ℝ))) := fun w _ =>
    measureReal_unitCubeDerivLipschitzSeminorm_anchoredLog_gt M w hK0
  have hmain := measureReal_stoppingDerivativeFailure_le
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure M grid B C m h x a j S hG0 hK0 hS hB
    hp1 hp2
  -- the two exponents, in natural-power form
  set E : ℝ := T / (9 * (d : ℝ) ^ 2 * M.delta ^ 2) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have htwo : ((2:ℝ)) = ((2:ℕ) : ℝ) := by norm_num
  have hg2 : ((3 / 2 * M.delta)⁻¹ * G0) ^ (2:ℝ) = E := by
    rw [htwo, Real.rpow_natCast, mul_pow, inv_pow, hG0def, div_pow, hsqrtT, hEdef]
    field_simp
    ring
  have hk2 : E ≤ ((9 / 8 * M.delta)⁻¹ * K0) ^ (2:ℝ) := by
    rw [htwo, Real.rpow_natCast, mul_pow, inv_pow, hK0def, div_pow, hEdef]
    have hrw : ((9 / 8 * M.delta) ^ 2)⁻¹ * (T ^ 2 / (4 * (d:ℝ)) ^ 2) =
        (4 * T ^ 2) / (81 * (d:ℝ) ^ 2 * M.delta ^ 2) := by
      field_simp
      ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hBH, hT0, hdR, hdelta, sq_nonneg ((d:ℝ) * M.delta),
      mul_pos (mul_pos hT0 hT0) (mul_pos (mul_pos hdR hdR) (mul_pos hdelta hdelta))]
  -- the per-site sum
  have hsum : 2 * Real.exp (-(((3 / 2 * M.delta)⁻¹ * G0) ^ (2:ℝ))) +
      2 * Real.exp (-(((9 / 8 * M.delta)⁻¹ * K0) ^ (2:ℝ))) ≤ 4 * Real.exp (-E) := by
    rw [hg2]
    have := Real.exp_le_exp.mpr (neg_le_neg hk2)
    linarith
  have hcard0 : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hstep : (S.card : ℝ) * (2 * Real.exp (-(((3 / 2 * M.delta)⁻¹ * G0) ^ (2:ℝ))) +
      2 * Real.exp (-(((9 / 8 * M.delta)⁻¹ * K0) ^ (2:ℝ)))) ≤
      Real.exp (Ccount * stoppingTestEntropy m h a j) * (4 * Real.exp (-E)) :=
    mul_le_mul hcount hsum (by positivity) (Real.exp_pos _).le
  refine le_trans hmain (le_trans hstep ?_)
  have hfinal : Real.exp (Ccount * stoppingTestEntropy m h a j) * (4 * Real.exp (-E)) =
      4 * Real.exp (Ccount * stoppingTestEntropy m h a j - E) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [hfinal]
  have hexp : Ccount * stoppingTestEntropy m h a j - E ≤
      -(T / (18 * (d : ℝ) ^ 2 * M.delta ^ 2)) + (-((a : ℝ) + 1) - (j : ℝ)) := by
    have hhalf : T / (18 * (d : ℝ) ^ 2 * M.delta ^ 2) * 2 = E := by
      rw [hEdef]; field_simp; ring
    linarith [hreserve, hhalf]
  calc 4 * Real.exp (Ccount * stoppingTestEntropy m h a j - E)
      ≤ 4 * Real.exp (-(T / (18 * (d : ℝ) ^ 2 * M.delta ^ 2)) +
          (-((a : ℝ) + 1) - (j : ℝ))) := by
        have := Real.exp_le_exp.mpr hexp
        linarith
    _ = 4 * Real.exp (-(T / (18 * (d : ℝ) ^ 2 * M.delta ^ 2))) *
        Real.exp (-((a : ℝ) + 1) - (j : ℝ)) := by
        rw [Real.exp_add]; ring

/-! ### The site set, and link 4 complete -/

/-- The sites the unit-scale derivative requirement can read at `x`: a unit grid-cube centre
within `rho` of `x`, shifted by a half-integer vector of size at most `Cv`. -/
def derivSites (grid : Finset (Vec d)) (x : Vec d) (rho Cv : ℝ) : Finset (Vec d) :=
  grid.biUnion fun g =>
    ((Fintype.piFinset fun i : Fin d => Finset.Icc ⌈x i - g i - rho⌉ ⌊x i - g i + rho⌋) ×ˢ
      (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(⌈2 * Cv⌉)) ⌈2 * Cv⌉)).image
      (fun t => (fun i => g i + (t.1 i : ℝ) + (t.2 i : ℝ) / 2 : Vec d))

theorem mem_derivSites (grid : Finset (Vec d)) (x : Vec d) {rho Cv : ℝ} {y v : Vec d}
    (hy : IsGridCube grid y 1) (hdist : ∀ i, |y i - x i| ≤ rho)
    (hhalf : ∀ i, ∃ n : ℤ, v i = (n : ℝ) / 2) (hball : ∀ i, |v i| ≤ Cv) :
    y + v ∈ derivSites grid x rho Cv := by
  classical
  obtain ⟨g, hg, m, k, hside, hyeq⟩ := hy
  have hm : m = 0 := by
    have hinj := zpow_right_injective₀ (by norm_num : (0:ℝ) < 3) (by norm_num : (3:ℝ) ≠ 1)
    have h0 : (3:ℝ) ^ m = (3:ℝ) ^ (0:ℤ) := by rw [← hside]; norm_num
    exact hinj h0
  subst hm
  have hycoord : ∀ i, y i = g i + (k i : ℝ) := by
    intro i
    rw [hyeq]
    norm_num
  choose w hw using hhalf
  refine Finset.mem_biUnion.mpr ⟨g, hg, ?_⟩
  refine Finset.mem_image.mpr ⟨(k, w), ?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_,
      Fintype.mem_piFinset.mpr fun i => ?_⟩
    · have hd := hdist i
      rw [abs_le] at hd
      rw [hycoord i] at hd
      refine Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith [hd.1]),
        Int.le_floor.mpr (by linarith [hd.2])⟩
    · have hb := hball i
      rw [hw i, abs_div] at hb
      have h2 : |(2:ℝ)| = 2 := by norm_num
      rw [h2] at hb
      have hwb : |(w i : ℝ)| ≤ 2 * Cv := by linarith
      rw [abs_le] at hwb
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · have : -(2 * Cv) ≤ (w i : ℝ) := hwb.1
        have hce : -((⌈2 * Cv⌉ : ℤ) : ℝ) ≤ (w i : ℝ) := by
          have := Int.le_ceil (2 * Cv)
          linarith
        exact_mod_cast hce
      · exact Int.le_ceil_iff.mpr (by linarith [hwb.2, Int.sub_one_lt_iff.mpr (le_refl (⌈2 * Cv⌉))])
  · funext i
    show g i + (k i : ℝ) + (w i : ℝ) / 2 = y i + v i
    rw [hycoord i, hw i]

theorem card_Icc_ceil_floor_le (A rho : ℝ) :
    (Finset.Icc ⌈A - rho⌉ ⌊A + rho⌋).card ≤ ⌈2 * rho⌉₊ + 2 := by
  rw [Int.card_Icc]
  have h1 : (⌊A + rho⌋ : ℝ) ≤ A + rho := Int.floor_le _
  have h2 : A - rho ≤ (⌈A - rho⌉ : ℝ) := Int.le_ceil _
  have hle : ((⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ) : ℝ) ≤ 2 * rho + 1 := by
    push_cast
    linarith
  have hceil : (2 : ℝ) * rho ≤ (⌈2 * rho⌉₊ : ℝ) := Nat.le_ceil _
  have hnat : ((⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ).toNat : ℝ) ≤ (⌈2 * rho⌉₊ : ℝ) + 2 := by
    rcases le_or_gt (⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ) 0 with hneg | hpos
    · have : ((⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ).toNat : ℝ) = 0 := by
        rw [Int.toNat_of_nonpos hneg]; norm_num
      rw [this]; positivity
    · have hz : ((⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ).toNat : ℤ) =
          (⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ) := Int.toNat_of_nonneg (le_of_lt hpos)
      have hcast : ((⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ).toNat : ℝ) =
          ((⌊A + rho⌋ + 1 - ⌈A - rho⌉ : ℤ) : ℝ) := by exact_mod_cast congrArg Int.cast hz
      rw [hcast]; linarith
  exact_mod_cast hnat

theorem card_Icc_neg_ceil_le (Cv : ℝ) (hCv : 0 ≤ Cv) :
    (Finset.Icc (-(⌈2 * Cv⌉)) ⌈2 * Cv⌉).card ≤ 2 * ⌈2 * Cv⌉₊ + 1 := by
  rw [Int.card_Icc]
  have hnn : (0:ℝ) ≤ 2 * Cv := by linarith
  have hce : (⌈2 * Cv⌉ : ℤ) = (⌈2 * Cv⌉₊ : ℤ) := (Int.natCast_ceil_eq_ceil hnn).symm
  rw [hce]
  have : ((⌈2 * Cv⌉₊ : ℤ) + 1 - -(⌈2 * Cv⌉₊ : ℤ)).toNat = 2 * ⌈2 * Cv⌉₊ + 1 := by
    omega
  rw [this]

theorem card_derivSites_le (grid : Finset (Vec d)) (x : Vec d) {rho Cv : ℝ}
    (hCv : 0 ≤ Cv) :
    (derivSites grid x rho Cv).card ≤
      grid.card * ((⌈2 * rho⌉₊ + 2) * (2 * ⌈2 * Cv⌉₊ + 1)) ^ d := by
  classical
  refine le_trans (Finset.card_biUnion_le) ?_
  have hterm : ∀ g ∈ grid,
      (((Fintype.piFinset fun i : Fin d => Finset.Icc ⌈x i - g i - rho⌉ ⌊x i - g i + rho⌋) ×ˢ
        (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(⌈2 * Cv⌉)) ⌈2 * Cv⌉)).image
        (fun t => (fun i => g i + (t.1 i : ℝ) + (t.2 i : ℝ) / 2 : Vec d))).card ≤
      ((⌈2 * rho⌉₊ + 2) * (2 * ⌈2 * Cv⌉₊ + 1)) ^ d := by
    intro g _
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset, mul_pow]
    refine Nat.mul_le_mul ?_ ?_
    · refine le_trans (Finset.prod_le_pow_card _ _ (⌈2 * rho⌉₊ + 2) ?_) ?_
      · intro i _
        have := card_Icc_ceil_floor_le (x i - g i) rho
        simpa only [sub_sub] using this
      · simp
    · refine le_trans (Finset.prod_le_pow_card _ _ (2 * ⌈2 * Cv⌉₊ + 1) ?_) ?_
      · intro i _
        exact card_Icc_neg_ceil_le Cv hCv
      · simp
  calc ∑ g ∈ grid, _ ≤ ∑ _g ∈ grid, ((⌈2 * rho⌉₊ + 2) * (2 * ⌈2 * Cv⌉₊ + 1)) ^ d :=
        Finset.sum_le_sum hterm
    _ = grid.card * ((⌈2 * rho⌉₊ + 2) * (2 * ⌈2 * Cv⌉₊ + 1)) ^ d := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Link 4, with the site set constructed.**  The only remaining hypothesis is the numeric
count `hcount`, whose left side is the explicit cardinality bound of `card_derivSites_le`. -/
theorem measureReal_stoppingDerivativeFailure_exp_le_derivSites (M : GMCModel d)
    (grid : Finset (Vec d)) (B C : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ) (Ccount : ℝ)
    (hd : 0 < d) (hC : 0 ≤ C / 2 + 1 / 4)
    (hBH : 9 / 4 ≤ B * (stoppingTestHeight h a j : ℝ))
    (hcount : (grid.card : ℝ) *
        (((⌈2 * (C * stoppingTestRadius m h a j 0)⌉₊ + 2) *
          (2 * ⌈2 * (C / 2 + 1 / 4)⌉₊ + 1)) ^ d : ℕ) ≤
      Real.exp (Ccount * stoppingTestEntropy m h a j))
    (hreserve : Ccount * stoppingTestEntropy m h a j + ((a : ℝ) + 1) + (j : ℝ) ≤
      B * (stoppingTestHeight h a j : ℝ) / (18 * (d : ℝ) ^ 2 * M.delta ^ 2)) :
    (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
        (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
        (stoppingDerivativeFailure M grid B C m h x a j) ≤
      4 * Real.exp (-(B * (stoppingTestHeight h a j : ℝ) /
        (18 * (d : ℝ) ^ 2 * M.delta ^ 2))) * Real.exp (-((a : ℝ) + 1) - (j : ℝ)) := by
  refine measureReal_stoppingDerivativeFailure_exp_le M grid B C m h x a j
    (derivSites grid x (C * stoppingTestRadius m h a j 0) (C / 2 + 1 / 4)) Ccount ?_ hd hBH ?_
    hreserve
  · intro y hgrid hdist v hhalf hball
    refine mem_derivSites grid x hgrid (fun i => ?_) hhalf hball
    exact le_trans (abs_apply_le_euclideanNorm (y - x) i) hdist
  · refine le_trans ?_ hcount
    have hcard := card_derivSites_le grid x (rho := C * stoppingTestRadius m h a j 0)
      (Cv := C / 2 + 1 / 4) hC
    exact_mod_cast hcard

/-! ### The site count, and the derivative group discharged -/

/-- The testing radius at the native scale zero is below `e^{V_{a,j}}`: the entropy is the
logarithm of the radius plus the reserve `a+1`. -/
theorem stoppingTestRadius_zero_le_exp_entropy (m h a j : ℕ) :
    stoppingTestRadius m h a j 0 ≤ Real.exp (stoppingTestEntropy m h a j) := by
  have hm : (0:ℝ) < (m : ℝ) + 2 := by positivity
  have hpow : ((m : ℝ) + 2) ^ (a + 1) =
      Real.exp (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2)) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  have hR : stoppingTestRadius m h a j 0 =
      Real.exp (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2)) *
        Real.exp (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)) := by
    unfold stoppingTestRadius
    rw [hpow]
    norm_num
  have hV : stoppingTestEntropy m h a j =
      (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2) +
        (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ))) + ((a + 1 : ℕ) : ℝ) := by
    unfold stoppingTestEntropy
    ring
  rw [hR, hV]
  have heq : Real.exp ((((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2) +
        (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ))) + ((a + 1 : ℕ) : ℝ)) =
      Real.exp (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2)) *
        Real.exp (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)) *
        Real.exp (((a + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_add ((((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2) +
        (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)))) (((a + 1 : ℕ) : ℝ)),
      Real.exp_add (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2))
        ((((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)))]
  rw [heq]
  have hpos : (0:ℝ) < Real.exp (((a + 1 : ℕ) : ℝ) * Real.log ((m : ℝ) + 2)) *
      Real.exp (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)) := by positivity
  have hone : (1:ℝ) ≤ Real.exp (((a + 1 : ℕ) : ℝ)) :=
    Real.one_le_exp (by positivity)
  nlinarith [hpos, hone]

theorem one_le_stoppingTestEntropy (m h a j : ℕ) : 1 ≤ stoppingTestEntropy m h a j := by
  unfold stoppingTestEntropy
  have hlog : (0:ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hh : (0:ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have ha : (1:ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) a
    push_cast
    linarith
  nlinarith [hlog, hh, hj, ha]

theorem one_le_stoppingTestRadius_zero (m h a j : ℕ) : 1 ≤ stoppingTestRadius m h a j 0 := by
  unfold stoppingTestRadius
  have h1 : (1:ℝ) ≤ ((m : ℝ) + 2) ^ (a + 1) := by
    refine one_le_pow₀ ?_
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have h2 : (1:ℝ) ≤ Real.exp (((a + 1 : ℕ) : ℝ) * (h : ℝ) + (j : ℝ)) := by
    refine Real.one_le_exp ?_
    positivity
  have h3 : ((3:ℝ) ^ (0:ℕ)) = 1 := by norm_num
  rw [h3, mul_one]
  nlinarith [h1, h2]

/-- **The site count is `e^{C V_{a,j}}`.**  This is the last hypothesis of
`measureReal_stoppingDerivativeFailure_exp_le_derivSites`, and it closes the derivative
group: the radius enters only through `log R_{a,j,0} = V_{a,j} - (a+1)`, and the entropy is
at least one, so the fixed factors are absorbed by enlarging the constant. -/
theorem exists_derivSites_count_bound (grid : Finset (Vec d)) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ m h a j : ℕ,
      (grid.card : ℝ) * ((((⌈2 * (C * stoppingTestRadius m h a j 0)⌉₊ + 2) *
          (2 * ⌈2 * (C / 2 + 1 / 4)⌉₊ + 1)) ^ d : ℕ) : ℝ) ≤
        Real.exp (Ccount * stoppingTestEntropy m h a j) := by
  classical
  set K : ℕ := 2 * ⌈2 * (C / 2 + 1 / 4)⌉₊ + 1 with hKdef
  set A : ℝ := max 1 ((grid.card : ℝ) * ((2 * C + 3) * (K : ℝ)) ^ d) with hAdef
  have hA1 : (1:ℝ) ≤ A := le_max_left _ _
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA1
  have hlogA : (0:ℝ) ≤ Real.log A := Real.log_nonneg hA1
  refine ⟨Real.log A + (d : ℝ) + 1, by positivity, ?_⟩
  intro m h a j
  set R : ℝ := stoppingTestRadius m h a j 0 with hRdef
  set V : ℝ := stoppingTestEntropy m h a j with hVdef
  have hR1 : (1:ℝ) ≤ R := one_le_stoppingTestRadius_zero m h a j
  have hRV : R ≤ Real.exp V := stoppingTestRadius_zero_le_exp_entropy m h a j
  have hV1 : (1:ℝ) ≤ V := one_le_stoppingTestEntropy m h a j
  have hKR : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  -- the per-coordinate factor
  have hceil : ((⌈2 * (C * R)⌉₊ : ℝ)) ≤ 2 * (C * R) + 1 := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * (C * R) by positivity)
    linarith
  have hfac : (((⌈2 * (C * R)⌉₊ + 2 : ℕ)) : ℝ) * (K : ℝ) ≤ (2 * C + 3) * (K : ℝ) * R := by
    have hstep : (((⌈2 * (C * R)⌉₊ + 2 : ℕ)) : ℝ) ≤ (2 * C + 3) * R := by
      push_cast
      nlinarith [hceil, hR1, hC]
    nlinarith [hstep, hKR, hR1]
  -- raise to the dimension
  have hpow : ((((⌈2 * (C * R)⌉₊ + 2) * K) ^ d : ℕ) : ℝ) ≤ ((2 * C + 3) * (K : ℝ)) ^ d * R ^ d := by
    have hnn : (0:ℝ) ≤ (((⌈2 * (C * R)⌉₊ + 2 : ℕ)) : ℝ) * (K : ℝ) := by positivity
    have := pow_le_pow_left₀ hnn hfac d
    calc ((((⌈2 * (C * R)⌉₊ + 2) * K) ^ d : ℕ) : ℝ)
        = ((((⌈2 * (C * R)⌉₊ + 2 : ℕ)) : ℝ) * (K : ℝ)) ^ d := by push_cast; ring
      _ ≤ ((2 * C + 3) * (K : ℝ) * R) ^ d := this
      _ = ((2 * C + 3) * (K : ℝ)) ^ d * R ^ d := by rw [mul_pow]
  have hRd : R ^ d ≤ Real.exp ((d : ℝ) * V) := by
    calc R ^ d ≤ (Real.exp V) ^ d := pow_le_pow_left₀ (by linarith) hRV d
      _ = Real.exp ((d : ℝ) * V) := by rw [Real.exp_nat_mul]
  have hcard : (0:ℝ) ≤ (grid.card : ℝ) := Nat.cast_nonneg _
  have hbase : (grid.card : ℝ) * (((2 * C + 3) * (K : ℝ)) ^ d) ≤ A := le_max_right _ _
  -- assemble
  have hmain : (grid.card : ℝ) * ((((⌈2 * (C * R)⌉₊ + 2) * K) ^ d : ℕ) : ℝ) ≤
      A * Real.exp ((d : ℝ) * V) := by
    have h1 : (grid.card : ℝ) * ((((⌈2 * (C * R)⌉₊ + 2) * K) ^ d : ℕ) : ℝ) ≤
        (grid.card : ℝ) * (((2 * C + 3) * (K : ℝ)) ^ d * R ^ d) :=
      mul_le_mul_of_nonneg_left hpow hcard
    have h2 : (grid.card : ℝ) * (((2 * C + 3) * (K : ℝ)) ^ d * R ^ d) ≤
        A * Real.exp ((d : ℝ) * V) := by
      have hRdnn : (0:ℝ) ≤ R ^ d := by positivity
      nlinarith [hbase, hRd, hcard, hRdnn, hA0,
        mul_nonneg hcard (pow_nonneg (by positivity : (0:ℝ) ≤ (2 * C + 3) * (K : ℝ)) d)]
    linarith
  refine le_trans hmain ?_
  have hAexp : A * Real.exp ((d : ℝ) * V) = Real.exp (Real.log A + (d : ℝ) * V) := by
    rw [Real.exp_add, Real.exp_log hA0]
  rw [hAexp]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hlogA, hV1]

/-- **The derivative requirement group, discharged.**  One constant `Ccount`, depending only
on the grid, the geometric constant `C` and the dimension, serves every `(m,h,a,j)`: the
failure of `e.weighted.scale.zero.derivative.bound` has probability
`4 exp(-B H_{a,j}/(18 d^2 delta^2)) exp(-(a+1)-j)`, which is the `K2` slot of
`measureReal_stoppingLevelFailure_display`. -/
theorem exists_measureReal_stoppingDerivativeFailure_bound (M : GMCModel d)
    (grid : Finset (Vec d)) {C : ℝ} (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ Ccount : ℝ, 0 < Ccount ∧ ∀ (B : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ),
      9 / 4 ≤ B * (stoppingTestHeight h a j : ℝ) →
      Ccount * stoppingTestEntropy m h a j + ((a : ℝ) + 1) + (j : ℝ) ≤
          B * (stoppingTestHeight h a j : ℝ) / (18 * (d : ℝ) ^ 2 * M.delta ^ 2) →
        (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
            (measure_anchoredC11GoodSet_eq_one M)).toMeasure.real
            (stoppingDerivativeFailure M grid B C m h x a j) ≤
          4 * Real.exp (-(B * (stoppingTestHeight h a j : ℝ) /
            (18 * (d : ℝ) ^ 2 * M.delta ^ 2))) * Real.exp (-((a : ℝ) + 1) - (j : ℝ)) := by
  obtain ⟨Ccount, hCcount, hbound⟩ := exists_derivSites_count_bound (d := d) grid hC
  refine ⟨Ccount, hCcount, ?_⟩
  intro B m h x a j hBH hreserve
  exact measureReal_stoppingDerivativeFailure_exp_le_derivSites M grid B C m h x a j Ccount hd
    (by linarith) hBH (hbound m h a j) hreserve

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
