import SubdiffusiveProcess.MacroAllCube.ResidualG2
import SubdiffusiveProcess.Model.ZeroLevel
import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange

/-!
# The boundedly dilated residual GMC model

For a `GMCModel d` `M` and `1 ≤ s ≤ 3`, the seed law
`(zeroPotentialLaw M.P).map (spatialScale s)` satisfies every level-zero
requirement `SubdiffusiveProcess.Model.ZeroLevelLaw` at disorder `residualDisorderFactor d * M.delta`,
provided `M.delta ≤ (2 * residualDisorderFactor d)⁻¹` (only for the frozen
`delta ≤ 1/2` field).  The product model over it is then an actual
`GMCModel d` with exactly that seed law.

The native constructor `SubdiffusiveProcess.Model.nonempty_gmcModel_of_zeroLevelLaw` exports only
`Nonempty (GMCModel d)`, which forgets the seed law.  `modelOfZeroLevelLaw`
below is the same construction (same fields, same upstream lemmas
`sampleLaw`, `zeroLaw_eq`, `marginal_eq`, `coord_zero_map`,
`indepFun_sampleLaw`) as a definition, so the seed law can be read back.
-/

open MeasureTheory ProbabilityTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open scoped Pointwise

noncomputable section

namespace ResidualModel

variable {d : ℕ}

/-! ## The native product model, as a definition -/

section OfZeroLevel

variable {delta : ℝ} {μ : ProbabilityMeasure (PotentialField d)}

theorem sampleLaw_shellPrefix (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    ShellLawPrefix d delta (SubdiffusiveProcess.Model.sampleLaw μ) where
  dimension := h.dimension
  delta_pos := h.delta_pos
  delta_le_half := h.delta_le_half
  independent := SubdiffusiveProcess.Model.indepFun_sampleLaw μ
  marginal_scaling := by
    intro k
    apply ProbabilityMeasure.toMeasure_injective
    show (potentialMarginalLaw (SubdiffusiveProcess.Model.sampleLaw μ) k : Measure (PotentialField d))
      = (zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d)).map
          (PotentialField.triadicScale k)
    rw [SubdiffusiveProcess.Model.marginal_eq, SubdiffusiveProcess.Model.zeroLaw_eq μ, SubdiffusiveProcess.Model.levelLaw]

theorem sampleLaw_G1 (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    ShellLawG1 d (SubdiffusiveProcess.Model.sampleLaw μ) := by
  have hzero : (zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d))
      = (μ : Measure (PotentialField d)) := SubdiffusiveProcess.Model.zeroLaw_eq μ
  have hm : AEMeasurable (fun ω : PotentialSample d => ω 0)
      (SubdiffusiveProcess.Model.sampleLaw μ : Measure (PotentialSample d)) :=
    (measurable_potentialCoordinate 0).aemeasurable
  refine { integrable := ?_, mean_zero := ?_, stationary := ?_, range_dependence := ?_ }
  · intro x
    have hi := integrable_map_measure
      (g := fun g : PotentialField d => g x)
      (by rw [SubdiffusiveProcess.Model.coord_zero_map]; exact (PotentialField.measurable_eval x).aestronglyMeasurable)
      hm
    rw [SubdiffusiveProcess.Model.coord_zero_map] at hi
    exact hi.mp (h.integrable x)
  · intro x
    have hmap := integral_map (μ := (SubdiffusiveProcess.Model.sampleLaw μ : Measure (PotentialSample d)))
      (φ := fun ω : PotentialSample d => ω 0) (f := fun g : PotentialField d => g x)
      hm (by rw [SubdiffusiveProcess.Model.coord_zero_map]; exact (PotentialField.measurable_eval x).aestronglyMeasurable)
    rw [SubdiffusiveProcess.Model.coord_zero_map] at hmap
    rw [← hmap]
    exact h.mean_zero x
  · intro z; rw [hzero]; exact h.stationary z
  · intro U V hU hV hsep; rw [hzero]; exact h.range_dependence U V hU hV hsep

theorem sampleLaw_G2 (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    ShellLawG2 d delta (SubdiffusiveProcess.Model.sampleLaw μ) where
  regularity_expectation := by rw [SubdiffusiveProcess.Model.zeroLaw_eq μ]; exact h.regularity

theorem sampleLaw_G3 (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    ShellLawG3 d (SubdiffusiveProcess.Model.sampleLaw μ) := by
  have hzero : (zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d))
      = (μ : Measure (PotentialField d)) := SubdiffusiveProcess.Model.zeroLaw_eq μ
  refine { signed_coordinate_permutations := ?_, negation := ?_ }
  · intro R hR
    apply ProbabilityMeasure.toMeasure_injective
    show (zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d)).map
        (PotentialField.rotate R hR) = _
    rw [hzero]; exact h.signed_permutation R hR
  · apply ProbabilityMeasure.toMeasure_injective
    show (zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d)).map
        PotentialField.negate = _
    rw [hzero]; exact h.negation

theorem sampleLaw_G4 (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    ShellLawG4 d (SubdiffusiveProcess.Model.sampleLaw μ) := by
  have hzero : (zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d))
      = (μ : Measure (PotentialField d)) := SubdiffusiveProcess.Model.zeroLaw_eq μ
  refine { exponential_integrable := ?_, tauSq_pos := ?_ }
  · rw [hzero]; exact h.exponential_integrable
  · show 0 < Real.log (∫ g : PotentialField d, Real.exp (g 0)
      ∂(zeroPotentialLaw (SubdiffusiveProcess.Model.sampleLaw μ) : Measure (PotentialField d)))
    rw [hzero]
    exact h.tauSq_pos

/-- The model of `SubdiffusiveProcess.Model.nonempty_gmcModel_of_zeroLevelLaw`, kept as data. -/
def modelOfZeroLevelLaw (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) : GMCModel d where
  delta := delta
  P := SubdiffusiveProcess.Model.sampleLaw μ
  shellPrefix := sampleLaw_shellPrefix h
  G1 := sampleLaw_G1 h
  G2 := sampleLaw_G2 h
  G3 := sampleLaw_G3 h
  G4 := sampleLaw_G4 h

theorem modelOfZeroLevelLaw_delta (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    (modelOfZeroLevelLaw h).delta = delta := rfl

theorem modelOfZeroLevelLaw_P (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    (modelOfZeroLevelLaw h).P = SubdiffusiveProcess.Model.sampleLaw μ := rfl

theorem zeroPotentialLaw_modelOfZeroLevelLaw (h : SubdiffusiveProcess.Model.ZeroLevelLaw d delta μ) :
    zeroPotentialLaw (modelOfZeroLevelLaw h).P = μ :=
  ProbabilityMeasure.toMeasure_injective (SubdiffusiveProcess.Model.zeroLaw_eq μ)

end OfZeroLevel

/-! ## Level-zero facts of a model -/

theorem zeroLaw_toMeasure (M : GMCModel d) :
    (zeroPotentialLaw M.P : Measure (PotentialField d)) =
      Measure.map (fun ω : PotentialSample d => ω 0) M.P.toMeasure := by
  unfold zeroPotentialLaw potentialMarginalLaw
  rw [ProbabilityMeasure.toMeasure_map]

theorem integrable_zeroLaw (M : GMCModel d) (x : Vec d) :
    Integrable (fun g : PotentialField d => g x) (zeroPotentialLaw M.P : Measure (PotentialField d)) := by
  rw [zeroLaw_toMeasure]
  exact (integrable_map_measure (PotentialField.measurable_eval x).aestronglyMeasurable
    (measurable_potentialCoordinate 0).aemeasurable).mpr (M.G1.integrable x)

theorem integral_zeroLaw (M : GMCModel d) (x : Vec d) :
    ∫ g : PotentialField d, g x ∂(zeroPotentialLaw M.P : Measure (PotentialField d)) = 0 := by
  rw [zeroLaw_toMeasure, integral_map (measurable_potentialCoordinate 0).aemeasurable
    (PotentialField.measurable_eval x).aestronglyMeasurable]
  exact M.G1.mean_zero x

/-! ## Commutation of the dilation with the symmetry actions -/

theorem translate_comp_spatialScale (s : ℝ) (z : Vec d) :
    PotentialField.translate z ∘ PotentialField.spatialScale s =
      PotentialField.spatialScale s ∘ PotentialField.translate (s • z) := by
  funext g
  apply PotentialField.ext
  intro x
  simp only [Function.comp_apply, PotentialField.translate_apply,
    PotentialField.spatialScale_apply, smul_add]

theorem rotate_comp_spatialScale (s : ℝ) (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    PotentialField.rotate R hR ∘ PotentialField.spatialScale s =
      PotentialField.spatialScale s ∘ PotentialField.rotate R hR := by
  funext g
  apply PotentialField.ext
  intro x
  simp only [Function.comp_apply, PotentialField.rotate_apply,
    PotentialField.spatialScale_apply, matVecMul_smul]

theorem negate_comp_spatialScale (s : ℝ) :
    PotentialField.negate ∘ PotentialField.spatialScale (d := d) s =
      PotentialField.spatialScale s ∘ PotentialField.negate := by
  funext g
  apply PotentialField.ext
  intro x
  simp only [Function.comp_apply, PotentialField.negate_apply,
    PotentialField.spatialScale_apply]

/-- Spatial dilation transports the integral-local sigma field to the dilated
observation set (the `spatialScale` form of the private
`ACutoffRange.measurable_triadicScale_local`). -/
theorem measurable_spatialScale_local {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) :
    @Measurable (PotentialField d) (PotentialField d)
      (PotentialField.localSigma (s • U)) (PotentialField.localSigma U)
      (PotentialField.spatialScale s) := by
  have hforget : @Measurable (PotentialField d) (RegCoeffField d)
      (PotentialField.localSigma (s • U)) (LocalSigmaR (s • U))
      PotentialField.forgetPotential :=
    Measurable.of_comap_le le_rfl
  change @Measurable (PotentialField d) (PotentialField d)
    (MeasurableSpace.comap PotentialField.forgetPotential (LocalSigmaR (s • U)))
    (MeasurableSpace.comap PotentialField.forgetPotential (LocalSigmaR U))
    (PotentialField.spatialScale s)
  rw [measurable_comap_iff]
  have h := (SubdiffusiveProcess.CoarseGrainingVocab.measurable_smulReg_local s hs U).comp hforget
  simpa only [Function.comp_apply, PotentialField.forgetPotential_apply,
    smulReg_apply, PotentialField.spatialScale_apply] using h

/-! ## The dilated seed law -/



def dilatedSeedLaw (M : GMCModel d) (s : ℝ) : ProbabilityMeasure (PotentialField d) :=
  (zeroPotentialLaw M.P).map (PotentialField.continuous_spatialScale s).measurable.aemeasurable

theorem dilatedSeedLaw_toMeasure (M : GMCModel d) (s : ℝ) :
    (dilatedSeedLaw M s : Measure (PotentialField d)) =
      Measure.map (PotentialField.spatialScale s)
        (zeroPotentialLaw M.P : Measure (PotentialField d)) :=
  ProbabilityMeasure.toMeasure_map _ _

theorem indep_dilatedSeedLaw (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s)
    (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) :
    Indep (PotentialField.localSigma U) (PotentialField.localSigma V)
      (dilatedSeedLaw M s : Measure (PotentialField d)) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  have hS : Measurable (PotentialField.spatialScale (d := d) s) :=
    (PotentialField.continuous_spatialScale s).measurable
  have hUs : MeasurableSet (s • U) := hU.const_smul_of_ne_zero hs0.ne'
  have hVs : MeasurableSet (s • V) := hV.const_smul_of_ne_zero hs0.ne'
  have hsep' : ∀ ⦃x y : Vec d⦄, x ∈ s • U → y ∈ s • V →
      Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y) := by
    rintro x y ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
    rw [← smul_sub, euclideanNorm_smul, abs_of_pos hs0]
    have h0 := hsep hx0 hy0
    have hn : 0 ≤ euclideanNorm (x0 - y0) := euclideanNorm_nonneg _
    nlinarith
  have hzero := M.G1.range_dependence (s • U) (s • V) hUs hVs hsep'
  have hcomap : Indep ((PotentialField.localSigma U).comap (PotentialField.spatialScale s))
      ((PotentialField.localSigma V).comap (PotentialField.spatialScale s))
      (zeroPotentialLaw M.P : Measure (PotentialField d)) :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hzero (measurable_spatialScale_local hs0.ne' U).comap_le)
      (measurable_spatialScale_local hs0.ne' V).comap_le
  rw [dilatedSeedLaw_toMeasure]
  exact (SubdiffusiveProcess.CoarseGrainingVocab.indep_comap_iff_indep_map hS.aemeasurable
    (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_le_borel U)
    (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_le_borel V)).mp hcomap

/-- **The dilated seed law is a level-zero law** at disorder
`residualDisorderFactor d * M.delta`.  The hypothesis on `M.delta` is used only
for the frozen `delta ≤ 1/2` clause. -/
theorem zeroLevelLaw_dilatedSeedLaw (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) :
    SubdiffusiveProcess.Model.ZeroLevelLaw d (residualDisorderFactor d * M.delta) (dilatedSeedLaw M s) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  have hS : Measurable (PotentialField.spatialScale (d := d) s) :=
    (PotentialField.continuous_spatialScale s).measurable
  have hD := residualDisorderFactor_pos d
  have hδpos := M.shellPrefix.delta_pos
  set μ0 : Measure (PotentialField d) := (zeroPotentialLaw M.P : Measure (PotentialField d))
    with hμ0
  have hν := dilatedSeedLaw_toMeasure M s
  refine
    { dimension := M.shellPrefix.dimension
      delta_pos := mul_pos hD hδpos
      delta_le_half := ?_
      integrable := ?_
      mean_zero := ?_
      stationary := ?_
      regularity := ?_
      signed_permutation := ?_
      negation := ?_
      exponential_integrable := ?_
      range_dependence := ?_
      tauSq_pos := ?_ }
  · calc residualDisorderFactor d * M.delta
        ≤ residualDisorderFactor d * (2 * residualDisorderFactor d)⁻¹ :=
          mul_le_mul_of_nonneg_left hδ hD.le
      _ = 1 / 2 := by field_simp
  · intro x
    rw [hν]
    exact (integrable_map_measure (PotentialField.measurable_eval x).aestronglyMeasurable
      hS.aemeasurable).mpr (integrable_zeroLaw M (s • x))
  · intro x
    rw [hν, integral_map hS.aemeasurable (PotentialField.measurable_eval x).aestronglyMeasurable]
    exact integral_zeroLaw M (s • x)
  · intro z
    rw [hν, Measure.map_map (PotentialField.measurable_translate z) hS,
      translate_comp_spatialScale, ← Measure.map_map hS
        (PotentialField.measurable_translate (s • z)),
      M.G1.stationary (s • z)]
  · rw [hν]
    exact ogammaLE_g2Observable_map_spatialScale μ0 hδpos hs0 hs3 M.G1.stationary
      M.G2.regularity_expectation
  · intro R hR
    have h3 := congrArg ProbabilityMeasure.toMeasure (M.G3.signed_coordinate_permutations R hR)
    rw [ProbabilityMeasure.toMeasure_map] at h3
    rw [hν, Measure.map_map (PotentialField.measurable_rotate R hR) hS,
      rotate_comp_spatialScale, ← Measure.map_map hS (PotentialField.measurable_rotate R hR),
      h3]
  · have h3 := congrArg ProbabilityMeasure.toMeasure M.G3.negation
    rw [ProbabilityMeasure.toMeasure_map] at h3
    rw [hν, Measure.map_map PotentialField.measurable_negate hS,
      negate_comp_spatialScale, ← Measure.map_map hS PotentialField.measurable_negate, h3]
  · rw [hν]
    refine (integrable_map_measure
      (PotentialField.measurable_eval 0).exp.aestronglyMeasurable hS.aemeasurable).mpr ?_
    have h4 := M.G4.exponential_integrable
    refine h4.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Function.comp_apply, PotentialField.spatialScale_apply, smul_zero]
  · exact indep_dilatedSeedLaw M hs1
  · have h4 := M.G4.tauSq_pos
    unfold tauSq at h4
    rw [hν, integral_map hS.aemeasurable
      (PotentialField.measurable_eval 0).exp.aestronglyMeasurable]
    simpa only [PotentialField.spatialScale_apply, smul_zero] using h4

/-! ## The residual model -/

/-- **The boundedly dilated model `M_s`**: the product model over the dilated seed law. -/
def residualModel (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) : GMCModel d :=
  modelOfZeroLevelLaw (zeroLevelLaw_dilatedSeedLaw M hs1 hs3 hδ)

theorem residualModel_delta (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) :
    (residualModel M hs1 hs3 hδ).delta = residualDisorderFactor d * M.delta := rfl

theorem residualModel_seed (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) :
    zeroPotentialLaw (residualModel M hs1 hs3 hδ).P =
      (zeroPotentialLaw M.P).map
        (PotentialField.continuous_spatialScale s).measurable.aemeasurable :=
  zeroPotentialLaw_modelOfZeroLevelLaw _

/-- The zero-point exponential moment, hence `τ²`, is unchanged. -/
theorem residualModel_tauSq (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * residualDisorderFactor d)⁻¹) :
    tauSq (residualModel M hs1 hs3 hδ).P = tauSq M.P := by
  unfold tauSq
  rw [residualModel_seed, ProbabilityMeasure.toMeasure_map,
    integral_map (PotentialField.continuous_spatialScale s).measurable.aemeasurable
      (PotentialField.measurable_eval 0).exp.aestronglyMeasurable]
  simp only [PotentialField.spatialScale_apply, smul_zero]



theorem exists_residualModel (d : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (M : GMCModel d) (s : ℝ), 1 ≤ s → s ≤ 3 →
      M.delta ≤ (2 * D)⁻¹ →
      ∃ Ms : GMCModel d, Ms.delta ≤ D * M.delta ∧
        zeroPotentialLaw Ms.P =
          (zeroPotentialLaw M.P).map
            (PotentialField.continuous_spatialScale s).measurable.aemeasurable ∧
        tauSq Ms.P = tauSq M.P := by
  refine ⟨residualDisorderFactor d, one_le_residualDisorderFactor d, ?_⟩
  intro M s hs1 hs3 hδ
  exact ⟨residualModel M hs1 hs3 hδ, le_of_eq (residualModel_delta M hs1 hs3 hδ),
    residualModel_seed M hs1 hs3 hδ, residualModel_tauSq M hs1 hs3 hδ⟩

end ResidualModel






