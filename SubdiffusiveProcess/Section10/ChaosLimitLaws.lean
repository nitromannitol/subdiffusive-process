module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-! This file proves translation invariance of the common-scale environment law. -/
open MeasureTheory ProbabilityTheory Topology SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Spatial translation acting on a continuous scalar field by precomposition. -/
def aux_lim_measure_spatialShift {d : ℕ} (z : SpatialCoordinates d) :
    C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => x + z,
      continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))

/-- The same spatial translation acting on every scale of a bilateral field. -/
def aux_lim_measure_bilateralShift {d : ℕ} (z : SpatialCoordinates d) :
    BilateralField d → BilateralField d :=
  fun omega j => aux_lim_measure_spatialShift z (omega j)

/-- Pushforward commutes with a density under a measure-preserving measurable equivalence. -/
theorem aux_lim_measure_map_withDensity_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (hmp : MeasurePreserving e μ ν) (g : α → ℝ≥0∞) (hg : Measurable g) :
    Measure.map e (μ.withDensity g) = ν.withDensity (g ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    hmp.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Translating a finite chaos cutoff translates its underlying measure. -/
theorem aux_lim_measure_chaosCutoff_spatialShift
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (y : SpatialCoordinates d) :
    chaosCutoff M N (aux_lim_measure_bilateralShift (-y) omega) =
      (chaosCutoff M N omega).map (fun x => x + y) := by
  let eh : SpatialCoordinates d ≃ₜ SpatialCoordinates d := Homeomorph.addRight y
  let e : SpatialCoordinates d ≃ᵐ SpatialCoordinates d := eh.toMeasurableEquiv
  have he : MeasurePreserving e (volume : Measure (SpatialCoordinates d)) volume := by
    simpa [e, eh, Homeomorph.addRight] using! measurePreserving_add_right (volume : Measure (SpatialCoordinates d)) y
  have hden : ∀ x, fineDensity M N (aux_lim_measure_bilateralShift (-y) omega) x =
      fineDensity M N omega (e.symm x) := by
    intro x
    simp [fineDensity, finePotential, aux_lim_measure_bilateralShift,
      aux_lim_measure_spatialShift, eh, e, Homeomorph.addRight, sub_eq_add_neg,
      ← Finset.sum_apply]
  have hg : Measurable (fun x => ENNReal.ofReal
      (fineDensity M N omega (e.symm x))) := by
    exact ((continuous_fineDensity M N omega).comp eh.symm.continuous).measurable.ennreal_ofReal
  change volume.withDensity (fun x => ENNReal.ofReal
      (fineDensity M N (aux_lim_measure_bilateralShift (-y) omega) x)) = _
  rw [show (fun x => ENNReal.ofReal
      (fineDensity M N (aux_lim_measure_bilateralShift (-y) omega) x)) =
      (fun x => ENNReal.ofReal (fineDensity M N omega (e.symm x))) from funext (fun x =>
        congrArg ENNReal.ofReal (hden x))]
  change volume.withDensity
      ((fun x => ENNReal.ofReal (fineDensity M N omega x)) ∘ e.symm) = _
  rw [← aux_lim_measure_map_withDensity_equiv e volume volume he
    (fun x => ENNReal.ofReal (fineDensity M N omega x))
    ((continuous_fineDensity M N omega).measurable.ennreal_ofReal)]
  rfl

/-- The common-scale field law is invariant under spatial translations. -/
theorem aux_lim_measure_chaosSampleLaw_spatialShift
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_lim_measure_bilateralShift z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  let nu := chaosRootFieldLaw M
  have hnu : MeasurePreserving (aux_lim_measure_spatialShift z) nu.toMeasure nu.toMeasure := by
    simpa [nu, chaosRootFieldLaw, aux_lim_measure_spatialShift, ContinuousMap.compRightContinuousMap] using!
      gmc_zero_field_law_stationary M z
  have hcoord : ∀ j : ℤ,
      Measure.map (aux_lim_measure_spatialShift z)
        (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)) =
        (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)) := by
    intro j
    let a : ℝ := (3 : ℝ) ^ (-j)
    have hcomm :
        aux_lim_measure_spatialShift z ∘ layerScaling d j =
          layerScaling d j ∘ aux_lim_measure_spatialShift (a • z) := by
      ext f x
      simp [aux_lim_measure_spatialShift, layerScaling, a, smul_add]
    have hnu_a : MeasurePreserving (aux_lim_measure_spatialShift (a • z))
        nu.toMeasure nu.toMeasure := by
      simpa [nu, chaosRootFieldLaw, aux_lim_measure_spatialShift, ContinuousMap.compRightContinuousMap] using!
        gmc_zero_field_law_stationary M (a • z)
    change Measure.map (aux_lim_measure_spatialShift z)
      (Measure.map (layerScaling d j) nu.toMeasure) = Measure.map (layerScaling d j) nu.toMeasure
    rw [Measure.map_map (aux_lim_measure_spatialShift z).continuous.measurable
      (layerScaling d j).continuous.measurable, hcomm]
    rw [← Measure.map_map (layerScaling d j).continuous.measurable
      (aux_lim_measure_spatialShift (a • z)).continuous.measurable, hnu_a.map_eq]
  have hmeas : Measurable (aux_lim_measure_bilateralShift z) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (aux_lim_measure_spatialShift z).continuous.measurable.comp
      (measurable_pi_apply j)
  have hmap : Measure.map (aux_lim_measure_bilateralShift z)
      (Measure.infinitePi (fun j : ℤ =>
        (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))) =
      Measure.infinitePi (fun j : ℤ =>
        Measure.map (aux_lim_measure_spatialShift z)
          (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) := by
    exact Measure.infinitePi_map_pi _ (fun _ =>
      (aux_lim_measure_spatialShift z).continuous.measurable)
  have hnew_prob : ∀ j : ℤ, IsProbabilityMeasure
      (Measure.map (aux_lim_measure_spatialShift z)
        (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) := by
    intro j
    infer_instance
  let : ∀ j : ℤ, IsProbabilityMeasure
      (Measure.map (aux_lim_measure_spatialShift z)
        (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) := hnew_prob
  refine ⟨hmeas, ?_⟩
  change Measure.map (aux_lim_measure_bilateralShift z)
      (Measure.infinitePi (fun j : ℤ =>
        (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))) =
    Measure.infinitePi (fun j : ℤ =>
      (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
  rw [hmap]
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.infinitePi_pi (fun j : ℤ =>
        Measure.map (aux_lim_measure_spatialShift z)
          (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
      (fun j hj => ht j)]
  apply Finset.prod_congr rfl
  intro j hj
  exact congrArg (fun m : Measure C(SpatialCoordinates d, ℝ) => m (t j)) (hcoord j)

end SubdiffusiveProcess.Paper
