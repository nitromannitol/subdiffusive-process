module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic

@[expose] public section

/-! This module establishes ps eta exists for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- ps layers potential in the finite stopping construction. -/
theorem ps_layers_potential
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ k : ℤ,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, ∀ x, g x = omega k x := by

  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
  have h_forget_cont : Continuous forget := forget.continuous
  have h_forget_meas : Measurable forget := h_forget_cont.measurable
  have h_forget_inj : Function.Injective forget := by
    intro g h h_eq
    apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
    intro x
    have hx := congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x) h_eq
    simpa only [ContinuousMap.coe_mk, forget] using! hx
  have h_forget_emb : MeasurableEmbedding forget :=
    h_forget_meas.measurableEmbedding h_forget_inj
  let S : Set (C(SpatialCoordinates d, ℝ)) := Set.range forget
  have hS_meas : MeasurableSet S := h_forget_emb.measurableSet_range

  have hS_layer (j : ℤ) (f : C(SpatialCoordinates d, ℝ)) (hf : f ∈ S) :
      SubdiffusiveProcess.layerScaling d j f ∈ S := by
    rcases hf with ⟨g, rfl⟩
    refine ⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)) g, ?_⟩
    ext x
    simp only [zpow_neg, ContinuousMap.coe_mk, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply, layerScaling, ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply, forget]
    rfl

  have h_layer_forget_eq (j : ℤ) (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (x : SpatialCoordinates d) :
      (SubdiffusiveProcess.layerScaling d j ∘ forget) g x =
      (forget ∘ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)))) g x := by
    simp only [layerScaling, zpow_neg, ContinuousMap.coe_mk, Function.comp_apply, ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply, forget]
    rfl

  have h_forget_meas' : Measurable forget := h_forget_cont.measurable
  have h_layer_meas' (j : ℤ) : Measurable (SubdiffusiveProcess.layerScaling d j) :=
    (SubdiffusiveProcess.layerScaling d j).continuous.measurable

  have h_layer_ae (j : ℤ) : ∀ᵐ f ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      f ∈ S := by
    have h_map_eq : (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure =
        ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure).map
          (forget ∘ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)))) := by
      calc
        (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure =
            ((chaosRootFieldLaw model).toMeasure).map
              (SubdiffusiveProcess.layerScaling d j) := by
          rw [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
        _ = (((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure).map
              forget).map
              (SubdiffusiveProcess.layerScaling d j) := by
          rw [chaosRootFieldLaw, ProbabilityMeasure.toMeasure_map]
        _ = ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure).map
              (SubdiffusiveProcess.layerScaling d j ∘ forget) := by
          exact Measure.map_map (h_layer_meas' j) h_forget_meas'
        _ = ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure).map
              (forget ∘ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)))) := by
          have h_eq_fun : (SubdiffusiveProcess.layerScaling d j ∘ forget) =
              (forget ∘ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)))) := by
            ext g x
            exact h_layer_forget_eq j g x
          rw [h_eq_fun]
    rw [h_map_eq]
    have h_meas_f : Measurable
        (forget ∘ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)))) :=
      h_forget_meas'.comp
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale ((3:ℝ)^(-j))).measurable
    have h_meas_f_aemeas : AEMeasurable
        (forget ∘ (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j))))
        ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure) :=
      h_meas_f.aemeasurable
    refine ((ae_map_iff h_meas_f_aemeas hS_meas).mpr ?_)
    filter_upwards with x
    exact ⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3:ℝ)^(-j)) x, rfl⟩

  have h_infinitePi_ae : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ k : ℤ, omega k ∈ S := by
    rw [ae_all_iff]
    intro k
    have h_eval_meas : Measurable (fun (omega : ℤ → C(SpatialCoordinates d, ℝ)) => omega k) :=
      measurable_pi_apply k
    have h_pi_meas : MeasurableSet {f : C(SpatialCoordinates d, ℝ) | f ∈ S} := hS_meas
    rw [← ae_map_iff h_eval_meas.aemeasurable h_pi_meas]
    dsimp [chaosSampleLaw, SubdiffusiveProcess.commonScaleLaw]
    have h_map := Measure.infinitePi_map_eval
      (μ := fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) j : Measure C(SpatialCoordinates d, ℝ))) k
    rw [h_map]
    exact h_layer_ae k

  filter_upwards [h_infinitePi_ae] with omega hS
  intro k
  rcases hS k with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro x
  have hx := congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x) hg
  simpa only [ContinuousMap.coe_mk, forget] using! hx

/-- ps eta exists of layers in the finite stopping construction. -/
theorem ps_eta_exists_of_layers
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hlay : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ k : ℤ,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, ∀ x, g x = omega k x) :
    ∃ eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x) := by
  classical
  let zero : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    ⟨((0 : C(Homogenization.Vec d, ℝ)),
      (0 : C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ))), by
      constructor
      · intro x
        simpa only [ContinuousMap.coe_zero, ContinuousMap.zero_apply] using!
          hasFDerivAt_const (0 : ℝ) x
      · intro K hK
        exact ⟨0, by simp only [LipschitzOnWith, ContinuousMap.zero_apply,
          edist_self, ENNReal.coe_zero, zero_mul, le_refl, implies_true]⟩⟩
  let select (omega : BilateralField d) (k : ℤ) : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    if h : ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, ∀ x, g x = omega k x
      then h.choose else zero
  refine ⟨fun N omega i => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale
    ((3 : ℝ) ^ (-(N : ℤ))) (select omega ((i : ℤ) - (N : ℤ))), ?_⟩
  filter_upwards [hlay] with omega hom
  intro N i x
  have hselect : select omega ((i : ℤ) - (N : ℤ)) =
      (hom ((i : ℤ) - (N : ℤ))).choose := dif_pos _
  change (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3 : ℝ) ^ (-(N : ℤ)))
    (select omega ((i : ℤ) - (N : ℤ)))) x = _
  rw [hselect, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply]
  exact (hom ((i : ℤ) - (N : ℤ))).choose_spec ((3 : ℝ) ^ (-(N : ℤ)) • x)

/-- ps eta exists in the finite stopping construction. -/
theorem ps_eta_exists
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∃ eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x) :=
  SubdiffusiveProcess.FiniteStopping.ps_eta_exists_of_layers model (SubdiffusiveProcess.FiniteStopping.ps_layers_potential model)

end SubdiffusiveProcess.FiniteStopping
