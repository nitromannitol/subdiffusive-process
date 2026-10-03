module

public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_moments
public import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_det

@[expose] public section

/-! The layer-norm moments of `prop_conc_fine_layer_moments` for the actual model `M`, in the two forms used
by the fine-layer step: as a function of the chaos configuration `η ↦ S(η j)`, and as a function of the layer
value `y` under the layer law.  The disorder is `model.delta ∈ (0, 1/2]`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

theorem prop_conc_fine_layer_mom (d : ℕ) (hd : 2 ≤ d)
    (q κ lam γ : ℝ) (hq : 0 < q) (hκ : 0 ≤ κ) (hlam : 0 ≤ lam) (hγ : 0 < γ) :
    ∃ Cm : ℝ, 0 < Cm ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (zcell : SpatialCoordinates d) (k n : ℕ) (r : ℝ)
        (_hrk : r = (3 : ℝ) ^ (-(k : ℝ))) (j : ℤ) (_hj : j = -((n + k : ℕ) : ℤ)),
        eLpNorm (fun eta : BilateralField d =>
            (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) ^ κ *
              Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
          (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Cm * model.delta ^ κ * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) ∧
        eLpNorm (fun y : C(SpatialCoordinates d, ℝ) =>
            (aux_prop_conc_fine_fibre_det_S zcell r y) ^ κ *
              Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r y))
          (ENNReal.ofReal q) (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure ≤
          ENNReal.ofReal (Cm * model.delta ^ κ * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) := by
  obtain ⟨Cm, hCm, hM⟩ := prop_conc_fine_layer_moments d hd q κ lam γ hq hκ hlam hγ
  refine ⟨Cm, hCm, ?_⟩
  intro _ _ model zcell k n r hrk j hj
  have hδ0 : 0 < model.delta := model.shellPrefix.delta_pos
  have hδ1 : model.delta ≤ 1 := model.shellPrefix.delta_le_half.trans (by norm_num)
  have h1 := hM model.delta hδ0 hδ1 model.P model.G1 model.G2 zcell k n
  have hjc : j = -((n + k : ℕ) : ℤ) := hj
  have hS : ∀ y : C(SpatialCoordinates d, ℝ), aux_prop_conc_fine_fibre_det_S zcell r y =
      sSup ((fun x : SpatialCoordinates d => ‖y x‖) '' Metric.closedBall zcell (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2)) := by
    intro y
    rw [hrk]
    exact aux_lem_15_u_supn_eq_sSup _ _ y
  have hchaos : eLpNorm (fun eta : BilateralField d =>
            (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) ^ κ *
              Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r (eta j)))
          (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (Cm * model.delta ^ κ * ((3 : ℝ) ^ (-(n : ℝ))) ^ (-γ)) := by
    have e : (fun eta : BilateralField d =>
            (aux_prop_conc_fine_fibre_det_S zcell r (eta j)) ^ κ *
              Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r (eta j))) =
        (fun omega : BilateralField d =>
          (sSup ((fun x : SpatialCoordinates d => ‖omega (-((n + k : ℕ) : ℤ)) x‖) ''
              Metric.closedBall zcell (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2))) ^ κ *
            Real.exp (lam * sSup ((fun x : SpatialCoordinates d => ‖omega (-((n + k : ℕ) : ℤ)) x‖) ''
              Metric.closedBall zcell (3 * (3 : ℝ) ^ (-(k : ℝ)) / 2)))) := by
      funext eta
      rw [hS, hjc]
    rw [e]
    exact h1
  refine ⟨hchaos, ?_⟩
  -- transfer to the layer law
  have hmeas : Measurable (fun y : C(SpatialCoordinates d, ℝ) =>
      (aux_prop_conc_fine_fibre_det_S zcell r y) ^ κ *
        Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r y)) := by
    have hSm : Measurable (fun y : C(SpatialCoordinates d, ℝ) => aux_prop_conc_fine_fibre_det_S zcell r y) :=
      (aux_lem_15_u_supn_continuous _ _).measurable
    exact (hSm.pow_const κ).mul (Real.measurable_exp.comp (hSm.const_mul lam))
  have hlayer : (chaosSampleLaw model).toMeasure.map (fun eta : BilateralField d => eta j) =
      (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure :=
    Measure.infinitePi_map_eval (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) i : Measure C(SpatialCoordinates d, ℝ))) j
  have h := eLpNorm_map_measure (μ := (chaosSampleLaw model).toMeasure) (p := ENNReal.ofReal q)
    (f := fun eta : BilateralField d => eta j)
    (g := fun y : C(SpatialCoordinates d, ℝ) => (aux_prop_conc_fine_fibre_det_S zcell r y) ^ κ *
      Real.exp (lam * aux_prop_conc_fine_fibre_det_S zcell r y))
    (by rw [hlayer]; exact hmeas.aestronglyMeasurable) (measurable_pi_apply j).aemeasurable
  rw [hlayer] at h
  rw [h]
  exact hchaos

end
end Paper
