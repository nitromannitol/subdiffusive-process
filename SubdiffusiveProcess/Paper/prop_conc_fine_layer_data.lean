module

public import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_det
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw

@[expose] public section

/-! The fibrewise input data of the fine-layer step, abstracted from the model bookkeeping: on a probability
space `(Ω, P)` with a measurable `field` of law the chaos law, for almost every `ω` there is a pair `X` of limiting
forms on the observation cell (weighted identification: `f (update (field ω) j y) = θ_X(y - ω_j)` for a.e. layer
value `y`; masked growth: the canonical masked pairs `mask X (1_q (y - ω_j))` have the growth constant
`K (update (field ω) j y)`), together with the moment bound of the growth constant `K`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology
namespace Paper
noncomputable section

/-- The a.e. fibre data. -/
def aux_prop_conc_fine_layer_data_FD (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C0 m M : ℝ) (Q : Opens (SpatialCoordinates d))
    (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (c : ℝ) (pvec : Fin d → ℝ) (t : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (f K : BilateralField d → ℝ) (j : ℤ) : Prop :=
  ∀ᵐ omega ∂P, ∃ X : prop_conc_pair_data Q zcell r hr C0 m M,
    (∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      f (Function.update (field omega) j y) =
        aux_prop_conc_pair_data_theta X c pvec (fun x => y x - (field omega) j x)) ∧
    (∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure,
      ∀ (hw : Measurable (aux_prop_conc_fine_fibre_det_wY zcell r hr ((field omega) j) y)) (Kw : ℝ)
        (hKw : ∀ x, |aux_prop_conc_fine_fibre_det_wY zcell r hr ((field omega) j) y x| ≤ Kw),
        aux_prop_conc_pair_data_growth
          (aux_prop_conc_pair_mask_pair X (aux_prop_conc_fine_fibre_det_wY zcell r hr ((field omega) j) y)
            hw Kw hKw)
          (aux_prop_conc_pair_data_slopes d) t (K (Function.update (field omega) j y)))

/-- The standing fibre data of the fine-layer step (a `Prop` bundle; nothing is assumed about the response
beyond the two a.e. statements and the moment of `K`). -/
structure prop_conc_fine_layer_data (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C0 m M : ℝ) (Q : Opens (SpatialCoordinates d))
    (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (c : ℝ) (pvec : Fin d → ℝ) (t p B : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (f K : BilateralField d → ℝ) (j : ℤ) : Prop where
  hP : IsProbabilityMeasure P
  hfield : Measurable field
  hlaw : Measure.map field P = (chaosSampleLaw model).toMeasure
  hf : Measurable f
  hKm : AEStronglyMeasurable K (chaosSampleLaw model).toMeasure
  hK0 : ∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, 0 ≤ K eta
  hKB : eLpNorm K (ENNReal.ofReal (2 * p)) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal B
  hfd : aux_prop_conc_fine_layer_data_FD d model C0 m M Q zcell r hr c pvec t P field f K j

end
end Paper
