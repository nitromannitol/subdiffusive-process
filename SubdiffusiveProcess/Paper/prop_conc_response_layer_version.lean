module

public import SubdiffusiveProcess.Paper.prop_conc_cutoff_affine_coercivity
public import SubdiffusiveProcess.Probability.ResampledLimit
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-! # Actual relative responses on the independent layer space

The two supplied affine-response limits determine a measurable relative response
on the original layer law. All single-layer differences are simultaneous limits
of their literal cutoff counterparts. No influence or concentration bound is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Probability
open scoped Topology BigOperators ENNReal NNReal

namespace SubdiffusiveProcess.Paper
noncomputable section

variable {d : ℕ}
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
variable (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
variable (H : BilateralField d → C(SpatialCoordinates d, ℝ))
variable (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
  ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
    K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)

/-- The actual affine cutoff response in units of the observation-cell volume. -/
def aux_prop_conc_response_layer_version_value
    (N : ℕ) (om : BilateralField d) (v : Fin d → ℝ) : ℝ :=
  affineDirichletResponse (centeredCube_isBounded z hr) hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H om N z hr) v /
      (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal

/-- The literal relative cutoff response for the two supplied subsequences. -/
def aux_prop_conc_response_layer_version_cutoff
    (NE NF : ℕ → ℕ) (c : ℝ) (v : Fin d → ℝ) (n : ℕ) (om : BilateralField d) : ℝ :=
  (aux_prop_conc_response_layer_version_value model H z hr hP (NF n) om v -
    c * aux_prop_conc_response_layer_version_value model H z hr hP (NE n) om v) /
      ∑ i : Fin d,
        aux_prop_conc_response_layer_version_value model H z hr hP (NE n) om (Pi.single i 1)

/-- Every relative cutoff observable is measurable on the original layer space. -/
theorem aux_prop_conc_response_layer_version_cutoff_measurable
    (hH : Measurable H) (NE NF : ℕ → ℕ) (c : ℝ) (v : Fin d → ℝ) (n : ℕ) :
    Measurable (aux_prop_conc_response_layer_version_cutoff model H z hr hP NE NF c v n) := by
  have hvalue (N : ℕ) (p : Fin d → ℝ) :
      Measurable (fun om => aux_prop_conc_response_layer_version_value model H z hr hP N om p) :=
    (aux_prop_conc_resp_measurable model H hH N z hr hP p).div_const _
  exact ((hvalue (NF n) v).sub ((hvalue (NE n) v).const_mul c)).div
    (Finset.measurable_sum _ fun i _ => hvalue (NE n) (Pi.single i 1))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Coordinate quadratic values sum to the trace of any real matrix. -/
theorem aux_prop_conc_response_layer_version_trace (A : Matrix (Fin d) (Fin d) ℝ) :
    (∑ i : Fin d, Pi.single i (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single i 1)) = Matrix.trace A := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, ite_mul,
    zero_mul, mul_zero, one_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Both actual scalar cutoff limits and the nonzero trace give the relative cutoff limit. -/
theorem aux_prop_conc_response_layer_version_cutoff_tendsto
    (NE NF : ℕ → ℕ) (AE AF : Matrix (Fin d) (Fin d) ℝ) (om : BilateralField d)
    (hE : ∀ p : Fin d → ℝ,
      Tendsto (fun n => aux_prop_conc_response_layer_version_value model H z hr hP (NE n) om p)
        atTop (𝓝 (p ⬝ᵥ AE.mulVec p)))
    (hF : ∀ p : Fin d → ℝ,
      Tendsto (fun n => aux_prop_conc_response_layer_version_value model H z hr hP (NF n) om p)
        atTop (𝓝 (p ⬝ᵥ AF.mulVec p)))
    (htrace : Matrix.trace AE ≠ 0) (c : ℝ) (v : Fin d → ℝ) :
    Tendsto (fun n => aux_prop_conc_response_layer_version_cutoff model H z hr hP NE NF c v n om)
      atTop (𝓝 ((v ⬝ᵥ AF.mulVec v - c * (v ⬝ᵥ AE.mulVec v)) / Matrix.trace AE)) := by
  have hden := tendsto_finsetSum Finset.univ (fun i _ => hE (Pi.single i 1))
  rw [aux_prop_conc_response_layer_version_trace] at hden
  exact ((hF v).sub ((hE v).const_mul c)).div hden htrace

/-- The supplied two matrix limits have a measurable relative version and simultaneous
single-layer cutoff-difference limits, with exact transport of integrability. -/
theorem prop_conc_response_layer_version
    (hH : Measurable H) (NE NF : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure)
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ᵐ om ∂P, ∀ p : Fin d → ℝ,
      Tendsto (fun n => aux_prop_conc_response_layer_version_value model H z hr hP (NE n)
        (field om) p) atTop (𝓝 (p ⬝ᵥ (AE om).mulVec p)))
    (hAF : ∀ᵐ om ∂P, ∀ p : Fin d → ℝ,
      Tendsto (fun n => aux_prop_conc_response_layer_version_value model H z hr hP (NF n)
        (field om) p) atTop (𝓝 (p ⬝ᵥ (AF om).mulVec p)))
    (htrace : ∀ᵐ om ∂P, Matrix.trace (AE om) ≠ 0)
    (c : ℝ) (v : Fin d → ℝ) :
    ∃ f : BilateralField d → ℝ,
      Measurable f ∧
      ((fun om => (v ⬝ᵥ (AF om).mulVec v - c * (v ⬝ᵥ (AE om).mulVec v)) /
        Matrix.trace (AE om)) =ᵐ[P] f ∘ field) ∧
      (Integrable f (chaosSampleLaw model).toMeasure ↔
        Integrable (fun om => (v ⬝ᵥ (AF om).mulVec v - c * (v ⬝ᵥ (AE om).mulVec v)) /
          Matrix.trace (AE om)) P) ∧
      (∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
        Tendsto (fun n => aux_prop_conc_response_layer_version_cutoff model H z hr hP NE NF c v n om)
          atTop (𝓝 (f om))) ∧
      (∀ᵐ q ∂((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure),
        ∀ j : ℤ,
        Tendsto (fun n =>
          aux_prop_conc_response_layer_version_cutoff model H z hr hP NE NF c v n q.1 -
          aux_prop_conc_response_layer_version_cutoff model H z hr hP NE NF c v n
            (Function.update q.1 j (q.2 j))) atTop
          (𝓝 (f q.1 - f (Function.update q.1 j (q.2 j))))) := by
  let R : Ω → ℝ := fun om =>
    (v ⬝ᵥ (AF om).mulVec v - c * (v ⬝ᵥ (AE om).mulVec v)) / Matrix.trace (AE om)
  let F := aux_prop_conc_response_layer_version_cutoff model H z hr hP NE NF c v
  have hFm : ∀ n, Measurable (F n) :=
    aux_prop_conc_response_layer_version_cutoff_measurable model H z hr hP hH NE NF c v
  have hconv : ∀ᵐ om ∂P, Tendsto (fun n => F n (field om)) atTop (𝓝 (R om)) := by
    filter_upwards [hAE, hAF, htrace] with om hE hF ht
    exact aux_prop_conc_response_layer_version_cutoff_tendsto model H z hr hP NE NF
      (AE om) (AF om) (field om) hE hF ht c v
  let f := realSequenceLimit F
  have hfm : Measurable f := measurable_realSequenceLimit hFm
  have heq : f ∘ field =ᵐ[P] R := realSequenceLimit_comp_ae hconv
  have hlim : ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => F n om) atTop (𝓝 (f om)) :=
    ae_tendsto_realSequenceLimit_of_pullback hfield hFm
      (hconv.mono fun om h => ⟨R om, h⟩)
  refine ⟨f, hfm, heq.symm, ?_, hlim, ?_⟩
  · exact (hfield.integrable_comp hfm.aestronglyMeasurable).symm.trans (integrable_congr heq)
  · exact ae_tendsto_resampled_sub
      (fun j => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure) hlim

end
end SubdiffusiveProcess.Paper
