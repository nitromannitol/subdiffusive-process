module

public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.paper_responses_bank

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Replace only the numerical moment constant and its proofs by the uniform
GMC response theorem. All actual fields of the supplied witness are retained. -/
noncomputable def aux_thm_prop_responses_with_uniform_constant
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} (R : in_responses d M) : in_responses d M := by
  have hcoeff (m : ℕ) (om : BilateralField d) : R.coeffAt m om =
      fun x => Homogenization.scalarMatrix
        (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
          ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
    funext x
    rw [R.coeffAt_eq, R.coeffScalar_eq]
  have hIG (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d) :
      IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = Homogenization.ResponseJ
          (centeredCube y ((3 : ℝ) ^ m) (by positivity) : Set (Homogenization.Vec d))
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) • e)
          (fun x => Homogenization.scalarMatrix
            (Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
              ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))}
        (R.defect m y om) := by
    have h := R.defect_isGreatest m y om
    rw [R.cubeAt_eq m y (by positivity), hcoeff m om] at h
    exact h
  exact { R with
    C := aux_rbpf_C0 d
    C_pos := (aux_rbpf_C0_spec d).1
    defect_memLp := fun xi hxi hbound m y =>
      (aux_rbpf_defect_moment hd M R.defect R.defect_nonneg hIG xi hxi hbound m y).1
    moment := fun xi hxi hbound m y =>
      (aux_rbpf_defect_moment hd M R.defect R.defect_nonneg hIG xi hxi hbound m y).2 }

/-- The constant is chosen before all measurable instances and models, exactly
as required by the coherent-prefix and base-good-event suppliers. -/
theorem aux_thm_prop_uniform_response_input (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (R : in_responses d M),
        ∃ R' : in_responses d M,
          R'.C = Cresp ∧ R'.defect = R.defect ∧ R'.coeffAt = R.coeffAt ∧
          R'.coeffScalar = R.coeffScalar ∧ R'.cubeAt = R.cubeAt ∧
          R'.bRef = R.bRef ∧ R'.refScalar = R.refScalar := by
  refine ⟨aux_rbpf_C0 d, (aux_rbpf_C0_spec d).1, ?_⟩
  intro _ _ M R
  exact ⟨aux_thm_prop_responses_with_uniform_constant hd R, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The uniform-response input, factored out of `thm_prop` (a pure move) so that the density
chain can use it without importing `thm_prop`. -/
theorem uniform_response_input (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (R : in_responses d M),
        ∃ R' : in_responses d M,
          R'.C = Cresp ∧ R'.defect = R.defect ∧ R'.coeffAt = R.coeffAt ∧
          R'.coeffScalar = R.coeffScalar ∧ R'.cubeAt = R.cubeAt ∧
          R'.bRef = R.bRef ∧ R'.refScalar = R.refScalar :=
  aux_thm_prop_uniform_response_input d hd

end SubdiffusiveProcess.Paper
