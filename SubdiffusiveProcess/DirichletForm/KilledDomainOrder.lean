import SubdiffusiveProcess.DirichletForm.KilledCoreClosure

/-! Comparable forms on the same domain have the same killed domains.
The proof compares their energy norms and compactly supported cores. -/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DirichletForm.ClosedForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}

/-- A one-sided quadratic-form bound compares the squared energy norms. -/
theorem energyNormSq_le_of_form_le
    (E F : ClosedForm mu) (C : ℝ) (hC : 0 ≤ C)
    (hform : ∀ v ∈ E.domain, F.form v v ≤ C * E.form v v)
    (v : Lp ℝ 2 mu) (hv : v ∈ E.domain) :
    F.energyNormSq v ≤ (C + 1) * E.energyNormSq v := by
  have hE := E.form_nonneg v hv
  have h := hform v hv
  dsimp only [energyNormSq]
  nlinarith only [h, hE, sq_nonneg ‖v‖, mul_nonneg hC (sq_nonneg ‖v‖)]

/-- A quadratic-form upper bound transfers every killed-domain approximation. -/
theorem killedCoreClosure_le_of_form_le
    (E F : ClosedForm mu) (hdom : E.domain = F.domain)
    (C : ℝ) (hC : 0 ≤ C)
    (hform : ∀ v ∈ E.domain, F.form v v ≤ C * E.form v v) (U : Set X) :
    E.killedCoreClosure U ≤ F.killedCoreClosure U := by
  intro v hv
  refine ⟨hdom ▸ hv.1, ?_⟩
  intro eps heps
  have hC1 : 0 < C + 1 := by linarith only [hC]
  obtain ⟨w, hw, hsmall⟩ := hv.2 (eps / (C + 1)) (div_pos heps hC1)
  refine ⟨w, ⟨hdom ▸ hw.1, hw.2⟩, ?_⟩
  have hle := energyNormSq_le_of_form_le E F C hC hform (v - w) (E.domain.sub_mem hv.1 hw.1)
  exact hle.trans_lt ((mul_lt_mul_of_pos_left hsmall hC1).trans_eq
    (mul_div_cancel₀ eps hC1.ne'))

/-- Two comparable quadratic forms with the same domain have identical killed core closures. -/
theorem killedCoreClosure_eq_of_form_bounds
    (E F : ClosedForm mu) (hdom : E.domain = F.domain)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hform : ∀ v ∈ E.domain, c * E.form v v ≤ F.form v v ∧ F.form v v ≤ C * E.form v v)
    (U : Set X) : E.killedCoreClosure U = F.killedCoreClosure U := by
  apply le_antisymm
  · exact killedCoreClosure_le_of_form_le E F hdom C hC (fun v hv => (hform v hv).2) U
  · exact killedCoreClosure_le_of_form_le F E hdom.symm c⁻¹ (inv_nonneg.mpr hc.le)
      (fun v hv => (le_inv_mul_iff₀ hc).mpr ((hform v (hdom.symm ▸ hv)).1)) U

end DirichletForm.ClosedForm
