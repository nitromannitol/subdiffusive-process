module

public import SubdiffusiveProcess.Meyers.GlueMain
public import SubdiffusiveProcess.Meyers.DimZero
public import SubdiffusiveProcess.Meyers.OneDMain

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem E2Body.mono_eps {d : ℕ} {p epsilon epsilon' C : ℝ} (h : E2Body d p epsilon C)
    (hle : epsilon' ≤ epsilon) : E2Body d p epsilon' C := by
  intro x0 l hl a a0 ha0 haM hnear F Kf hFM hKf hFb u heq
  exact h x0 l hl a a0 ha0 haM
    (hnear.mono (fun x hx => hx.trans (mul_le_mul_of_nonneg_right hle ha0.le))) F Kf hFM hKf hFb u heq

/-- `d ≥ 2`: from the exact Meyers leaf. -/
theorem e2_from_leaf {d : ℕ} (hd : 2 ≤ d) {p : ℝ} (hp : 2 ≤ p)
    (hleaf : ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 < C ∧ MeyersEstimate d p epsilon C) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 2 ∧ 0 < C ∧ E2Body d p epsilon C := by
  obtain ⟨epsilon, C0, hε, hC0, hM⟩ := hleaf
  exact ⟨min epsilon (1 / 2), glueConst d p C0, lt_min hε (by norm_num), min_le_right _ _,
    glueConst_pos hd p hC0, (e2_glue hd hp hC0 hM).mono_eps (min_le_left _ _)⟩

/-- `d ≤ 1`: direct proofs. -/
theorem e2_lowdim {d : ℕ} (hd : d < 2) {p : ℝ} (hp : 2 ≤ p) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 2 ∧ 0 < C ∧ E2Body d p epsilon C := by
  interval_cases d
  · exact ⟨1 / 2, 1, by norm_num, le_rfl, by norm_num, e2_dim_zero p (1 / 2)⟩
  · exact ⟨1 / 2, 12, by norm_num, le_rfl, by norm_num, e2_dim_one p hp⟩

end SubdiffusiveProcess.Meyers
