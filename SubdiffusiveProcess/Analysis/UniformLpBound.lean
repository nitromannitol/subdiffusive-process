module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-!
# A uniform `Lᵖ`-norm bound from `Lᵖ`-relative compactness

If a family `f : ℕ → α → E` is relatively compact as a family of `Lᵖ`-space elements
(`MemLp.toLp`), it is in particular bounded in `Lᵖ` norm by a single real constant, uniformly
in the index. This module does **not** claim the converse (boundedness alone need not give
precompactness).
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A relatively-compact `Lᵖ` family has a single uniform `Lᵖ`-norm bound `B`, obtained from
metric boundedness of the compact closure via `IsCompact.isBounded`. -/
theorem uniform_eLpNorm_bound_of_compact_range (f : ℕ → α → E) (hmem : ∀ K, MemLp (f K) p μ)
    (hcompact : IsCompact (closure (Set.range (fun K => (hmem K).toLp (f K))))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ K, eLpNorm (f K) p μ ≤ ENNReal.ofReal B := by
  obtain ⟨B, hB0, hBbd⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨B, hB0.le, fun K => ?_⟩
  have hnorm := hBbd _ (subset_closure ⟨K, rfl⟩)
  rw [Lp.norm_toLp] at hnorm
  rw [← ENNReal.ofReal_toReal (hmem K).eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hnorm

/-- Scaling by a real constant of norm `≤ 1` never increases `Lᵖ` seminorm: a crude one-sided
bound, sufficient for absorbing a fixed averaging factor (e.g. the `1/2` in a polarization
identity) into a uniform bound without tracking its exact value. -/
theorem eLpNorm_const_smul_le_of_norm_le_one {F : Type*} [NormedAddCommGroup F] [Module ℝ F]
    [IsBoundedSMul ℝ F] {c : ℝ} (hc : ‖c‖ ≤ 1) (f : α → F) (q : ℝ≥0∞) (ν : Measure α) :
    eLpNorm (c • f) q ν ≤ eLpNorm f q ν := by
  calc eLpNorm (c • f) q ν ≤ ‖c‖ₑ * eLpNorm f q ν := eLpNorm_const_smul_le
    _ ≤ 1 * eLpNorm f q ν := by
        gcongr
        calc ‖c‖ₑ = ENNReal.ofReal |c| := Real.enorm_eq_ofReal_abs c
          _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by rwa [← Real.norm_eq_abs])
    _ = eLpNorm f q ν := one_mul _

end
