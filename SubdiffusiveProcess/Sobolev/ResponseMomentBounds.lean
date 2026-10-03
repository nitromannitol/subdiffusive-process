module

public import SubdiffusiveProcess.Sobolev.ResponsePositivity
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Deterministic bounds on a scalar inverse response from one competitor.
No probabilistic moment or cutoff convergence assertion is made here. -/

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace SubdiffusiveProcess

/-- A positive lower bound on a competitor's load bounds the reciprocal response. -/
theorem inverseResponse_inv_le_of_load_lower
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : PositiveCoefficient Q)
    (L : S.space →L[ℝ] ℝ) (w : S.space)
    {b : ℝ} (hb : 0 < b) (hload : b ≤ L w) :
    0 < inverseResponse S a L ∧
      (inverseResponse S a L)⁻¹ ≤ responseForm S a w w / b ^ 2 := by
  have hL : L ≠ 0 := by
    intro h
    have : b ≤ 0 := by simpa only [h, ContinuousLinearMap.zero_apply] using hload
    exact (not_le_of_gt hb) this
  have hpos := (inverseResponse_pos_iff S a L).2 hL
  have hsq : b ^ 2 ≤ (L w) ^ 2 := pow_le_pow_left₀ hb.le hload 2
  have hbound := hsq.trans (sq_load_le_inverseResponse_mul_responseForm S a L w)
  refine ⟨hpos, (le_div_iff₀ (sq_pos_of_pos hb)).2 ?_⟩
  calc
    (inverseResponse S a L)⁻¹ * b ^ 2 ≤
        (inverseResponse S a L)⁻¹ *
          (inverseResponse S a L * responseForm S a w w) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
    _ = responseForm S a w w := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- An approximation within half the source norm has a uniformly positive source pairing. -/
theorem half_sq_norm_le_inner_of_dist_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f v : E) (hclose : ‖v - f‖ ≤ ‖f‖ / 2) :
    ‖f‖ ^ 2 / 2 ≤ inner ℝ f v := by
  have hCS : |inner ℝ f (v - f)| ≤ ‖f‖ * ‖v - f‖ := abs_real_inner_le_norm f (v - f)
  have hupper := mul_le_mul_of_nonneg_left hclose (norm_nonneg f)
  have hlow := (neg_le_abs (inner ℝ f (v - f))).trans (hCS.trans hupper)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hlow
  linarith only [hlow]

/-- A source approximation gives a reciprocal response bound by its energy. -/
theorem inverseResponse_inv_le_of_source_approximation
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : PositiveCoefficient Q)
    (f : DomainL2 Q) (hf : f ≠ 0) (w : S.space)
    (hclose : ‖w.val.1 - f‖ ≤ ‖f‖ / 2) :
    0 < inverseResponse S a ((sobolevVolumeLoad f).comp S.space.subtypeL) ∧
      (inverseResponse S a ((sobolevVolumeLoad f).comp S.space.subtypeL))⁻¹ ≤
        responseForm S a w w / (‖f‖ ^ 2 / 2) ^ 2 := by
  apply inverseResponse_inv_le_of_load_lower S a _ w
    (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hf)) (by norm_num))
  exact half_sq_norm_le_inner_of_dist_le f w.val.1 hclose

end SubdiffusiveProcess
