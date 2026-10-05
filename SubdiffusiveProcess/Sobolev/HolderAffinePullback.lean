module

public import SubdiffusiveProcess.Sobolev.NormalizedBoundaryHolder
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison

@[expose] public section

/-! This module proves Hölder preservation under positive affine pullback and its unit-cube
specialization. It does not give any extension or regularity result beyond these setwise bounds.
-/

open Set MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess

private theorem affinePullback_injective {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) {x y : SpatialCoordinates d}
    (hxy : z + r • x = z + r • y) : x = y := by
  apply funext
  intro j
  have hj := congrArg (fun w : SpatialCoordinates d => w j) hxy
  have hcoord : z j + r * x j = z j + r * y j := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hj
  have hmul : r * x j = r * y j := by
    linarith only [hcoord]
  exact (mul_left_cancel₀ hr.ne' hmul)

private theorem affinePullback_euclideanDistance {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, ((z + r • x) j - (z + r • y) j) ^ 2) =
      r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  have hcoord : ∀ j : Fin d,
      (z + r • x) j - (z + r • y) j = r * (x j - y j) := by
    intro j
    have hxj : (z + r • x) j = z j + r * x j := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hyj : (z + r • y) j = z j + r * y j := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith only [hxj, hyj]
  have hsum :
      (∑ j : Fin d, ((z + r • x) j - (z + r • y) j) ^ 2) =
        r ^ 2 * (∑ j : Fin d, (x j - y j) ^ 2) := by
    calc
      _ = ∑ j : Fin d, (r * (x j - y j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoord j]
      _ = ∑ j : Fin d, r ^ 2 * (x j - y j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_pow]
      _ = r ^ 2 * (∑ j : Fin d, (x j - y j) ^ 2) := by
        rw [Finset.mul_sum]
  calc
    Real.sqrt (∑ j : Fin d, ((z + r • x) j - (z + r • y) j) ^ 2) =
        Real.sqrt (r ^ 2 * (∑ j : Fin d, (x j - y j) ^ 2)) := by rw [hsum]
    _ = Real.sqrt (r ^ 2) * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      Real.sqrt_mul (sq_nonneg r) _
    _ = r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]

private theorem affinePullback_mem_closure_ball {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {x : SpatialCoordinates d}
    (hx : x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :
    z + r • x ∈ closure (Metric.ball z (r / 2)) := by
  have hxnorm : ‖x‖ ≤ 1 / 2 := by
    change dist x 0 ≤ 1 / 2 at hx
    simpa only [dist_eq_norm, sub_zero] using hx
  rw [closure_ball z (ne_of_gt (half_pos hr))]
  change dist (z + r • x) z ≤ r / 2
  calc
    dist (z + r • x) z = ‖r • x‖ := by
      rw [dist_eq_norm]
      congr 1
      simp only [add_sub_cancel_left]
    _ = ‖r‖ * ‖x‖ := norm_smul _ _
    _ = r * ‖x‖ := by rw [Real.norm_eq_abs, abs_of_pos hr]
    _ ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left hxnorm hr.le
    _ = r / 2 := by ring

/-- Positive affine pullback and subtraction of a constant preserve setwise Hölder regularity. -/
theorem isHolderOn_comp_affine_sub_const
    {d : ℕ} (alpha : ℝ) (S T : Set (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r c : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ)
    (hMap : MapsTo (fun x => z + r • x) S T) (hU : IsHolderOn alpha T U) :
    IsHolderOn alpha S (fun x => U (z + r • x) - c) := by
  let F : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
  have hV : IsHolderOn alpha S (fun x => U (F x)) := by
    unfold IsHolderOn at hU ⊢
    obtain ⟨K, hK⟩ := hU
    refine ⟨r ^ alpha * max K 0, ?_⟩
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    have hFxy : F x ≠ F y := by
      intro h
      exact hxy (affinePullback_injective z hr h)
    have he : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
      sqrt_sum_sq_sub_pos hxy
    have hscale :
        Real.sqrt (∑ j : Fin d, (F x j - F y j) ^ 2) =
          r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      exact affinePullback_euclideanDistance z hr x y
    have hphysical :
        |U (F x) - U (F y)| /
          (Real.sqrt (∑ j : Fin d, (F x j - F y j) ^ 2)) ^ alpha ≤ K :=
      hK ⟨F x, hMap hx, F y, hMap hy, hFxy, rfl⟩
    rw [hscale] at hphysical
    have hdenom :
        (r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha =
          r ^ alpha * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.mul_rpow hr.le (Real.sqrt_nonneg _)
    have hphysicalNum :
        |U (F x) - U (F y)| ≤
          (r ^ alpha * max K 0) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
      have hnum : |U (F x) - U (F y)| ≤ K *
          (r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
        (div_le_iff₀ (Real.rpow_pos_of_pos (mul_pos hr he) alpha)).mp hphysical
      rw [hdenom] at hnum
      calc
        |U (F x) - U (F y)| ≤
            (r ^ alpha * K) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
          calc
            _ ≤ K * (r ^ alpha *
                (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := hnum
            _ = (r ^ alpha * K) *
                (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by ring
        _ ≤ (r ^ alpha * max K 0) *
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_left K 0)
              (Real.rpow_nonneg hr.le alpha))
            (Real.rpow_nonneg (Real.sqrt_nonneg _) alpha)
    have hquot :
        |U (F x) - U (F y)| /
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤
          r ^ alpha * max K 0 :=
      (div_le_iff₀ (Real.rpow_pos_of_pos he alpha)).2 hphysicalNum
    exact hquot
  exact (FiniteStopping.isHolderOn_sub_const alpha (fun x => U (F x)) c).mpr hV

/-- A Hölder function on the physical closed cube pulls back to the normalized unit cube. -/
theorem isHolderOn_normalized_cube
    {d : ℕ} (alpha : ℝ) (z : SpatialCoordinates d) (r c : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ)
    (hU : IsHolderOn alpha (closure (Metric.ball z (r / 2))) U) :
    IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + r • x) - c) := by
  apply isHolderOn_comp_affine_sub_const alpha
    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
    (closure (Metric.ball z (r / 2))) z r c hr U ?_ hU
  intro x hx
  exact affinePullback_mem_closure_ball z hr hx

end SubdiffusiveProcess
