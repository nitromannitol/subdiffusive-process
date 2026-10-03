module

public import SubdiffusiveProcess.Geometry.ReflectionCalculus
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Tactic

@[expose] public section

/-! # The literal coordinate fold and its compact root

`I` selects the active planes and `P` the negatively oriented half-spaces.
Thus the prescribed sign is minus one on `P` and plus one elsewhere. The
fold preserves distance to the center but is generally not injective.
-/
open Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Fold the selected coordinates onto their prescribed signed half-spaces. -/
def coordinateFold (z : SpatialCoordinates d) (I P : Finset (Fin d))
    (x : SpatialCoordinates d) : SpatialCoordinates d :=
  fun i => if i ∈ I then z i + coordinateReflectionSign P i * |x i - z i| else x i

/-- Each folded coordinate retains its distance from its center coordinate. -/
theorem coordinateFold_abs_sub_center (z x : SpatialCoordinates d)
    (I P : Finset (Fin d)) (i : Fin d) :
    |coordinateFold z I P x i - z i| = |x i - z i| := by
  by_cases hi : i ∈ I
  · simp only [coordinateFold, hi, if_pos, add_sub_cancel_left, abs_mul, abs_abs]
    unfold coordinateReflectionSign
    split_ifs <;> norm_num
  · simp only [coordinateFold, hi, if_false]

/-- The fold preserves distance from the root center in the spatial cube norm. -/
theorem coordinateFold_dist_center (z x : SpatialCoordinates d) (I P : Finset (Fin d)) :
    dist (coordinateFold z I P x) z = dist x z := by
  simp only [dist_pi_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply Subtype.ext
  change dist (coordinateFold z I P x i) (z i) = dist (x i) (z i)
  simpa only [Real.dist_eq] using coordinateFold_abs_sub_center z x I P i

/-- The coordinate fold is nonexpansive in the spatial maximum norm. -/
theorem coordinateFold_nonexpansive (z : SpatialCoordinates d) (I P : Finset (Fin d))
    (x y : SpatialCoordinates d) :
    dist (coordinateFold z I P x) (coordinateFold z I P y) ≤ dist x y := by
  by_cases hne : Nonempty (Fin d)
  · rw [dist_pi_le_iff' (β := Fin d)]
    intro i
    unfold coordinateFold
    by_cases hi : i ∈ I
    · simp only [hi, if_pos]
      rw [Real.dist_eq]
      simp [add_sub_add_left_eq_sub]
      -- goal: |coordinateReflectionSign P i * |x i - z i| - coordinateReflectionSign P i * |y i - z i|| ≤ dist x y
      rw [← mul_sub, abs_mul]
      have habs : |coordinateReflectionSign P i| = 1 := by
        unfold coordinateReflectionSign
        split_ifs <;> simp
      rw [habs, one_mul]
      -- goal: |(|x i - z i| - |y i - z i|)| ≤ dist x y
      calc
        |(|x i - z i| - |y i - z i|)| ≤ |(x i - z i) - (y i - z i)| :=
          abs_abs_sub_abs_le_abs_sub (x i - z i) (y i - z i)
        _ = |x i - y i| := by ring_nf
        _ = dist (x i) (y i) := by rw [Real.dist_eq]
        _ ≤ dist x y := (dist_pi_le_iff' (f := x) (g := y)).mp le_rfl i
    · simp only [hi, if_false]
      -- goal: dist (x i) (y i) ≤ dist x y
      have h := (dist_pi_le_iff' (f := x) (g := y)).mp le_rfl i
      rwa [Real.dist_eq] at h
  · -- Fin d is empty (d = 0), so both sides are 0
    have h_empty : IsEmpty (Fin d) := not_nonempty_iff.mp hne
    have hxy : x = y := by
      ext i
      exact h_empty.elim i
    simp [hxy]

/-- The fold is continuous, including along all active planes. -/
theorem coordinateFold_continuous (z : SpatialCoordinates d) (I P : Finset (Fin d)) :
    Continuous (coordinateFold z I P) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ I
  · simpa only [coordinateFold, hi, if_pos] using!
      (continuous_const.add (continuous_const.mul
        ((continuous_apply i).sub continuous_const).abs) :
        Continuous (fun x : SpatialCoordinates d =>
          z i + coordinateReflectionSign P i * |x i - z i|))
  · simpa only [coordinateFold, hi, if_false] using (continuous_apply i :
      Continuous (fun x : SpatialCoordinates d => x i))

/-- The actual closed cube enclosing the finite-cutoff observation domain. -/
def closedCube (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r) :
    Compacts (SpatialCoordinates d) :=
  ⟨Metric.closedBall z (r / 2), isCompact_closedBall z (r / 2)⟩

/-- The original open cube is contained in its compact root. -/
theorem centeredCube_subset_closedCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr :=
  Metric.ball_subset_closedBall

/-- The folded point stays inside the same compact root. -/
theorem coordinateFold_mem_closedCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I P : Finset (Fin d)) {x : SpatialCoordinates d} (hx : x ∈ closedCube z r hr) :
    coordinateFold z I P x ∈ closedCube z r hr := by
  change dist (coordinateFold z I P x) z ≤ r / 2
  rw [coordinateFold_dist_center]
  exact hx

/-- The continuous fold as a self-map of the actual compact cube. -/
def coordinateFoldOnCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I P : Finset (Fin d)) : C(closedCube z r hr, closedCube z r hr) where
  toFun x := ⟨coordinateFold z I P x, coordinateFold_mem_closedCube z hr I P x.property⟩
  continuous_toFun := ((coordinateFold_continuous z I P).comp continuous_subtype_val).subtype_mk _

/-- The compact-root self-map is exactly the prescribed fold. -/
theorem coordinateFoldOnCube_coe (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (I P : Finset (Fin d)) (x : closedCube z r hr) :
    (coordinateFoldOnCube z hr I P x : SpatialCoordinates d) = coordinateFold z I P x := rfl

end SubdiffusiveProcess
