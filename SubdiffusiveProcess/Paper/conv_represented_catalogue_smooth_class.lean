module

public import Mathlib
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Analysis.HolderDilationToolkit
public import SubdiffusiveProcess.CutoffsBoundaryNorm

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Pair estimate implies `IsHolderOn` (copy of the private helper of the collar norm lemma). -/
theorem aux_conv_represented_catalogue_smooth_class_holder {d : ℕ} {b : ℝ} (hb : 0 < b)
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ C * (dist x y) ^ b) : IsHolderOn b S f := by
  unfold IsHolderOn
  refine ⟨C, ?_⟩
  intro v hv
  rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
  let R : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)
  have hRpos : 0 < R := by
    dsimp [R]
    apply Real.sqrt_pos.mpr
    have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
      by_contra hn
      apply hxy
      funext i
      have hi : x i - y i = 0 := by
        by_contra hi
        exact hn ⟨i, hi⟩
      linarith
    obtain ⟨i, hi⟩ := hne
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg _
    · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hRE : dist x y ≤ R := by
    simpa [R, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.norm_le_euclideanNorm (x - y))
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos b)).2
  exact (hpair x hx y hy).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hRE hb.le) hC)

/-- Points of the frontier of the unit cube lie at sup-distance `1/2` from the origin. -/
theorem aux_conv_represented_catalogue_smooth_class_frontier {d : ℕ} (x : SpatialCoordinates d)
    (hx : x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) : dist x 0 = 1 / 2 := by
  change x ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) at hx
  rw [frontier_ball _ (by norm_num), Metric.mem_sphere] at hx
  exact hx

/-- **Smooth data are boundary-class data (used to feed the absolute trace estimate).**  Every
`C^∞` function on `ℝ^d` lies in the `β`-cell boundary class of every cube, for `0 < β ≤ 1`. -/
theorem conv_represented_catalogue_smooth_class {d : ℕ} (beta : ℝ) (hb0 : 0 < beta)
    (hb1 : beta ≤ 1) (z : SpatialCoordinates d) (r : ℝ) (theta : SpatialCoordinates d → ℝ)
    (hth : ContDiff ℝ ∞ theta) : IsCellBoundaryClass beta z r theta := by
  set G : SpatialCoordinates d → ℝ := rescaledDatum z r theta with hG
  have hGeq : G = fun y => theta (cubeDilation z 0 r y) := by
    rw [hG]
    funext y
    unfold rescaledDatum
    congr 1
    funext i
    simp [cubeDilation]
  have hdil : ContDiff ℝ ∞ (cubeDilation z (0 : SpatialCoordinates d) r) := by
    refine contDiff_pi.2 fun i => ?_
    simp only [cubeDilation]
    exact contDiff_const.add (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))
  have hGs : ContDiff ℝ ∞ G := by rw [hGeq]; exact hth.comp hdil
  set K : Set (SpatialCoordinates d) := Metric.closedBall (0 : SpatialCoordinates d) 1 with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hderiv : ContinuousOn (fderiv ℝ G) K := (hGs.continuous_fderiv (by simp)).continuousOn
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hderiv
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hGs.continuous.continuousOn
  have hdiff : ∀ x : SpatialCoordinates d, DifferentiableAt ℝ G x :=
    fun x => (hGs.differentiable (by simp)) x
  have hSK : frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) ⊆ K := by
    intro x hx
    rw [hK, Metric.mem_closedBall, aux_conv_represented_catalogue_smooth_class_frontier x hx]
    norm_num
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hpair : ∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1
        one_pos : Set (SpatialCoordinates d)), |G x - G y| ≤ max C 0 * (dist x y) ^ beta := by
    intro x hx y hy
    have hxK := hSK hx
    have hyK := hSK hy
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := G) (s := K) (C := max C 0)
      (fun x _ => hdiff x) (fun x hx => (hC x hx).trans (le_max_left _ _))
      (convex_closedBall (0 : SpatialCoordinates d) 1) hyK hxK
    have hdist : dist x y ≤ 1 := by
      have h1 := aux_conv_represented_catalogue_smooth_class_frontier x hx
      have h2 := aux_conv_represented_catalogue_smooth_class_frontier y hy
      calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
        _ = 1 := by rw [h1, dist_comm 0 y, h2]; norm_num
    calc |G x - G y| = ‖G x - G y‖ := (Real.norm_eq_abs _).symm
      _ ≤ max C 0 * ‖x - y‖ := hmv
      _ = max C 0 * dist x y := by rw [dist_eq_norm]
      _ ≤ max C 0 * (dist x y) ^ beta :=
        mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg hdist hb1) hC0
  refine ⟨aux_conv_represented_catalogue_smooth_class_holder hb0 _ G (max C 0) hC0 hpair, ?_⟩
  refine ⟨max B 0, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  exact (hB x (hSK hx)).trans (le_max_left _ _)

end Paper
