module

public import SubdiffusiveProcess.Geometry.CoordinateFold
@[expose] public section

open Set TopologicalSpace
namespace SubdiffusiveProcess

/-- Projection onto a newly active nearest face moves the center by its actual face distance. A cube of side s is covered after increasing the side by twice that distance; geometric radii increase by the distance itself. -/
theorem nearestFace_projection_distance_and_cover
    {d : ℕ} (x : SpatialCoordinates d)
    (hx : ∀ j : Fin d, |x j| < (1 / 2 : ℝ))
    (I P : Finset (Fin d)) (hP : ∀ j : Fin d, j ∈ P ↔ 0 ≤ x j)
    (i : Fin d) (hi : i ∉ I) :
    let z : SpatialCoordinates d := fun j =>
      if j ∈ I then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
    let z' : SpatialCoordinates d := fun j =>
      if j ∈ insert i I then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
    dist z z' = (1 / 2 : ℝ) - |x i| ∧
      ∀ s : ℝ, 0 < s →
        Metric.ball z (s / 2) ⊆
          Metric.ball z' ((s + 2 * ((1 / 2 : ℝ) - |x i|)) / 2) := by
  dsimp only
  have hdist :
      dist (fun j : Fin d =>
          if j ∈ I then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j)
        (fun j : Fin d =>
          if j ∈ insert i I then
            (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j) =
        (1 / 2 : ℝ) - |x i| := by
    classical
    let δ : NNReal := ⟨(1 / 2 : ℝ) - abs (x i), sub_nonneg.mpr (hx i).le⟩
    have hcoord : ∀ b : Fin d,
        nndist
            (if b ∈ I then (if b ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x b)
            (if b ∈ insert i I then
              (if b ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x b) =
          if b = i then δ else 0 := by
      intro b
      by_cases hbi : b = i
      · subst b
        simp only [hi, Finset.mem_insert, true_or, ite_false, ite_true, hP]
        apply NNReal.eq
        change |x i - (if 0 ≤ x i then (1 / 2 : ℝ) else -(1 / 2 : ℝ))| =
          (1 / 2 : ℝ) - |x i|
        by_cases hxi : 0 ≤ x i
        · rw [ite_eq_left hxi, abs_of_nonneg hxi]
          rw [abs_of_nonpos]
          · ring
          · linarith [(abs_lt.mp (hx i)).2]
        · rw [ite_eq_right hxi, abs_of_neg (lt_of_not_ge hxi)]
          rw [abs_of_nonneg]
          · ring
          · linarith [(abs_lt.mp (hx i)).1]
      · by_cases hbI : b ∈ I <;> simp [Finset.mem_insert, hbi, hbI]
    rw [dist_pi_def]
    simp_rw [hcoord]
    rw [Finset.sup_ite]
    have hfilter : Finset.filter (fun b : Fin d => b = i) Finset.univ = {i} := by
      ext b
      simp [eq_comm]
    rw [hfilter]
    have hz : (Finset.filter (fun b : Fin d => ¬ b = i) Finset.univ).sup
        (fun _ => (0 : NNReal)) = 0 :=
      le_antisymm Finset.sup_const_le bot_le
    rw [Finset.sup_singleton, hz, max_eq_left (show (0 : NNReal) ≤ δ from bot_le)]
    rfl
  refine ⟨hdist, ?_⟩
  intro s hs
  apply Metric.ball_subset_ball'
  rw [hdist]
  ring_nf
  exact le_rfl

end SubdiffusiveProcess
