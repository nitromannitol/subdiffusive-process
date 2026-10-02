import Mathlib
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Geometry.Cube

open Set
open scoped Topology
open SubdiffusiveProcess

noncomputable section
namespace Paper

/-- A continuous function on a preconnected set that takes values in [0,1]
and never takes a value in (0,1) is constant 0 or constant 1. -/
theorem aux_cutoffs_plateau_constant_on_preconnected {α : Type*} [TopologicalSpace α]
    {S : Set α} (hS_conn : IsPreconnected S)
    {θ : α → ℝ} (hθ_cont : ContinuousOn θ S)
    (hθ_range : ∀ x ∈ S, 0 ≤ θ x ∧ θ x ≤ 1)
    (hθ_no_mid : ¬∃ x ∈ S, 0 < θ x ∧ θ x < 1) :
    (∀ x ∈ S, θ x = 0) ∨ (∀ x ∈ S, θ x = 1) := by
  -- From hθ_range and hθ_no_mid, every value on S is either 0 or 1
  have hθ_binary : ∀ x ∈ S, θ x = 0 ∨ θ x = 1 := by
    intro x hx
    rcases hθ_range x hx with ⟨hx0, hx1⟩
    by_cases hx0' : θ x = 0
    · exact Or.inl hx0'
    · have hxpos : 0 < θ x := lt_of_le_of_ne hx0 (Ne.symm hx0')
      by_cases hx1' : θ x = 1
      · exact Or.inr hx1'
      · have hxlt1 : θ x < 1 := lt_of_le_of_ne hx1 hx1'
        exact absurd ⟨x, hx, hxpos, hxlt1⟩ hθ_no_mid
  -- The image θ '' S is preconnected (by continuity)
  have h_image_conn : IsPreconnected (θ '' S) :=
    hS_conn.image θ hθ_cont
  -- If the image contains both 0 and 1, we get a contradiction with preconnectedness
  by_cases h0 : (0 : ℝ) ∈ θ '' S
  · by_cases h1 : (1 : ℝ) ∈ θ '' S
    · -- Both 0 and 1 are in the image; derive a contradiction using IsPreconnected
      have hU_open : IsOpen (Set.Iio (1/2 : ℝ)) := isOpen_Iio
      have hV_open : IsOpen (Set.Ioi (1/2 : ℝ)) := isOpen_Ioi
      have h_cover : θ '' S ⊆ Set.Iio (1/2 : ℝ) ∪ Set.Ioi (1/2 : ℝ) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hθ_binary x hx with (h | h)
        · rw [h]
          exact Or.inl (by norm_num)
        · rw [h]
          exact Or.inr (by norm_num)
      have h_nonempty_U : (θ '' S ∩ Set.Iio (1/2 : ℝ)).Nonempty := by
        rcases h0 with ⟨x, hx, hx0⟩
        refine ⟨0, ⟨x, hx, hx0⟩, ?_⟩
        norm_num
      have h_nonempty_V : (θ '' S ∩ Set.Ioi (1/2 : ℝ)).Nonempty := by
        rcases h1 with ⟨x, hx, hx1⟩
        refine ⟨1, ⟨x, hx, hx1⟩, ?_⟩
        norm_num
      have h_empty_inter : ¬ (θ '' S ∩ (Set.Iio (1/2 : ℝ) ∩ Set.Ioi (1/2 : ℝ))).Nonempty := by
        rintro ⟨y, ⟨hy, hyU, hyV⟩⟩
        rcases hy with ⟨x, hx, rfl⟩
        rcases hθ_binary x hx with (h | h)
        · rw [h] at hyV
          norm_num at hyV
        · rw [h] at hyU
          norm_num at hyU
      -- Apply the definition of IsPreconnected to get a contradiction
      have h_contra := h_image_conn (Set.Iio (1/2 : ℝ)) (Set.Ioi (1/2 : ℝ))
        hU_open hV_open h_cover h_nonempty_U h_nonempty_V
      exact absurd h_contra h_empty_inter
    · -- 1 not in image, so image ⊆ {0}, hence all values are 0
      left
      intro x hx
      rcases hθ_binary x hx with (h | h)
      · exact h
      · exfalso
        exact h1 ⟨x, hx, h⟩
  · -- 0 not in image, so image ⊆ {1}, hence all values are 1
    right
    intro x hx
    rcases hθ_binary x hx with (h | h)
    · exfalso
      exact h0 ⟨x, hx, h⟩
    · exact h

/-- The closure of an odd grid cell is preconnected. -/
theorem aux_cutoffs_oddGridCell_closure_isPreconnected {d : ℕ} {z : SpatialCoordinates d}
    {r : ℝ} (hr : 0 < r) (m : ℕ) (k : OddGridIndex d m) :
    IsPreconnected (closure (oddGridCell z r hr m k : Set (SpatialCoordinates d))) := by
  have h_conv : Convex ℝ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
    dsimp [oddGridCell, centeredCube]
    exact convex_ball _ _
  have h_closure_conv : Convex ℝ (closure (oddGridCell z r hr m k : Set (SpatialCoordinates d))) :=
    h_conv.closure
  exact h_closure_conv.isPreconnected


end Paper
