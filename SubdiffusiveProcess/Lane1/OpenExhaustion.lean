import SubdiffusiveProcess.Main.BilateralField
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Exhausting an open set by compacts with Urysohn functions

For the measurability of the vague limit we need, for each open `U`, a
COUNTABLE family of test functions whose functional values determine `mu U`.
The family is Urysohn functions for an increasing exhaustion of `U` by
compacts.
-/

open Metric Set

open scoped CompactlySupported

noncomputable section
namespace SubdiffusiveProcess

/-- The `n`-th piece of the canonical exhaustion of an open set: the points of
the closed ball of radius `n` that are at distance at least `1/(n+1)` from the
complement.  Stated without `infDist` so that the empty complement is handled
uniformly. -/
def openPiece {d : ℕ} (U : Set (SpatialCoordinates d)) (n : ℕ) :
    Set (SpatialCoordinates d) :=
  Metric.closedBall (0 : SpatialCoordinates d) (n : ℝ) ∩
    {x | ∀ y, y ∉ U → 1 / ((n : ℝ) + 1) ≤ dist x y}

theorem isClosed_openPiece {d : ℕ} (U : Set (SpatialCoordinates d)) (n : ℕ) :
    IsClosed (openPiece U n) := by
  refine IsClosed.inter Metric.isClosed_closedBall ?_
  have : {x : SpatialCoordinates d | ∀ y, y ∉ U → 1 / ((n : ℝ) + 1) ≤ dist x y}
      = ⋂ y ∈ Uᶜ, {x : SpatialCoordinates d | 1 / ((n : ℝ) + 1) ≤ dist x y} := by
    ext x
    simp [Set.mem_iInter]
  rw [this]
  refine isClosed_biInter fun y _ => ?_
  exact isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem isCompact_openPiece {d : ℕ} (U : Set (SpatialCoordinates d)) (n : ℕ) :
    IsCompact (openPiece U n) :=
  (isCompact_closedBall (0 : SpatialCoordinates d) (n : ℝ)).of_isClosed_subset
    (isClosed_openPiece U n) Set.inter_subset_left

theorem openPiece_subset {d : ℕ} (U : Set (SpatialCoordinates d)) (n : ℕ) :
    openPiece U n ⊆ U := by
  intro x hx
  by_contra hxU
  have := hx.2 x hxU
  simp only [dist_self] at this
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- Each piece sits in the interior of the next. -/
theorem openPiece_subset_interior {d : ℕ} (U : Set (SpatialCoordinates d))
    (n : ℕ) : openPiece U n ⊆ interior (openPiece U (n + 1)) := by
  intro x hx
  set eps : ℝ := 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) with hepsdef
  have hepspos : 0 < eps := by
    rw [hepsdef]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [sub_pos, div_lt_div_iff₀ h2 h1]
    linarith
  refine mem_interior.mpr ⟨Metric.ball x (min eps (1 / 2)), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity)⟩
  intro z hz
  have hzx : dist z x < min eps (1 / 2) := Metric.mem_ball.mp hz
  constructor
  · have hxb : dist x (0 : SpatialCoordinates d) ≤ (n : ℝ) :=
      Metric.mem_closedBall.mp hx.1
    refine Metric.mem_closedBall.mpr ?_
    have := dist_triangle z x (0 : SpatialCoordinates d)
    have hlt : dist z x < 1 / 2 := lt_of_lt_of_le hzx (min_le_right _ _)
    push_cast
    linarith
  · intro y hy
    have hxy := hx.2 y hy
    have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
    have hzx' : dist x z < eps := by
      rw [dist_comm]
      exact lt_of_lt_of_le hzx (min_le_left _ _)
    have hlow : 1 / ((n : ℝ) + 1) - eps ≤ dist z y := by linarith
    calc 1 / ((((n + 1 : ℕ)) : ℝ) + 1) = 1 / ((n : ℝ) + 2) := by push_cast; ring
      _ = 1 / ((n : ℝ) + 1) - eps := by rw [hepsdef]; ring
      _ ≤ dist z y := hlow

theorem monotone_openPiece {d : ℕ} (U : Set (SpatialCoordinates d)) :
    Monotone (openPiece U) := by
  refine monotone_nat_of_le_succ fun n => ?_
  exact (openPiece_subset_interior U n).trans interior_subset

/-- The pieces exhaust the open set. -/
theorem iUnion_openPiece {d : ℕ} {U : Set (SpatialCoordinates d)} (hU : IsOpen U) :
    (⋃ n, openPiece U n) = U := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => openPiece_subset U n) ?_
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (max (dist x (0 : SpatialCoordinates d)) (1 / r))
  refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
  · exact Metric.mem_closedBall.mpr (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  · intro y hy
    have hxy : r ≤ dist x y := by
      by_contra hcon
      push_neg at hcon
      rw [dist_comm] at hcon
      exact hy (hball (Metric.mem_ball.mpr hcon))
    have hrn : 1 / r < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hnr : 1 / ((n : ℝ) + 1) ≤ r := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hr] at hrn
      nlinarith
    linarith

/-- Urysohn functions subordinate to the exhaustion: one for each piece, equal
to one on it and compactly supported inside the open set. -/
theorem exists_urysohn_openPiece {d : ℕ} {U : Set (SpatialCoordinates d)}
    (hU : IsOpen U) (n : ℕ) :
    ∃ f : C_c(SpatialCoordinates d, ℝ),
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ openPiece U n, f x = 1) ∧
        tsupport (f : SpatialCoordinates d → ℝ) ⊆ U := by
  have hdisj : Disjoint (openPiece U n) (interior (openPiece U (n + 1)))ᶜ :=
    disjoint_compl_right_iff_subset.mpr (openPiece_subset_interior U n)
  obtain ⟨g, hg1, hg0, hgcs, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_openPiece U n)
      isOpen_interior.isClosed_compl hdisj
  refine ⟨⟨g, hgcs⟩, fun x => ⟨(hg01 x).1, (hg01 x).2⟩, fun x hx => hg1 hx, ?_⟩
  have hsupp : Function.support (g : SpatialCoordinates d → ℝ)
      ⊆ interior (openPiece U (n + 1)) := by
    intro x hx
    by_contra hxi
    exact hx (hg0 hxi)
  have hcl : closure (Function.support (g : SpatialCoordinates d → ℝ))
      ⊆ openPiece U (n + 1) := by
    refine (closure_mono hsupp).trans ?_
    refine (closure_mono interior_subset).trans ?_
    rw [(isClosed_openPiece U (n + 1)).closure_eq]
  exact hcl.trans (openPiece_subset U (n + 1))

end SubdiffusiveProcess
