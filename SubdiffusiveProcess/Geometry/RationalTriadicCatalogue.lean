import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Data.Countable.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A countable catalogue contains every rational-centred triadic cube and admits
expanding calibration roots. This module contains no probabilistic extraction. -/

open Set Filter Topology

namespace SubdiffusiveProcess
noncomputable section

/-- A fixed surjective enumeration of rational centres and integer triadic scales. -/
def rationalTriadicEnumeration (d : ℕ) : ℕ → (Fin d → ℚ) × ℤ :=
  (exists_surjective_nat ((Fin d → ℚ) × ℤ)).choose

/-- Every rational centre and integer scale occurs in the catalogue. -/
theorem rationalTriadicEnumeration_surjective (d : ℕ) :
    Function.Surjective (rationalTriadicEnumeration d) :=
  (exists_surjective_nat ((Fin d → ℚ) × ℤ)).choose_spec

/-- The spatial centre of a rational triadic catalogue entry. -/
def rationalTriadicCenter (d i : ℕ) : SpatialCoordinates d :=
  fun j => ((rationalTriadicEnumeration d i).1 j : ℝ)

/-- The positive side length of a rational triadic catalogue entry. -/
def rationalTriadicSide (d i : ℕ) : ℝ := (3 : ℝ) ^ (rationalTriadicEnumeration d i).2

/-- Every side in the rational triadic catalogue is strictly positive. -/
theorem rationalTriadicSide_pos (d i : ℕ) : 0 < rationalTriadicSide d i :=
  zpow_pos zero_lt_three _

/-- An index for a specified rational centre and integer scale. -/
def rationalTriadicIndex (d : ℕ) (z : Fin d → ℚ) (k : ℤ) : ℕ :=
  (rationalTriadicEnumeration_surjective d (z, k)).choose

/-- The chosen index has exactly its prescribed centre and side. -/
theorem rationalTriadicIndex_spec (d : ℕ) (z : Fin d → ℚ) (k : ℤ) :
    rationalTriadicCenter d (rationalTriadicIndex d z k) = (fun j => (z j : ℝ)) ∧
    rationalTriadicSide d (rationalTriadicIndex d z k) = (3 : ℝ) ^ k := by
  have h := (rationalTriadicEnumeration_surjective d (z, k)).choose_spec
  change rationalTriadicEnumeration d (rationalTriadicIndex d z k) = (z, k) at h
  constructor
  · funext j
    change ((rationalTriadicEnumeration d (rationalTriadicIndex d z k)).1 j : ℝ) = (z j : ℝ)
    rw [h]
  · change (3 : ℝ) ^ (rationalTriadicEnumeration d (rationalTriadicIndex d z k)).2 = _
    rw [h]

/-- Every positive rational-centred cube with a triadic side has an exact catalogue index. -/
theorem rationalTriadicCatalogue_complete
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hz : ∀ j : Fin d, ∃ q : ℚ, z j = (q : ℝ)) (hr : ∃ k : ℤ, r = (3 : ℝ) ^ k) :
    ∃ i : ℕ, rationalTriadicCenter d i = z ∧ rationalTriadicSide d i = r := by
  classical
  choose q hq using hz
  obtain ⟨k, hk⟩ := hr
  obtain ⟨hc, hs⟩ := rationalTriadicIndex_spec d q k
  refine ⟨rationalTriadicIndex d q k, hc.trans ?_, hs.trans hk.symm⟩
  exact funext fun j => (hq j).symm

/-- A finite initial family of positive cubes fits compactly inside one expanding triadic root. -/
theorem exists_triadic_root_for_prefix
    {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (k : ℕ) :
    ∃ m : ℕ, ∀ i ≤ k,
      closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ m)
          (pow_pos zero_lt_three m) : Set (SpatialCoordinates d)) := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun i : Fin (k + 1) => 2 * ‖z i‖ + r i)).bddAbove
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop C |>.exists
  refine ⟨m, ?_⟩
  intro i hi x hx
  have hix : dist x (z i) ≤ r i / 2 :=
    closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hx
  have hbound : 2 * ‖z i‖ + r i ≤ C := hC ⟨⟨i, by omega⟩, rfl⟩
  have htri := dist_triangle x (z i) 0
  change dist x 0 < (3 : ℝ) ^ m / 2
  simp only [dist_zero_right] at htri ⊢
  linarith only [hix, hbound, htri, hm]

end
end SubdiffusiveProcess
