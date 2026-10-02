import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.FiniteStopping.CellRegularity
import SubdiffusiveProcess.FiniteStopping.ObservationTree

/-! This module establishes k toNat eq for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- cell2 radius eq in the finite stopping construction. -/
theorem cell2_radius_eq
    (H1 N : ℕ) (hH1 : 0 < H1) (j : ℤ)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (s : ℕ) :
    descendantSide (subdivisionHalfWidth H1) s
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) =
      (3 : ℝ) ^ (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ) : ℤ)) := by
  have hm1 : 2 * 1 + 1 = 3 ^ 1 := by norm_num
  rw [SubdiffusiveProcess.FiniteStopping.descendantSide_zpow 1 1 hm1 j
      (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j)]
  simp only [one_mul]
  rw [SubdiffusiveProcess.FiniteStopping.descendantSide_zpow H1 (subdivisionHalfWidth H1)
      (two_mul_subdivisionHalfWidth_add_one H1)
      (j - (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℤ)) s]
  congr 1
  have ht0 : (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℤ) =
      ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j := by
    unfold SubdiffusiveProcess.FiniteStopping.obsT0
    exact Int.toNat_of_nonneg hj0
  push_cast [ht0]
  ring

/-- cell2 succ le parent in the finite stopping construction. -/
theorem cell2_succ_le_parent
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin (s + 1) → OddGridIndex d mg) :
    SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 (s + 1) w ≤
      SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s (fun i => w i.castSucc) :=
  SetLike.coe_subset_coe.1 (descendantCell_succ_subset mg
    (descendantCenter 1 z _ t0 w0) (descendantSide_pos 1 t0 hr) s w)

/-- parent side eq Lr in the finite stopping construction. -/
theorem parent_side_eq_Lr
    (H1 N : ℕ) (hH1 : 0 < H1) (j : ℤ)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (s : ℕ) :
    descendantSide (subdivisionHalfWidth H1) s
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) =
      (3 : ℝ) ^ H1 *
        (3 : ℝ) ^ (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)) := by
  rw [SubdiffusiveProcess.FiniteStopping.cell2_parent_side_eq H1
      (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s,
    SubdiffusiveProcess.FiniteStopping.cell2_radius_eq H1 N hH1 j hj0 (s + 1)]

/-- pad margin two in the finite stopping construction. -/
theorem pad_margin_two {pad : ℝ} (hpad3 : pad ≤ 3) :
    pad < 2 * (2 : ℕ) + 1 := by
  norm_num
  linarith only [hpad3]

/-- Reg premises at stage in the finite stopping construction. -/
theorem Reg_premises_at_stage
    (H1 N : ℕ) (hH1 : 0 < H1) (z : SpatialCoordinates d) (j : ℤ)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
    (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1))
    (pad : ℝ) (hpad1 : 1 < pad) (hpad3 : pad ≤ 3)
    (hPad : SubdiffusiveProcess.FiniteStopping.padLabel 2 (w (Fin.last s))) :
    descendantCenter (subdivisionHalfWidth H1)
        (descendantCenter 1 z ((3 : ℝ) ^ j)
          (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
        (s + 1) w =
      oddGridCenter
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j)
            (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
          s (fun i => w i.castSucc))
        ((3 : ℝ) ^ H1 *
          (3 : ℝ) ^ (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)))
        (subdivisionHalfWidth H1) (w (Fin.last s)) ∧
    (closedCube
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j)
            (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
          (s + 1) w)
        (pad * (3 : ℝ) ^ (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)))
        (mul_pos (lt_trans zero_lt_one hpad1) (by positivity)) : Set (SpatialCoordinates d)) ⊆
      (centeredCube
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j)
            (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
          s (fun i => w i.castSucc))
        ((3 : ℝ) ^ H1 *
          (3 : ℝ) ^ (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)))
        (mul_pos (pow_pos (by norm_num) H1) (by positivity)) : Set (SpatialCoordinates d)) := by
  set L : ℝ := (3 : ℝ) ^ H1 with hL
  set r : ℝ := (3 : ℝ) ^
    (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)) with hr
  have hLmg : L = 2 * (subdivisionHalfWidth H1 : ℝ) + 1 := by
    rw [hL]
    exact_mod_cast (two_mul_subdivisionHalfWidth_add_one H1).symm
  have hside : descendantSide (subdivisionHalfWidth H1) s
      (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) = L * r :=
    SubdiffusiveProcess.FiniteStopping.parent_side_eq_Lr H1 N hH1 j hj0 s
  have hcenter := SubdiffusiveProcess.FiniteStopping.cell2_succ_eq_oddGridCenter z
    (r := (3 : ℝ) ^ j) (by positivity) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j)
    (subdivisionHalfWidth H1) w0 s w
  rw [hside] at hcenter
  refine ⟨hcenter, ?_⟩
  have hcontain := SubdiffusiveProcess.FiniteStopping.padded_contains
    (descendantCenter (subdivisionHalfWidth H1)
      (descendantCenter 1 z ((3 : ℝ) ^ j)
        (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
      (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) s
      (fun i => w i.castSucc))
    L r (by positivity) (by positivity) (subdivisionHalfWidth H1) hLmg
    (w (Fin.last s)) 2 hPad pad (lt_trans zero_lt_one hpad1)
    (SubdiffusiveProcess.FiniteStopping.pad_margin_two hpad3)
  rwa [← hcenter] at hcontain

/-- k eq in the finite stopping construction. -/
theorem k_eq
    (H1 N : ℕ) (j : ℤ)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    (s : ℕ) :
    ((H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + s : ℕ) : ℤ) -
        (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j) =
      ((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) : ℕ) : ℤ) := by
  have hZ : (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j : ℤ) =
      (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
        SubdiffusiveProcess.FiniteStopping.rootQ H1 j := by
    unfold SubdiffusiveProcess.FiniteStopping.obsLoZ
    exact Int.toNat_of_nonneg hq0
  push_cast [hZ]
  ring

/-- k toNat eq in the finite stopping construction. -/
theorem k_toNat_eq
    (H1 N : ℕ) (j : ℤ)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    (s : ℕ) :
    (((H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + s : ℕ) : ℤ) -
        (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)).toNat =
      H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + s) := by
  rw [SubdiffusiveProcess.FiniteStopping.k_eq H1 N j hq0 s, Int.toNat_natCast]

end SubdiffusiveProcess.FiniteStopping
