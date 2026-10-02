import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.DirichletForm.All
import Mathlib.Tactic
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Geometry.CoordinateFold

/-! Extracted local form data for the relative concentration proof.
This module proves the stated deterministic implications; it does not construct random bounds. -/

open MeasureTheory Filter Set Topology TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.LimitFormCore
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Soft thresholding `t ↦ sign t (|t| - s)⁺ = t - clamp_{[-s,s]} t`. -/
def softThreshold (s t : ℝ) : ℝ := t - max (-s) (min s t)

/-- Soft thresholding fixes zero at every nonnegative threshold. -/
theorem softThreshold_zero {s : ℝ} (hs : 0 ≤ s) :
    SubdiffusiveProcess.LimitFormCore.softThreshold s 0 = 0 := by
  unfold SubdiffusiveProcess.LimitFormCore.softThreshold
  rw [min_eq_right hs, max_eq_right (neg_nonpos.mpr hs)]
  ring

/-- Soft thresholding is monotone and does not increase increments. -/
theorem softThreshold_mono_le {s : ℝ} (_hs : 0 ≤ s) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ SubdiffusiveProcess.LimitFormCore.softThreshold s b - SubdiffusiveProcess.LimitFormCore.softThreshold s a ∧
      SubdiffusiveProcess.LimitFormCore.softThreshold s b - SubdiffusiveProcess.LimitFormCore.softThreshold s a ≤ b - a := by
  have hmono : max (-s) (min s a) ≤ max (-s) (min s b) :=
    max_le_max_left _ (min_le_min_left _ hab)
  have hlip : LipschitzWith 1 (fun t : ℝ => max (-s) (min s t)) :=
    (LipschitzWith.id.const_min s).const_max (-s)
  have hdist := hlip.dist_le_mul b a
  simp only [Real.dist_eq, NNReal.coe_one, one_mul,
    abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hab)] at hdist
  unfold SubdiffusiveProcess.LimitFormCore.softThreshold
  constructor <;> linarith only [hmono, hdist]

/-- Soft thresholding is a normal contraction. -/
theorem softThreshold_isNormalContraction {s : ℝ} (hs : 0 ≤ s) :
    DirichletForm.IsNormalContraction (SubdiffusiveProcess.LimitFormCore.softThreshold s) where
  map_zero := SubdiffusiveProcess.LimitFormCore.softThreshold_zero hs
  dist_le a b := by
    rcases le_total a b with hab | hab
    · obtain ⟨h1, h2⟩ := SubdiffusiveProcess.LimitFormCore.softThreshold_mono_le hs hab
      rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
      exact h2
    · obtain ⟨h1, h2⟩ := SubdiffusiveProcess.LimitFormCore.softThreshold_mono_le hs hab
      rw [abs_of_nonneg h1, abs_of_nonneg (sub_nonneg.mpr hab)]
      exact h2

/-- Soft thresholding moves each real number by at most the threshold. -/
theorem softThreshold_sub_le {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    |SubdiffusiveProcess.LimitFormCore.softThreshold s t - t| ≤ s := by
  unfold SubdiffusiveProcess.LimitFormCore.softThreshold
  rw [abs_le]
  have hlo := le_max_left (-s) (min s t)
  have hhi : max (-s) (min s t) ≤ s :=
    max_le (neg_le_self hs) (min_le_left _ _)
  constructor <;> linarith only [hlo, hhi]

/-- A nonzero thresholded value has absolute input at least the threshold. -/
theorem softThreshold_ne_zero {s t : ℝ}
    (h : SubdiffusiveProcess.LimitFormCore.softThreshold s t ≠ 0) : s ≤ |t| := by
  by_contra hlt
  push_neg at hlt
  apply h
  unfold SubdiffusiveProcess.LimitFormCore.softThreshold
  have h1 : -s ≤ t := by linarith only [hlt, neg_abs_le t]
  have h2 : t ≤ s := by linarith only [hlt, le_abs_self t]
  rw [min_eq_right h2, max_eq_right h1]
  ring

/-- Soft thresholding is continuous. -/
theorem continuous_softThreshold (s : ℝ) :
    Continuous (SubdiffusiveProcess.LimitFormCore.softThreshold s) := by
  unfold SubdiffusiveProcess.LimitFormCore.softThreshold
  fun_prop


/-- Volume restricted to a bounded open cube is finite. -/
theorem isFiniteMeasure_cube (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  rw [isFiniteMeasure_restrict, centeredCube_volume]
  exact ENNReal.ofReal_ne_top

/-- A continuous function vanishing off the open cube, soft-thresholded at level `s > 0`,
has compact support inside the cube. -/
theorem softThreshold_support (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {s : ℝ} (hs : 0 < s) (U : SpatialCoordinates d → ℝ) (hU : Continuous U)
    (hU0 : ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) :
    HasCompactSupport (fun x => SubdiffusiveProcess.LimitFormCore.softThreshold s (U x)) ∧
      tsupport (fun x => SubdiffusiveProcess.LimitFormCore.softThreshold s (U x)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hclosed : IsClosed {x : SpatialCoordinates d | s ≤ |U x|} :=
    isClosed_le continuous_const (continuous_abs.comp hU)
  have hsub : tsupport (fun x => SubdiffusiveProcess.LimitFormCore.softThreshold s (U x)) ⊆
      {x : SpatialCoordinates d | s ≤ |U x|} := by
    refine closure_minimal ?_ hclosed
    intro x hx
    exact SubdiffusiveProcess.LimitFormCore.softThreshold_ne_zero hx
  have hQ : {x : SpatialCoordinates d | s ≤ |U x|} ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    by_contra hxQ
    have : |U x| = 0 := by rw [hU0 x hxQ, abs_zero]
    have hx' : s ≤ |U x| := hx
    linarith only [hs, hx', this]
  have hcpt : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    (closedCube z r hr).isCompact
  refine ⟨?_, hsub.trans hQ⟩
  refine HasCompactSupport.intro' hcpt ?_ ?_
  · exact (closedCube z r hr).isCompact.isClosed
  · intro x hx
    have : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      fun h => hx (centeredCube_subset_closedCube z hr h)
    rw [hU0 x this]
    exact SubdiffusiveProcess.LimitFormCore.softThreshold_zero hs.le

/-- The Q-core of a closed form, as a submodule. -/
def coreSubmodule {Q : TopologicalSpace.Opens (SpatialCoordinates d)}
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    Submodule ℝ (DomainL2 Q) where
  carrier := {w | F.MemCoreOn (Q : Set (SpatialCoordinates d)) w}
  zero_mem' := F.memCoreOn_zero _
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun c _ hu => hu.smul c

end SubdiffusiveProcess.LimitFormCore
