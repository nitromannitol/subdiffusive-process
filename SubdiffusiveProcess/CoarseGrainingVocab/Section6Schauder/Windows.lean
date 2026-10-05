module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows




-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryLaneWindows.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepWindows.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitLift.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open MeasureTheory
open Homogenization (axisCube openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### The carrier -/



def truncatedWindow (x : Vec d) (m k : ℤ) : Set (Vec d) :=
  ((fun y => x + y) '' openCubeSet (originCube d k)) ∩ openCubeSet (originCube d m)

theorem truncatedWindow_eq (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k = truncatedCube d m k x := rfl

theorem truncatedWindow_subset_translate (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k ⊆ (fun y => x + y) '' openCubeSet (originCube d k) :=
  truncatedCube_subset_translatedCube d m k x

theorem truncatedWindow_subset_domain (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k ⊆ openCubeSet (originCube d m) :=
  truncatedCube_subset_cube d m k x

/-! ### Nesting, membership, regularity -/

/-- The truncated windows are nested in the scale. -/
theorem truncatedWindow_mono (x : Vec d) (m : ℤ) {k l : ℤ} (hkl : k ≤ l) :
    truncatedWindow x m k ⊆ truncatedWindow x m l :=
  truncatedCube_mono d m x hkl

/-- The centre of a truncated window lies in it, as soon as it lies in the
domain cube. -/
theorem mem_truncatedWindow_self {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) : x ∈ truncatedWindow x m k :=
  mem_truncatedCube_self k hx

theorem truncatedWindow_nonempty {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) : (truncatedWindow x m k).Nonempty :=
  ⟨x, mem_truncatedWindow_self k hx⟩

theorem isOpen_truncatedWindow (x : Vec d) (m k : ℤ) : IsOpen (truncatedWindow x m k) :=
  isOpen_truncatedCube d m k x

theorem convex_truncatedWindow (x : Vec d) (m k : ℤ) : Convex ℝ (truncatedWindow x m k) :=
  convex_truncatedCube d m k x

theorem measurableSet_truncatedWindow (x : Vec d) (m k : ℤ) :
    MeasurableSet (truncatedWindow x m k) :=
  measurableSet_truncatedCube d m k x

theorem volume_truncatedWindow_lt_top (x : Vec d) (m k : ℤ) :
    volume (truncatedWindow x m k) < ⊤ :=
  volume_truncatedCube_lt_top d m k x

/-! ### Volumes and normalizers -/

theorem volume_toReal_truncatedWindow_bounds {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    ((3 : ℝ) ^ (k - 2)) ^ d ≤ (volume (truncatedWindow x m k)).toReal ∧
      (volume (truncatedWindow x m k)).toReal ≤ ((3 : ℝ) ^ k) ^ d :=
  volume_toReal_truncatedCube_bounds x hx hkm

theorem volume_toReal_truncatedWindow_pos {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    0 < (volume (truncatedWindow x m k)).toReal :=
  volume_toReal_truncatedCube_pos x hx hkm

/-- The two-sided comparison of the `|W|^{-1/d}` normalizer with the paper's
scale normalizer `3^{-k}` on a truncated window. -/
theorem rpow_volume_truncatedWindow_bounds (hd : d ≠ 0) {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    (3 : ℝ) ^ (-k) ≤ ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) ∧
      ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) ≤ 9 * (3 : ℝ) ^ (-k) := by
  obtain ⟨hlo, hhi⟩ := volume_toReal_truncatedWindow_bounds x hx hkm
  exact rpow_normalizer_bounds (d := d) hd hlo hhi

theorem integrableOn_sub_affineEval_sq_truncatedWindow {m k : ℤ} (x : Vec d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (truncatedWindow x m k)))
    (c : ℝ) (g : Vec d) :
    IntegrableOn (fun p => (u p - affineEval c g p) ^ 2) (truncatedWindow x m k) :=
  integrableOn_sub_affineEval_sq_truncatedCube x hu c g

/-! ### The window diameter -/

/-- Points of a truncated window are within sup-distance `3^k/2` of its centre. -/
theorem norm_sub_le_of_mem_truncatedWindow {x p : Vec d} {m k : ℤ}
    (hp : p ∈ truncatedWindow x m k) : ‖p - x‖ ≤ (3 : ℝ) ^ k / 2 := by
  obtain ⟨y, hy, hpy⟩ := hp.1
  have hpx : p - x = y := by
    rw [← hpy]
    exact add_sub_cancel_left x y
  rw [hpx]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Homogenization.mem_openCubeSet_originCube_iff] at hy
  have h := hy i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [h.1, h.2]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
