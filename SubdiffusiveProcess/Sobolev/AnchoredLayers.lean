module

public import SubdiffusiveProcess.Sobolev.FiniteLayerPotentials
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! # Actual anchored negative layer increments on a compact root

Index n enumerates the negative integer layer -n-1. The pointwise and norm
bounds use only local Lipschitz control on the root together with the anchor.
No global supremum of a random field is required.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The actual anchored increment from negative layer -n-1, restricted to a compact root. -/
def anchoredNegativeLayer (K : Compacts (SpatialCoordinates d)) (n : ℕ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) : C(K, ℝ) :=
  (ω (-(n : ℤ) - 1)).restrict (K : Set (SpatialCoordinates d)) -
    ContinuousMap.const K (ω (-(n : ℤ) - 1) 0)

/-- The index and subtraction agree exactly with the infrared series. -/
theorem anchoredNegativeLayer_apply (K : Compacts (SpatialCoordinates d)) (n : ℕ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) (x : K) :
    anchoredNegativeLayer K n ω x = ω (-(n : ℤ) - 1) x - ω (-(n : ℤ) - 1) 0 := rfl

/-- Restriction and anchoring are continuous in the actual field-coordinate topology. -/
theorem continuous_anchoredNegativeLayer (K : Compacts (SpatialCoordinates d)) (n : ℕ) :
    Continuous (anchoredNegativeLayer K n) :=
  ((ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp
    (continuous_apply (-(n : ℤ) - 1))).sub
      (ContinuousMap.continuous_const'.comp ((continuous_eval_const (0 : SpatialCoordinates d)).comp
        (continuous_apply (-(n : ℤ) - 1))))

/-- Local Lipschitz control bounds the anchored root norm; the anchor can lie outside the root. -/
theorem norm_anchoredNegativeLayer_le (K : Compacts (SpatialCoordinates d)) (n : ℕ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) {k : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (hK : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R)
    (hf : LipschitzOnWith k (ω (-(n : ℤ) - 1)) (insert 0 (K : Set (SpatialCoordinates d)))) :
    ‖anchoredNegativeLayer K n ω‖ ≤ (k : ℝ) * R := by
  apply (ContinuousMap.norm_le _ (mul_nonneg k.coe_nonneg hR)).mpr
  intro x
  have hb := hf.dist_le_mul x.val (mem_insert_of_mem _ x.property) 0 (mem_insert _ _)
  have hdist : ‖ω (-(n : ℤ) - 1) x - ω (-(n : ℤ) - 1) 0‖ ≤ (k : ℝ) * ‖(x : SpatialCoordinates d)‖ := by
    simpa only [dist_eq_norm, sub_zero] using hb
  exact hdist.trans (mul_le_mul_of_nonneg_left (hK x x.property) k.coe_nonneg)

end SubdiffusiveProcess
