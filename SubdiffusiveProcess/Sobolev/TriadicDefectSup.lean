import SubdiffusiveProcess.Sobolev.RestrictedTriadicResponse
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Original-grid suprema of actual unit-slope defects

The supremum ranges over all cells and all Euclidean unit slopes. The
same root coefficient supplies a finite upper bound at every depth.
Consequently the geometric response series is genuinely summable at a
fixed cutoff, before any probabilistic or coefficient limit.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (a : PositiveCoefficient (centeredCube z r hr))

/-- The actual original-grid defect values over all Euclidean unit slopes. -/
def triadicDefectRange (J : ℕ) : Set ℝ :=
  {y | ∃ (k : OddGridIndex d (triadicHalf J)) (p : Fin d → ℝ),
    (∑ i : Fin d, (p i)^2) = 1 ∧
    affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
      (hD J k) (hN J k)
      (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf J) k) a) p = y}

/-- Positive dimension supplies an actual unit slope and therefore a nonempty range. -/
theorem triadicDefectRange_nonempty (hd : 0 < d) (J : ℕ) :
    (triadicDefectRange z hr hD hN a J).Nonempty := by
  let i : Fin d := ⟨0, hd⟩
  let k : OddGridIndex d (triadicHalf J) := fun _ => 0
  refine ⟨_, k, (fun j => if j = i then 1 else 0), ?_, rfl⟩
  simp

/-- The root coefficient bounds every cell response, with no depth dependence. -/
theorem triadicDefectRange_le_of_bounds {c A : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ a.val x)
    (hA : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), a.val x ≤ A)
    (J : ℕ) {y : ℝ} (hy : y ∈ triadicDefectRange z hr hD hN a J) :
    y ≤ (A + c⁻¹) / 2 - 1 := by
  obtain ⟨k, p, hp, rfl⟩ := hy
  exact affineDiagonalDefect_le_of_unit_slope _ _ _ _ _ hp hc
    (positiveCoefficientRestrict_lower _ a ha) (positiveCoefficientRestrict_upper _ a hA)

/-- At a fixed coefficient the original-grid unit-slope range is bounded above. -/
theorem triadicDefectRange_bddAbove (J : ℕ) :
    BddAbove (triadicDefectRange z hr hD hN a J) := by
  obtain ⟨c, hc, ha⟩ := a.property
  refine ⟨(‖a.val‖ + c⁻¹) / 2 - 1, ?_⟩
  intro y hy
  exact triadicDefectRange_le_of_bounds z hr hD hN a hc ha
    ((boundedPotential_ae_bound a.val).mono fun x hx => (le_abs_self _).trans hx) J hy

/-- The literal supremum of original-grid unit-slope defects in positive dimension. -/
def triadicDefectSup (_hd : 0 < d) (J : ℕ) : ℝ :=
  sSup (triadicDefectRange z hr hD hN a J)

/-- The supremum has its full least-upper-bound characterization on the actual response range. -/
theorem triadicDefectSup_isLUB (hd : 0 < d) (J : ℕ) :
    IsLUB (triadicDefectRange z hr hD hN a J) (triadicDefectSup z hr hD hN a hd J) :=
  isLUB_csSup (triadicDefectRange_nonempty z hr hD hN a hd J)
    (triadicDefectRange_bddAbove z hr hD hN a J)

/-- Every actual original-grid unit-slope defect is bounded by the literal supremum. -/
theorem le_triadicDefectSup (hd : 0 < d) (J : ℕ)
    (k : OddGridIndex d (triadicHalf J)) {p : Fin d → ℝ}
    (hp : (∑ i : Fin d, (p i)^2) = 1) :
    affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
      (hD J k) (hN J k)
      (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf J) k) a) p ≤
        triadicDefectSup z hr hD hN a hd J :=
  (triadicDefectSup_isLUB z hr hD hN a hd J).1 ⟨k, p, hp, rfl⟩

/-- Original-grid defect suprema are nonnegative. -/
theorem triadicDefectSup_nonneg (hd : 0 < d) (J : ℕ) :
    0 ≤ triadicDefectSup z hr hD hN a hd J := by
  obtain ⟨y, k, p, hp, rfl⟩ := triadicDefectRange_nonempty z hr hD hN a hd J
  exact (affineDiagonalDefect_nonneg _ _ _ _ _ p).trans
    (le_triadicDefectSup z hr hD hN a hd J k hp)

/-- The same fixed root bounds control the supremum at every descendant depth. -/
theorem triadicDefectSup_le_of_bounds (hd : 0 < d) {c A : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ a.val x)
    (hA : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), a.val x ≤ A)
    (J : ℕ) : triadicDefectSup z hr hD hN a hd J ≤ (A + c⁻¹) / 2 - 1 :=
  (triadicDefectSup_isLUB z hr hD hN a hd J).2
    (fun _ hy => triadicDefectRange_le_of_bounds z hr hD hN a hc ha hA J hy)

/-- The full geometric response series is summable at each fixed root coefficient. -/
theorem triadicDefectSup_summable (hd : 0 < d) :
    Summable (fun j : ℕ => ((d : ℝ) / (3 : ℝ)^j) *
      triadicDefectSup z hr hD hN a hd (j + 1)) := by
  obtain ⟨c, hc, ha⟩ := a.property
  let C := (‖a.val‖ + c⁻¹) / 2 - 1
  have hC : ∀ j, triadicDefectSup z hr hD hN a hd j ≤ C :=
    triadicDefectSup_le_of_bounds z hr hD hN a hd hc ha
      ((boundedPotential_ae_bound a.val).mono fun x hx => (le_abs_self _).trans hx)
  have hgeom : Summable (fun j : ℕ => ((d : ℝ) / (3 : ℝ)^j) * C) := by
    have h := (summable_geometric_of_lt_one (r := (1 / 3 : ℝ))
      (by norm_num) (by norm_num)).mul_left ((d : ℝ) * C)
    convert h using 1
    funext j
    rw [one_div_pow]
    ring
  exact Summable.of_nonneg_of_le
    (fun j => mul_nonneg (by positivity) (triadicDefectSup_nonneg z hr hD hN a hd (j + 1)))
    (fun j => mul_le_mul_of_nonneg_left (hC (j + 1)) (by positivity)) hgeom

end SubdiffusiveProcess
