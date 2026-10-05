module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationLeg

@[expose] public section

/-!
# Composing the Step 6 transfer with the printed family

The transfer `exists_gridCentre_oscillation_le` moves the oscillation from the
off-grid window at scale `j` to the base-grid window at scale `j + 1`; the family
`exists_interiorCampanatoFamily` bounds the latter in its *normalized* form
`3 ^ (-(j+1)) * osc`.  Composing them costs exactly one factor of `3`, because

```text
  3 ^ (-j) = 3 * 3 ^ (-(j+1)) ,
```

so the off-grid normalized oscillation is bounded by `3 * price * E * (...)`.
This is the paper's "Campanato price absorbed into `C`": the whole factor
`3 * sqrt ((3^3)^d)` is dimension-only.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- **The composition, as arithmetic.**  `oscx` is the off-grid oscillation at
scale `j`, `oscz` the base-grid oscillation at scale `j + 1`. -/
theorem oscillationLeg_compose {j top : ℤ} {oscx oscz oscTop D price E : ℝ}
    (htrans : oscx ≤ price * oscz)
    (hfam : (3 : ℝ) ^ (-(j + 1)) * oscz ≤
      E * ((3 : ℝ) ^ (-top) * oscTop + D))
    (hprice : 0 ≤ price) :
    (3 : ℝ) ^ (-j) * oscx ≤
      3 * price * (E * ((3 : ℝ) ^ (-top) * oscTop + D)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hsplit : (3 : ℝ) ^ (-j) = 3 * (3 : ℝ) ^ (-(j + 1)) := by
    rw [show -j = 1 + -(j + 1) by ring, zpow_add₀ (ne_of_gt h3)]
    norm_num
  have hzpos : (0 : ℝ) < (3 : ℝ) ^ (-j) := zpow_pos h3 _
  calc (3 : ℝ) ^ (-j) * oscx
      ≤ (3 : ℝ) ^ (-j) * (price * oscz) :=
        mul_le_mul_of_nonneg_left htrans hzpos.le
    _ = 3 * price * ((3 : ℝ) ^ (-(j + 1)) * oscz) := by
        rw [hsplit]; ring
    _ ≤ 3 * price * (E * ((3 : ℝ) ^ (-top) * oscTop + D)) := by
        refine mul_le_mul_of_nonneg_left hfam ?_
        positivity

/-- The dimension-only constant carried by the oscillation leg. -/
def oscillationLegPrice (d : ℕ) : ℝ := 3 * Real.sqrt (((3 : ℝ) ^ (3 : ℤ)) ^ d)

theorem oscillationLegPrice_nonneg (d : ℕ) : 0 ≤ oscillationLegPrice d := by
  unfold oscillationLegPrice
  positivity

/-- **The oscillation leg at the frozen base points.**  For an arbitrary
`x ∈ cube d m`, the normalized off-grid oscillation at scale `j` is bounded by
the printed family's right-hand side at the base-grid centre `z`, at the
dimension-only price `oscillationLegPrice d`. -/
theorem oscillationLeg_of_gridCentre (d m j : ℕ) (x : Vec d)
    (hx : x ∈ cube d (m : ℤ)) (hjm : j ≤ m)
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    {top : ℤ} {oscTop D E : ℝ}
    (hfam : ∀ z : Vec d, OnTriadicGrid j z → z ∈ cube d (m : ℤ) →
      (3 : ℝ) ^ (-((j : ℤ) + 1)) *
          normalizedL2On (truncatedCube d (m : ℤ) ((j : ℤ) + 1) z)
            (fun p ↦ u.toFun p -
              averageOn (truncatedCube d (m : ℤ) ((j : ℤ) + 1) z) u.toFun) ≤
        E * ((3 : ℝ) ^ (-top) * oscTop + D)) :
    (3 : ℝ) ^ (-(j : ℤ)) *
        normalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) x)
          (fun p ↦ u.toFun p -
            averageOn (truncatedCube d (m : ℤ) (j : ℤ) x) u.toFun) ≤
      oscillationLegPrice d * (E * ((3 : ℝ) ^ (-top) * oscTop + D)) := by
  obtain ⟨z, hzgrid, hzcube, _hdist, htrans⟩ :=
    exists_gridCentre_oscillation_le d m j x hx hjm u
  have h := oscillationLeg_compose (j := (j : ℤ)) (top := top)
    htrans (hfam z hzgrid hzcube) (Real.sqrt_nonneg _)
  calc (3 : ℝ) ^ (-(j : ℤ)) *
      normalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) x)
        (fun p ↦ u.toFun p -
          averageOn (truncatedCube d (m : ℤ) (j : ℤ) x) u.toFun)
      ≤ 3 * Real.sqrt (((3 : ℝ) ^ (3 : ℤ)) ^ d) *
          (E * ((3 : ℝ) ^ (-top) * oscTop + D)) := h
    _ = oscillationLegPrice d * (E * ((3 : ℝ) ^ (-top) * oscTop + D)) := by
        unfold oscillationLegPrice; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
