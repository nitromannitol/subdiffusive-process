module

public import SubdiffusiveProcess.Paper.aux_translated_grid_cover
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace Paper



theorem aux_local_growth_cover_mass
    (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : Fin d → ℝ) (t ell r Ccov : ℝ)
    (ht : (d : ℝ) - 1 < t) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hr : 0 < r) (hsep : Cc * r < ell) (hCcov : 0 ≤ Ccov)
    (nStrip : ℕ) (stripCenters : Fin nStrip → SpatialCoordinates d)
    (stripRadii : Fin nStrip → ℝ)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (K : ℝ) (hK : 0 ≤ K) :
    let Q : Opens (SpatialCoordinates d) := centeredCube z R hR
    let strips : Set (SpatialCoordinates d) :=
      (Q : Set (SpatialCoordinates d)) ∩
        {x | ∃ i : Fin d, ∃ j : ℤ,
          |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r}
    (∀ j : Fin nStrip,
      stripCenters j ∈ (Q : Set (SpatialCoordinates d)) ∧
        0 < stripRadii j ∧ stripRadii j ≤ 1) →
    strips ⊆ ⋃ j : Fin nStrip,
      Metric.ball (stripCenters j) (stripRadii j) →
    (∑ j : Fin nStrip, (stripRadii j) ^ t) ≤
      Ccov * (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) →
    (∀ x ∈ (Q : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        nu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) ≤
          ENNReal.ofReal (K * rad ^ t)) →
    nu strips ≤ ENNReal.ofReal
      (Ccov * K * (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1)) := by
  intro Q strips hmem hsub hsum hgrowth
  have hsub' :
      (Q : Set (SpatialCoordinates d)) ∩
          {x | ∃ i : Fin d, ∃ j : ℤ,
            |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r} ⊆
        ⋃ j : Fin nStrip,
          (Metric.ball (stripCenters j) (stripRadii j) ∩ (Q : Set (SpatialCoordinates d))) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hsub hx) with ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, ⟨hj, hx.1⟩⟩
  calc
    nu ((Q : Set (SpatialCoordinates d)) ∩
        {x | ∃ i : Fin d, ∃ j : ℤ,
          |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r})
        ≤ nu (⋃ j : Fin nStrip,
          (Metric.ball (stripCenters j) (stripRadii j) ∩ (Q : Set (SpatialCoordinates d))) ) :=
      measure_mono hsub'
    _ ≤ ∑ j : Fin nStrip,
        nu (Metric.ball (stripCenters j) (stripRadii j) ∩ (Q : Set (SpatialCoordinates d))) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ j : Fin nStrip, ENNReal.ofReal (K * (stripRadii j) ^ t) := by
      exact Finset.sum_le_sum (fun j _ =>
        hgrowth (stripCenters j) (hmem j).1 (stripRadii j)
          (hmem j).2.1 (hmem j).2.2)
    _ = ENNReal.ofReal (∑ j : Fin nStrip, K * (stripRadii j) ^ t) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact mul_nonneg hK (Real.rpow_nonneg (le_of_lt (hmem j).2.1) _)
    _ = ENNReal.ofReal (K * ∑ j : Fin nStrip, (stripRadii j) ^ t) := by
      rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal
        (K * (Ccov * (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum hK)
    _ = ENNReal.ofReal
        (Ccov * K * (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1)) := by
      congr 1
      ring

end Paper
