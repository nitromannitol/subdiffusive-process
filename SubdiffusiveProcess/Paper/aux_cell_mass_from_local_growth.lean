import SubdiffusiveProcess.Paper.aux_translated_grid_cover
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace Paper



theorem aux_cell_mass_from_local_growth
    (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : Fin d → ℝ) (t ell r Ccov : ℝ)
    (ht : (d : ℝ) - 1 < t) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hr : 0 < r) (hsep : Cc * r < ell) (hCcov : 0 ≤ Ccov)
    (nCell : (Fin d → ℤ) → ℕ)
    (cellCenters : ∀ idx : Fin d → ℤ,
      Fin (nCell idx) → SpatialCoordinates d)
    (cellRadii : ∀ idx : Fin d → ℤ, Fin (nCell idx) → ℝ)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (K : ℝ) (hK : 0 ≤ K) :
    let Q : Opens (SpatialCoordinates d) := centeredCube z R hR
    let actualCell : (Fin d → ℤ) → Set (SpatialCoordinates d) :=
      fun idx =>
        (Q : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d,
            a i + (idx i : ℝ) * ell ≤ x i ∧
              x i < a i + ((idx i : ℝ) + 1) * ell}
    (∀ idx : Fin d → ℤ,
      (∀ j : Fin (nCell idx),
        cellCenters idx j ∈ (Q : Set (SpatialCoordinates d)) ∧
          0 < cellRadii idx j ∧ cellRadii idx j ≤ 1) ∧
      actualCell idx ⊆
        ⋃ j : Fin (nCell idx),
          Metric.ball (cellCenters idx j) (cellRadii idx j) ∧
      (∑ j : Fin (nCell idx), (cellRadii idx j) ^ t) ≤ Ccov * ell ^ t) →
    (∀ x ∈ (Q : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        nu (Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d))) ≤
          ENNReal.ofReal (K * rad ^ t)) →
    iSup (fun idx : Fin d → ℤ => nu (actualCell idx)) ≤
      ENNReal.ofReal (Ccov * K * ell ^ t) := by
  dsimp
  intro hcover hgrowth
  apply iSup_le
  intro idx
  obtain ⟨hcc, hsub, hsum⟩ := hcover idx
  have hsub' :
      (centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d,
            a i + (idx i : ℝ) * ell ≤ x i ∧
              x i < a i + ((idx i : ℝ) + 1) * ell} ⊆
        ⋃ j : Fin (nCell idx),
          (Metric.ball (cellCenters idx j) (cellRadii idx j) ∩
            (centeredCube z R hR : Set (SpatialCoordinates d))) := by
    intro x hx
    rcases Set.mem_iUnion.mp (hsub hx) with ⟨j, hxj⟩
    exact Set.mem_iUnion.mpr ⟨j, ⟨hxj, hx.1⟩⟩
  have hmeasure :
      nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d,
            a i + (idx i : ℝ) * ell ≤ x i ∧
              x i < a i + ((idx i : ℝ) + 1) * ell}) ≤
        ∑ j : Fin (nCell idx),
          nu (Metric.ball (cellCenters idx j) (cellRadii idx j) ∩
            (centeredCube z R hR : Set (SpatialCoordinates d))) := by
    exact (measure_mono hsub').trans
      (measure_iUnion_fintype_le nu (fun j : Fin (nCell idx) =>
        Metric.ball (cellCenters idx j) (cellRadii idx j) ∩
          (centeredCube z R hR : Set (SpatialCoordinates d))))
  have hballs :
      (∑ j : Fin (nCell idx),
          nu (Metric.ball (cellCenters idx j) (cellRadii idx j) ∩
            (centeredCube z R hR : Set (SpatialCoordinates d)))) ≤
        ∑ j : Fin (nCell idx), ENNReal.ofReal
          (K * (cellRadii idx j) ^ t) := by
    exact Finset.sum_le_sum fun j _ =>
      hgrowth (cellCenters idx j) (hcc j).1 (cellRadii idx j)
        (hcc j).2.1 (hcc j).2.2
  have hsum_nonneg :
      0 ≤ ∑ j : Fin (nCell idx), K * (cellRadii idx j) ^ t := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg hK (Real.rpow_nonneg (le_of_lt (hcc j).2.1) t)
  have hsum_ofReal :
      (∑ j : Fin (nCell idx), ENNReal.ofReal
          (K * (cellRadii idx j) ^ t)) =
        ENNReal.ofReal (∑ j : Fin (nCell idx), K * (cellRadii idx j) ^ t) := by
    symm
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro j hj
    exact mul_nonneg hK (Real.rpow_nonneg (le_of_lt (hcc j).2.1) t)
  have hsum_real :
      (∑ j : Fin (nCell idx), K * (cellRadii idx j) ^ t) ≤
        K * (Ccov * ell ^ t) := by
    calc
      (∑ j : Fin (nCell idx), K * (cellRadii idx j) ^ t) =
          K * (∑ j : Fin (nCell idx), (cellRadii idx j) ^ t) := by
            rw [Finset.mul_sum]
      _ ≤ K * (Ccov * ell ^ t) :=
        mul_le_mul_of_nonneg_left hsum hK
  calc
    nu ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
        {x | ∀ i : Fin d,
          a i + (idx i : ℝ) * ell ≤ x i ∧
            x i < a i + ((idx i : ℝ) + 1) * ell}) ≤
        ∑ j : Fin (nCell idx),
          nu (Metric.ball (cellCenters idx j) (cellRadii idx j) ∩
            (centeredCube z R hR : Set (SpatialCoordinates d))) := hmeasure
    _ ≤ ∑ j : Fin (nCell idx), ENNReal.ofReal
          (K * (cellRadii idx j) ^ t) := hballs
    _ = ENNReal.ofReal (∑ j : Fin (nCell idx), K * (cellRadii idx j) ^ t) := hsum_ofReal
    _ ≤ ENNReal.ofReal (K * (Ccov * ell ^ t)) :=
      ENNReal.ofReal_le_ofReal hsum_real
    _ = ENNReal.ofReal (Ccov * K * ell ^ t) := by
      congr 1
      ring

end Paper
