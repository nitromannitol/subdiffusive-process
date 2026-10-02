import SubdiffusiveProcess.Analysis.CellAverageJensen
import SubdiffusiveProcess.Geometry.OddGridPartition


/-! # Triadic child averages

Sum the child-parent Jensen inequalities on the literal triadic partition.
The coefficient retains both exact cell volumes. The child mass bound is an
internal input to be supplied by the measure-growth estimate in the trace proof.
-/

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

/-- The child-mass weighted average increments obey the exact double-integral bound. -/
theorem sum_triadic_child_mass_mul_average_sub_average_sq_le
    {d : ℕ} (z : SpatialCoordinates d) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (μ : Measure (SpatialCoordinates d)) [IsFiniteMeasure μ]
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hmass : ∀ k : OddGridIndex d 1,
      μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) ≤ M) :
    (∑ k : OddGridIndex d 1,
        μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) *
          |averageOn (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
            averageOn (centeredCube z r hr : Set (SpatialCoordinates d)) f| ^ 2) ≤
      M * (((r / 3) ^ d) * (r ^ d))⁻¹ *
        (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), |f y - f x| ^ 2) := by
  classical
  let P : Set (SpatialCoordinates d) := centeredCube z r hr
  let g : SpatialCoordinates d → ℝ := fun y =>
    ∫ x in P, |f y - f x| ^ 2
  have hf1 : IntegrableOn f P := hf.integrable (by norm_num)
  have hf2 : IntegrableOn (fun x => f x ^ 2) P := hf.integrable_sq
  have hprod : Integrable
      (fun w : SpatialCoordinates d × SpatialCoordinates d =>
        (f w.1 - f w.2) ^ 2)
      ((volume.restrict P).prod (volume.restrict P)) := by
    have hfst : Integrable
        (fun w : SpatialCoordinates d × SpatialCoordinates d => f w.1 ^ 2)
        ((volume.restrict P).prod (volume.restrict P)) :=
      hf2.comp_fst (volume.restrict P)
    have hsnd : Integrable
        (fun w : SpatialCoordinates d × SpatialCoordinates d => f w.2 ^ 2)
        ((volume.restrict P).prod (volume.restrict P)) :=
      hf2.comp_snd (volume.restrict P)
    have hcross : Integrable
        (fun w : SpatialCoordinates d × SpatialCoordinates d => f w.1 * f w.2)
        ((volume.restrict P).prod (volume.restrict P)) :=
      hf1.mul_prod hf1
    have heq : (fun w : SpatialCoordinates d × SpatialCoordinates d =>
        (f w.1 - f w.2) ^ 2) =
        (fun w => f w.1 ^ 2 - 2 * (f w.1 * f w.2) + f w.2 ^ 2) := by
      funext w
      ring
    rw [heq]
    exact (hfst.sub (hcross.const_mul 2)).add hsnd
  have hgintegrable : IntegrableOn g P := by
    have h := hprod.integral_prod_left
    have h' : Integrable
        (fun y => ∫ x in P, (f y - f x) ^ 2) (volume.restrict P) := by
      simpa only [Prod.fst, Prod.snd] using h
    change Integrable g (volume.restrict P)
    have heq : g = (fun y => ∫ x in P, (f y - f x) ^ 2) := by
      funext y
      dsimp [g]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change |f y - f x| ^ 2 = (f y - f x) ^ 2
        rw [sq_abs])
    rw [heq]
    exact h'
  have hcell_integrable : ∀ k : OddGridIndex d 1,
      IntegrableOn g (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) := by
    intro k
    exact hgintegrable.mono_set (oddGridCell_subset z hr 1 k)
  have hsum_integral :
      (∫ y in P, g y) =
        ∑ k : OddGridIndex d 1,
          ∫ y in (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)), g y := by
    calc
      (∫ y in P, g y) =
          ∫ y in ⋃ k : OddGridIndex d 1,
            (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)), g y := by
        exact setIntegral_congr_set (oddGrid_union_ae_eq z hr 1).symm
      _ = ∑ k : OddGridIndex d 1,
          ∫ y in (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)), g y := by
        exact integral_iUnion_fintype
          (fun k => (oddGridCell z r hr 1 k).isOpen.measurableSet)
          (oddGridCell_pairwiseDisjoint z hr 1) hcell_integrable
  have hvolP : volume.real P = r ^ d := by
    dsimp [P]
    exact centeredCube_volume_real z hr
  have hvolK : ∀ k : OddGridIndex d 1,
      volume.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) = (r / 3) ^ d := by
    intro k
    convert oddGridCell_volume_real z hr 1 k using 1 <;> norm_num
  have hvolPpos : 0 < volume.real P := by
    rw [hvolP]
    positivity
  have hvolKpos : ∀ k : OddGridIndex d 1,
      0 < volume.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) := by
    intro k
    rw [hvolK k]
    positivity
  have hchild : ∀ k : OddGridIndex d 1,
      μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) *
          |averageOn (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
            averageOn P f| ^ 2 ≤
        M * (((r / 3) ^ d) * (r ^ d))⁻¹ *
          (∫ y in (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)), g y) := by
    intro k
    let K : Set (SpatialCoordinates d) := oddGridCell z r hr 1 k
    have hKsub : K ⊆ P := oddGridCell_subset z hr 1 k
    have hKpos : 0 < volume.real K := by
      dsimp [K]
      rw [hvolK k]
      positivity
    have hJ := averageOn_sub_averageOn_sq_le_double_setIntegral
      (Q := P) (P := K) (f := f)
      (centeredCube z r hr).isOpen.measurableSet
      (oddGridCell z r hr 1 k).isOpen.measurableSet hKsub
      (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
      (by rw [oddGridCell_volume]; exact ENNReal.ofReal_ne_top)
      hvolPpos hKpos hf
    have hmass0 : 0 ≤ μ.real K := measureReal_nonneg
    have hsq0 : 0 ≤ |averageOn K f - averageOn P f| ^ 2 := sq_nonneg _
    have hcoef0 : 0 ≤ (((r / 3) ^ d) * (r ^ d))⁻¹ := by positivity
    have hJ' : |averageOn K f - averageOn P f| ^ 2 ≤
        (((r / 3) ^ d) * (r ^ d))⁻¹ * (∫ y in K, g y) := by
      have hvolK' : volume.real K = (r / 3) ^ d := by
        dsimp [K]
        exact hvolK k
      have hvolP' : volume.real P = r ^ d := hvolP
      have hvolK'' : (volume K).toReal = (r / 3) ^ d := by
        simpa [measureReal_def] using hvolK'
      have hvolP'' : (volume P).toReal = r ^ d := by
        simpa [measureReal_def] using hvolP'
      rw [hvolK'', hvolP''] at hJ
      simpa [K, P, g, sq_abs] using hJ
    calc
      μ.real K * |averageOn K f - averageOn P f| ^ 2 ≤
          μ.real K * ((((r / 3) ^ d) * (r ^ d))⁻¹ * (∫ y in K, g y)) :=
        mul_le_mul_of_nonneg_left hJ' hmass0
      _ ≤ M * ((((r / 3) ^ d) * (r ^ d))⁻¹ * (∫ y in K, g y)) := by
        apply mul_le_mul_of_nonneg_right (hmass k)
        exact mul_nonneg hcoef0 (integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun y => integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun x => sq_nonneg |f y - f x|)))
      _ = M * (((r / 3) ^ d) * (r ^ d))⁻¹ * (∫ y in K, g y) := by ring
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (OddGridIndex d 1)))
    (fun k _ => hchild k)
  calc
    (∑ k : OddGridIndex d 1,
        μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) *
          |averageOn (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
            averageOn (centeredCube z r hr : Set (SpatialCoordinates d)) f| ^ 2) ≤
        ∑ k : OddGridIndex d 1,
          M * (((r / 3) ^ d) * (r ^ d))⁻¹ *
            (∫ y in (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)), g y) := by
      simpa [P] using hsum
    _ = M * (((r / 3) ^ d) * (r ^ d))⁻¹ * (∫ y in P, g y) := by
      rw [← Finset.mul_sum]
      rw [← hsum_integral]
    _ = M * (((r / 3) ^ d) * (r ^ d))⁻¹ *
        (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), |f y - f x| ^ 2) := by
      simp [P, g]

end SubdiffusiveProcess
