import SubdiffusiveProcess.Geometry.OddGridPartition
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

noncomputable section

namespace SubdiffusiveProcess

/-- The energy of a global Sobolev function is the sum of its energies on the actual odd-grid cells. Source: `eq:mfd-18`. -/
theorem energy_eq_sum_oddGridCell_restrict
    {d : ℕ} (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) (m : ℕ)
    (a : SpatialCoordinates d → ℝ)
    (w : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hint : IntegrableOn
      (fun x => a x * vecDot (w.grad x) (w.grad x))
      (centeredCube z R hR : Set (SpatialCoordinates d)) volume) :
    energy a (centeredCube z R hR : Set (SpatialCoordinates d)) w =
      ∑ k : OddGridIndex d m,
        energy a (oddGridCell z R hR m k : Set (SpatialCoordinates d))
          (w.restrict (oddGridCell z R hR m k).isOpen
            (oddGridCell_subset z hR m k)) := by
  let f : SpatialCoordinates d → ℝ :=
    fun x => a x * vecDot (w.grad x) (w.grad x)
  have hcell : ∀ k : OddGridIndex d m,
      IntegrableOn f (oddGridCell z R hR m k : Set (SpatialCoordinates d)) volume := by
    intro k
    exact hint.mono_set (oddGridCell_subset z hR m k)
  have hunion :
      (∫ x in ⋃ k : OddGridIndex d m,
          (oddGridCell z R hR m k : Set (SpatialCoordinates d)), f x) =
        ∑ k : OddGridIndex d m,
          ∫ x in (oddGridCell z R hR m k : Set (SpatialCoordinates d)), f x := by
    exact integral_iUnion_fintype
      (fun k => (oddGridCell z R hR m k).isOpen.measurableSet)
      (oddGridCell_pairwiseDisjoint z hR m) hcell
  calc
    energy a (centeredCube z R hR : Set (SpatialCoordinates d)) w =
        ∫ x in (centeredCube z R hR : Set (SpatialCoordinates d)), f x := by
          rfl
    _ = ∫ x in ⋃ k : OddGridIndex d m,
          (oddGridCell z R hR m k : Set (SpatialCoordinates d)), f x := by
      exact setIntegral_congr_set (oddGrid_union_ae_eq z hR m).symm
    _ = ∑ k : OddGridIndex d m,
          ∫ x in (oddGridCell z R hR m k : Set (SpatialCoordinates d)), f x := hunion
    _ = ∑ k : OddGridIndex d m,
        energy a (oddGridCell z R hR m k : Set (SpatialCoordinates d))
          (w.restrict (oddGridCell z R hR m k).isOpen
            (oddGridCell_subset z hR m k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rfl

end SubdiffusiveProcess
