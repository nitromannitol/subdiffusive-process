module

public import SubdiffusiveProcess.Paper.cor_fold
public import SubdiffusiveProcess.Paper.lem_repair_err_fold_localization

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped NNReal
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem mfd_thm_fold
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
    (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
    (hd : 0 < d) (m : ℕ)
    (I P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ)) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1/2) :
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr hD hN af hd (m+n)) ≤
      (1 + 3*(d : ℝ)/((3 : ℝ)^(1-2*s)-1)) *
        ∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr hD hN a hd (m+n) := by
  intro a af
  refine (SubdiffusiveProcess.triadicDefectSup_fold_discounts z hr hD hN hd m I P g hs hs1 ?_).2
  intro N k p
  dsimp
  intro J hdisj hcover
  have hI : (triadicObservationPlanes N I k).Nonempty :=
    triadicAdaptivePlanes_nonempty_of_ae_cover _ _ _ _ hcover
  constructor
  · exact triadicAdaptive_affineDirichletResponse_le_sum _ _ hI J
      (hD N k) (fun n l => observation_killedPoincare z hr hD N k n l) _ p
  · exact triadicAdaptive_affineInverseNeumannResponse_le_sum _ _ hI J
      (hN N k) (fun n l => observation_meanZeroPoincare z hr hN N k n l) _ p

end SubdiffusiveProcess.Paper
