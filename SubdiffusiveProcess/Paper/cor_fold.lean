import SubdiffusiveProcess.Sobolev.FoldDiscounts

open MeasureTheory Set TopologicalSpace
open scoped NNReal
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

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



theorem cor_fold (hd : 0 < d) (m : ℕ)
    (I P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ)) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1/2) :
    let a := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let af := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∀ (N : ℕ) (k : OddGridIndex d (triadicHalf N)) (p : Fin d → ℝ),
      let w := oddGridCenter z r (triadicHalf N) k
      let s := r / (2 * (triadicHalf N : ℝ) + 1)
      let hs : 0 < s := div_pos hr (by positivity)
      let D := observation_killedPoincare z hr hD N k
      let V := observation_meanZeroPoincare z hr hN N k
      let I' := triadicObservationPlanes N I k
      let afU := positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf N) k) af
      ∀ J,
        (triadicAdaptiveLabels I' J : Set (TriadicAdaptiveIndex d J)).PairwiseDisjoint
          (fun t => (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d))) →
        ((⋃ t ∈ triadicAdaptiveLabels I' J,
          (triadicAdaptiveCell w s hs J t : Set (SpatialCoordinates d)))
          =ᵐ[volume] (centeredCube w s hs : Set (SpatialCoordinates d))) →
        (affineDirichletResponse (centeredCube_isBounded w hs) (hD N k) afU p ≤
          ∑ t ∈ triadicAdaptiveLabels I' J,
            affineDirichletResponse (triadicAdaptiveCell_isBounded w hs J t)
              (triadicAdaptiveCell_killedPoincare w hs D J t)
              (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) afU) p) ∧
        (affineInverseNeumannResponse (hN N k) afU p ≤
          ∑ t ∈ triadicAdaptiveLabels I' J,
            affineInverseNeumannResponse (triadicAdaptiveCell_meanZeroPoincare w hs V J t)
              (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root w hs J t) afU) p)) →
    ((∑' n : ℕ, ((3 : ℝ)^(-s))^n * Real.sqrt (triadicDefectSup z hr hD hN af hd (m+n))) ≤
      (1 + Real.sqrt (3*(d : ℝ))/((3 : ℝ)^(1/2-s)-1)) *
        ∑' n : ℕ, ((3 : ℝ)^(-s))^n * Real.sqrt (triadicDefectSup z hr hD hN a hd (m+n))) ∧
    ((∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr hD hN af hd (m+n)) ≤
      (1 + 3*(d : ℝ)/((3 : ℝ)^(1-2*s)-1)) *
        ∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr hD hN a hd (m+n)) :=
  SubdiffusiveProcess.triadicDefectSup_fold_discounts z hr hD hN hd m I P g hs hs1

end Paper
