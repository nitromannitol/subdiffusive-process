module

public import SubdiffusiveProcess.Lane4.ProbeAssembly
public import SubdiffusiveProcess.Lane4.FoldedProbe
public import SubdiffusiveProcess.Lane4.LogRepresentation
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Paper.cor_fold

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

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



theorem lane4_folded_probe_discounted_le
    (hd : 0 < d) (m : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1 / 2)
    (a : SpatialCoordinates d → ℝ) (alpha : ℝ) (halpha : 0 < alpha)
    (I P : Finset (Fin d)) (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    (hz : z = 0) (hrr : r = (3 : ℝ) ^ m)
    (origData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a)
    (foldData : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
      (fun x => a (coordinateFold z I P x))) :
    let g := logPotentialOnCube z hr (fun x => a x / alpha)
      (hcont.div_const alpha) (fun x => div_pos (hpos x) halpha)
    let af := expPotentialCoefficient (Ω := centeredCube z r hr)
      (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
        (g.comp (coordinateFoldOnCube z hr I P)))
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
    (∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
        SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
          (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))
          foldData.toTriadicCoeffFamily alpha) ≤
      ENNReal.ofReal (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s) - 1)) *
        ∑' l : ℕ, ENNReal.ofReal (Homogenization.Book.Ch02.geometricWeight s 2 l) *
          SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
            (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))
            origData.toTriadicCoeffFamily alpha := by
  intro g af hsub
  have hbc : Continuous fun x => a x / alpha := hcont.div_const alpha
  have hbp : ∀ x, 0 < a x / alpha := fun x => div_pos (hpos x) halpha
  have ht0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s)) := Real.rpow_nonneg (by norm_num) _
  have ht1 : (3 : ℝ) ^ (-(2 * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  have hden : (0 : ℝ) < (3 : ℝ) ^ (1 - 2 * s) - 1 := by
    have h1 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * s) :=
      (Real.one_lt_rpow_iff_of_pos (by norm_num)).2 (Or.inl ⟨by norm_num, by linarith⟩)
    linarith
  have hC : (0 : ℝ) ≤ 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s) - 1) := by positivity
  set aRoot := expPotentialCoefficient (Ω := centeredCube z r hr)
    (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr) g) with haR
  have hRoot : ((aRoot.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => a x / alpha) :=
    expPotentialCoefficient_logPotentialOnCube_coeFn z hr _ hbc hbp
  have hFold : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => a (coordinateFold z I P x) / alpha) :=
    expPotentialCoefficient_foldedLogPotential_coeFn z hr I P _ hbc hbp
  have hcells : ∀ (l : ℕ) (j : OddGridIndex d (triadicHalf l)),
      (oddGridCell z r hr (triadicHalf l) j : Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet (descendantCube (d := d) m l j) := by
    subst hz
    subst hrr
    exact fun l j => oddGridCell_eq_openCubeSet_descendantCube m l hr j
  have hpO : ∀ l : ℕ,
      SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
          (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))
          origData.toTriadicCoeffFamily alpha =
        ENNReal.ofReal (triadicDefectSup z hr hD hN aRoot hd l) :=
    fun l => paperMaxDescendantProbeAtScale_eq_ofReal_triadicDefectSup
      z hr hD hN aRoot hd m l halpha origData hRoot (hcells l)
  have hpF : ∀ l : ℕ,
      SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
          (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))
          foldData.toTriadicCoeffFamily alpha =
        ENNReal.ofReal (triadicDefectSup z hr hD hN af hd l) :=
    fun l => paperMaxDescendantProbeAtScale_eq_ofReal_triadicDefectSup
      z hr hD hN af hd m l halpha foldData hFold (hcells l)
  have hreal := (triadicDefectSup_fold_discounts z hr hD hN hd 0 I P g hs hs1 hsub).2
  simp only [Nat.zero_add] at hreal
  have hsF : Summable fun l : ℕ =>
      ((3 : ℝ) ^ (-(2 * s))) ^ l * triadicDefectSup z hr hD hN af hd l := by
    simpa using triadicDefectSup_discount_summable z hr hD hN af hd 0 ht0 ht1
  have hsO : Summable fun l : ℕ =>
      ((3 : ℝ) ^ (-(2 * s))) ^ l * triadicDefectSup z hr hD hN aRoot hd l := by
    simpa using triadicDefectSup_discount_summable z hr hD hN aRoot hd 0 ht0 ht1
  simp only [hpO, hpF]
  exact tsum_geometricWeight_ofReal_le_of_real hs hs1
    (fun l => triadicDefectSup_nonneg z hr hD hN af hd l)
    (fun l => triadicDefectSup_nonneg z hr hD hN aRoot hd l) hC hsF hsO hreal

end Paper
