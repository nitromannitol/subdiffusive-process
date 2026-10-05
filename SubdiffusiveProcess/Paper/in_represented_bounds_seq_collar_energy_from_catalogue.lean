module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_energy

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Supply the cell costs of the exact collar from the actual represented catalogue. -/
theorem in_represented_bounds_seq_collar_energy_from_catalogue
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) (κ : ℤ) (hκ : rad j0 = (3 : ℝ) ^ κ)
    (g0 : Grid) (hg0 : gridRoot g0 = j0 ∧ origin g0 = z j0)
    (omega : Ω) (homega : omega ∈ G) (n : ℕ) (Kn : ℝ) (hKn : 0 ≤ Kn)
    (hgrid : constants (gridKey g0) n omega ≤ Kn)
    (Mhi : ℝ)
    (hMhi : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      cutoffCoefficient M H (env n omega) (cutoff n) x ≤ Mhi)
    (hMK : Mhi ≤ Kn * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta))
    (k : ℕ) (r : ℝ) (hr : r = rad j0 / (10 * (3 : ℝ) ^ k))
    (jc : OddGridIndex d (triadicHalf (k + 5)) → J)
    (hjz : ∀ q, z (jc q) = oddGridCenter (z j0) (rad j0) (triadicHalf (k + 5)) q)
    (hjr : ∀ q, rad (jc q) = rad j0 / (3 : ℝ) ^ (k + 5))
    (hcoarse : ∀ q, ((k + 5 : ℕ) : ℤ) < κ → constants (extensionKey (jc q)) n omega ≤ Kn)
    (phi : H1Function (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
    (hsmooth : ContDiff ℝ ∞ phi.toFun) (hcompact : HasCompactSupport phi.toFun)
    (hsupport : tsupport phi.toFun ⊆ (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
    (hrange : ∀ x, 0 ≤ phi.toFun x ∧ phi.toFun x ≤ 1)
    (hzero : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ ≤ 3 * r / 2 →
        phi.toFun x = 0)
    (hone : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      5 * r / 2 ≤ Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ →
        phi.toFun x = 1)
    (hgrad : ∀ x, ‖fderiv ℝ phi.toFun x‖ ≤ Cgrad / r) :
    ∃ w : H10Function (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun
        (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        0 ≤ w.toH1Function.toFun x ∧ w.toH1Function.toFun x ≤ 1) ∧
      (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ ≤ r →
          w.toH1Function.toFun x = 0) ∧
      (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        3 * r ≤ Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ →
          w.toH1Function.toFun x = 1) ∧
      (∀ q : OddGridIndex d (triadicHalf (k + 5)),
        IsWeaklyHarmonicOn (cutoffCoefficient M H (env n omega) (cutoff n))
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf (k + 5)) q : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf (k + 5)) q).isOpen
            (oddGridCell_subset (z j0) (hrad j0) (triadicHalf (k + 5)) q)) ∧
        HasZeroTraceDifferenceOn
          (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf (k + 5)) q : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf (k + 5)) q).isOpen
            (oddGridCell_subset (z j0) (hrad j0) (triadicHalf (k + 5)) q))
          (phi.restrict (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf (k + 5)) q).isOpen
            (oddGridCell_subset (z j0) (hrad j0) (triadicHalf (k + 5)) q))) ∧
      energy (cutoffCoefficient M H (env n omega) (cutoff n)) (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) w.toH1Function ≤
        ((d : ℝ) * 148 * (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) * (rad j0) ^ (d - 1) * (10 / 243 : ℝ) ^ (-1 - eta)) *
          Kn * r ^ (-1 - eta) := by
  have : NeZero d := ⟨by omega⟩
  have hrpos : 0 < r := by rw [hr]; exact div_pos (hrad j0) (by positivity)
  have hmeshpos : 0 < rad j0 / (3 : ℝ) ^ (k + 5) := div_pos (hrad j0) (by positivity)
  have hm := aux_in_represented_bounds_seq_collar_energy_mesh (rad j0) (hrad j0) k
  rw [← hr] at hm
  have hgradMesh : ∀ x, ‖fderiv ℝ phi.toFun x‖ ≤
      Cgrad / (rad j0 / (3 : ℝ) ^ (k + 5)) := by
    intro x
    exact (hgrad x).trans (div_le_div_of_nonneg_left hCgrad.le hmeshpos
      (hm.2.1.trans (by linarith)))
  obtain ⟨hacont, hapos⟩ := aux_lem_cutoffs_cutoffCoefficient_cont_pos M H (env n omega) (cutoff n)
  have hCext : 0 < Cext := hrepresented.2.2.2.1
  have hCcell : 0 ≤ Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) +
      (d : ℝ) * Cgrad ^ 2 := by
    have := Real.rpow_nonneg (hrad j0).le eta
    positivity
  apply in_represented_bounds_seq_collar_energy hd (z j0) (rad j0) (hrad j0)
    k r hr (cutoffCoefficient M H (env n omega) (cutoff n)) hacont hapos phi
    hsmooth hcompact hsupport hrange hzero hone eta _ Kn hCcell hKn
  intro q
  exact aux_lem_cutoffs_rep_collar_cell d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z rad
    hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G coercivityKey
    extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
    cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented Cgrad hCgrad κ hκ g0 hg0
    omega homega n Kn hKn hgrid Mhi hMhi hMK (k + 5) q (jc q) (hjz q) (hjr q) (hcoarse q)
    phi.toFun hsmooth hrange hgradMesh phi rfl

end SubdiffusiveProcess.Paper
