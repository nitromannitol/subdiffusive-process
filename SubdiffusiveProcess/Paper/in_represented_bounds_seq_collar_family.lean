module

public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_energy_from_catalogue
public import SubdiffusiveProcess.Paper.in_represented_bounds_seq_finite_mesh
@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- One family simultaneously supplies exact collar profiles, uniform Holder bounds,
and the quantitative energy bound from the represented catalogue. -/
theorem in_represented_bounds_seq_collar_family
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
    (omega : Ω) (homega : omega ∈ G)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (hgrid : ∀ n, constants (gridKey g0) n omega ≤ KN n)
    (Mhi : ℕ → ℝ)
    (hMhi : ∀ n, ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      cutoffCoefficient M H (env n omega) (cutoff n) x ≤ Mhi n)
    (hMK : ∀ n, Mhi n ≤ KN n * (3 : ℝ) ^ (((cutoff n : ℕ) : ℝ) * eta))
    (k : ℕ) (r : ℝ) (hr : r = rad j0 / (10 * (3 : ℝ) ^ k))
    (jc : OddGridIndex d (triadicHalf (k + 5)) → J)
    (hjz : ∀ q, z (jc q) = oddGridCenter (z j0) (rad j0) (triadicHalf (k + 5)) q)
    (hjr : ∀ q, rad (jc q) = rad j0 / (3 : ℝ) ^ (k + 5))
    (hcoarse : ∀ n q, ((k + 5 : ℕ) : ℤ) < κ → constants (extensionKey (jc q)) n omega ≤ KN n)
    (b : T j0)
    (hsmooth : ContDiff ℝ ∞ (thetaH1 j0 b).toFun)
    (hcompact : HasCompactSupport (thetaH1 j0 b).toFun)
    (hsupport : tsupport (thetaH1 j0 b).toFun ⊆
      (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
    (hrange : ∀ x, 0 ≤ (thetaH1 j0 b).toFun x ∧ (thetaH1 j0 b).toFun x ≤ 1)
    (hzero : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ ≤ 3 * r / 2 →
        (thetaH1 j0 b).toFun x = 0)
    (hone : ∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      5 * r / 2 ≤ Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ →
        (thetaH1 j0 b).toFun x = 1)
    (hgrad : ∀ x, ‖fderiv ℝ (thetaH1 j0 b).toFun x‖ ≤ Cgrad / r) :
    ∃ w : ℕ → H10Function (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
      ∃ Kchi : ℝ, 0 ≤ Kchi ∧ ∀ n,
        ContinuousOn (w n).toH1Function.toFun
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
          (w n).toH1Function.toFun ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
          (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
          (w n).toH1Function.toFun ≤ Kchi ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          0 ≤ (w n).toH1Function.toFun x ∧ (w n).toH1Function.toFun x ≤ 1) ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ ≤ r →
            (w n).toH1Function.toFun x = 0) ∧
        (∀ x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
          3 * r ≤ Metric.infDist x (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))ᶜ →
            (w n).toH1Function.toFun x = 1) ∧
        energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) (w n).toH1Function ≤
          ((d : ℝ) * 148 * (Cext * (1 + Cgrad) ^ 2 * (1 + rad j0 ^ eta) + (d : ℝ) * Cgrad ^ 2) *
            (rad j0) ^ (d - 1) * (10 / 243 : ℝ) ^ (-1 - eta)) * KN n * r ^ (-1 - eta) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hrootpos : 0 < rad j0 := hrad j0
  have halpha : 0 < alpha := by
    have hba := hrepresented.2.2.1
    linarith [hba.1, hba.2]
  choose w hwcont hwrange hwzero hwone hwharm hwenergy using fun n =>
    in_represented_bounds_seq_collar_energy_from_catalogue d hd M H Cext beta alpha eta t orders Ω P
      cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented Cgrad
      hCgrad κ hκ g0 hg0 omega homega n (KN n) (hKN n) (hgrid n) (Mhi n) (hMhi n) (hMK n)
      k r hr jc hjz hjr (hcoarse n) (thetaH1 j0 b) hsmooth hcompact hsupport hrange hzero hone hgrad
  choose Ec Gc Hc hEc hGc hHc hcell using fun q : OddGridIndex d (triadicHalf (k + 5)) =>
    aux_lem_cutoffs_rep_plateau_cell d hd M H Cext beta alpha eta t orders Ω P cutoff env J j0 z rad
      hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants G coercivityKey
      extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
      cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented omega homega b (k + 5) q
  let Hsum : ℝ := ∑ q : OddGridIndex d (triadicHalf (k + 5)), Hc q
  have hHsum : 0 ≤ Hsum := Finset.sum_nonneg fun q _ => hHc q
  have hHle : ∀ q, Hc q ≤ Hsum := fun q =>
    Finset.single_le_sum (fun q _ => hHc q) (Finset.mem_univ q)
  refine ⟨w, 1 + (d : ℝ) * (2 * Hsum + 2 * 1 *
    (rad j0 / (2 * (triadicHalf (k + 5) : ℝ) + 1)) ^ (-alpha)), by positivity, ?_⟩
  intro n
  have hholder := aux_in_represented_finite_mesh_global_holder (z j0) (rad j0) (hrad j0)
    (triadicHalf (k + 5)) alpha halpha 1 Hsum zero_le_one hHsum (w n).toH1Function.toFun
    (fun x hx => by rw [abs_of_nonneg (hwrange n x hx).1]; exact (hwrange n x hx).2) ?_
  · exact ⟨hwcont n, hholder.1, hholder.2, hwrange n, hwzero n, hwone n, hwenergy n⟩
  · intro q x hx y hy
    have hb := hcell q n ((w n).toH1Function.restrict
      (oddGridCell (z j0) (rad j0) (hrad j0) (triadicHalf (k + 5)) q).isOpen
      (oddGridCell_subset (z j0) (hrad j0) (triadicHalf (k + 5)) q))
      (hwharm n q).1 (hwharm n q).2
      ((hwcont n).mono (closure_mono
        (oddGridCell_subset (z j0) (hrad j0) (triadicHalf (k + 5)) q)))
    exact (hb.2.2 x hx y hy).trans (mul_le_mul_of_nonneg_right (hHle q)
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _))

end SubdiffusiveProcess.Paper