module

public import SubdiffusiveProcess.Paper.Support.B7cHolderAssembly
public import SubdiffusiveProcess.Paper.Support.B7cSmoothTracePackages
public import SubdiffusiveProcess.Paper.Support.B7cCatalogueCells
public import SubdiffusiveProcess.Paper.Support.B7cTraceTransports
public import SubdiffusiveProcess.Paper.Support.HolderSourcesFromRepresented
public import SubdiffusiveProcess.Section9.HolderCompactExtension

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- Derive the Hölder trace package from the actual represented catalogue. -/
theorem aux_mfd_prop_gluing_trace_exists
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hr : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (omega : Ω) (iQ : J)
    (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq)
    (hz : z iQ = zq) (hrad : rad iQ = 3 * rq)
    (S0 : ResponseSpace (centeredCube zq (3 * rq) h3rq))
    (G0 : DomainL2 (centeredCube zq (3 * rq) h3rq) →L[ℝ]
      DomainL2 (centeredCube zq (3 * rq) h3rq))
    (L : aux_limit_form_package_limit_side d hd zq (3 * rq) h3rq S0 G0
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) zq h3rq))
    (hR : conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) (hmem : omega ∈ G)
    (hS0 : S0.space = killedSobolevGraph (centeredCube zq (3 * rq) h3rq))
    (b : SpatialCoordinates d → ℝ)
    (hb : Lane4.IsHolderOn alpha (frontier (centeredCube zq rq hrq : Set (SpatialCoordinates d))) b) :
    ∃ Lam : ℝ, ∃ U : DomainL2 (centeredCube zq (3 * rq) h3rq),
      ∃ Uc : SpatialCoordinates d → ℝ,
        aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
          zq rq hrq zq (3 * rq) h3rq rfl rfl S0 G0 L E Cext beta alpha b Lam U Uc := by

  classical
  haveI : NeZero d := ⟨by omega⟩
  have hb0 : 0 ≤ beta := by linarith only [hR.2.2.1.1]
  have hba : beta ≤ alpha := hR.2.2.1.2.le
  have ha0 : 0 < alpha := by linarith only [hR.2.2.1.1, hR.2.2.1.2]
  have ha1 : alpha ≤ 1 := hR.2.1.1.le
  have hC : 0 ≤ Cext := hR.2.2.2.1.le
  have hQeq : centeredCube (z iQ) (rad iQ) (hr iQ) = centeredCube zq (3 * rq) h3rq := by
    apply SetLike.coe_injective
    change Metric.ball (z iQ) (rad iQ / 2) = Metric.ball zq (3 * rq / 2)
    rw [hz, hrad]
  obtain ⟨B, hBc, hBsupp, hBinside, hBholder, hBb⟩ :=
    SubdiffusiveProcess.Section9.exists_holder_compact_cube_extension zq rq hrq h3rq alpha ha0 ha1 b hb
  obtain ⟨g, hgU, hgHol, hgBdd, hgNorm⟩ :=
    aux_prop_gluing_holder_sources_from_represented d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hR iQ B hBc hBsupp
      (by simpa only [hQeq] using hBinside) hBholder
  have hSmooth := fun k => aux_mfd_prop_gluing_smooth_trace_package d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    omega iQ zq rq hrq h3rq hz hrad S0 G0 L (g k) hR hmem hS0
  choose PhiH Phiq W WS Uk Uck hPhiH hPhiq hW hUk1 hUk2 hUk3 hUk4 hUk5 hUk6 hUk7 hUk8 hUk9
    using hSmooth
  obtain ⟨jc, hjc⟩ := aux_mfd_prop_gluing_catalogue_cells d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    hR omega hmem iQ zq rq hrq h3rq hz hrad
  let Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ := fun k n =>
    E.Lam (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq
      (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
        (oddGridCenter zq (3 * rq) (triadicHalf 1) k) hrq)
      (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq ((beta - 1 / 2) / 4) 2
  let UgridStar := fun k => sSup (Set.range (Ugrid k))
  have hBanks : ∀ k : OddGridIndex d (triadicHalf 1),
      BddAbove (Set.range (Ugrid k)) ∧ 0 ≤ UgridStar k ∧
      (∀ n, 0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k) ∧
      ∀ n, ∀ e : H1Function (centeredCube
          (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun (closure (centeredCube
          (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq e.toFun →
        cellDirichletInfimum (cutoffCoefficient M H (env n omega) (cutoff n))
          (centeredCube (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq : Set (SpatialCoordinates d)) e ≤
        Cext * Ugrid k n * rq ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq e.toFun ^ 2 := by
    intro k
    have hk := aux_mfd_prop_gluing_extension_bank d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hR omega hmem (jc k)
    exact aux_mfd_prop_gluing_bank_congr M H (fun n => env n omega) cutoff E Cext beta
      (z (jc k)) (oddGridCenter zq (3 * rq) (triadicHalf 1) k) (rad (jc k)) rq
      (hr (jc k)) hrq (hjc k).1 (hjc k).2 hk
  have hGridBound : ∀ k n, ∀ e : H1Function
      (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq e.toFun →
      cellDirichletInfimum (cutoffCoefficient M H (env n omega) (cutoff n))
        (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d)) e ≤
      Cext * Ugrid k n * rq ^ ((d : ℝ) - 2) *
        cellBoundaryQuotientNorm beta (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq e.toFun ^ 2 := by
    intro k
    exact aux_mfd_prop_gluing_finite_bound_congr
      (centeredCube (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq : Set (SpatialCoordinates d))
      (oddGridCell zq (3 * rq) h3rq (triadicHalf 1) k : Set (SpatialCoordinates d))
      (aux_prop_gluing_cell_eq zq rq hrq h3rq k).symm
      (fun n => cutoffCoefficient M H (env n omega) (cutoff n))
      (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq beta Cext (Ugrid k)
      (hBanks k).2.2.2
  let mid : OddGridIndex d (triadicHalf 1) := fun _ => ⟨triadicHalf 1, by omega⟩
  have hmid : oddGridCenter zq (3 * rq) (triadicHalf 1) mid = zq := by
    funext i
    simp [oddGridCenter, mid, triadicHalf]
  have hMidBank := aux_mfd_prop_gluing_bank_congr M H (fun n => env n omega) cutoff E Cext beta
    (oddGridCenter zq (3 * rq) (triadicHalf 1) mid) zq rq rq hrq hrq hmid rfl (hBanks mid)
  have hf := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact aux_mfd_prop_gluing_holder_from_smooth hd M H (fun n => env n omega) cutoff E alpha
    zq rq hrq h3rq (aux_mfd_prop_gluing_triple_subset zq zq rq (3 * rq) hrq h3rq rfl rfl)
    (fun k => oddGridCell_subset zq h3rq (triadicHalf 1) k) beta hb0 S0 G0 L Cext hC
    hMidBank.1 hMidBank.2.2.1 hMidBank.2.2.2 Ugrid UgridStar
    (fun k => (hBanks k).2.2.1) hGridBound (fun k => f iQ (g k)) B hBc hBsupp hBinside
    hBholder (fun k => (hf iQ (g k)).1.continuous) hgU
    (by simpa only [hQeq] using hgHol) (by simpa only [hQeq] using hgBdd)
    (by simpa only [hQeq] using hgNorm) b hba hb hBb PhiH hPhiH Phiq hPhiq W WS hW
    Uk Uck hUk1 hUk2 hUk3 hUk4 hUk5 hUk6 hUk7 hUk9 hUk8

end Paper
