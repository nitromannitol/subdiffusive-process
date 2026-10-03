module

public import SubdiffusiveProcess.Paper.Support.B7cCatalogueBounds
public import SubdiffusiveProcess.Paper.Support.B7cExtensionBank

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- Every cell in the actual triple mesh has an index in the represented catalogue. -/
theorem aux_mfd_prop_gluing_catalogue_cells
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
    (hrepresented : conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
      Index resp respLim constants G coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
      cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (omega : Ω) (hmem : omega ∈ G) (iQ : J)
    (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq) (h3rq : 0 < 3 * rq)
    (hz : z iQ = zq) (hrad : rad iQ = 3 * rq)
 :
    ∃ jc : OddGridIndex d (triadicHalf 1) → J,
      ∀ k, z (jc k) = oddGridCenter zq (3 * rq) (triadicHalf 1) k ∧ rad (jc k) = rq := by
  classical
  rcases hrepresented with
    ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeas, hlaw, hseq, hroot, hrat, htri,
      hcomplete, horigin, hgrid, hS, hdense, hsource, hsdense, htrace,
      hsourceTrace, hrestrict, happrox, hplateau, hcmeas, hmoment, hnonneg,
      hresponse, hcoarse, hcoercive, habsolute, hgridbound, hsourcebound, hcellbound⟩
  have hQeq : centeredCube (z iQ) (rad iQ) (hr iQ) = centeredCube zq (3 * rq) h3rq := by
    apply SetLike.coe_injective
    change Metric.ball (z iQ) (rad iQ / 2) = Metric.ball zq (3 * rq / 2)
    rw [hz, hrad]
  obtain ⟨ell, hell⟩ := htri iQ
  have hRq : rq = (3 : ℝ) ^ (ell - 1) := by
    calc rq = rad iQ / 3 := by rw [hrad]; ring
      _ = (3 : ℝ) ^ ell / 3 := by rw [hell]
      _ = (3 : ℝ) ^ (ell - 1) := by
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  have hRootRat : ∀ i : Fin d, ∃ q : ℚ, zq i = (q : ℝ) := by
    simpa only [hz] using hrat iQ
  have hSideRat : ∃ q : ℚ, 3 * rq = (q : ℝ) := by
    refine ⟨(3 : ℚ) ^ ell, ?_⟩
    rw [← hrad, hell]
    simp only [Rat.cast_zpow, Rat.cast_ofNat]
  have hex : ∀ k : OddGridIndex d (triadicHalf 1),
      ∃ jc : J, z jc = oddGridCenter zq (3 * rq) (triadicHalf 1) k ∧ rad jc = rq := by
    intro k
    have hratK := aux_in_represented_catalogue_ratCoord_oddGridCenter d (triadicHalf 1)
      zq (3 * rq) k hRootRat hSideRat
    have hInRoot : (centeredCube (oddGridCenter zq (3 * rq) (triadicHalf 1) k) rq hrq :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (rad j0) (hr j0) : Set (SpatialCoordinates d)) := by
      rw [← aux_prop_gluing_cell_eq zq rq hrq h3rq k]
      exact (oddGridCell_subset zq h3rq (triadicHalf 1) k).trans
        (by simpa only [hQeq] using hroot iQ)
    exact hcomplete _ rq hrq hratK ⟨ell - 1, hRq⟩ hInRoot
  choose jc hjz hjr using hex
  exact ⟨jc, fun k => ⟨hjz k, hjr k⟩⟩

end Paper
