module

public import SubdiffusiveProcess.Paper.conv_represented_estimates

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The genuine represented extension bank supplies the guarded supremum of the
ACTUAL coarse coefficient and the finite trace inequality used by gluing. -/
theorem aux_mfd_prop_gluing_extension_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
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
    (omega : Ω) (hmem : omega ∈ G) (j : J) :
    let Uq := fun n => E.Lam (z j) (rad j) (hr j)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hr j))
      (z j) (rad j) ((beta - 1 / 2) / 4) 2
    BddAbove (Set.range Uq) ∧ 0 ≤ sSup (Set.range Uq) ∧
    (∀ n, 0 ≤ Uq n ∧ Uq n ≤ sSup (Set.range Uq)) ∧
    ∀ n, ∀ e : H1Function (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (z j) (rad j) e.toFun →
      cellDirichletInfimum (cutoffCoefficient M H (env n omega) (cutoff n))
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)) e ≤
      Cext * Uq n * (rad j) ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta (z j) (rad j) e.toFun ^ 2 := by
  classical
  rcases hrepresented with
    ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeas, hlaw, hseq, hroot, hrat, htri,
      hcomplete, horigin, hgrid, hS, hdense, hsource, hsdense, htrace,
      hsourceTrace, hrestrict, happrox, hplateau, hcmeas, hmoment, hnonneg,
      hresponse, hcoarse, hcoercive, habsolute, hgridbound, hsourcebound, hcellbound⟩
  let Uq := fun n => E.Lam (z j) (rad j) (hr j)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hr j))
      (z j) (rad j) ((beta - 1 / 2) / 4) 2
  have hEq : ∀ n, constants (extensionKey j) n omega = Uq n :=
    fun n => (hcoarse j n omega hmem).1
  have hU0 : ∀ n, 0 ≤ Uq n := fun n => hEq n ▸ hnonneg (extensionKey j) omega hmem n
  obtain ⟨B, hB⟩ := hseq.2.2.2.2 (extensionKey j) omega hmem
  have hBdd : BddAbove (Set.range Uq) := by
    refine ⟨B, ?_⟩
    rintro v ⟨n, rfl⟩
    rw [← hEq n]
    exact (le_abs_self _).trans (hB n)
  have hUS : ∀ n, Uq n ≤ sSup (Set.range Uq) :=
    fun n => le_csSup hBdd (Set.mem_range_self n)
  refine ⟨hBdd, (hU0 0).trans (hUS 0), (fun n => ⟨hU0 n, hUS n⟩), ?_⟩
  intro n e he hc
  have h := habsolute j n omega hmem e he hc
  rw [hEq n] at h
  exact h

end SubdiffusiveProcess.Paper
