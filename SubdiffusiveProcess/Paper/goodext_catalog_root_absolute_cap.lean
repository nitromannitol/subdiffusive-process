module

public import SubdiffusiveProcess.Paper.goodext_catalog_grid_coefficient_bound

@[expose] public section



open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- The actual root's grid has one pathwise coefficient cap for all cutoff-guarded cells. -/
theorem goodext_catalog_root_absolute_cap
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
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
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta
      thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (z0 : SpatialCoordinates d) (R0 : ℝ) (hR0 : 0 < R0)
    (hRoot : z j0 = z0 ∧ r j0 = R0) :
    ∀ om ∈ G, ∃ K : ℝ, 0 ≤ K ∧ ∀ (n k : ℕ) (idx : Fin d → ℤ),
      k ≤ cutoff n →
      let wc : SpatialCoordinates d := fun a => z0 a + (3 : ℝ) ^ (-(k : ℤ)) * idx a
      let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      ∀ hc : 0 < rc,
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R0 hR0 : Set (SpatialCoordinates d)) →
      E.Lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2 +
        (E.lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2)⁻¹ ≤ K * rc ^ (-eta) := by
  classical
  have hGridRoots : ∀ j : J, ∃ g : Grid, gridRoot g = j ∧ origin g = z j := by
    exact hRep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨g0, hgRoot, hgOrigin⟩ := hGridRoots j0
  have hBound := goodext_catalog_grid_coefficient_bound d hd M H Ω P cutoff env J j0 z r hr
    S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
    constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
    sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    hRep 1 (fun _ => g0) (fun _ => hgRoot)
  intro om hom
  obtain ⟨K, hK, hcap⟩ := hBound om hom
  refine ⟨K, hK, ?_⟩
  intro n k idx hk wc rc hc hsub
  have heq : origin g0 = z0 := hgOrigin.trans hRoot.1
  have hrootEq : (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) =
      (centeredCube z0 R0 hR0 : Set (SpatialCoordinates d)) := by
    simp only [centeredCube, hRoot.1, hRoot.2]
  have hcap' := hcap n k 0 idx hk hc
  rw [heq, hrootEq] at hcap'
  exact hcap' hsub

end SubdiffusiveProcess.Paper
