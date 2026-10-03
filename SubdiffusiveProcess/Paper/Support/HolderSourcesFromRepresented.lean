module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Section9.HolderSourceApproximation

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped Topology ContDiff
noncomputable section
namespace Paper

/-- The existing represented catalogue supplies the whole-cube Hölder source approximation
needed by gluing. Only its genuine standing smooth density is consumed. -/
theorem aux_prop_gluing_holder_sources_from_represented
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [∀ j, Countable (T j)]
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
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hR : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (j : J) (B : SpatialCoordinates d → ℝ) (hBc : Continuous B)
    (hBs : HasCompactSupport B)
    (hBQ : tsupport B ⊆ (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (hB : IsHolderOn alpha Set.univ B) :
    ∃ g : ℕ → D j,
      TendstoUniformly (fun n => f j (g n)) B atTop ∧
      (∀ n, IsHolderOn beta
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (fun x => f j (g n) x - B x)) ∧
      (∀ n, BddAbove {v : ℝ | ∃ x ∈ closure
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        v = |f j (g n) x - B x|}) ∧
      Tendsto (fun n => cAlphaNorm beta
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (fun x => f j (g n) x - B x)) atTop (𝓝 0) := by
  haveI : NeZero d := ⟨by omega⟩
  have haR := hR.2.1
  have hbR := hR.2.2.1
  have hf := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdens := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply SubdiffusiveProcess.Section9.exists_holder_source_approximation
    (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
    (centeredCube (z j) (r j) (hr j)).isOpen (f j)
    (fun g => ⟨(hf j g).1, (hf j g).2.1, (hf j g).2.2.1⟩) (hdens j)
    alpha beta (by linarith only [hbR.1, hbR.2])
    (by linarith only [hbR.1]) hbR.2 (by linarith only [haR.1, hbR.2])
    B hBc hBs hBQ hB

end Paper
