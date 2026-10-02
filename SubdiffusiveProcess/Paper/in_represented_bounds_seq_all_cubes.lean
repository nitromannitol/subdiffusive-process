import SubdiffusiveProcess.Paper.in_represented_bounds_seq_from_catalogue
import SubdiffusiveProcess.Paper.conv_represented_estimates_subcatalogue

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- All cubes of a represented catalogue satisfy the bounds simultaneously. -/
theorem in_represented_bounds_seq_all_cubes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
    (E : Paper.in_J d)
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
      Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hext : InfraredCharacterization M H → aux_lem_cutoffs_root_uniform_extrema d M H eta)
    (hseed : ∀ (j : J) (k : ℕ), ∃ b : T j, (thetaH1 j b).toFun =
      bufferedCollarProfile d (z j) (rad j) (rad j / (10 * (3 : ℝ) ^ k)))
    (Glim : ∀ j : J, Ω → DomainL2 (centeredCube (z j) (rad j) (hrad j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (rad j) (hrad j)))
    (hconv : ∀ j : J, ∀ᵐ omega ∂P, ∀ g : DomainL2 (centeredCube (z j) (rad j) (hrad j)),
      Tendsto (fun n => (responseSolution (S j)
        (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hrad j))
        ((sobolevVolumeLoad g).comp (S j).space.subtypeL)).val.1) atTop (𝓝 (Glim j omega g))) :
    ∀ᵐ omega ∂P, ∀ j : J, in_represented_bounds_seq d hd (z j) (rad j) (hrad j) (S j)
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hrad j))
      (Glim j omega) := by
  classical
  rw [ae_all_iff]
  intro jTarget
  let Q := fun j => (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d))
  let Small := {j : J // Q j ⊆ Q jTarget}
  let SmallGrid := {g : Grid // Q (gridRoot g) ⊆ Q jTarget}
  have hsub := conv_represented_estimates_subcatalogue d hd M H Cext beta alpha eta t orders
    Ω P cutoff env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim
    constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented jTarget
  exact in_represented_bounds_seq_from_catalogue d hd M H Cext beta alpha eta t orders Ω P
    cutoff env Small ⟨jTarget, subset_rfl⟩
    (fun j => z j.val) (fun j => rad j.val) (fun j => hrad j.val)
    (fun j => S j.val) (fun j => D j.val) (fun j => f j.val)
    (fun j => T j.val) (fun j => theta j.val) (fun j => thetaH1 j.val)
    (fun j => usrc j.val) (fun j => srcRep j.val) (fun j => ucell j.val)
    E Index resp respLim constants G
    (fun j => coercivityKey j.val) (fun j => extensionKey j.val) (fun j => lambdaKey j.val)
    (fun j => sourceResponseKey j.val) (fun j => sourceGrowthKey j.val)
    (fun j => sourceHolderKey j.val) (fun j => cellResponseKey j.val)
    (fun j => cellGrowthKey j.val) (fun j => cellHolderKey j.val)
    SmallGrid (fun g => origin g.val) (fun g => ⟨gridRoot g.val, g.property⟩)
    (fun g => gridKey g.val) hsub hInterp hext (hseed jTarget) (Glim jTarget) (hconv jTarget)

end Paper

