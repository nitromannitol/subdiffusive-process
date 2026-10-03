module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

/-- Two standing coefficient interfaces agree on every valid cell because both
charts are tied to the same actual coefficient. -/
theorem aux_thm_prop_coarse_input_eq
    {d : ℕ} (I J : in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (hsub : (centeredCube w s hs : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (q : ℝ≥0∞) (hq : 1 ≤ q) :
    I.lam z r hr a w s sigma q = J.lam z r hr a w s sigma q ∧
    I.Lam z r hr a w s sigma q = J.Lam z r hr a w s sigma q := by
  have hc : ∀ (k : ℤ) (S : Homogenization.TriadicCube d),
      S ∈ descendantsAtScale (originCube d 0) k →
      Book.Ch02.CoeffOn.AEEq ((I.chart z r hr a w s).coeffOn S)
        ((J.chart z r hr a w s).coeffOn S) := by
    intro k S hS
    have hcontain := openCubeSet_subset_of_mem_descendantsAtScale
      (descendant_scale_le_of_mem_descendantsAtScale hS) hS
    change ((I.chart z r hr a w s).coeffOn S).toCoeffField
      =ᵐ[volume.restrict (openCubeSet S)] ((J.chart z r hr a w s).coeffOn S).toCoeffField
    filter_upwards [I.chart_eq z r hr a w s hs hsub S hcontain,
      J.chart_eq z r hr a w s hs hsub S hcontain] with x hxI hxJ
    exact hxI.trans hxJ.symm
  constructor
  · rw [I.lam_eq z r hr a w s hs hsub sigma hsigma q hq,
      J.lam_eq z r hr a w s hs hsub sigma hsigma q hq]
    exact SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.lambdaSq_eq_of_descendantAEEq
      (originCube d 0) hc sigma _
  · rw [I.Lam_eq z r hr a w s hs hsub sigma hsigma q hq,
      J.Lam_eq z r hr a w s hs hsub sigma hsigma q hq]
    exact SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.LambdaSq_eq_of_descendantAEEq
      (originCube d 0) hc sigma _

theorem aux_thm_prop_catalogue_change_input
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
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (E2 : in_J d)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) :
    conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E2 Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey := by
  have hba := hRep.2.2.1
  have halpha := hRep.2.1.1
  have hsigma : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hba.1, hba.2]
  have hfun (j : J) (n : ℕ) (om : Ω) := aux_thm_prop_coarse_input_eq E E2 (z j) (r j) (hr j)
    (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
    (z j) (r j) (hr j) subset_rfl ((beta - 1 / 2) / 4) hsigma 2 (by norm_num)
  have hLam (j : J) (n : ℕ) (om : Ω) := (hfun j n om).2
  have hlam (j : J) (n : ℕ) (om : Ω) := (hfun j n om).1
  simpa only [conv_represented_estimates, hLam, hlam] using hRep




theorem conv_represented_estimates_change_input
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
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (E2 : in_J d)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) :
    conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E2 Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey :=
  aux_thm_prop_catalogue_change_input d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey E2 hRep

end Paper
