module

public import SubdiffusiveProcess.Paper.conv_represented_estimates

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Shrinking the probability-one event of a represented catalogue to a smaller measurable
probability-one event keeps every represented estimate: all pathwise clauses quantify over the event. -/
theorem conv_represented_estimates_event
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
    (G' : Set Ω) (hsub : G' ⊆ G) (hmeas : MeasurableSet G') (hnull : P G'ᶜ = 0)
    (hrepresented : _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) :
    _root_.SubdiffusiveProcess.Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G' coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey := by
  classical
  rcases hrepresented with
    ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeasE, hlaw, hseq, hroot, hrat, htri,
      hcomplete, horigin, hgrid, hS, hdense, hsource, hsdense, htrace,
      hsourceTrace, hrestrict, happrox, hplateau, hcmeas, hmoment, hnonneg,
      hresponse, hcoarse, hcoercive, habsolute, hgridbound, hsourcebound, hcellbound⟩
  obtain ⟨hcount, _, _, hconv, hbdd⟩ := hseq
  refine ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeasE, hlaw,
    ⟨hcount, hmeas, hnull, fun i om hom => hconv i om (hsub hom),
      fun i om hom => hbdd i om (hsub hom)⟩,
    hroot, hrat, htri, hcomplete, horigin, hgrid, hS, hdense, hsource, hsdense, htrace,
    hsourceTrace, hrestrict, happrox, hplateau, hcmeas, hmoment,
    fun i om hom n => hnonneg i om (hsub hom) n,
    fun j n om hom => hresponse j n om (hsub hom),
    fun j n om hom => hcoarse j n om (hsub hom),
    fun j n om hom => hcoercive j n om (hsub hom),
    fun j n om hom => habsolute j n om (hsub hom),
    fun g n k j om hom => hgridbound g n k j om (hsub hom),
    fun j g n om hom => hsourcebound j g n om (hsub hom),
    fun j h n om hom => hcellbound j h n om (hsub hom)⟩

end SubdiffusiveProcess.Paper
