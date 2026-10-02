import SubdiffusiveProcess.Paper.conv_represented_estimates

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_conv_represented_estimates_subcatalogue_union
    {A B X : Type*} [DecidableEq B] (s : Finset A) (e : A → B) (f : B → Set X) :
    (⋃ b ∈ s.image e, f b) = ⋃ a ∈ s, f (e a) := by
  ext x
  simp only [mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨a, ha, hx⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨e a, ⟨a, ha, rfl⟩, hx⟩

/-- Restricting the catalogue and its grids to any catalogue cube preserves all represented estimates. -/
theorem conv_represented_estimates_subcatalogue
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
    (jTarget : J) :
    let Q := fun j => (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d))
    let Small := {j : J // Q j ⊆ Q jTarget}
    let SmallGrid := {g : Grid // Q (gridRoot g) ⊆ Q jTarget}
    conv_represented_estimates d hd M H Ω P cutoff env Small ⟨jTarget, subset_rfl⟩
      (fun j => z j.val) (fun j => rad j.val) (fun j => hrad j.val)
      (fun j => S j.val) (fun j => D j.val) (fun j => f j.val)
      (fun j => T j.val) (fun j => theta j.val) (fun j => thetaH1 j.val)
      (fun j => usrc j.val) (fun j => srcRep j.val) (fun j => ucell j.val)
      Cext beta alpha eta t orders E Index resp respLim constants G
      (fun j => coercivityKey j.val) (fun j => extensionKey j.val) (fun j => lambdaKey j.val)
      (fun j => sourceResponseKey j.val) (fun j => sourceGrowthKey j.val)
      (fun j => sourceHolderKey j.val) (fun j => cellResponseKey j.val)
      (fun j => cellGrowthKey j.val) (fun j => cellHolderKey j.val)
      SmallGrid (fun g => origin g.val) (fun g => ⟨gridRoot g.val, g.property⟩)
      (fun g => gridKey g.val) := by
  classical
  dsimp only
  rcases hrepresented with
    ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeas, hlaw, hseq, hroot, hrat, htri,
      hcomplete, horigin, hgrid, hS, hdense, hsource, hsdense, htrace,
      hsourceTrace, hrestrict, happrox, hplateau, hcmeas, hmoment, hnonneg,
      hresponse, hcoarse, hcoercive, habsolute, hgridbound, hsourcebound, hcellbound⟩
  refine ⟨ht, ha, hb, hC, hord, hcut, hIR, hmeas, hlaw, hseq,
    fun j => j.property, fun j => hrat j.val, fun j => htri j.val, ?_,
    fun g => horigin g.val, ?_, fun j => hS j.val, fun j => hdense j.val,
    fun j => hsource j.val, fun j => hsdense j.val, fun j => htrace j.val,
    fun j => hsourceTrace j.val, fun j k => hrestrict j.val k.val,
    fun j => happrox j.val, ?_, hcmeas, hmoment, hnonneg,
    fun j => hresponse j.val, fun j => hcoarse j.val, fun j => hcoercive j.val,
    fun j => habsolute j.val, fun g n k j => hgridbound g.val n k j.val,
    fun j => hsourcebound j.val, fun j => hcellbound j.val⟩
  · intro z' r' hr' hzr hrt hsub
    obtain ⟨j, hjz, hjr⟩ := hcomplete z' r' hr' hzr hrt (hsub.trans (hroot jTarget))
    have hj : (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jTarget) (rad jTarget) (hrad jTarget) : Set (SpatialCoordinates d)) := by
      simpa only [centeredCube, hjz, hjr] using hsub
    exact ⟨⟨j, hj⟩, hjz, hjr⟩
  · intro j
    obtain ⟨g, hg, hgo⟩ := hgrid j.val
    have hsub : (centeredCube (z (gridRoot g)) (rad (gridRoot g)) (hrad (gridRoot g)) :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jTarget) (rad jTarget) (hrad jTarget) : Set (SpatialCoordinates d)) := by
      rw [hg]
      exact j.property
    exact ⟨⟨g, hsub⟩, Subtype.ext hg, hgo⟩
  · intro j s o hs ho m
    have hs' : (⋃ k ∈ s.image Subtype.val,
        closure (centeredCube (z k) (rad k) (hrad k) : Set (SpatialCoordinates d))) ⊆
        (⋃ k ∈ o.image Subtype.val,
          (centeredCube (z k) (rad k) (hrad k) : Set (SpatialCoordinates d))) := by
      simpa only [aux_conv_represented_estimates_subcatalogue_union] using hs
    have ho' : closure (⋃ k ∈ o.image Subtype.val,
        (centeredCube (z k) (rad k) (hrad k) : Set (SpatialCoordinates d))) ⊆
        (centeredCube (z j.val) (rad j.val) (hrad j.val) : Set (SpatialCoordinates d)) := by
      simpa only [aux_conv_represented_estimates_subcatalogue_union] using ho
    obtain ⟨b, W, hW, hSW, hWO, hrange, hone, hsupp⟩ :=
      hplateau j.val (s.image Subtype.val) (o.image Subtype.val) hs' ho' m
    refine ⟨b, W, hW, ?_, ?_, hrange, hone, ?_⟩
    · simpa only [aux_conv_represented_estimates_subcatalogue_union] using hSW
    · simpa only [aux_conv_represented_estimates_subcatalogue_union] using hWO
    · simpa only [aux_conv_represented_estimates_subcatalogue_union] using hsupp

end Paper

