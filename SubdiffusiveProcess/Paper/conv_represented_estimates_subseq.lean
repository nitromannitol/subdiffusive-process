import SubdiffusiveProcess.Paper.conv_represented_estimates
import SubdiffusiveProcess.Paper.conv_represented_sequence

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal

noncomputable section
namespace Paper

/-! This file establishes that `conv_represented_estimates` (the standing
represented-catalogue convention of the local-estimate subsection) restricts
along any subsequence `psi : ℕ → ℕ` of its cutoff/environment sequence:
precomposing every ℕ-indexed field with `psi` again satisfies the same
convention.  It does not construct or use any new represented sequence; it is
a purely reindexing lemma, since every clause of `conv_represented_estimates`
is index-free or a bare `∀ n : ℕ` universal. -/

/-- The represented-sequence convention (`conv_represented_sequence`)
restricts to every subsequence of its cutoff index. -/
theorem aux_conv_represented_estimates_subseq_sequence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ)
    (const : ι → ℕ → Ω → ℝ) (G : Set Ω)
    (hseq : Paper.conv_represented_sequence P resp respLim const G)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) :
    Paper.conv_represented_sequence P (fun i n => resp i (psi n)) respLim
      (fun i n => const i (psi n)) G := by
  unfold Paper.conv_represented_sequence at hseq ⊢
  obtain ⟨hCount, hMeas, hProb, hTendResp, hBoundConst⟩ := hseq
  refine ⟨hCount, hMeas, hProb, ?_, ?_⟩
  · exact fun i om hom => (hTendResp i om hom).comp hpsi.tendsto_atTop
  · exact fun i om hom =>
      let ⟨M, hM⟩ := hBoundConst i om hom
      ⟨M, fun N => hM (psi N)⟩

/-- The represented catalogue restricts to every subsequence of its
cutoff/environment sequence: precomposing every index-dependent field of
`conv_represented_estimates` with a strictly monotone `psi : ℕ → ℕ` preserves
the whole convention, since every clause is either index-free or a bare
`∀ n : ℕ` universal, so specializing at `psi n` suffices. -/
theorem conv_represented_estimates_subseq
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
    (hrep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta thetaH1
      usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) :
    conv_represented_estimates d hd M H Ω P (fun n => cutoff (psi n)) (fun n => env (psi n))
      J j0 z r hr S D f T theta thetaH1
      (fun j g n => usrc j g (psi n)) (fun j g n => srcRep j g (psi n))
      (fun j h n => ucell j h (psi n)) Cext beta alpha eta t orders E Index
      (fun i n => resp i (psi n)) respLim (fun i n => constants i (psi n)) G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey := by
  unfold Paper.conv_represented_estimates at hrep ⊢
  obtain ⟨hA1, hA2, hA3, hA4, hA5,
    hB1, hB2, hB3, hB4, hB5,
    hC1, hC2, hC3, hC4, hC5, hC6,
    hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9,
    hE1, hE2, hE3,
    hF, hG, hH, hI, hJc, hK, hL⟩ := hrep
  refine ⟨hA1, hA2, hA3, hA4, hA5,
    hB1.comp hpsi, hB2, fun n => hB3 (psi n), fun n => hB4 (psi n),
    aux_conv_represented_estimates_subseq_sequence P resp respLim constants G hB5 psi hpsi,
    hC1, hC2, hC3, hC4, hC5, hC6,
    hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9,
    fun i n => hE1 i (psi n),
    fun i p hp =>
      let ⟨B, hB0, hBall⟩ := hE2 i p hp
      ⟨B, hB0, fun n => hBall (psi n)⟩,
    fun i om hom n => hE3 i om hom (psi n),
    fun j n om hom => hF j (psi n) om hom,
    fun j n om hom => hG j (psi n) om hom,
    fun j n om hom v => hH j (psi n) om hom v,
    fun j n om hom e hce hicb => hI j (psi n) om hom e hce hicb,
    fun g n k j om hom hk1 hk2 hk3 => hJc g (psi n) k j om hom hk1 hk2 hk3,
    fun j g n om hom => hK j g (psi n) om hom,
    fun j h n om hom => hL j h (psi n) om hom⟩

end Paper
