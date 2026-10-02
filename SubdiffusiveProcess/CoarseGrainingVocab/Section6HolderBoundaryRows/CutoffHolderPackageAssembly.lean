import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderRowsBelow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderRowsAbove
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.ThresholdedPackageAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.StoppingSaturation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GammaOneComposition




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The three frozen boundary rows at the finite-cutoff stopping carrier. -/
def BoundaryCutoffRowsAt (d : ℕ) (C C1 C2 : ℝ) (step : ℕ) : Prop :=
  ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ C⁻¹ →
  ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
  ∀ L m : ℕ, ∀ omega,
  ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
    IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (originCube d m) u h g →
    MemHolder (cube d m) (1 / 2) g → MemHolder (cube d m) (1 / 2) h.grad →
    HolderRegularityConclusions M C L omega alpha m
      (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega) u h g

/-- The three frozen boundary rows at the cutoff-independent carrier, uniformly
in every cutoff `J ≥ m`. -/
def BoundaryUncutRowsAt (d : ℕ) (C C1 C2 : ℝ) (step : ℕ) : Prop :=
  ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ C⁻¹ →
  ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
  ∀ m J : ℕ, m ≤ J → ∀ omega,
  ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
    IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J omega)
        (originCube d m) u h g →
    MemHolder (cube d m) (1 / 2) g → MemHolder (cube d m) (1 / 2) h.grad →
    HolderRegularityConclusions M C J omega alpha m
      (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega) u h g

/-- **The rows at both manuscript carriers.**  Above the cutoff the carriers
coincide, so the landed above-cutoff rows serve both; below the cutoff the
finite-cutoff rows of `CutoffHolderRowsBelow` serve the cutoff carrier. -/
theorem exists_boundaryCutoffAndUncutRows (d : ℕ) [NeZero d]
    (hExcess : BoundaryHolderExcessDecayInput d)
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d)
    (hharmCut : Section6ExcessDecay.BoundaryCutoffHarmonicApproximationInputV6 d)
    (hExcessCut : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ C0 C1 C2 : ℝ, 0 < C0 ∧ 1 ≤ C1 ∧ 1 ≤ C2 ∧
      (∀ C : ℝ, C0 ≤ C → BoundaryCutoffRowsAt d C C1 C2 21) ∧
      (∀ C : ℝ, C0 ≤ C → BoundaryUncutRowsAt d C C1 C2 21) := by
  classical
  obtain ⟨C1a, C2a, Ca, hC1two, hC1C2, hCa, habove⟩ :=
    exists_boundaryRowsAboveCutoff_free d hExcess hHarmonic
  obtain ⟨C1b, C2b, Cb, hC1b, hC12b, hCb, hbelow⟩ :=
    CutoffHolderBelow.exists_boundaryRowsBelowCutoff_thresholded d hharmCut hExcessCut
  set C1 : ℝ := max C1a C1b with hC1def
  set C2 : ℝ := max (max C2a C2b) C1 with hC2def
  have hC1twoM : (2 : ℝ) ≤ C1 := hC1two.trans (le_max_left _ _)
  have hC1C2M : C1 ≤ C2 := le_max_right _ _
  have hC1one : (1 : ℝ) ≤ C1 := by linarith
  have hC2one : (1 : ℝ) ≤ C2 := hC1one.trans hC1C2M
  have hC1a' : C1a ≤ C1 := le_max_left _ _
  have hC1b' : C1b ≤ C1 := le_max_right _ _
  have hC2a' : C2a ≤ C2 := (le_max_left C2a C2b).trans (le_max_left _ _)
  have hC2b' : C2b ≤ C2 := (le_max_right C2a C2b).trans (le_max_left _ _)
  refine ⟨max (max 46 C1) (max (1024 * C2 ^ 2) (max Ca Cb)), C1, C2, ?_,
    hC1one, hC2one, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num)
      (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _))
  · intro C hC0 M hdelta alpha halpha L m omega u h g hsol hg hh
    have h46 : (46 : ℝ) ≤ C :=
      le_trans (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC1 : C1 ≤ C :=
      le_trans (le_trans (le_max_right (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC2 : 1024 * C2 ^ 2 ≤ C :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC0
    have hCA : Ca ≤ C :=
      le_trans (le_trans (le_max_left Ca Cb)
        (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
    have hCB : Cb ≤ C :=
      le_trans (le_trans (le_max_right Ca Cb)
        (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
    obtain ⟨hsmall, halpha', heps, hlam⟩ :=
      holderStopping_model_conditions M hC1one hC2one h46 hCC1 hCC2 hdelta halpha
    rcases le_or_gt m L with hmL | hLm
    · rw [Section6HolderBelowCutoff.measurableCutoffHolderStoppingScale_eq_of_le_cutoff
        M hmL alpha (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) 21]
      exact habove C1 C2 hC1a' hC2a' hC1C2M C hCA 21 le_rfl M hsmall alpha
        halpha' heps hlam L m hmL omega u h g hsol hg hh
    · exact hbelow C1 C2 hC1b' hC2b' hC1C2M C hCB 21 le_rfl M hsmall alpha
        halpha' heps hlam L m hLm omega u h g hsol hg hh
  · intro C hC0 M hdelta alpha halpha m J hJ omega u h g hsol hg hh
    have h46 : (46 : ℝ) ≤ C :=
      le_trans (le_trans (le_max_left (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC1 : C1 ≤ C :=
      le_trans (le_trans (le_max_right (46 : ℝ) C1) (le_max_left _ _)) hC0
    have hCC2 : 1024 * C2 ^ 2 ≤ C :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC0
    have hCA : Ca ≤ C :=
      le_trans (le_trans (le_max_left Ca Cb)
        (le_trans (le_max_right _ _) (le_max_right _ _))) hC0
    obtain ⟨hsmall, halpha', heps, hlam⟩ :=
      holderStopping_model_conditions M hC1one hC2one h46 hCC1 hCC2 hdelta halpha
    exact habove C1 C2 hC1a' hC2a' hC1C2M C hCA 21 le_rfl M hsmall alpha
      halpha' heps hlam J m hJ omega u h g hsol hg hh

/-- Tail plus rows give the fixed-cutoff sample-space package. -/
theorem boundaryCutoffPathwiseInput_of_tailAndRows {d : ℕ} {C C1 C2 : ℝ} {step : ℕ}
    (htail : CutoffGammaOneTailAt d C C1 C2 step)
    (hrows : BoundaryCutoffRowsAt d C C1 C2 step) :
    BoundaryCutoffPathwiseInput d C := by
  intro M hdelta alpha halpha L m
  exact ⟨Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    Section6Stopping.measurable_measurableCutoffHolderStoppingScale _ _ _ _ _ _ _,
    fun omega => Section6Stopping.measurableCutoffHolderStoppingScale_pos _ _ _ _ _ _ _ omega,
    fun k hk => htail M hdelta alpha halpha L m k hk,
    fun omega u h g hsol hg hh => hrows M hdelta alpha halpha L m omega u h g hsol hg hh⟩

/-- Tail plus rows give the cutoff-uniform sample-space package. -/
theorem boundaryCutoffUniformInput_of_tailAndRows {d : ℕ} {C C1 C2 : ℝ} {step : ℕ}
    (htail : UncutGammaOneTailAt d C C1 C2 step)
    (hrows : BoundaryUncutRowsAt d C C1 C2 step) :
    BoundaryCutoffUniformInput d C := by
  intro M hdelta alpha halpha m
  exact ⟨Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda C1 alpha)
      (Section6Stopping.holderStoppingEpsilon C2 alpha) step m,
    Section6Stopping.measurable_measurableHolderStoppingScale _ _ _ _ _ _,
    fun omega => Section6Stopping.measurableHolderStoppingScale_pos _ _ _ _ _ _ omega,
    fun k hk => htail M hdelta alpha halpha m k hk,
    fun J hJ omega u h g hsol hg hh =>
      hrows M hdelta alpha halpha m J hJ omega u h g hsol hg hh⟩

/-- **The two sample-space packages of the boundary cutoff anchor, at the
manuscript's own carriers.**  Both Γ₁ tails are theorems, so no probabilistic
obligation survives. -/
theorem exists_boundaryCutoffInputs (d : ℕ) [NeZero d]
    (hExcess : BoundaryHolderExcessDecayInput d)
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d)
    (hharmCut : Section6ExcessDecay.BoundaryCutoffHarmonicApproximationInputV6 d)
    (hExcessCut : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ C : ℝ, 0 < C ∧ BoundaryCutoffPathwiseInput d C ∧
      BoundaryCutoffUniformInput d C := by
  classical
  obtain ⟨C0, C1, C2, hC0, hC1, hC2, hrowsCut, hrowsUncut⟩ :=
    exists_boundaryCutoffAndUncutRows d hExcess hHarmonic hharmCut hExcessCut
  obtain ⟨Cc, hCc, htailC⟩ := exists_cutoffGammaOneTail d 21 hC1 hC2
  obtain ⟨Cu, hCu, htailU⟩ := exists_uncutGammaOneTail d 21 hC1 hC2
  refine ⟨max (max Cc Cu) C0, lt_of_lt_of_le hCc
    (le_trans (le_max_left Cc Cu) (le_max_left _ _)), ?_, ?_⟩
  · exact boundaryCutoffPathwiseInput_of_tailAndRows
      (cutoffGammaOneTailAt_mono hCc
        (le_trans (le_max_left Cc Cu) (le_max_left _ _)) htailC)
      (hrowsCut _ (le_max_right _ _))
  · exact boundaryCutoffUniformInput_of_tailAndRows
      (uncutGammaOneTailAt_mono hCu
        (le_trans (le_max_right Cc Cu) (le_max_left _ _)) htailU)
      (hrowsUncut _ (le_max_right _ _))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
