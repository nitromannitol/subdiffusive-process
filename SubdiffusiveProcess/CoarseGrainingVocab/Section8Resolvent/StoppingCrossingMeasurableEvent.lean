module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingScaleCapExclusion
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFixedSpheres
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsExteriorAudit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTailSummability

@[expose] public section

/-!
# Measurable fixed-code event for repaired short crossings

The repaired stopping-cell type depends on the sample.  The fixed code carrier
turns the short-crossing event into a measurable countable union.  A geometric
measure bound for these events then supplies the random last bad bracket used
by the bracket form of the exterior row.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- A short repaired-graph crossing expressed on the sample-independent cell
code.  The witness `n` is the exact graph sphere of the code. -/
def repairedStoppingShortCrossingCodeEvent
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R epsilon : ℝ) (k : ℕ) : Set Omega :=
  {omega | ∃ c : RepairedStoppingCellCode d,
    (translatedCube d (repairedStoppingCellCodeScale c)
        (repairedStoppingCellCodeCenter c) ∩
      (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty ∧
    ∃ n : ℕ, n < ⌈epsilon * (3 : ℝ) ^ k⌉₊ ∧
      IsExactRepairedStoppingCodeSphere failure base x0 R n omega c}

variable [MeasurableSpace Omega]

/-- The fixed-code short-crossing event is measurable whenever every input
cube-failure event is measurable. -/
theorem measurableSet_repairedStoppingShortCrossingCodeEvent
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R epsilon : ℝ) (k : ℕ) :
    MeasurableSet
      (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k) := by
  have heq : repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k =
      ⋃ c : RepairedStoppingCellCode d, ⋃ n : ℕ,
        {omega |
          (translatedCube d (repairedStoppingCellCodeScale c)
              (repairedStoppingCellCodeCenter c) ∩
            (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty ∧
          n < ⌈epsilon * (3 : ℝ) ^ k⌉₊ ∧
          IsExactRepairedStoppingCodeSphere failure base x0 R n omega c} := by
    ext omega
    simp only [repairedStoppingShortCrossingCodeEvent, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨c, hc, n, hn, hsphere⟩
      exact ⟨c, n, hc, hn, hsphere⟩
    · rintro ⟨c, n, hc, hn, hsphere⟩
      exact ⟨c, hc, n, hn, hsphere⟩
  rw [heq]
  refine MeasurableSet.iUnion fun c ↦ MeasurableSet.iUnion fun n ↦ ?_
  by_cases hc :
      (translatedCube d (repairedStoppingCellCodeScale c)
          (repairedStoppingCellCodeCenter c) ∩
        (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty
  · by_cases hn : n < ⌈epsilon * (3 : ℝ) ^ k⌉₊
    · simpa [hc, hn] using
        measurableSet_isExactRepairedStoppingCodeSphere
          (base := base) failure hfailure x0 R n c
    · simp [hn]
  · simp [hc]

omit [MeasurableSpace Omega] in
/-- The fixed-code event agrees samplewise with the original crossing
predicate at the canonical repaired source. -/
theorem mem_repairedStoppingShortCrossingCodeEvent_iff [NeZero d]
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) (R epsilon : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    omega ∈ repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k ↔
      RepairedStoppingShortCrossing
        (repairedStoppingSourceCells hinitial hrepair x0 R)
        (repairedStoppingSourceCells_nonempty hinitial hrepair x0
          hR) x0 R epsilon k := by
  let hsource := repairedStoppingSourceCells_nonempty hinitial hrepair x0
    hR
  have hconnected := repairedStoppingGraph_connected failure omega hinitial hrepair
  constructor
  · rintro ⟨c, hc, n, hn, hsphere⟩
    obtain ⟨q, hqlevel, hqc⟩ :=
      (isExactRepairedStoppingCodeSphere_iff
        hinitial hrepair x0 R hsource n c).mp hsphere
    refine ⟨q, ?_, ?_⟩
    · simpa only [← hqc, repairedStoppingCellCodeScale_apply,
        repairedStoppingCellCodeCenter_apply] using hc
    · have hdistance :=
        (mem_stoppingGraphLevelCells_iff repairedStoppingGraph hconnected
          hsource n q).mp hqlevel
      rwa [hdistance]
  · rintro ⟨q, hqmeet, hqdistance⟩
    let n := stoppingGraphDistance repairedStoppingGraph
      (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q
    refine ⟨repairedStoppingCellCode q, ?_, n, hqdistance, ?_⟩
    · simpa only [repairedStoppingCellCodeScale_apply,
        repairedStoppingCellCodeCenter_apply] using hqmeet
    · apply (isExactRepairedStoppingCodeSphere_iff
        hinitial hrepair x0 R hsource n (repairedStoppingCellCode q)).mpr
      refine ⟨q, ?_, rfl⟩
      exact (mem_stoppingGraphLevelCells_iff repairedStoppingGraph hconnected
        hsource n q).mpr rfl

/-- Last bad bracket for the fixed-code crossing events. -/
def repairedStoppingCrossingCodeDepth
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R epsilon : ℝ) (omega : Omega) : ℕ :=
  (failureHeightAt
    (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon)
      omega).untopD 0

omit [MeasurableSpace Omega] in
/-- A finite fixed-code crossing height excludes every event at or above its
natural-valued depth. -/
theorem not_mem_repairedStoppingShortCrossingCodeEvent_of_depth_le
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R epsilon : ℝ) {omega : Omega}
    (hfinite : failureHeightAt
      (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon)
        omega ≠ (⊤ : WithTop ℕ))
    {k : ℕ}
    (hk : repairedStoppingCrossingCodeDepth failure base x0 R epsilon omega ≤ k) :
    omega ∉ repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k := by
  intro hbad
  have hcontribution : ((k + 1 : ℕ) : WithTop ℕ) ≤
      failureHeightAt
        (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon)
          omega :=
    coe_succ_le_extendedFailureHeight hbad
  generalize hheight : failureHeightAt
    (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon) omega =
      height at hcontribution
  cases height with
  | top => exact (hfinite hheight).elim
  | coe H =>
      have hnat : k + 1 ≤ H := WithTop.coe_le_coe.mp hcontribution
      have hkH : H ≤ k := by
        simpa only [repairedStoppingCrossingCodeDepth, hheight,
          WithTop.untopD_coe] using hk
      omega

/-- A geometric measure bound for the measurable fixed-code crossing events
produces the required almost-sure random last bad bracket, in the exact
canonical-source shape consumed by the bracket exterior row. -/
theorem ae_forall_exists_lastBadBracket_of_codeEvent_geometric [NeZero d]
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (x0 : Vec d) {R epsilon : ℝ} (hR : 0 < R)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ k,
      mu (repairedStoppingShortCrossingCodeEvent
        failure base x0 R epsilon k) ≤ C * q ^ k) :
    ∀ᵐ omega ∂mu,
      ∀ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega P))
        (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
          cubeSet P.1),
        ∃ K : ℕ, ∀ k, K ≤ k →
          ¬ RepairedStoppingShortCrossing
            (refinedStoppingSource hinitial hrepair x0 R)
            (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le)
            x0 R epsilon k := by
  filter_upwards [ae_failureHeightAt_ne_top_of_le_geometric mu
    (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon)
    C q hC hq hmeasure] with omega hfinite
  intro hinitial hrepair
  refine ⟨repairedStoppingCrossingCodeDepth failure base x0 R epsilon omega,
    fun k hk hcross ↦ ?_⟩
  have hnot := not_mem_repairedStoppingShortCrossingCodeEvent_of_depth_le
    failure base x0 R epsilon hfinite hk
  apply hnot
  have hcross' : RepairedStoppingShortCrossing
      (repairedStoppingSourceCells hinitial hrepair x0 R)
      (repairedStoppingSourceCells_nonempty hinitial hrepair x0 hR.le)
      x0 R epsilon k := by
    simpa only [refinedStoppingSource, repairedStoppingSourceCells] using hcross
  exact (mem_repairedStoppingShortCrossingCodeEvent_iff
    hinitial hrepair x0 R epsilon hR.le k).mpr hcross'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
