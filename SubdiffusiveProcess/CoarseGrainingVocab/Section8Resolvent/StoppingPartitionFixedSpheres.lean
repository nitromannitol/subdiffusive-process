module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairStages
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedSource
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedLevels

@[expose] public section

/-!
# Measurable source and graph spheres on fixed stopping-cell codes

Inactive codes are isolated.  On selected codes, adjacency is the repaired
near-cube graph.  Recursive reachability therefore describes graph balls
without ever placing the sample in the carrier type.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- Fixed-code source membership: the code is selected and its one-scale
enlargement meets the closed source ball. -/
def IsRepairedStoppingSourceCode
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ) (q : RepairedStoppingCellCode d) : Prop :=
  IsSelectedRepairedCellCode failure omega base q ∧
    (translatedCube d (repairedStoppingCellCodeScale q + 1)
      (repairedStoppingCellCodeCenter q) ∩ Metric.closedBall x0 R).Nonempty

/-- Fixed-code adjacency.  Requiring selection at both endpoints makes every
inactive code an isolated vertex. -/
def AreAdjacentRepairedStoppingCodes
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (q r : RepairedStoppingCellCode d) : Prop :=
  q ≠ r ∧ IsSelectedRepairedCellCode failure omega base q ∧
    IsSelectedRepairedCellCode failure omega base r ∧
    StoppingCubesNear q.1 r.1

/-- Samplewise repaired graph on the fixed code carrier. -/
def fixedRepairedStoppingGraph
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :
    SimpleGraph (RepairedStoppingCellCode d) :=
  SimpleGraph.fromRel fun q r ↦
    IsSelectedRepairedCellCode failure omega base q ∧
      IsSelectedRepairedCellCode failure omega base r ∧
      StoppingCubesNear q.1 r.1

theorem fixedRepairedStoppingGraph_adj_iff
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (q r : RepairedStoppingCellCode d) :
    (fixedRepairedStoppingGraph failure omega base).Adj q r ↔
      AreAdjacentRepairedStoppingCodes failure omega base q r := by
  rw [fixedRepairedStoppingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h.1, h.2.1, h.2.2⟩
    · exact ⟨hne, h.2.1, h.1,
        (stoppingCubesNear_comm r.1 q.1).mp h.2.2⟩
  · rintro ⟨hne, hq, hr, hnear⟩
    exact ⟨hne, Or.inl ⟨hq, hr, hnear⟩⟩

/-- The fixed graph restricts along the code equivalence to the original
repaired stopping graph. -/
theorem fixedRepairedStoppingGraph_adj_code_iff
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q r : RefinedStoppingCell failure omega base) :
    (fixedRepairedStoppingGraph failure omega base).Adj
        (repairedStoppingCellCode q) (repairedStoppingCellCode r) ↔
      repairedStoppingGraph.Adj q r := by
  rw [fixedRepairedStoppingGraph_adj_iff,
    repairedStoppingGraph_adj_iff]
  simp only [AreAdjacentRepairedStoppingCodes,
    isSelectedRepairedCellCode_repairedStoppingCellCode,
    repairedStoppingCellCode_fst, true_and]
  exact and_congr
    ⟨fun h hqr ↦ h (congrArg repairedStoppingCellCode hqr),
      fun h hcode ↦ h (repairedStoppingCellCode_injective hcode)⟩
    Iff.rfl

/-- Every selected code is the code of a repaired stopping cell. -/
theorem exists_repairedStoppingCellCode_eq_of_selected
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    {c : RepairedStoppingCellCode d}
    (hc : IsSelectedRepairedCellCode failure omega base c) :
    ∃ q : RefinedStoppingCell failure omega base,
      repairedStoppingCellCode q = c := by
  refine ⟨(refinedStoppingCellEquivSelectedCode failure omega base).symm ⟨c, hc⟩, ?_⟩
  exact congrArg Subtype.val
    ((refinedStoppingCellEquivSelectedCode failure omega base).apply_symm_apply
      ⟨c, hc⟩)

/-- Codes reachable from the source in at most `j` graph steps. -/
def IsRepairedStoppingCodeReachableWithin
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ) : ℕ → Omega → RepairedStoppingCellCode d → Prop
  | 0, omega, q => IsRepairedStoppingSourceCode failure omega base x0 R q
  | j + 1, omega, q =>
      IsRepairedStoppingCodeReachableWithin failure base x0 R j omega q ∨
        ∃ p : RepairedStoppingCellCode d,
          IsRepairedStoppingCodeReachableWithin failure base x0 R j omega p ∧
          AreAdjacentRepairedStoppingCodes failure omega base p q

/-- Exact recursive sphere: the source at level zero and the new vertices
added at each subsequent graph step. -/
def IsExactRepairedStoppingCodeSphere
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ) : ℕ → Omega → RepairedStoppingCellCode d → Prop
  | 0, omega, q => IsRepairedStoppingSourceCode failure omega base x0 R q
  | j + 1, omega, q =>
      IsRepairedStoppingCodeReachableWithin failure base x0 R (j + 1) omega q ∧
        ¬ IsRepairedStoppingCodeReachableWithin failure base x0 R j omega q

variable [MeasurableSpace Omega]

/-- Source membership of a fixed code is measurable. -/
theorem measurableSet_isRepairedStoppingSourceCode
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ) (q : RepairedStoppingCellCode d) :
    MeasurableSet
      {omega | IsRepairedStoppingSourceCode failure omega base x0 R q} := by
  by_cases hgeom :
      (translatedCube d (repairedStoppingCellCodeScale q + 1)
        (repairedStoppingCellCodeCenter q) ∩ Metric.closedBall x0 R).Nonempty
  · simpa [IsRepairedStoppingSourceCode, hgeom] using
      measurableSet_isSelectedRepairedCellCode
        (base := base) failure hfailure q
  · simp [IsRepairedStoppingSourceCode, hgeom]

/-- Fixed-code adjacency is a measurable event. -/
theorem measurableSet_areAdjacentRepairedStoppingCodes
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (q r : RepairedStoppingCellCode d) :
    MeasurableSet
      {omega | AreAdjacentRepairedStoppingCodes failure omega base q r} := by
  by_cases hstatic : q ≠ r ∧ StoppingCubesNear q.1 r.1
  · have heq : {omega | AreAdjacentRepairedStoppingCodes failure omega base q r}
        = {omega | IsSelectedRepairedCellCode failure omega base q}
          ∩ {omega | IsSelectedRepairedCellCode failure omega base r} := by
      ext omega
      simp only [mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        exact ⟨hstatic.1, h2, h3, hstatic.2⟩
    rw [heq]
    exact MeasurableSet.inter
      (measurableSet_isSelectedRepairedCellCode (base := base) failure hfailure q)
      (measurableSet_isSelectedRepairedCellCode (base := base) failure hfailure r)
  · have heq : {omega | AreAdjacentRepairedStoppingCodes failure omega base q r} = ∅ := by
      ext omega
      simp only [mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact hstatic ⟨h1, h4⟩
      · rintro h
        exact False.elim h
    rw [heq]
    exact MeasurableSet.empty

/-- Reachability of a fixed code in a fixed number of steps is measurable. -/
theorem measurableSet_isRepairedStoppingCodeReachableWithin
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ) :
    ∀ j q, MeasurableSet
      {omega |
        IsRepairedStoppingCodeReachableWithin failure base x0 R j omega q} := by
  intro j
  induction j with
  | zero =>
      intro q
      exact measurableSet_isRepairedStoppingSourceCode
        (base := base) failure hfailure x0 R q
  | succ j ih =>
      intro q
      have hnext : MeasurableSet
          {omega | ∃ p : RepairedStoppingCellCode d,
            IsRepairedStoppingCodeReachableWithin failure base x0 R j omega p ∧
            AreAdjacentRepairedStoppingCodes failure omega base p q} := by
        have heq : {omega | ∃ p : RepairedStoppingCellCode d,
            IsRepairedStoppingCodeReachableWithin failure base x0 R j omega p ∧
            AreAdjacentRepairedStoppingCodes failure omega base p q} =
            ⋃ p : RepairedStoppingCellCode d,
              {omega |
                IsRepairedStoppingCodeReachableWithin failure base x0 R j omega p ∧
                AreAdjacentRepairedStoppingCodes failure omega base p q} := by
          ext omega
          simp only [mem_ofPred_eq, mem_iUnion]
        rw [heq]
        exact MeasurableSet.iUnion fun p ↦
          (ih p).inter
            (measurableSet_areAdjacentRepairedStoppingCodes
              (base := base) failure hfailure p q)
      change MeasurableSet
        ({omega |
          IsRepairedStoppingCodeReachableWithin failure base x0 R j omega q} ∪
        {omega | ∃ p : RepairedStoppingCellCode d,
          IsRepairedStoppingCodeReachableWithin failure base x0 R j omega p ∧
          AreAdjacentRepairedStoppingCodes failure omega base p q})
      exact (ih q).union hnext

/-- Each exact repaired-graph sphere is represented by measurable fixed-code
membership events. -/
theorem measurableSet_isExactRepairedStoppingCodeSphere
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ) :
    ∀ j q, MeasurableSet
      {omega | IsExactRepairedStoppingCodeSphere failure base x0 R j omega q} := by
  intro j
  cases j with
  | zero =>
      intro q
      exact measurableSet_isRepairedStoppingSourceCode
        (base := base) failure hfailure x0 R q
  | succ j =>
      intro q
      exact (measurableSet_isRepairedStoppingCodeReachableWithin
        (base := base) failure hfailure x0 R (j + 1) q).inter
          (measurableSet_isRepairedStoppingCodeReachableWithin
            (base := base) failure hfailure x0 R j q).compl

/-- Measurable ENNReal supremum of source-cell side lengths.  It is finite
whenever the selected source-code set is finite. -/
def repairedStoppingSourceRadius
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ) (omega : Omega) : ENNReal :=
  ⨆ q : RepairedStoppingCellCode d,
    if IsRepairedStoppingSourceCode failure omega base x0 R q then
      ENNReal.ofReal ((3 : ℝ) ^ repairedStoppingCellCodeScale q) else 0

theorem measurable_repairedStoppingSourceRadius
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ) :
    Measurable (repairedStoppingSourceRadius failure base x0 R) := by
  apply Measurable.iSup
  intro q
  exact measurable_const.ite
    (measurableSet_isRepairedStoppingSourceCode
      (base := base) failure hfailure x0 R q) measurable_const

omit [MeasurableSpace Omega] in
/-- Source membership agrees with the old finite source after encoding. -/
theorem isRepairedStoppingSourceCode_code_iff_mem [NeZero d]
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) (R : ℝ)
    (q : RefinedStoppingCell failure omega base) :
    IsRepairedStoppingSourceCode failure omega base x0 R
        (repairedStoppingCellCode q) ↔
      q ∈ repairedStoppingSourceCells hinitial hrepair x0 R := by
  rw [mem_repairedStoppingSourceCells_iff]
  simp only [IsRepairedStoppingSourceCode,
    isSelectedRepairedCellCode_repairedStoppingCellCode,
    repairedStoppingCellCodeScale_apply,
    repairedStoppingCellCodeCenter_apply, true_and]

omit [MeasurableSpace Omega] in
/-- Every cell within graph distance `j` of the repaired source has a code
reachable from the fixed source code in at most `j` steps. -/
theorem isRepairedStoppingCodeReachableWithin_code_of_dist_le [NeZero d]
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) (R : ℝ)
    (hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty) :
    ∀ (j : ℕ) (q : RefinedStoppingCell failure omega base),
      stoppingGraphDistance repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q ≤ j →
      IsRepairedStoppingCodeReachableWithin failure base x0 R j omega
        (repairedStoppingCellCode q) := by
  have hconnected := repairedStoppingGraph_connected failure omega hinitial hrepair
  intro j
  induction j with
  | zero =>
    intro q hq
    obtain ⟨s, hs, hqs⟩ :=
      exists_source_dist_eq_stoppingGraphDistance repairedStoppingGraph hsource q
    have h0 : stoppingGraphDistance repairedStoppingGraph
        (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q = 0 :=
      Nat.eq_zero_of_le_zero hq
    rw [h0] at hqs
    have hqeq : q = s := hconnected.dist_eq_zero_iff.mp hqs
    subst hqeq
    show IsRepairedStoppingSourceCode failure omega base x0 R (repairedStoppingCellCode q)
    exact (isRepairedStoppingSourceCode_code_iff_mem hinitial hrepair x0 R q).mpr hs
  | succ j ih =>
    intro q hq
    rcases Nat.lt_or_ge (stoppingGraphDistance repairedStoppingGraph
        (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q) (j + 1) with hlt | hge
    · have hle : stoppingGraphDistance repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q ≤ j :=
        Nat.le_of_lt_succ hlt
      exact Or.inl (ih q hle)
    · have hd : stoppingGraphDistance repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q = j + 1 :=
        le_antisymm hq hge
      obtain ⟨p, hqp, hp⟩ := exists_adj_stoppingGraphDistance_eq_pred repairedStoppingGraph
        hconnected hsource hd
      refine Or.inr ⟨repairedStoppingCellCode p, ih p (le_of_eq hp), ?_⟩
      exact (fixedRepairedStoppingGraph_adj_iff failure omega base
        (repairedStoppingCellCode p) (repairedStoppingCellCode q)).mp
        ((fixedRepairedStoppingGraph_adj_code_iff p q).mpr hqp.symm)

omit [MeasurableSpace Omega] in
/-- Conversely, every code reachable within `j` steps is the code of a
repaired stopping cell at graph distance at most `j` from the source. -/
theorem exists_code_eq_and_dist_le_of_reachableWithin [NeZero d]
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) (R : ℝ)
    (hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty) :
    ∀ (j : ℕ) (c : RepairedStoppingCellCode d),
      IsRepairedStoppingCodeReachableWithin failure base x0 R j omega c →
      ∃ q : RefinedStoppingCell failure omega base,
        repairedStoppingCellCode q = c ∧
        stoppingGraphDistance repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q ≤ j := by
  intro j
  induction j with
  | zero =>
    intro c hc
    obtain ⟨q, rfl⟩ := exists_repairedStoppingCellCode_eq_of_selected hc.1
    refine ⟨q, rfl, ?_⟩
    have hmem : q ∈ repairedStoppingSourceCells hinitial hrepair x0 R :=
      (isRepairedStoppingSourceCode_code_iff_mem hinitial hrepair x0 R q).1 hc
    exact le_of_eq (stoppingGraphDistance_eq_zero_of_mem _ hsource hmem)
  | succ j ih =>
    intro c hc
    rcases hc with hc | ⟨p, hp, hadj⟩
    · obtain ⟨q, hq, hd⟩ := ih c hc
      exact ⟨q, hq, hd.trans (Nat.le_succ _)⟩
    · obtain ⟨q, rfl⟩ := exists_repairedStoppingCellCode_eq_of_selected hadj.2.2.1
      obtain ⟨p', hp', hd⟩ := ih p hp
      have h1 : (fixedRepairedStoppingGraph failure omega base).Adj p
          (repairedStoppingCellCode q) :=
        (fixedRepairedStoppingGraph_adj_iff failure omega base p
          (repairedStoppingCellCode q)).2 hadj
      rw [← hp'] at h1
      have h2 : repairedStoppingGraph.Adj p' q :=
        (fixedRepairedStoppingGraph_adj_code_iff p' q).1 h1
      refine ⟨q, rfl, ?_⟩
      have h3 := stoppingGraphDistance_le_succ_of_adj repairedStoppingGraph
        (repairedStoppingGraph_connected failure omega hinitial hrepair) hsource h2.symm
      omega

omit [MeasurableSpace Omega] in
/-- **The exact repaired-graph spheres over the fixed code.**  A fixed code
lies on the `j`-th sphere exactly when it is the code of a repaired stopping
cell at graph distance `j` from the repaired source. -/
theorem isExactRepairedStoppingCodeSphere_iff [NeZero d]
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega P))
    (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
      cubeSet P.1)
    (x0 : Vec d) (R : ℝ)
    (hsource : (repairedStoppingSourceCells hinitial hrepair x0 R).Nonempty)
    (j : ℕ) (c : RepairedStoppingCellCode d) :
    IsExactRepairedStoppingCodeSphere failure base x0 R j omega c ↔
      ∃ q ∈ stoppingGraphLevelCells repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource j,
        repairedStoppingCellCode q = c := by
  have hconn := repairedStoppingGraph_connected failure omega hinitial hrepair
  have hlevel := mem_stoppingGraphLevelCells_iff repairedStoppingGraph hconn hsource
  cases j with
  | zero =>
    constructor
    · intro hc
      have hc0 : IsRepairedStoppingSourceCode failure omega base x0 R c := hc
      obtain ⟨q, hq⟩ := exists_repairedStoppingCellCode_eq_of_selected hc0.1
      refine ⟨q, ?_, hq⟩
      rw [hlevel]
      have hmem : q ∈ repairedStoppingSourceCells hinitial hrepair x0 R :=
        (isRepairedStoppingSourceCode_code_iff_mem hinitial hrepair x0 R q).mp
          (by rw [hq]; exact hc0)
      rw [stoppingGraphDistance_eq_zero_of_mem repairedStoppingGraph hsource hmem]
    · rintro ⟨q, hqmem, hqc⟩
      rw [hlevel] at hqmem
      have hd0 : stoppingGraphDistance repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q ≤ 0 := by
        omega
      have h := isRepairedStoppingCodeReachableWithin_code_of_dist_le
        hinitial hrepair x0 R hsource 0 q hd0
      rw [hqc] at h
      exact h
  | succ j =>
    constructor
    · intro hc
      obtain ⟨q, hqc, hdq⟩ := exists_code_eq_and_dist_le_of_reachableWithin
        hinitial hrepair x0 R hsource (j+1) c hc.1
      refine ⟨q, ?_, hqc⟩
      rw [hlevel]
      have hnj : ¬ stoppingGraphDistance repairedStoppingGraph
          (repairedStoppingSourceCells hinitial hrepair x0 R) hsource q ≤ j := by
        intro hle
        have h := isRepairedStoppingCodeReachableWithin_code_of_dist_le
          hinitial hrepair x0 R hsource j q hle
        rw [hqc] at h
        exact hc.2 h
      omega
    · rintro ⟨q, hqmem, hqc⟩
      rw [hlevel] at hqmem
      show IsRepairedStoppingCodeReachableWithin failure base x0 R (j+1) omega c ∧
        ¬ IsRepairedStoppingCodeReachableWithin failure base x0 R j omega c
      refine ⟨?_, ?_⟩
      · have h := isRepairedStoppingCodeReachableWithin_code_of_dist_le
          hinitial hrepair x0 R hsource (j+1) q (by omega)
        rw [hqc] at h
        exact h
      · intro hreach
        obtain ⟨q', hq'c, hdq'⟩ := exists_code_eq_and_dist_le_of_reachableWithin
          hinitial hrepair x0 R hsource j c hreach
        have hqq : q' = q := repairedStoppingCellCode_injective (by rw [hq'c, hqc])
        subst hqq
        omega





def fixedRepairedShellSum
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (j : ℕ) (omega : Omega) : ℝ≥0∞ :=
  ∑' c : RepairedStoppingCellCode d,
    if IsExactRepairedStoppingCodeSphere failure base x0 R j omega c then
      ENNReal.ofReal
          ((((3 : ℝ) ^ repairedStoppingCellCodeScale c) / R) ^ (d + 6)) * W c omega
    else 0

theorem measurable_fixedRepairedShellSum
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (hW : ∀ c, Measurable (W c)) (j : ℕ) :
    Measurable (fixedRepairedShellSum failure base x0 R W j) := by
  unfold fixedRepairedShellSum
  apply Measurable.tsum
  intro c
  apply Measurable.ite (measurableSet_isExactRepairedStoppingCodeSphere (base := base)
    failure hfailure x0 R j c)
  · exact measurable_const.mul (hW c)
  · exact measurable_const

/-- The real-valued measurable shell field over the fixed code carrier. -/
def fixedRepairedShell
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (j : ℕ) (omega : Omega) : ℝ :=
  (fixedRepairedShellSum failure base x0 R W j omega).toReal

theorem measurable_fixedRepairedShell
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (hW : ∀ c, Measurable (W c)) (j : ℕ) :
    Measurable (fixedRepairedShell failure base x0 R W j) := by
  unfold fixedRepairedShell
  exact ENNReal.measurable_toReal.comp
    (measurable_fixedRepairedShellSum failure hfailure x0 R W hW j)

omit [MeasurableSpace Omega] in
theorem fixedRepairedShell_nonneg
    (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ)
    (W : RepairedStoppingCellCode d → Omega → ℝ≥0∞)
    (j : ℕ) (omega : Omega) :
    0 ≤ fixedRepairedShell failure base x0 R W j omega := by
  unfold fixedRepairedShell
  exact ENNReal.toReal_nonneg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
