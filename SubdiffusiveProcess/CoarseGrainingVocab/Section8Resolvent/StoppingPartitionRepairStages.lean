import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFailureMeasurability




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- A fixed cube occurs in the range of the random initial-candidate map. -/
def IsInitialStoppingCubeCode
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (Q : TriadicCube d) : Prop :=
  ∃ P : StoppingBaseCube d base,
    triadicStoppingCandidate failure omega P = Q

/-- Fixed-carrier version of maximality in the initial laminar family. -/
def IsMaximalInitialStoppingCubeCode
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (Q : TriadicCube d) : Prop :=
  IsInitialStoppingCubeCode failure omega base Q ∧
    ∀ R : TriadicCube d, IsInitialStoppingCubeCode failure omega base R →
      cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q



def StoppingRepairGeneratedWithin
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :
    ℕ → TriadicCube d → Prop
  | 0, Q => IsMaximalInitialStoppingCubeCode failure omega base Q
  | n + 1, Q =>
      StoppingRepairGeneratedWithin failure omega base n Q ∨
        ∃ A R : TriadicCube d,
          StoppingRepairGeneratedWithin failure omega base n A ∧
          StoppingRepairGeneratedWithin failure omega base n R ∧
          StoppingCubesNear A R ∧ A.scale + 2 < R.scale ∧
          parentCube A = Q

theorem stoppingRepairGeneratedWithin_add
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    {n : ℕ} {Q : TriadicCube d}
    (hQ : StoppingRepairGeneratedWithin failure omega base n Q) :
    ∀ k, StoppingRepairGeneratedWithin failure omega base (n + k) Q := by
  intro k
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [Nat.add_succ, StoppingRepairGeneratedWithin]
      exact Or.inl ih

theorem stoppingRepairGeneratedWithin_sound
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ} :
    ∀ {n Q}, StoppingRepairGeneratedWithin failure omega base n Q →
      StoppingRepairGenerated failure omega base Q := by
  intro n
  induction n with
  | zero =>
      intro Q hQ
      rcases hQ with ⟨⟨P, hP⟩, hmax⟩
      let S : MaximalInitialStoppingCube failure omega base :=
        ⟨⟨Q, ⟨P, hP⟩⟩, by
          intro R hsub
          exact hmax R.1 R.2 hsub⟩
      exact StoppingRepairGenerated.initial S
  | succ n ih =>
      intro Q hQ
      rcases hQ with hQ | ⟨A, R, hA, hR, hnear, hscale, hparent⟩
      · exact ih hQ
      · rw [← hparent]
        exact StoppingRepairGenerated.parent (ih hA) (ih hR) hnear hscale

theorem stoppingRepairGenerated_iff_exists_within
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    {Q : TriadicCube d} :
    StoppingRepairGenerated failure omega base Q ↔
      ∃ n, StoppingRepairGeneratedWithin failure omega base n Q := by
  constructor
  · intro hQ
    induction hQ with
    | initial S =>
        refine ⟨0, S.1.2, ?_⟩
        intro R hR hsub
        exact S.2 ⟨R, hR⟩ hsub
    | @parent A R hA hR hnear hscale ihA ihR =>
        rcases ihA with ⟨n, hn⟩
        rcases ihR with ⟨m, hm⟩
        refine ⟨n + m + 1, Or.inr ⟨A, R,
          stoppingRepairGeneratedWithin_add hn m, ?_, hnear, hscale, rfl⟩⟩
        simpa only [Nat.add_comm] using
          (stoppingRepairGeneratedWithin_add hm n)
  · rintro ⟨n, hn⟩
    exact stoppingRepairGeneratedWithin_sound hn



theorem isSelectedRepairedCubeCode_iff
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    {Q : TriadicCube d} :
    IsSelectedRepairedCubeCode failure omega base Q ↔
      (∃ n, StoppingRepairGeneratedWithin failure omega base n Q) ∧
        ∀ R : TriadicCube d,
          (∃ n, StoppingRepairGeneratedWithin failure omega base n R) →
          cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q := by
  simp only [IsSelectedRepairedCubeCode,
    stoppingRepairGenerated_iff_exists_within]

variable [MeasurableSpace Omega]

/-- Initial-range membership is measurable from measurable cube failures. -/
theorem measurableSet_isInitialStoppingCubeCode
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (Q : TriadicCube d) :
    MeasurableSet
      {omega | IsInitialStoppingCubeCode failure omega base Q} := by
  have heq : {omega | IsInitialStoppingCubeCode failure omega base Q} =
      ⋃ P : StoppingBaseCube d base,
        {omega | triadicStoppingCandidate failure omega P = Q} := by
    ext omega
    simp only [mem_setOf_eq, IsInitialStoppingCubeCode, mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun P ↦
    measurableSet_triadicStoppingCandidate_eq failure hfailure P Q

/-- Maximal initial selection is a measurable predicate on fixed cubes. -/
theorem measurableSet_isMaximalInitialStoppingCubeCode
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (Q : TriadicCube d) :
    MeasurableSet
      {omega | IsMaximalInitialStoppingCubeCode failure omega base Q} := by
  have hQ := measurableSet_isInitialStoppingCubeCode
    (base := base) failure hfailure Q
  have hR : ∀ R : TriadicCube d, MeasurableSet
      {omega | IsInitialStoppingCubeCode failure omega base R →
        cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
    intro R
    have hstatic : MeasurableSet
        {omega : Omega | cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
      by_cases h : cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q
      · simp
      · simp [h]
    exact (measurableSet_isInitialStoppingCubeCode
      (base := base) failure hfailure R).imp hstatic
  have hforall : MeasurableSet
      {omega | ∀ R : TriadicCube d,
        IsInitialStoppingCubeCode failure omega base R →
          cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
    have heq : {omega | ∀ R : TriadicCube d,
        IsInitialStoppingCubeCode failure omega base R →
          cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} =
        ⋂ R : TriadicCube d,
          {omega | IsInitialStoppingCubeCode failure omega base R →
            cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
      ext omega
      simp only [mem_setOf_eq, mem_iInter]
    rw [heq]
    exact MeasurableSet.iInter hR
  change MeasurableSet
    ({omega | IsInitialStoppingCubeCode failure omega base Q} ∩
      {omega | ∀ R : TriadicCube d,
        IsInitialStoppingCubeCode failure omega base R →
          cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q})
  exact hQ.inter hforall



theorem measurableSet_stoppingRepairGeneratedWithin
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q)) :
    ∀ n Q, MeasurableSet
      {omega | StoppingRepairGeneratedWithin failure omega base n Q} := by
  intro n
  induction n with
  | zero =>
      intro Q
      exact measurableSet_isMaximalInitialStoppingCubeCode
        (base := base) failure hfailure Q
  | succ n ih =>
      intro Q
      have hparents : MeasurableSet
          {omega | ∃ A R : TriadicCube d,
            StoppingRepairGeneratedWithin failure omega base n A ∧
            StoppingRepairGeneratedWithin failure omega base n R ∧
            StoppingCubesNear A R ∧ A.scale + 2 < R.scale ∧
            parentCube A = Q} := by
        have heq : {omega | ∃ A R : TriadicCube d,
            StoppingRepairGeneratedWithin failure omega base n A ∧
            StoppingRepairGeneratedWithin failure omega base n R ∧
            StoppingCubesNear A R ∧ A.scale + 2 < R.scale ∧
            parentCube A = Q} =
            ⋃ A : TriadicCube d, ⋃ R : TriadicCube d,
              {omega | StoppingRepairGeneratedWithin failure omega base n A ∧
                StoppingRepairGeneratedWithin failure omega base n R ∧
                StoppingCubesNear A R ∧ A.scale + 2 < R.scale ∧
                parentCube A = Q} := by
          ext omega
          simp only [mem_setOf_eq, mem_iUnion]
        rw [heq]
        apply MeasurableSet.iUnion
        intro A
        apply MeasurableSet.iUnion
        intro R
        by_cases hstatic :
            StoppingCubesNear A R ∧ A.scale + 2 < R.scale ∧ parentCube A = Q
        · simp only [hstatic, and_self, and_true]
          change MeasurableSet
            ({omega | StoppingRepairGeneratedWithin failure omega base n A} ∩
              {omega | StoppingRepairGeneratedWithin failure omega base n R})
          exact (ih A).inter (ih R)
        · simp [hstatic]
      change MeasurableSet
        ({omega | StoppingRepairGeneratedWithin failure omega base n Q} ∪
          {omega | ∃ A R : TriadicCube d,
            StoppingRepairGeneratedWithin failure omega base n A ∧
            StoppingRepairGeneratedWithin failure omega base n R ∧
            StoppingCubesNear A R ∧ A.scale + 2 < R.scale ∧
            parentCube A = Q})
      exact (ih Q).union hparents



theorem measurableSet_stoppingRepairGenerated
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (Q : TriadicCube d) :
    MeasurableSet {omega | StoppingRepairGenerated failure omega base Q} := by
  have heq : {omega | StoppingRepairGenerated failure omega base Q} =
      ⋃ n : ℕ,
        {omega | StoppingRepairGeneratedWithin failure omega base n Q} := by
    ext omega
    simp only [mem_setOf_eq, mem_iUnion,
      stoppingRepairGenerated_iff_exists_within]
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦
    measurableSet_stoppingRepairGeneratedWithin
      (base := base) failure hfailure n Q

/-- Selection of a repaired fixed cube is measurable. -/
theorem measurableSet_isSelectedRepairedCubeCode
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (Q : TriadicCube d) :
    MeasurableSet {omega | IsSelectedRepairedCubeCode failure omega base Q} := by
  have hQ := measurableSet_stoppingRepairGenerated
    (base := base) failure hfailure Q
  have hforall : MeasurableSet {omega | ∀ R : TriadicCube d,
      StoppingRepairGenerated failure omega base R →
        cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
    have heq : {omega | ∀ R : TriadicCube d,
        StoppingRepairGenerated failure omega base R →
          cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} =
        ⋂ R : TriadicCube d,
          {omega | StoppingRepairGenerated failure omega base R →
            cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
      ext omega
      simp only [mem_setOf_eq, mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter
    intro R
    have hstatic : MeasurableSet
        {omega : Omega | cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q} := by
      by_cases h : cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q
      · simp
      · simp [h]
    exact (measurableSet_stoppingRepairGenerated
      (base := base) failure hfailure R).imp hstatic
  change MeasurableSet
    ({omega | StoppingRepairGenerated failure omega base Q} ∩
      {omega | ∀ R : TriadicCube d,
        StoppingRepairGenerated failure omega base R →
          cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q})
  exact hQ.inter hforall

/-- Selection of a repaired fixed cell code is measurable. -/
theorem measurableSet_isSelectedRepairedCellCode
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (q : RepairedStoppingCellCode d) :
    MeasurableSet {omega | IsSelectedRepairedCellCode failure omega base q} :=
  measurableSet_isSelectedRepairedCubeCode
    (base := base) failure hfailure q.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
