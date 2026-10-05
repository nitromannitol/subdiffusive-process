module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridRefinement

@[expose] public section

/-!
# Sample-independent codes for repaired stopping cells

The repaired stopping-cell subtype depends on the sample.  This file separates
the countable code of a possible cell from the measurable assertion that the
cell is selected in a given sample.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- A fixed code for a repaired stopping cell: a possible selected triadic
cube and one of the finitely many half-grid offsets. -/
def RepairedStoppingCellCode (d : ℕ) :=
  TriadicCube d × StoppingHalfGridOffset d

instance : Countable (RepairedStoppingCellCode d) := by
  dsimp only [RepairedStoppingCellCode]
  infer_instance

instance : DecidableEq (RepairedStoppingCellCode d) := by
  exact Classical.decEq _

instance : Encodable (RepairedStoppingCellCode d) :=
  Encodable.ofCountable _



def IsSelectedRepairedCubeCode
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (Q : TriadicCube d) : Prop :=
  StoppingRepairGenerated failure omega base Q ∧
    ∀ R : TriadicCube d, StoppingRepairGenerated failure omega base R →
      cubeSet Q ⊆ cubeSet R → cubeSet R ⊆ cubeSet Q

/-- Membership of a fixed cell code in the repaired half-grid family. -/
def IsSelectedRepairedCellCode
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ)
    (q : RepairedStoppingCellCode d) : Prop :=
  IsSelectedRepairedCubeCode failure omega base q.1

/-- Forget the sample-dependent subtype proof and retain the fixed code. -/
def repairedStoppingCellCode
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ} :
    RefinedStoppingCell failure omega base → RepairedStoppingCellCode d :=
  fun q ↦ (refinedStoppingFailureCube q, q.2)

@[simp]
theorem repairedStoppingCellCode_fst
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) :
    (repairedStoppingCellCode q).1 = refinedStoppingFailureCube q :=
  rfl

@[simp]
theorem repairedStoppingCellCode_snd
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) :
    (repairedStoppingCellCode q).2 = q.2 :=
  rfl

theorem isSelectedRepairedCellCode_repairedStoppingCellCode
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) :
    IsSelectedRepairedCellCode failure omega base
      (repairedStoppingCellCode q) := by
  refine ⟨q.1.1.2, ?_⟩
  intro R hR hsub
  exact q.1.2 ⟨R, hR⟩ hsub

/-- Fixed codes satisfying the selection predicate are exactly the original
sample-dependent refined stopping cells. -/
def refinedStoppingCellEquivSelectedCode
    (failure : TriadicCube d → Set Omega) (omega : Omega) (base : ℤ) :
    RefinedStoppingCell failure omega base ≃
      {q : RepairedStoppingCellCode d //
        IsSelectedRepairedCellCode failure omega base q} where
  toFun q := ⟨repairedStoppingCellCode q,
    isSelectedRepairedCellCode_repairedStoppingCellCode q⟩
  invFun q :=
    (⟨⟨q.1.1, q.2.1⟩, by
      intro R hsub
      exact q.2.2 R.1 R.2 hsub⟩, q.1.2)
  left_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      rfl
    · rfl
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext rfl rfl

/-- The fixed-code map is injective. -/
theorem repairedStoppingCellCode_injective
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ} :
    Function.Injective
      (repairedStoppingCellCode (failure := failure) (omega := omega)
        (base := base)) := by
  intro q r hqr
  exact (refinedStoppingCellEquivSelectedCode failure omega base).injective
    (Subtype.ext hqr)

/-- Scale readout on the fixed carrier. -/
def repairedStoppingCellCodeScale (q : RepairedStoppingCellCode d) : ℤ :=
  q.1.scale

/-- Center readout on the fixed carrier. -/
def repairedStoppingCellCodeCenter (q : RepairedStoppingCellCode d) : Vec d :=
  stoppingRelativeGridCentre q.1.scale (cubeCenter q.1) q.2.1

@[simp]
theorem repairedStoppingCellCodeScale_apply
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) :
    repairedStoppingCellCodeScale (repairedStoppingCellCode q) =
      refinedStoppingScale q :=
  rfl

@[simp]
theorem repairedStoppingCellCodeCenter_apply
    {failure : TriadicCube d → Set Omega} {omega : Omega} {base : ℤ}
    (q : RefinedStoppingCell failure omega base) :
    repairedStoppingCellCodeCenter (repairedStoppingCellCode q) =
      refinedStoppingCenter q :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
