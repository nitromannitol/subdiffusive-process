module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.SecondMomentBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannSourceL8
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Renormalized.RenormalizedFromSharp
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.SharpAsymptoticFromDual
public import SubdiffusiveProcess.Providers.Section5.OneStepConcretePrimalClosure
public import SubdiffusiveProcess.Providers.Section5.SharpAsymptoticCore

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
open SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-! ## The almost-everywhere weak-Hessian transport -/

/-- **A weak Hessian depends on its `H¹` argument only through the gradient's
almost-everywhere class.**  The a.e. counterpart of `nfWeakHessianOfGradEq`;
the `hess` field is untouched, so every quantity built from it — in particular
`oneStepCellB` — is unchanged. -/
def weakHessianOfGradAeEq {U : Set (Vec d)} {u v : H1Function U}
    (hgrad : u.grad =ᵐ[volumeMeasureOn U] v.grad)
    (H : HasWeakHessianOn U v) :
    HasWeakHessianOn U u where
  hess := H.hess
  hess_memL2 := H.hess_memL2
  weak_second := by
    intro i j phi hphi hphis hphisub
    have hbase := H.weak_second i j phi hphi hphis hphisub
    refine Eq.trans ?_ hbase
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx]

@[simp] theorem weakHessianOfGradAeEq_hess {U : Set (Vec d)}
    {u v : H1Function U} (hgrad : u.grad =ᵐ[volumeMeasureOn U] v.grad)
    (H : HasWeakHessianOn U v) :
    (weakHessianOfGradAeEq hgrad H).hess = H.hess := rfl

/-! ## The exponent-four budget -/

/-- The exponent-four source-cell energy budget is discharged. -/
theorem paperNeumannSourceCellEnergyFourthBudget_holds (d : ℕ) [NeZero d] :
    PaperNeumannSourceCellEnergyFourthBudget d :=
  exists_oneStepPaperNeumannSourceCellEnergy_four_budget d

/-- The normalized second moment, reduced to the single remaining pathwise
input. -/
theorem dualGluedCellSecondMoment_of_pathwise (d : ℕ) [NeZero d]
    (hpath : DualGluedCellPathwiseEnvelope d) :
    DualGluedCellSecondMoment d :=
  dualGluedCellSecondMoment_of_pathwise_and_fourthBudget d hpath
    (paperNeumannSourceCellEnergyFourthBudget_holds d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
