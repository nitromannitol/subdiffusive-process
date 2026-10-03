module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportResolvent
public import SubdiffusiveProcess.Processes.ResolventSolutionUniqueness

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalLocalTransport

/-- The active finite coefficient has the same further dilation as its density. -/
theorem localCoefficient_further_dilation {d : ℕ} (M : GMCModel d) {l m : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hlm : l ≤ m) (z : Vec d) (omega : AnchoredC11Sample d) (x : Vec d) :
    localCoefficient M l m z omega x =
      localCoefficient M l l z omega ((3 : ℝ) ^ (m - l) • x) := by
  simp only [localCoefficient, activeScale_coe, min_eq_right hlm, min_self,
    localSpeed_further_dilation M hlm]

/-- Weak-resolvent uniqueness for the literal local pair of the actual source coefficient. -/
theorem local_resolvent_unique {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (D E : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) D)
    (hE : IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) E) :
    D = E := by
  let B : MassiveCubeBounds (localCoefficient M L m z omega) (localSpeed M L m z omega) :=
    Classical.choice (SubdiffusiveProcess.nonempty_massiveCubeBounds_of_continuous_pos
    (c := localCoefficient M L m z omega) (rho := localSpeed M L m z omega)
    (continuous_const.mul (continuous_localSpeed M L m z omega))
    (continuous_localSpeed M L m z omega)
    (fun x => mul_pos (inv_pos.mpr (ahom_pos M (activeScale L m)))
      (localSpeed_pos M L m z omega x))
    (localSpeed_pos M L m z omega))
  have heq : D.solution = E.solution := by
    funext mu f
    ext x
    exact SubdiffusiveProcess.solution_eq_of_isWeakEllipticResolvent B hD hE mu f x
  cases D
  cases E
  dsimp only at heq
  cases heq
  rfl

/-- Every-start local path law is fixed by the actual coefficient pair and full FDDs.
The application module constructs these data, so this characterization is not a model premise. -/
theorem local_law_unique {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (D E : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) D)
    (hE : IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) E)
    (hdense : ∀ mu, DenseRange (D.operator mu)) (hedense : ∀ mu, DenseRange (E.operator mu))
    (K Q : Kernel (Vec d) (ContinuousPath (Vec d))) (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x)
    (hqfdd : ∀ I x, Q.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (E.fellerKernelSemigroup hedense) I x) : K = Q := by
  cases local_resolvent_unique M L m z omega D E hD hE
  exact PhysicalAttachment.physical_slice_unique _ K Q hK hfdd hqfdd

end SubdiffusiveProcess.Section10.PhysicalLocalTransport
