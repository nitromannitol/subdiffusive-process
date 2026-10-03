module

public import SubdiffusiveProcess.Section10.PhysicalAttachmentStrongMarkov

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/-- The actual coefficient determines its whole-space C0 resolvent. This removes
dependence on the choice of PDE solutions in the physical family construction. -/
theorem physical_resolvent_unique {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) (D E : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D)
    (hE : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) E) :
    D = E := by
  have hgraph : ∀ R : C0ResolventDatum (Vec d),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) R →
      ∀ (mu : Semigroup.PositiveShift) (f : C₀(Vec d, ℝ)),
        (physicalPotential M L omega, R.solution mu f) ∈
        pa_graph d 1 0 (mu : ℝ) f := by
    intro R hR mu f k
    have h := pa_cubeRel_of_weak hR mu f k
    change ∃ G, pa_cubeRel d k (mu : ℝ) f
      (fun x => 1 * Real.exp (physicalPotential M L omega x - 0))
      (fun x => Real.exp (physicalPotential M L omega x - 0)) (R.solution mu f) G
    simpa only [sub_zero, one_mul, exp_physicalPotential] using h
  have hsol : D.solution = E.solution := by
    funext mu f
    exact pa_graph_unique one_pos mu.2 f (physicalPotential M L omega)
      (D.solution mu f) (E.solution mu f) (hgraph D hD mu f) (hgraph E hE mu f)
  cases D
  cases E
  dsimp only at hsol
  cases hsol
  rfl

/-- The generated semigroup is independent of all resolvent and density-range
choices: two actual weak characterizations yield equal transition kernels. -/
theorem physical_fellerSemigroup_unique {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) (D E : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D)
    (hE : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) E)
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hedense : ∀ mu, DenseRange (E.operator mu)) :
    D.fellerKernelSemigroup hdense = E.fellerKernelSemigroup hedense := by
  cases physical_resolvent_unique M L omega D E hD hE
  rfl

/-- Every-start path laws attached to the actual coefficient agree, even when
their Section 8 resolvent data were constructed independently. Section 7 uses
this same generated semigroup and the same full-FDD path determination. -/
theorem physical_law_unique {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) (D E : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D)
    (hE : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) E)
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hedense : ∀ mu, DenseRange (E.operator mu))
    (K Q : Kernel (Vec d) (ContinuousPath (Vec d))) (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x)
    (hqfdd : ∀ I x, Q.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (E.fellerKernelSemigroup hedense) I x) :
    K = Q := by
  have heq := physical_fellerSemigroup_unique M L omega D E hD hE hdense hedense
  apply physical_slice_unique (D.fellerKernelSemigroup hdense) K Q hK hfdd
  simpa only [heq] using hqfdd

end SubdiffusiveProcess.Section10.PhysicalAttachment
