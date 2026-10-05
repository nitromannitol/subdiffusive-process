module

public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import MarkovProcess.Main
public import SubdiffusiveProcess.Processes.E7.Leaves
public import SubdiffusiveProcess.PartProcess.Identification

@[expose] public section

/-! Part-process association proved by restricted forms, bounded potential perturbation,
compact killing and exhaustion. The original theorem statement is retained. -/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
open SubdiffusiveProcess.E7
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- FOT §4.4: for a conservative Feller diffusion `K` associated with a regular Dirichlet form `E`
on `L²(m)` (`m` Radon with full support), the part form of `E` on an open set `U` is a closed form on
`L²(m|U)`, and the killed occupation resolvent of a nonnegative Borel `f ∈ L²(m|U)` is `m`-a.e. finite
and a version of the resolvent of the part form. -/
theorem inputs_classical_fot_part_process
    (d : ℕ) (m : Measure (Fin d → ℝ)) (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (hE : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hassoc : ∀ (μ : ℝ), 0 < μ → ∀ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m,
      _root_.SubdiffusiveProcess.DirichletForm.IsResolvent E.toClosedForm μ G →
      ∀ (g : (Fin d → ℝ) → ℝ) (_hg : Continuous g) (_hgc : HasCompactSupport g)
        (hgL : MemLp g 2 m),
        (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) *
            ∫ w, g (w (Real.toNNReal t)) ∂(K x)) =ᵐ[m] ⇑(G (hgL.toLp g)))
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    ∃ F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (m.restrict U), IsPartFormOn E.toClosedForm U F ∧
      ∀ (α : ℝ), 0 < α → ∀ G : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 (m.restrict U),
        _root_.SubdiffusiveProcess.DirichletForm.IsResolvent F α G →
        ∀ (f : (Fin d → ℝ) → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
          ∀ hf : MemLp f 2 (m.restrict U),
            (∀ᵐ x ∂(m.restrict U), killedOcc K U α f x < ⊤) ∧
            (fun x => (killedOcc K U α f x).toReal) =ᵐ[m.restrict U] ⇑(G (hf.toLp f)) := by
  let D : SubdiffusiveProcess.PartProcess.Data d m :=
    ⟨E, hE, P, hP, hF, K, hK, hfdd, hassoc⟩
  exact SubdiffusiveProcess.PartProcess.exists_part_with_association hm hpos D U hU

end SubdiffusiveProcess.Paper
