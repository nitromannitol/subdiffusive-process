import SubdiffusiveProcess.Processes.E7.Leaves
import SubdiffusiveProcess.Processes.E7.ResolventExists
import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
import SubdiffusiveProcess.DirichletForm.FOTProduct
import SubdiffusiveProcess.Processes.FellerRealizationInfinite
import MarkovProcess.Trajectory.FeynmanKacFunctional

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess

/-- Precisely the form/process hypotheses of the frozen part-process statement. -/
structure Data (d : ℕ) (m : Measure (Fin d → ℝ)) where
  form : _root_.DirichletForm m
  regular : DirichletForm.IsRegular form.toClosedForm
  semigroup : SubMarkovKernelSemigroup (Fin d → ℝ)
  conservative : semigroup.IsConservative
  feller : semigroup.IsFellerKernelSemigroup
  law : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))
  markov : IsMarkovKernel law
  marginals : ∀ I x, law.map (ContinuousPath.finsetEvaluation I) x =
    SubMarkovKernelSemigroup.finiteSetKernel semigroup I x
  associated : ∀ (α : ℝ), 0 < α →
    ∀ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m,
      DirichletForm.IsResolvent form.toClosedForm α G →
      ∀ (g : (Fin d → ℝ) → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
        (hgL : MemLp g 2 m),
        (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
          ∫ w, g (w (Real.toNNReal t)) ∂(law x)) =ᵐ[m] ⇑(G (hgL.toLp g))

/-- The nonnegative potential occupation operator on the supplied continuous-path law. -/
def potentialOcc {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (q : (Fin d → ℝ) → ℝ) (α : ℝ) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-α * t)) *
    ∫⁻ w, ENNReal.ofReal (Real.exp
      (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional q (Real.toNNReal t) w)) *
      ENNReal.ofReal (f (w (Real.toNNReal t))) ∂(K x)

/-- Vanishing off a measurable region is a property of an `L²` class. -/
def ZeroOutside {X : Type*} [MeasurableSpace X] {m : Measure X}
    (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  ∀ᵐ x ∂m, x ∉ U → u x = 0

/-- Closedness for the graph norm, without requiring density in ambient `L²`. -/
def GraphClosed {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) (D : Submodule ℝ (Lp ℝ 2 m)) : Prop :=
  D ≤ E.domain ∧ ∀ (u : ℕ → Lp ℝ 2 m) (v : Lp ℝ 2 m),
    (∀ n, u n ∈ D) → v ∈ E.domain →
    Tendsto (fun n => E.energyNormSq (u n - v)) atTop (𝓝 0) → v ∈ D

/-- The variational resolvent on a graph-closed subspace. -/
def IsDomainResolvent {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) (D : Submodule ℝ (Lp ℝ 2 m)) (α : ℝ)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Prop :=
  ∀ f, G f ∈ D ∧ ∀ v ∈ D,
    α * inner ℝ (G f) v + E.form (G f) v = inner ℝ f v

end SubdiffusiveProcess.PartProcess
