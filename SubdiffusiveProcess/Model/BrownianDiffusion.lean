module

public import SubdiffusiveProcess.Model.LifetimeProcess
public import SubdiffusiveProcess.Model.HeatSemigroupVec

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Model.HeatSemigroupVec
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Model.BrownianDiffusion

open SubdiffusiveProcess.Model.LifetimeProcess

variable {d : ℕ}

/-- **`d`-dimensional Brownian motion as a Section 9 path kernel.** -/
def brownianLifetimeProcess (d : ℕ) : Kernel (Vec d) (Path d) :=
  lifetimeProcess (heatSemigroupVec d) isConservative_heatSemigroupVec



theorem strongMarkov_brownianLifetimeProcess (d : ℕ) :
    StrongMarkov (brownianLifetimeProcess d) :=
  strongMarkov_lifetimeProcess _ _ isFellerKernelSemigroup_heatSemigroupVec
    kolmogorovRegular_heatSemigroupVec

instance isMarkovKernel_brownianLifetimeProcess : IsMarkovKernel (brownianLifetimeProcess d) := by
  refine ⟨fun x => ⟨?_⟩⟩
  exact lifetimeProcess_univ _ _ x



def KilledResolventSolvesMassive (c rho : Vec d → ℝ) (law : Kernel (Vec d) (Path d)) : Prop :=
  ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
    ∀ s : ℝ, 0 < s → ∀ f : Vec d → ℝ,
      MemLp f 2 ((weightedMeasure rho).restrict U) →
      ∃ u : H10Function U,
        (∀ᵐ x ∂(weightedMeasure rho).restrict U,
            u.toH1Function.toFun x = killedResolvent law U s f x) ∧
          SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
            c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x)

/-- `LocalDiffusion` is exactly `StrongMarkov`, local ellipticity, and
`KilledResolventSolvesMassive`. -/
theorem localDiffusion_iff (c rho : Vec d → ℝ) (law : Kernel (Vec d) (Path d)) :
    LocalDiffusion c rho law ↔
      StrongMarkov law ∧
        (∀ K : Set (Vec d), IsCompact K → CoefficientOn K c ∧ CoefficientOn K rho) ∧
        KilledResolventSolvesMassive c rho law :=
  Iff.rfl

/-- **The Brownian `LocalDiffusion (1/2) 1` construction, reduced to one analytic statement.** If the
killed resolvent of `d`-dimensional Brownian motion solves the massive equation weakly on
bounded open sets, then this law satisfies `LocalDiffusion (1/2) 1`. The conclusion does not
assert existence for other coefficient pairs or provide continuous killed densities. -/
theorem localDiffusion_of_killedResolventSolvesMassive (d : ℕ)
    (hres : KilledResolventSolvesMassive (fun _ => (1/2 : ℝ)) (fun _ => (1 : ℝ))
      (brownianLifetimeProcess d)) :
    LocalDiffusion (fun _ => (1/2 : ℝ)) (fun _ => (1 : ℝ)) (brownianLifetimeProcess d) :=
  ⟨strongMarkov_brownianLifetimeProcess d,
    fun K _ => ⟨coefficientOn_const (by norm_num) K, coefficientOn_one K⟩, hres⟩

/-- The same reduction for an arbitrary pair of positive constant coefficients and an arbitrary
strong Markov law: the second clause of `LocalDiffusion` is never the obstruction. -/
theorem exists_localDiffusion_of_exists_killedResolventSolvesMassive (d : ℕ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hres : ∃ law : Kernel (Vec d) (Path d), StrongMarkov law ∧
      KilledResolventSolvesMassive (fun _ => a) (fun _ => b) law) :
    ∃ law : Kernel (Vec d) (Path d),
      LocalDiffusion (fun _ => a) (fun _ => b) law := by
  obtain ⟨law, hSM, hR⟩ := hres
  exact ⟨law, hSM, fun K _ => ⟨coefficientOn_const ha K, coefficientOn_const hb K⟩, hR⟩

end SubdiffusiveProcess.Model.BrownianDiffusion
