module

public import SubdiffusiveProcess.Model.LifetimeProcess
public import SubdiffusiveProcess.Model.HeatSemigroupVec

@[expose] public section

/-!
# `d`-dimensional Brownian motion as a `Path d` kernel, and what is left of `LocalDiffusion`

`SubdiffusiveProcess.Model.HeatSemigroupVec` builds the `d`-dimensional heat semigroup and
`SubdiffusiveProcess.Model.LifetimeProcess` transports the continuous-path process of a Feller semigroup onto
the Section 9 carrier `Path d = LifetimePath (Vec d)`.  Composing the two gives
`brownianLifetimeProcess d : Kernel (Vec d) (Path d)`, an honest `d`-dimensional Brownian
motion, and `strongMarkov_brownianLifetimeProcess` shows it satisfies `StrongMarkov`.

`LocalDiffusion c ρ law` is the conjunction of three clauses.  The first two are discharged here
for that law and the constant coefficients `c ≡ 1/2`, `ρ ≡ 1`; the third — the resolvent clause —
is isolated as the predicate `KilledResolventSolvesMassive`, and

    `localDiffusion_of_killedResolventSolvesMassive`

says that it is the *only* thing missing: a proof of
`KilledResolventSolvesMassive (1/2) 1 (brownianLifetimeProcess d)` yields
`LocalDiffusion (1/2) 1 (brownianLifetimeProcess d)`. This would inhabit the bare predicate
for that coefficient pair. It would not produce a diffusion for a prescribed GMC coefficient,
nor supply the continuous killed densities required by `LocalDiffusionData`.

## The normalisation

`IsMassiveWeakSolutionOn c ρ s⁻¹ U u (s⁻¹ f)` is the weak form of
`s⁻¹ ρ u - ∇·(c ∇u) = s⁻¹ ρ f`, i.e. the resolvent equation of the generator `ρ⁻¹ ∇·(c ∇)`.
The killed resolvent of the *definition* is `s⁻¹ (s⁻¹ - L^U)^{-1} f`, so the clause asks for
`L^U = ρ⁻¹ ∇·(c ∇)`.  `heatSemigroupVec` has variance `t`, whose generator is `Δ/2`; the
matching coefficient pair is therefore `c ≡ 1/2`, `ρ ≡ 1`, and both are `CoefficientOn` data
because `CoefficientOn` only asks for a *positive* lower bound.  (Variance `2t` would give
`c ≡ ρ ≡ 1`; nothing below depends on the choice.)

## The remaining mathematics, stated exactly

`KilledResolventSolvesMassive (1/2) 1 law` says: for every bounded open `U`, every `s > 0` and
every `f ∈ L²(U)`, the killed resolvent
`killedResolvent law U s f = s⁻¹ ∫₀^∞ e^{-t/s} E_x[f(X_t) 1_{t < τ_U}] dt` agrees almost
everywhere on `U` with an `H¹₀(U)` function `u` satisfying

    `s⁻¹ ∫_U u φ + (1/2) ∫_U ∇u · ∇φ = s⁻¹ ∫_U f φ`   for all `φ ∈ H¹₀(U)`.

This is the identification of the `L²` generator of the killed process with the Dirichlet
Laplacian on `U`, i.e. the Dirichlet-form content of Section 8.  Two remarks on where it stands:

* Nothing in `MarkovProcess` supplies it.  `MarkovProcess/Killed/` constructs killed semigroups
  and their resolvents on a subtype carrier and proves resolvent identities *inside* that
  semigroup theory; it never meets `H¹` or a weak formulation, and `Killed/ExitTimeIdentification`
  concerns a different `killedResolvent` from the formalization's.
* The Section 8 files that look upstream (`KilledResolventLp.lean`, `KilledSemigroupLp.lean`,
  `LocalKilledLowerOccupationSolution.lean`) all consume this very clause: they take
  `hD : LocalDiffusion c rho law` and read the resolvent clause off it. The independent
  Brownian subinvariance and L² construction in `SubdiffusiveProcess.Model.KilledBrownian` removes that
  input from the L² operators, but does not identify their Sobolev domain or generator.

The display above already has the correct `Δ/2` normalisation. A witness for the different
pair `c = ρ = 1` would instead require the time change `t ↦ 2t` (variance `2t`), followed by
the same killed-generator identification. Neither coefficient pair alone supplies the
continuous-density clause of `LocalDiffusionData`.
-/

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

/-- Brownian motion satisfies the formalization's `StrongMarkov` predicate. -/
theorem strongMarkov_brownianLifetimeProcess (d : ℕ) :
    StrongMarkov (brownianLifetimeProcess d) :=
  strongMarkov_lifetimeProcess _ _ isFellerKernelSemigroup_heatSemigroupVec
    kolmogorovRegular_heatSemigroupVec

instance isMarkovKernel_brownianLifetimeProcess : IsMarkovKernel (brownianLifetimeProcess d) := by
  refine ⟨fun x => ⟨?_⟩⟩
  exact lifetimeProcess_univ _ _ x

/-- The third clause of `LocalDiffusion`, named on its own: the killed resolvent of `law` on
every bounded open set is an `H¹₀` solution of the massive equation.  This is the only part of
`LocalDiffusion` that the formalization cannot currently produce for any law. -/
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
