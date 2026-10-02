import Mathlib
import MarkovProcess.Lifetime.ExitTimeStopping




set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Input

/-- The finite-coordinate state space, with its usual product norm and volume. -/
abbrev State (d : ℕ) := Fin d → ℝ

/-- The live state, extended by zero at the cemetery solely to totalize evaluation. -/
def stateAt {d : ℕ} (t : NNReal) (w : LifetimePath (State d)) : State d :=
  (LifetimePath.coordinate t w).elim id (fun _ => 0)

/-- The speed measure of the divergence operator `rho⁻¹ div(c grad)`. -/
def speedMeasure {d : ℕ} (rho : State d → ℝ) : Measure (State d) :=
  volume.withDensity (fun x => ENNReal.ofReal (rho x))

/-- The normalized, exit-killed Laplace integral of the supplied path law. -/
def occupationResolvent {d : ℕ} (law : Kernel (State d) (LifetimePath (State d)))
    (U : Set (State d)) (s : ℝ) (f : State d → ℝ) (x : State d) : ℝ :=
  s⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-t / s) *
    ∫ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
      f (stateAt (Real.toNNReal t) w) ∂law x

/-- Restart of a possibly explosive lifetime process, expressed as equality of measures. -/
def Restart {d : ℕ} (law : Kernel (State d) (LifetimePath (State d))) : Prop :=
  (∀ x, law x univ = 1) ∧
  (∀ x, ∀ᵐ w ∂law x, LifetimePath.coordinate 0 w = Cemetery.alive x) ∧
  ∀ x, ∀ T : LifetimePath (State d) → ENNReal,
    ∀ hT : IsStoppingTime LifetimePath.canonicalFiltration T,
      ∀ B, MeasurableSet[hT.measurableSpace] B →
        ((law x).restrict (B ∩ {w | T w < w.lifetime})).map
            (fun w => LifetimePath.shift (T w).toNNReal w) =
          ((law x).restrict (B ∩ {w | T w < w.lifetime})).bind
            (fun w => law (stateAt (T w).toNNReal w))



structure BoundaryApproximation {d : ℕ} (U : Set (State d))
    (u : State d → ℝ) (Du : State d → State d) where
  memLp : MemLp u 2 (volume.restrict U)
  grad_memLp : ∀ i, MemLp (fun x => Du x i) 2 (volume.restrict U)
  approx : ℕ → State d → ℝ
  smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  compactSupport : ∀ n, HasCompactSupport (approx n)
  support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_fun : Tendsto
    (fun n => eLpNorm (fun x => approx n x - u x) 2 (volume.restrict U)) atTop (𝓝 0)
  tendsto_grad : ∀ i, Tendsto
    (fun n => eLpNorm (fun x => (fderiv ℝ (approx n) x) (Pi.single i 1) - Du x i)
      2 (volume.restrict U)) atTop (𝓝 0)

/-- The two unresolved killed-generator obligations, stated on smooth tests and raw functions.
The normalization is `(s⁻¹ - L)u = s⁻¹f`, for `L = rho⁻¹ div(c grad)`.
This must hold on every bounded open set, including nonsmooth domains. -/
def KilledGenerator {d : ℕ} (c rho : State d → ℝ)
    (law : Kernel (State d) (LifetimePath (State d))) : Prop :=
  ∀ U : Set (State d), IsOpen U → Bornology.IsBounded U →
    ∀ s : ℝ, 0 < s → ∀ f : State d → ℝ,
      MemLp f 2 ((speedMeasure rho).restrict U) →
      ∃ u : State d → ℝ, ∃ Du : State d → State d,
        Nonempty (BoundaryApproximation U u Du) ∧
        (u =ᵐ[(speedMeasure rho).restrict U] occupationResolvent law U s f) ∧
        ∀ ψ : State d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ U →
          (∫ x in U, ∑ i, (c x * Du x i) * (fderiv ℝ ψ x) (Pi.single i 1)) =
            ∫ x in U, (rho x * (s⁻¹ * (f x - u x))) * ψ x

/-- A pointwise continuous density of the killed law relative to the specified speed measure.
This is a separate missing analytic input; a bare `L²` operator cannot identify all starts. -/
def ContinuousKilledDensities {d : ℕ} (rho : State d → ℝ)
    (law : Kernel (State d) (LifetimePath (State d))) : Prop :=
  ∀ U : Set (State d), IsOpen U → Bornology.IsBounded U →
    ∃ p : ℝ → State d → State d → ℝ,
      (∀ t > 0, Measurable (Function.uncurry (p t))) ∧
      (∀ t > 0, ∀ x ∈ U, ∀ y ∈ U, 0 ≤ p t x y) ∧
      (∀ t > 0, ∀ x ∈ U, ∀ B : Set (State d), MeasurableSet B →
        law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
          LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} =
          ∫⁻ y in B ∩ U, ENNReal.ofReal (p t x y) ∂speedMeasure rho) ∧
      ContinuousOn (fun z : ℝ × State d × State d => p z.1 z.2.1 z.2.2)
        (Ioi 0 ×ˢ U ×ˢ U)

/-- Differentiability with a derivative Lipschitz on every compact set. -/
def LocallyC11 {d : ℕ} (a : State d → ℝ) : Prop :=
  ∃ Da : State d → (State d →L[ℝ] ℝ),
    (∀ x, HasFDerivAt a (Da x) x) ∧
    ∀ K : Set (State d), IsCompact K → ∃ C : NNReal, LipschitzOnWith C Da K

/-- The absent realization theorem for positive locally `C¹ˑ¹` scalar coefficients.
It includes the stochastic construction and the two independent analytic identifications.
The interface permits explosion and contains no GMC diffusion or Sobolev predicate. -/
def SmoothRealization (d : ℕ) : Prop :=
  ∀ a : State d → ℝ, (∀ x, 0 < a x) → LocallyC11 a →
    ∀ rho : State d → ℝ, (rho = a ∨ rho = fun _ => 1) →
      ∃ law : Kernel (State d) (LifetimePath (State d)),
        Restart law ∧ KilledGenerator a rho law ∧ ContinuousKilledDensities rho law

end SubdiffusiveProcess.Probability.Diffusion.Input
