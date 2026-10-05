module

public import SubdiffusiveProcess.Probability.BrownianProduct.HeatInput

@[expose] public section

/-!
# The remaining bounded-potential ground-state operator theorem

This file imports only Mathlib through `HeatInput`. All semigroup data are
ordinary continuous linear maps; the resolvent is an explicit Bochner integral.
The path integral is written explicitly as well. There is no library law,
MarkovProcess semigroup, or target lower estimate in this obligation.

`GroundStateOperatorInput` is the explicit analytic interface of this module. Its difficult
content includes the Dirichlet Sobolev multiplier, bounded-potential
Feynman--Kac theorem, and continuous kernel construction.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Probability.BrownianProduct

attribute [local instance] pathMeasurableSpace

/-- The weighted measure for the ground-state transform. -/
def groundStateMeasure {d : ℕ} (a : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) :
    Measure (Fin d → ℝ) :=
  (volume.withDensity (fun x => ENNReal.ofReal (a x))).restrict W

/-- The zero-boundary Sobolev graph as smooth compactly supported approximation. -/
def SobolevGraph {d : ℕ} (W : Set (Fin d → ℝ))
    (u : (Fin d → ℝ) → ℝ) (g : (Fin d → ℝ) → Fin d → ℝ) : Prop :=
  MemLp u 2 (volume.restrict W) ∧
    (∀ i : Fin d, MemLp (fun x => g x i) 2 (volume.restrict W)) ∧
    ∃ f : ℕ → (Fin d → ℝ) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ W) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 (volume.restrict W)) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto
        (fun n => eLpNorm (fun x => fderiv ℝ (f n) x (Pi.single i 1) - g x i)
          2 (volume.restrict W)) atTop (𝓝 0)

/-- The original bounded coefficient and Lipschitz logarithmic derivative assumptions. -/
def RegularLogCoefficientOn {d : ℕ} (a : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) : Prop :=
  AEStronglyMeasurable a (volume.restrict W) ∧
    (∃ lo hi : ℝ, 0 < lo ∧ ∀ᵐ x ∂volume.restrict W, lo ≤ a x ∧ a x ≤ hi) ∧
    (∀ x ∈ W, DifferentiableAt ℝ (fun y => Real.log (a y)) x) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ W, ∀ i : Fin d,
      |fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1)| ≤ M) ∧
    ∃ C : ℝ≥0, ∀ i : Fin d, LipschitzOnWith C
      (fun x => fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1)) W

/-- The distributional ground-state potential identity against smooth test functions. -/
def WeakGroundStatePotential {d : ℕ} (a : (Fin d → ℝ) → ℝ)
    (W : Set (Fin d → ℝ)) (V : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ phi : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
    tsupport phi ⊆ W →
    (∫ x in W, V x * phi x) =
      -(1 / 2) * (∫ x in W, ∑ i,
        fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1) * fderiv ℝ phi x (Pi.single i 1)) +
      (1 / 4) * ∫ x in W, (∑ i,
        fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1) *
          fderiv ℝ (fun y => Real.log (a y)) x (Pi.single i 1)) * phi x

/-- The weighted operator construction for an already supplied Brownian path kernel. -/
structure GroundStateOperators {d : ℕ} (a : (Fin d → ℝ) → ℝ)
    (W : Set (Fin d → ℝ)) (V : (Fin d → ℝ) → ℝ)
    (ν : Kernel (Fin d → ℝ) C(ℝ≥0, Fin d → ℝ)) where
  density : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  kernel : ℝ≥0 → Kernel (Fin d → ℝ) (Fin d → ℝ)
  operator : ℝ≥0 → Lp ℝ 2 (groundStateMeasure a W) →L[ℝ] Lp ℝ 2 (groundStateMeasure a W)
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ _
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  opNorm_le_one : ∀ t, ‖operator t‖ ≤ 1
  continuous_orbit : ∀ f, Continuous (fun t => operator t f)
  kernel_subMarkov : ∀ t x, kernel t x univ ≤ 1
  kernel_subinvariant : ∀ t, kernel t ∘ₘ groundStateMeasure a W ≤ groundStateMeasure a W
  associated : ∀ t (f : Lp ℝ 2 (groundStateMeasure a W)),
    operator t f =ᵐ[groundStateMeasure a W] fun x => ∫ y, f y ∂kernel t x
  density_measurable : ∀ s : ℝ, 0 < s →
    Measurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => density s z.1 z.2)
  density_nonneg : ∀ s : ℝ, 0 < s → ∀ z ∈ W, ∀ w ∈ W, 0 ≤ density s z w
  density_continuous : ContinuousOn
    (fun z : ℝ × (Fin d → ℝ) × (Fin d → ℝ) => density z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ W ×ˢ W)
  kernel_density : ∀ s : ℝ, 0 < s → ∀ z ∈ W,
    kernel (Real.toNNReal s) z =
      (groundStateMeasure a W).withDensity (fun y => ENNReal.ofReal (density s z y))
  resolvent_one : ∀ f : Lp ℝ 2 (groundStateMeasure a W),
    ∃ u : (Fin d → ℝ) → ℝ, ∃ g : (Fin d → ℝ) → Fin d → ℝ,
      SobolevGraph W u g ∧
      ((∫ t in Ioi (0 : ℝ), Real.exp (-t) • operator (Real.toNNReal t) f :
          Lp ℝ 2 (groundStateMeasure a W))
        =ᵐ[groundStateMeasure a W] u) ∧
      ∀ v : (Fin d → ℝ) → ℝ, ∀ h : (Fin d → ℝ) → Fin d → ℝ, SobolevGraph W v h →
        (∫ x in W, a x * u x * v x) + (∫ x in W, ∑ i, a x * g x i * h x i) =
          ∫ x in W, a x * f x * v x
  feynmanKac_representation : ∀ s : ℝ, 0 < s → ∀ z ∈ W,
    ∀ A : Set (Fin d → ℝ), MeasurableSet A →
      (∫⁻ ω in {ω | (∀ r : ℝ≥0, r ≤ Real.toNNReal s → ω r ∈ W) ∧
          ω (Real.toNNReal s) ∈ A},
        ENNReal.ofReal (Real.exp (-(∫ r in (0 : ℝ)..(Real.toNNReal s : ℝ),
          V (ω (Real.toNNReal r))))) ∂ν z) =
      ∫⁻ y in A ∩ W, ENNReal.ofReal (Real.sqrt (a z * a y) * density s z y) ∂volume

/-- The exact remaining ground-state/Feynman--Kac operator existence theorem.
The continuous Brownian law is a hypothesis here and is constructed independently. -/
def GroundStateOperatorInput (d : ℕ) : Prop :=
  ∀ ν : Kernel (Fin d → ℝ) C(ℝ≥0, Fin d → ℝ), LaplacianBrownianLaw d ν →
    ∀ a : (Fin d → ℝ) → ℝ, (∀ x, 0 < a x) → ∀ z : Fin d → ℝ, ∀ L : ℝ, 0 < L →
      let W : Set (Fin d → ℝ) := pi univ (fun i => Ioo (z i - L / 2) (z i - L / 2 + L))
      RegularLogCoefficientOn a W →
      ∀ V : (Fin d → ℝ) → ℝ, Measurable V → (∃ Q : ℝ, ∀ x, |V x| ≤ Q) →
      WeakGroundStatePotential a W V → Nonempty (GroundStateOperators a W V ν)

end SubdiffusiveProcess.Probability.BrownianProduct
