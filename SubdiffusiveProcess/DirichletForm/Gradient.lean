/-
# Gradient-type energies and their Markov property
-/
import SubdiffusiveProcess.DirichletForm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gradient-type energies and their Markov property

Most concrete Dirichlet forms are given by a *gradient energy*

`E(u) = ∫ q(x, ∇u(x)) dμ(x)`

with `q(x, ·)` nonnegative and homogeneous of degree two — for a divergence-form
operator, `q(x, ξ) = ⟪A(x) ξ, ξ⟫`.  For such a form the Markov property is an
immediate consequence of one analytic fact: composition with a normal
contraction `T` keeps the element in the space and replaces the gradient by
`T'(u) ∇u`, with `|T'| ≤ 1` (Stampacchia).

Mathlib 4.26 has **no** Sobolev space and no weak-gradient chain rule (the only
Sobolev file is `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`, the
Gagliardo–Nirenberg–Sobolev inequality), so that fact is stated here as the
`Prop`-valued external input `DirichletForm.HasContractionChainRule`.  It is not
an axiom; it is passed as a hypothesis, exactly like the other inputs of this
library.

Given the input, `DirichletForm.GradientEnergy.exists_comp_energy_le` and
`DirichletForm.ClosedForm.isMarkovian_of_gradientEnergy` are **proved**: the
energy does not increase under a normal contraction, and a closed form whose
energy is a gradient energy is Markovian.

## References

* G. Stampacchia, *Le problème de Dirichlet pour les équations elliptiques du
  second ordre à coefficients discontinus*, Ann. Inst. Fourier 15 (1965)
  (truncation of Sobolev functions).
* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  Example 1.2.3 and Theorem 1.4.1.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace DirichletForm

variable {X : Type*} [MeasurableSpace X]

/-- A **gradient energy structure** on a type `H`: every element has a value
(a function on `X`) and a gradient (a `V`-valued function on `X`), and its energy
is the `μ`-integral of a nonnegative, degree-two homogeneous integrand of the
gradient.

Inhabited by: `DirichletForm.zeroGradientEnergy`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`DirichletForm.HasEnergyMeasure`. -/
structure GradientEnergy (μ : Measure X) (V : Type*) [SMul ℝ V] (H : Type*) where
  /-- The value of an element, as a function on `X`. -/
  value : H → X → ℝ
  /-- The gradient of an element. -/
  grad : H → X → V
  /-- The energy integrand `q(x, ξ)`. -/
  integrand : X → V → ℝ
  /-- The energy `E(u) = ∫ q(x, ∇u x) dμ`. -/
  energy : H → ℝ
  /-- `q(x, ξ) ≥ 0`. -/
  integrand_nonneg : ∀ (x : X) (ξ : V), 0 ≤ integrand x ξ
  /-- `q(x, cξ) = c² q(x, ξ)`: the integrand is a quadratic form in the
  gradient. -/
  integrand_smul : ∀ (x : X) (c : ℝ) (ξ : V), integrand x (c • ξ) = c ^ 2 * integrand x ξ
  /-- The energy is the integral of the integrand of the gradient. -/
  energy_eq : ∀ u : H, energy u = ∫ x, integrand x (grad u x) ∂μ
  /-- The integrand of the gradient is integrable. -/
  integrable : ∀ u : H, Integrable (fun x => integrand x (grad u x)) μ



structure HasContractionChainRule {μ : Measure X} {V : Type*} [SMul ℝ V] {H : Type*}
    (G : GradientEnergy μ V H) (m : Measure X) : Prop where
  /-- `T ∘ u` lies in the space with gradient `d · ∇u`, `|d| ≤ 1`. -/
  exists_comp : ∀ (u : H) (T : ℝ → ℝ), IsNormalContraction T →
    ∃ (v : H) (d : X → ℝ), (∀ x : X, |d x| ≤ 1) ∧
      ((G.value v) =ᵐ[m] fun x => T (G.value u x)) ∧
      ((G.grad v) =ᵐ[μ] fun x => d x • G.grad u x)

namespace GradientEnergy

variable {μ : Measure X} {V : Type*} [SMul ℝ V] {H : Type*} (G : GradientEnergy μ V H)

/-- Scaling the gradient by a factor bounded by `1` does not increase the
energy. -/
theorem energy_le_of_grad_smul {u v : H} {d : X → ℝ} (hd : ∀ x : X, |d x| ≤ 1)
    (hgrad : (G.grad v) =ᵐ[μ] fun x => d x • G.grad u x) : G.energy v ≤ G.energy u := by
  have hae : (fun x => G.integrand x (G.grad v x))
      =ᵐ[μ] fun x => d x ^ 2 * G.integrand x (G.grad u x) := by
    filter_upwards [hgrad] with x hx
    rw [hx, G.integrand_smul]
  rw [G.energy_eq v, G.energy_eq u, integral_congr_ae hae]
  refine integral_mono ((G.integrable v).congr hae) (G.integrable u) fun x => ?_
  have h1 : d x ^ 2 ≤ 1 := by
    have := hd x
    nlinarith [abs_nonneg (d x), sq_abs (d x)]
  nlinarith [G.integrand_nonneg x (G.grad u x)]

/-- **Markov property of a gradient energy.**  Given the chain rule for normal
contractions, composing with a normal contraction produces an element of the
structure whose value is `T ∘ u` and whose energy is at most that of `u`. -/
theorem exists_comp_energy_le {m : Measure X} (hchain : HasContractionChainRule G m)
    (u : H) (T : ℝ → ℝ) (hT : IsNormalContraction T) :
    ∃ v : H, ((G.value v) =ᵐ[m] fun x => T (G.value u x)) ∧ G.energy v ≤ G.energy u := by
  obtain ⟨v, d, hd, hval, hgrad⟩ := hchain.exists_comp u T hT
  exact ⟨v, hval, G.energy_le_of_grad_smul hd hgrad⟩

end GradientEnergy

namespace ClosedForm

/-- A closed form whose domain and energy are those of a gradient energy
structure is Markovian: every normal contraction operates on it. -/
theorem isMarkovian_of_gradientEnergy {m : Measure X} {μ : Measure X} {V : Type*}
    [SMul ℝ V] {H : Type*} (E : ClosedForm m) (G : GradientEnergy μ V H)
    (hchain : HasContractionChainRule G m) (toLp : H → Lp ℝ 2 m)
    (hmem : ∀ u : H, toLp u ∈ E.domain)
    (hsurj : ∀ u ∈ E.domain, ∃ h : H, toLp h = u)
    (hvalue : ∀ u : H, ⇑(toLp u) =ᵐ[m] G.value u)
    (hform : ∀ u : H, E.form (toLp u) (toLp u) = G.energy u) :
    E.IsMarkovian := by
  intro T hT u hu w hw
  obtain ⟨h, rfl⟩ := hsurj u hu
  obtain ⟨v, hval, hle⟩ := G.exists_comp_energy_le hchain h T hT
  have hwv : ⇑w =ᵐ[m] ⇑(toLp v) := by
    filter_upwards [hw, hval, hvalue h, hvalue v] with x hx hx1 hx2 hx3
    rw [hx, hx2, ← hx1, hx3]
  have hweq : w = toLp v := Lp.ext_iff.mpr hwv
  refine ⟨hweq ▸ hmem v, ?_⟩
  rw [hweq, hform v, hform h]
  exact hle

end ClosedForm

end DirichletForm
