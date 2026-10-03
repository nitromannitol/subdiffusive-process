module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section




open MeasureTheory Set

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

/-- A candidate local energy, given through its energy measure.
`gam u v s = Γ_E(u,v)(s)`; the form is `gam u v Set.univ`. -/
structure LocalEnergy (V : Type*) [AddCommGroup V] [Module ℝ V]
    (X : Type*) [MeasurableSpace X] where
  /-- The energy measure `Γ(u,v)(s)`. -/
  gam : V → V → Set X → ℝ
  gam_symm : ∀ u v s, gam u v s = gam v u s
  gam_add_left : ∀ u v w s, gam (u + v) w s = gam u w s + gam v w s
  gam_smul_left : ∀ (c : ℝ) (u v : V) (s : Set X), gam (c • u) v s = c * gam u v s
  gam_nonneg : ∀ (u : V) (s : Set X), 0 ≤ gam u u s
  gam_mono : ∀ (u : V) (s t : Set X), s ⊆ t → gam u u s ≤ gam u u t
  /-- Finite additivity of the energy measure on disjoint measurable sets. -/
  gam_add_disjoint : ∀ (u v : V) (s t : Set X), MeasurableSet s → MeasurableSet t → Disjoint s t → gam u v (s ∪ t) = gam u v s + gam u v t

namespace LocalEnergy

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]

/-- The energy form `E(u,v) = Γ_E(u,v)(X)`. -/
def form (E : LocalEnergy V X) (u v : V) : ℝ := E.gam u v Set.univ

theorem form_nonneg (E : LocalEnergy V X) (u : V) : 0 ≤ E.form u u :=
  E.gam_nonneg u Set.univ

theorem form_symm (E : LocalEnergy V X) (u v : V) : E.form u v = E.form v u :=
  E.gam_symm u v Set.univ

/-- Measure order `a Γ_E ≤ Γ_F` on all measurable sets, paper line 3253. -/
def measureLe (a : ℝ) (E F : LocalEnergy V X) : Prop :=
  ∀ (u : V) (s : Set X), MeasurableSet s → a * E.gam u u s ≤ F.gam u u s

/-- Form order `a E ≤ F`, paper line 3216. -/
def formLe (a : ℝ) (E F : LocalEnergy V X) : Prop :=
  ∀ u : V, a * E.form u u ≤ F.form u u

/-- The difference measure `Γ_D = Γ_F - c Γ_E` of Lemma `mfd:lem-diff`,
paper line 3275. -/
def diffGam (c : ℝ) (E F : LocalEnergy V X) (u v : V) (s : Set X) : ℝ :=
  F.gam u v s - c * E.gam u v s

end LocalEnergy

/-- A candidate local energy together with its domain inside an ambient
normed space `H`.  Used only where the paper compares two candidates whose
domains are not assumed equal (`mfd:prop-density`, `mfd:thm-C0`). -/
structure DomainedEnergy (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (X : Type*) [MeasurableSpace X] where
  /-- The form domain `D(E)`. -/
  dom : Submodule ℝ H
  /-- The energy measure on the domain. -/
  energy : LocalEnergy dom X

namespace DomainedEnergy

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {X : Type*} [MeasurableSpace X]

/-- The value of the form at an element of the domain. -/
def formAt (E : DomainedEnergy H X) (u : H) (hu : u ∈ E.dom) : ℝ :=
  E.energy.form ⟨u, hu⟩ ⟨u, hu⟩

end DomainedEnergy


/-- The exponent `e_d(α,β,γ,ζ)` of Lemma `mfd:lem-affine`, paper line 3525. -/
def affineExponent (d alpha beta gamma zeta : ℝ) : ℝ :=
  (d + zeta) / 2 -
    gamma * ((d - 2) / 2 + alpha + (alpha - beta) / (alpha + d / 2) * (2 - alpha))

/-- The continuous ramp of paper line 2648:
`ramp a b x = min 1 (max 0 ((x - a) / (b - a)))`, so that for `a < b`,
`1_{x > b} ≤ ramp a b x ≤ 1_{x > a}`. -/
def ramp (a b x : ℝ) : ℝ := min 1 (max 0 ((x - a) / (b - a)))

end Lane3
end SubdiffusiveProcess
