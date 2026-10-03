module

public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Strong locality in the sense of Fukushima--Oshima--Takeda**, relative to the state space `U`:
`E(u,v)=0` whenever `u,v ∈ D(E)` have compact supports in `U` and `u` is a.e. constant on a
neighbourhood of `supp[v]`.  Supports are the `m`-supports, so `supp[v] ⊆ K` for a closed `K` iff `v = 0`
a.e. off `K`; hence "`supp[v]` is compact and lies in the open set `W`" reads: some compact `K ⊆ U ∩ W` has
`v = 0` a.e. off `K`.  For `U = univ` this is the definition of FOT §1.1 for a form on a locally compact
separable metric space `X = U`. -/
def e5_fot_strongly_local {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) (U : Set X) : Prop :=
  ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    (∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∀ᵐ x ∂m, x ∉ K → u x = 0) →
    ∀ (c : ℝ) (W : Set X), IsOpen W →
      (∃ K : Set X, IsCompact K ∧ K ⊆ U ∩ W ∧ ∀ᵐ x ∂m, x ∉ K → v x = 0) →
      (∀ᵐ x ∂m, x ∈ W → u x = c) → E.form u v = 0

end Paper
