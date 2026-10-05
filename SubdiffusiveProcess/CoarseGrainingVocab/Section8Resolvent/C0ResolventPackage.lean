module

public import MarkovProcess.Feller.Resolvent

@[expose] public section

/-!
# The `C₀` resolvent package consumed by the process construction

Section 8 of *Subdiffusion in a log-correlated random potential* fixes, a pair of positive locally bounded functions
`(c, ρ)`, sets `dμ = ρ dx`, and lets `H` be the nonnegative operator on `L²(μ)`
associated with the energy form `ℰ(u,v) = ∫ c ∇u · ∇v dx`; the resolvent
`R_s = (I + s H)⁻¹` is then the object all of Section 8 estimates.  The pair
`(c, ρ) = (a, a)` is the reversible diffusion `X` and `(c, ρ) = (a, 1)` is the
divergence-form diffusion `Y` (matching the two
generators `a⁻¹ ∇·(a∇)` and `∇·(a∇)` printed ).

In the shift-normalised form used by the process library, `R_s = s⁻¹ R_{1/s}`
where `R_μ = (μ + H)⁻¹ = (μ - L)⁻¹` and `L = -H` is the generator.  This module
is the *interface* file for that object: it records the exact analytic facts a
PDE provider must supply about the map `f ↦ R_μ f` on `C₀(E, ℝ)`, and turns them
into `MarkovProcess.PositiveC0ContractiveResolvent`, from which
`SubdiffusiveProcess/CoarseGrainingVocab/Section8Resolvent/FellerBridge.lean` produces the
sub-Markov Feller kernel semigroup.

The five obligations are exactly the five clauses of `C0ResolventDatum`:

* linearity of `f ↦ R_μ f` (`solution_add`, `solution_smul`);
* the **maximum principle**, in the two halves `solution_nonneg` (positivity)
  and `norm_solution_le` (the contraction `μ ‖R_μ f‖_∞ ≤ ‖f‖_∞`);
* the **resolvent identity** `R_μ - R_ν = (ν - μ) R_μ R_ν`;
* **dense range**, for which `denseRange_of_tendsto_smul_solution` supplies the
  usual PDE route: strong convergence `μ R_μ f → f` on any dense set of `f`.

Nothing here is specific to the GMC coefficient; the ambient carrier is an
arbitrary topological space.  Everything is stated for `C₀` so that no `L²`
theory leaks into the process interface.

## Main declarations

* `C0ResolventDatum` — the PDE-facing obligations.
* `C0ResolventDatum.operator` — the bundled continuous linear resolvent.
* `C0ResolventDatum.range_operator_eq` — the range is independent of the shift.
* `C0ResolventDatum.denseRange_of_tendsto_smul_solution` — dense range from
  strong convergence of `μ R_μ` on a dense set.
* `C0ResolventDatum.toPositiveC0ContractiveResolvent` — the packaged object.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {E : Type*} [TopologicalSpace E]

/-- The analytic data a PDE provider must supply for the resolvent
`R_μ = (μ - L)⁻¹` of a Section 8 energy form, read on `C₀(E, ℝ)`.

The field names follow the printed structure of the argument: `solution μ f` is
the solution of the resolvent equation `(μ - L) u = f`, `solution_nonneg` and
`norm_solution_le` are the two halves of the maximum principle
and `solution_sub_solution` is the resolvent
identity in the sign convention of
`MarkovProcess.Semigroup.ContractiveResolvent.resolvent_identity`. -/
structure C0ResolventDatum (E : Type*) [TopologicalSpace E] where
  /-- The solution of `(μ - L) u = f`. -/
  solution : PositiveShift → C₀(E, ℝ) → C₀(E, ℝ)
  /-- The solution map is additive. -/
  solution_add : ∀ (μ : PositiveShift) (f g : C₀(E, ℝ)),
    solution μ (f + g) = solution μ f + solution μ g
  /-- The solution map is homogeneous. -/
  solution_smul : ∀ (μ : PositiveShift) (r : ℝ) (f : C₀(E, ℝ)),
    solution μ (r • f) = r • solution μ f
  /-- Positivity half of the maximum principle. -/
  solution_nonneg : ∀ (μ : PositiveShift) (f : C₀(E, ℝ)),
    (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ solution μ f x
  /-- Contraction half of the maximum principle: `μ ‖R_μ f‖_∞ ≤ ‖f‖_∞`. -/
  norm_solution_le : ∀ (μ : PositiveShift) (f : C₀(E, ℝ)),
    ‖solution μ f‖ ≤ ((μ : ℝ))⁻¹ * ‖f‖
  /-- The resolvent identity `R_μ - R_ν = (ν - μ) R_μ R_ν`. -/
  solution_sub_solution : ∀ (μ ν : PositiveShift) (f : C₀(E, ℝ)),
    solution μ f - solution ν f = ((ν : ℝ) - (μ : ℝ)) • solution μ (solution ν f)

namespace C0ResolventDatum

variable (D : C0ResolventDatum E)

/-- The resolvent as a linear map. -/
def linearMap (μ : PositiveShift) : C₀(E, ℝ) →ₗ[ℝ] C₀(E, ℝ) where
  toFun := D.solution μ
  map_add' := D.solution_add μ
  map_smul' r f := D.solution_smul μ r f

@[simp]
theorem linearMap_apply (μ : PositiveShift) (f : C₀(E, ℝ)) :
    D.linearMap μ f = D.solution μ f :=
  rfl

/-- The resolvent as a continuous linear map, with operator norm at most `μ⁻¹`. -/
def operator (μ : PositiveShift) : C₀(E, ℝ) →L[ℝ] C₀(E, ℝ) :=
  LinearMap.mkContinuous (D.linearMap μ) ((μ : ℝ))⁻¹ (D.norm_solution_le μ)

@[simp]
theorem operator_apply (μ : PositiveShift) (f : C₀(E, ℝ)) :
    D.operator μ f = D.solution μ f :=
  rfl

theorem opNorm_operator_le_inv (μ : PositiveShift) :
    ‖D.operator μ‖ ≤ ((μ : ℝ))⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 μ.property.le) _

/-- The resolvent identity in the bundled form required by
`MarkovProcess.Semigroup.ContractiveResolvent`. -/
theorem operator_sub_operator (μ ν : PositiveShift) :
    D.operator μ - D.operator ν =
      ((ν : ℝ) - (μ : ℝ)) • ((D.operator μ).comp (D.operator ν)) := by
  refine ContinuousLinearMap.ext fun f ↦ ?_
  simpa using D.solution_sub_solution μ ν f

/-- The resolvent at `ν` factors through the resolvent at `μ`. -/
theorem operator_eq_operator_comp (μ ν : PositiveShift) (f : C₀(E, ℝ)) :
    D.operator ν f =
      D.operator μ (f - ((ν : ℝ) - (μ : ℝ)) • D.operator ν f) := by
  have h := D.solution_sub_solution μ ν f
  rw [map_sub, map_smul]
  simp only [operator_apply]
  rw [← h]
  abel

/-- The range of the resolvent does not depend on the shift. -/
theorem range_operator_eq (μ ν : PositiveShift) :
    Set.range (D.operator μ) = Set.range (D.operator ν) := by
  have key : ∀ α β : PositiveShift,
      Set.range (D.operator β) ⊆ Set.range (D.operator α) := by
    intro α β g hg
    obtain ⟨f, rfl⟩ := hg
    exact ⟨f - ((β : ℝ) - (α : ℝ)) • D.operator β f,
      (D.operator_eq_operator_comp α β f).symm⟩
  exact Set.Subset.antisymm (key ν μ) (key μ ν)

/-- Dense range at one shift gives dense range at every shift. -/
theorem denseRange_operator_of_denseRange {ν : PositiveShift}
    (h : DenseRange (D.operator ν)) (μ : PositiveShift) :
    DenseRange (D.operator μ) := by
  rw [DenseRange, D.range_operator_eq μ ν]
  exact h

/-- **Dense range from strong convergence of the normalised resolvent.**
If `μ R_μ f → f` in `C₀` as `μ → ∞` for every `f` in a dense set, then every
resolvent has dense range.  This is the route a PDE provider takes: strong
continuity is proved on a convenient dense class (compactly supported smooth
functions), and dense range follows. -/
theorem denseRange_of_tendsto_smul_solution {S : Set C₀(E, ℝ)} (hS : Dense S)
    (h : ∀ f ∈ S, Tendsto (fun μ : PositiveShift ↦ (μ : ℝ) • D.solution μ f)
      atTop (nhds f)) (μ : PositiveShift) :
    DenseRange (D.operator μ) := by
  have hsub : S ⊆ closure (Set.range (D.operator μ)) := by
    intro f hf
    refine mem_closure_of_tendsto (h f hf) (Eventually.of_forall fun ν ↦ ?_)
    rw [D.range_operator_eq μ ν]
    exact ⟨(ν : ℝ) • f, by simp⟩
  have hcl : closure S ⊆ closure (Set.range (D.operator μ)) :=
    closure_minimal hsub isClosed_closure
  rw [DenseRange, dense_iff_closure_eq]
  exact Set.eq_univ_of_univ_subset (hS.closure_eq ▸ hcl)

/-- The contractive resolvent family carried by the datum. -/
def toContractiveResolvent (hdense : ∀ μ, DenseRange (D.operator μ)) :
    ContractiveResolvent C₀(E, ℝ) where
  operator := D.operator
  resolvent_identity := D.operator_sub_operator
  opNorm_le_inv := D.opNorm_operator_le_inv
  denseRange := hdense

@[simp]
theorem toContractiveResolvent_operator (hdense : ∀ μ, DenseRange (D.operator μ))
    (μ : PositiveShift) :
    (D.toContractiveResolvent hdense).operator μ = D.operator μ :=
  rfl

/-- **The packaged positive `C₀` contractive resolvent.**  This is the object
`MarkovProcess.Kernel.PositiveC0Resolvent` consumes: from it the library builds
the strongly continuous contraction semigroup on `C₀` and its sub-Markov Feller
kernel semigroup. -/
def toPositiveC0ContractiveResolvent (hdense : ∀ μ, DenseRange (D.operator μ)) :
    PositiveC0ContractiveResolvent E where
  toContractiveResolvent := D.toContractiveResolvent hdense
  isPositive μ f hf x := D.solution_nonneg μ f hf x

@[simp]
theorem toPositiveC0ContractiveResolvent_operator
    (hdense : ∀ μ, DenseRange (D.operator μ)) (μ : PositiveShift) :
    (D.toPositiveC0ContractiveResolvent hdense).toContractiveResolvent.operator μ =
      D.operator μ :=
  rfl



theorem tendsto_smul_solution (hdense : ∀ μ, DenseRange (D.operator μ))
    (f : C₀(E, ℝ)) :
    Tendsto (fun μ : PositiveShift ↦ (μ : ℝ) • D.solution μ f) atTop (nhds f) :=
  (D.toContractiveResolvent hdense).tendsto_scaledOperator_apply f

end C0ResolventDatum

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
