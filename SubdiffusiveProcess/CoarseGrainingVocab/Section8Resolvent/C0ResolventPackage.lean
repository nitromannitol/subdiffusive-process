import MarkovProcess.Feller.Resolvent




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter Topology
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {E : Type*} [TopologicalSpace E]



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
