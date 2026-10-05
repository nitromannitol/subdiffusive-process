module

public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Probability.IntegratedResponseCompactness

@[expose] public section

/-! # Conditional expectations of the canonical Sobolev responses

A retained continuous compact-root potential and an independent discarded
potential determine an actual exponential coefficient. The kernels below are
literal canonical variational responses, not arbitrary response coordinates.
Their joint measurability and comparison are proved here. Model layer maps
and the original higher-moment bounds remain separate inputs.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal MeasureTheory
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The actual inverse response to the sum of retained and discarded compact potentials. -/
def compactSourceResponseKernel (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (L : S.space →L[ℝ] ℝ) {Y : Type*} (T : Y → C(K, ℝ)) (p : C(K, ℝ) × Y) : ℝ :=
  inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (p.1 + T p.2))) L

/-- The actual boundary minimum for the same retained/discarded decomposition. -/
def compactBoundaryResponseKernel (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (b : weakSobolevGraph Ω) {Y : Type*} (T : Y → C(K, ℝ)) (p : C(K, ℝ) × Y) : ℝ :=
  dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (p.1 + T p.2))) b

variable (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)]
    {Y : Type*} [MeasurableSpace Y]

/-- Joint measurability is derived from the actual continuous response and discarded-potential map. -/
theorem measurable_compactSourceResponseKernel (L : S.space →L[ℝ] ℝ)
    {T : Y → C(K, ℝ)} (hT : Measurable T) : Measurable (compactSourceResponseKernel S K L T) :=
  (continuous_inverseResponse_compact S K L).measurable.comp
    (measurable_fst.add (hT.comp measurable_snd))

/-- Boundary kernels are likewise genuinely jointly measurable. -/
theorem measurable_compactBoundaryResponseKernel (b : weakSobolevGraph Ω)
    {T : Y → C(K, ℝ)} (hT : Measurable T) : Measurable (compactBoundaryResponseKernel S K b T) :=
  (continuous_dirichletResponse_compact S K b).measurable.comp
    (measurable_fst.add (hT.comp measurable_snd))

variable {μ : Measure C(K, ℝ)} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Actual inverse conditional responses have a continuous integral version, with no fiber premise. -/
theorem source_conditional_response_continuous_version (L : S.space →L[ℝ] ℝ)
    {T : Y → C(K, ℝ)} (hT : Measurable T)
    (hf : Integrable (compactSourceResponseKernel S K L T) (μ.prod ν)) :
    Continuous (fun v => ∫ y, compactSourceResponseKernel S K L T (v, y) ∂ν) ∧
      (μ.prod ν)[compactSourceResponseKernel S K L T |
        (inferInstance : MeasurableSpace C(K, ℝ)).comap Prod.fst] =ᵐ[μ.prod ν]
        fun p => ∫ y, compactSourceResponseKernel S K L T (p.1, y) ∂ν := by
  apply continuous_condExp_response_version
    (measurable_compactSourceResponseKernel S K L hT) hf
    (fun v y => inverseResponse_nonneg S _ L) (C := 1) (by norm_num)
  intro v w y
  simpa only [compactSourceResponseKernel, one_mul] using inverseResponse_compact_add_comparison S K L v w (T y)

/-- Actual boundary conditional responses have the same continuous-version property. -/
theorem boundary_conditional_response_continuous_version (b : weakSobolevGraph Ω)
    {T : Y → C(K, ℝ)} (hT : Measurable T)
    (hf : Integrable (compactBoundaryResponseKernel S K b T) (μ.prod ν)) :
    Continuous (fun v => ∫ y, compactBoundaryResponseKernel S K b T (v, y) ∂ν) ∧
      (μ.prod ν)[compactBoundaryResponseKernel S K b T |
        (inferInstance : MeasurableSpace C(K, ℝ)).comap Prod.fst] =ᵐ[μ.prod ν]
        fun p => ∫ y, compactBoundaryResponseKernel S K b T (p.1, y) ∂ν := by
  apply continuous_condExp_response_version
    (measurable_compactBoundaryResponseKernel S K b hT) hf
    (fun v y => dirichletResponse_nonneg S _ b) (C := 1) (by norm_num)
  intro v w y
  simpa only [compactBoundaryResponseKernel, one_mul] using dirichletResponse_compact_add_comparison S K b v w (T y)

/-- Strong compactness of actual inverse conditional responses, from original higher moments. -/
theorem source_conditional_responses_isCompact_closure (L : S.space →L[ℝ] ℝ)
    {ι : Type*} {T : ι → Y → C(K, ℝ)} (hT : ∀ i, Measurable (T i))
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ i, MemLp (compactSourceResponseKernel S K L (T i)) q (μ.prod ν))
    (hb : ∀ i, eLpNorm (compactSourceResponseKernel S K L (T i)) q (μ.prod ν) ≤ B) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)).toLp
        ((μ.prod ν)[compactSourceResponseKernel S K L (T i) |
          (inferInstance : MeasurableSpace C(K, ℝ)).comap Prod.fst])))) := by
  apply conditional_responses_isCompact_closure
    (fun i => measurable_compactSourceResponseKernel S K L (hT i))
    (fun i v y => inverseResponse_nonneg S _ L) (C := 1) (by norm_num)
    (fun i v w y => ?_) hpq hqt hB hf hb
  simpa only [compactSourceResponseKernel, one_mul] using inverseResponse_compact_add_comparison S K L v w (T i y)

/-- Strong compactness of actual boundary conditional responses with the same finite moment budget. -/
theorem boundary_conditional_responses_isCompact_closure (b : weakSobolevGraph Ω)
    {ι : Type*} {T : ι → Y → C(K, ℝ)} (hT : ∀ i, Measurable (T i))
    {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ i, MemLp (compactBoundaryResponseKernel S K b (T i)) q (μ.prod ν))
    (hb : ∀ i, eLpNorm (compactBoundaryResponseKernel S K b (T i)) q (μ.prod ν) ≤ B) :
    IsCompact (closure (range (fun i =>
      (memLp_condExp_prod_fst hp.out (ne_top_of_lt hpq) ((hf i).mono_exponent hpq.le)).toLp
        ((μ.prod ν)[compactBoundaryResponseKernel S K b (T i) |
          (inferInstance : MeasurableSpace C(K, ℝ)).comap Prod.fst])))) := by
  apply conditional_responses_isCompact_closure
    (fun i => measurable_compactBoundaryResponseKernel S K b (hT i))
    (fun i v y => dirichletResponse_nonneg S _ b) (C := 1) (by norm_num)
    (fun i v w y => ?_) hpq hqt hB hf hb
  simpa only [compactBoundaryResponseKernel, one_mul] using dirichletResponse_compact_add_comparison S K b v w (T i y)

end SubdiffusiveProcess
