module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import SubdiffusiveProcess.Compactness.DenseResponseTests
public import SubdiffusiveProcess.Compactness.OperatorCauchy
public import Mathlib.Analysis.Normed.Operator.Compact
@[expose] public section

open MeasureTheory Filter Set
open scoped Topology
/-! Construction of a unique compact positive symmetric norm limit from dense
quadratic responses. Collective compactness and the model response bounds
remain separate analytic obligations. -/

namespace SubdiffusiveProcess


theorem existsUnique_limit_of_collectively_compact_quadratic_responses
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℕ → H →L[ℝ] H} {D : Set H}
    (hD : Dense D) (hadd : ∀ x ∈ D, ∀ y ∈ D, x + y ∈ D)
    (hsym : ∀ n : ℕ, ∀ x y : H, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hpos : ∀ n : ℕ, ∀ x : H, 0 ≤ inner ℝ x (T n x))
    (hc : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : H) 1)))
    (hq : ∀ x ∈ D, CauchySeq (fun n => inner ℝ x (T n x))) :
    ∃! G : H →L[ℝ] H,
      Tendsto T atTop (𝓝 G) ∧ IsCompactOperator G ∧
        (∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y)) ∧
        (∀ x : H, 0 ≤ inner ℝ x (G x)) := by
  obtain ⟨C, _hC0, hC⟩ := exists_operatorNorm_bound_of_collectively_compact hc
  have hweak : ∀ x y : H, CauchySeq (fun n => inner ℝ (T n x) y) :=
    cauchySeq_inner_of_dense_quadratic_responses hD hadd hsym ⟨C, hC⟩ hq
  have hTcauchy : CauchySeq T :=
    cauchySeq_operator_of_collectively_compact_inner_cauchy hsym hc hweak
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hTcauchy
  have hGx (x : H) : Tendsto (fun n => T n x) atTop (𝓝 (G x)) := by
    exact ((continuous_id.clm_apply continuous_const).tendsto G).comp hG
  have hTcompact (n : ℕ) : IsCompactOperator (T n) := by
    rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
    refine ⟨Metric.closedBall (0 : H) 1, Metric.closedBall_mem_nhds _ zero_lt_one,
      closure (⋃ k : ℕ, (T k) '' Metric.closedBall (0 : H) 1), hc, ?_⟩
    exact (Set.image_subset_iff.mpr fun x hx =>
      subset_closure (Set.mem_iUnion.mpr ⟨n, x, hx, rfl⟩))
  have hGcompact : IsCompactOperator G :=
    isCompactOperator_of_tendsto hG (Eventually.of_forall hTcompact)
  have hGsym : ∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    apply tendsto_nhds_unique ((hGx x).inner tendsto_const_nhds)
    simpa only [hsym] using tendsto_const_nhds.inner (hGx y)
  have hGpos : ∀ x : H, 0 ≤ inner ℝ x (G x) := by
    intro x
    have hinner : Tendsto (fun n => inner ℝ x (T n x)) atTop
        (𝓝 (inner ℝ x (G x))) := tendsto_const_nhds.inner (hGx x)
    exact isClosed_Ici.mem_of_tendsto hinner
      (Eventually.of_forall fun n => hpos n x)
  refine ⟨G, ⟨hG, hGcompact, hGsym, hGpos⟩, ?_⟩
  intro G' hG'
  exact tendsto_nhds_unique hG'.1 hG


/-- Countably many response events give one pathwise full-sequence norm-limit event. -/
theorem ae_existsUnique_limit_of_countable_quadratic_responses
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure Ω) (T : Ω → ℕ → H →L[ℝ] H) (D : Set H)
    (hcount : D.Countable) (hdense : Dense D)
    (hadd : ∀ x ∈ D, ∀ y ∈ D, x + y ∈ D)
    (hsym : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ x y : H,
      inner ℝ (T ω n x) y = inner ℝ x (T ω n y))
    (hpos : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ x : H, 0 ≤ inner ℝ x (T ω n x))
    (hc : ∀ᵐ ω ∂P,
      IsCompact (closure (⋃ n : ℕ, (T ω n) '' Metric.closedBall (0 : H) 1)))
    (hq : ∀ x ∈ D, ∀ᵐ ω ∂P, CauchySeq (fun n => inner ℝ x (T ω n x))) :
    ∀ᵐ ω ∂P, ∃! G : H →L[ℝ] H,
      Tendsto (T ω) atTop (𝓝 G) ∧ IsCompactOperator G ∧
        (∀ x y : H, inner ℝ (G x) y = inner ℝ x (G y)) ∧
        (∀ x : H, 0 ≤ inner ℝ x (G x)) := by
  have hq' : ∀ᵐ ω ∂P, ∀ x ∈ D,
      CauchySeq (fun n => inner ℝ x (T ω n x)) :=
    (ae_ball_iff hcount).2 hq
  filter_upwards [hsym, hpos, hc, hq'] with ω hsymω hposω hcω hqω
  exact existsUnique_limit_of_collectively_compact_quadratic_responses
    hdense hadd hsymω hposω hcω hqω

end SubdiffusiveProcess
