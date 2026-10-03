module

public import Homogenization.Sobolev.L2Ambient
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter Topology
open scoped RealInnerProductSpace

noncomputable section

/-- Every norm-bounded sequence in a separable real Hilbert space has a
subsequence converging against every fixed vector. -/
theorem exists_subseq_tendsto_inner_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (x : ℕ → H) (C : ℝ) (hx : ∀ n, ‖x n‖ ≤ C) :
    ∃ y : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ z : H, Tendsto (fun n ↦ inner ℝ (x (φ n)) z) atTop (𝓝 (inner ℝ y z)) := by
  let q : ℕ → WeakDual ℝ H := fun n ↦
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (x n))
  have hq : ∀ n, q n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    change dist (InnerProductSpace.toDual ℝ H (x n)) 0 ≤ C
    simpa [dist_zero] using hx n
  obtain ⟨qLimit, _, φ, hφ, hqTendsto⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H 0 C) hq
  let y : H := (InnerProductSpace.toDual ℝ H).symm
    (WeakDual.toStrongDual qLimit)
  refine ⟨y, φ, hφ, fun z ↦ ?_⟩
  have heval := (WeakDual.eval_continuous (𝕜 := ℝ) (E := H) z).tendsto qLimit
  have ht := heval.comp hqTendsto
  simpa only [Function.comp_def, q, y, InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_symm_apply, StrongDual.toWeakDual_apply,
    WeakDual.toStrongDual_apply] using ht

/-- The specialization used for gradient fields on a fixed window. -/
theorem exists_subseq_tendsto_inner_hilbertVectorL2_of_norm_le
    {d : ℕ} (W : Set (Homogenization.Vec d))
    (x : ℕ → Homogenization.HilbertVectorL2 W) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) :
    ∃ y : Homogenization.HilbertVectorL2 W, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ z : Homogenization.HilbertVectorL2 W,
        Tendsto (fun n ↦ inner ℝ (x (φ n)) z) atTop (𝓝 (inner ℝ y z)) :=
  by
    letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    exact exists_subseq_tendsto_inner_of_norm_le x C hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
