import Mathlib.Tactic
import SubdiffusiveProcess.Compactness.OperatorLimits

/-! Deterministic lib data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace SubdiffusiveProcess.OperatorCompactness
noncomputable section

/-- Extracted property of limit argument from the pre-convergence deterministic proof. -/
theorem property_of_unique_limit {V : Type*} [TopologicalSpace V] [T2Space V]
    (GN : ℕ → V) (G : V) (hconv : Tendsto GN atTop (𝓝 G))
    (property : V → Prop) (hconv_of : ∀ x, property x → Tendsto GN atTop (𝓝 x))
    (hex : ∃! x, property x) : property G := by
  obtain ⟨x, hx, _⟩ := hex
  have hxG : x = G := tendsto_nhds_unique (hconv_of x hx) hconv
  exact hxG ▸ hx

/-- Extracted response cauchy argument from the pre-convergence deterministic proof. -/
theorem quadratic_response_cauchy_of_tendsto {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (GN : ℕ → V →L[ℝ] V) (G : V →L[ℝ] V)
    (hconv : Tendsto GN atTop (𝓝 G)) (f : V) :
    CauchySeq (fun n => inner ℝ f (GN n f)) := by
  have heval := ((ContinuousLinearMap.apply ℝ V f).continuous.tendsto G).comp hconv
  exact (tendsto_const_nhds.inner heval).cauchySeq

/-- Extracted operator cluster argument from the pre-convergence deterministic proof. -/
theorem exists_norm_cluster_of_collectively_compact
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [Module ℚ V]
    (T : ℕ → V →L[ℝ] V) (D : Submodule ℚ V)
    (hDcount : (D : Set V).Countable) (hDense : Dense (D : Set V))
    (hSym : ∀ n x y, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hPos : ∀ n x, 0 ≤ inner ℝ x (T n x))
    (hCompact : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : V) 1))) :
    ∃ (sigma : ℕ → ℕ) (G : V →L[ℝ] V), StrictMono sigma ∧
      Tendsto (fun n => T (sigma n)) atTop (𝓝 G) ∧ IsCompactOperator G ∧
      (∀ x y, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x, 0 ≤ inner ℝ x (G x)) := by
  classical
  letI instExtract1 : Countable D := Set.countable_coe_iff.mpr hDcount
  obtain ⟨C, hC, hBound⟩ := exists_operatorNorm_bound_of_collectively_compact hCompact
  let q : ℕ → D → ℝ := fun n f => inner ℝ f.val (T n f.val)
  have hqbound (n : ℕ) (f : D) : q n f ∈ Icc (0 : ℝ) (C * ‖f.val‖ ^ 2) := by
    refine ⟨hPos n f.val, ?_⟩
    calc
      q n f ≤ |inner ℝ f.val (T n f.val)| := le_abs_self _
      _ ≤ ‖f.val‖ * ‖T n f.val‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f.val‖ * (C * ‖f.val‖) :=
        mul_le_mul_of_nonneg_left
          ((T n).le_opNorm f.val |>.trans
            (mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _))) (norm_nonneg _)
      _ = C * ‖f.val‖ ^ 2 := by ring
  have hProd : IsCompact {p : D → ℝ | ∀ f, p f ∈ Icc (0 : ℝ) (C * ‖f.val‖ ^ 2)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨qlim, _hqlim, sigma, hsigma, hq⟩ := hProd.tendsto_subseq hqbound
  have hqCauchy : ∀ f ∈ (D : Set V),
      CauchySeq (fun n => inner ℝ f (T (sigma n) f)) := by
    intro f hf
    exact (((continuous_apply (⟨f, hf⟩ : D)).tendsto qlim).comp hq).cauchySeq
  have hsub : closure (⋃ n : ℕ, (T (sigma n)) '' Metric.closedBall (0 : V) 1) ⊆
      closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : V) 1) := by
    apply closure_mono
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨sigma n, hn⟩
  obtain ⟨G, hG, _hUnique⟩ := existsUnique_limit_of_collectively_compact_quadratic_responses
    hDense (fun x hx y hy => D.add_mem hx hy)
    (fun n => hSym (sigma n)) (fun n => hPos (sigma n))
    (hCompact.of_isClosed_subset isClosed_closure hsub) hqCauchy
  exact ⟨sigma, G, hsigma, hG⟩

end
end SubdiffusiveProcess.OperatorCompactness
