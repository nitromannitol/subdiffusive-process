module

public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Operator.NNNorm

@[expose] public section

/-! # Convergence of precompact symmetric operator families

These are functional-analysis implications used in the local-inverse argument.
The required PDE compactness and convergence of response matrix elements remain
separate hypotheses to be established for the actual coefficient sequence.
-/

open Filter Set
open scoped Topology
namespace SubdiffusiveProcess

/-- On a precompact sequence, convergence of all inner-product tests implies
strong convergence along the full sequence. -/
theorem tendsto_of_inner_tendsto_of_isCompact_closure_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : ℕ → H} {v : H}
    (hc : IsCompact (closure (Set.range u)))
    (hi : ∀ w : H, Tendsto (fun n => inner ℝ (u n) w) atTop
      (𝓝 (inner ℝ v w))) :
    Tendsto u atTop (𝓝 v) := by
  by_contra hconv
  obtain ⟨s, hsv, hfrequent⟩ :=
    not_tendsto_iff_exists_frequently_notMem.mp hconv
  obtain ⟨φ, hφ, hφout⟩ := extraction_of_frequently_atTop hfrequent
  have hφmem : ∀ n, u (φ n) ∈ closure (Set.range u) := fun n =>
    subset_closure ⟨φ n, rfl⟩
  obtain ⟨a, _ha, ψ, hψ, ha_lim⟩ := hc.tendsto_subseq hφmem
  have huv : a = v := by
    have hinner (w : H) : inner ℝ a w = inner ℝ v w := by
      have ha_inner :
          Tendsto (fun n => inner ℝ (u (φ (ψ n))) w) atTop
            (𝓝 (inner ℝ a w)) :=
        ha_lim.inner tendsto_const_nhds
      have hv_inner :
          Tendsto (fun n => inner ℝ (u (φ (ψ n))) w) atTop
            (𝓝 (inner ℝ v w)) := by
        simpa only [Function.comp_def] using
          (hi w).comp (hφ.comp hψ).tendsto_atTop
      exact tendsto_nhds_unique ha_inner hv_inner
    have hz : inner ℝ (a - v) (a - v) = 0 := by
      rw [inner_sub_left, hinner (a - v), sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  have hin : ∀ᶠ n in atTop, u (φ (ψ n)) ∈ s := by
    rw [huv] at ha_lim
    exact ha_lim hsv
  have hout : ∀ n, u (φ (ψ n)) ∉ s := fun n => hφout (ψ n)
  exact (hin.and (Eventually.of_forall hout)).exists.elim fun _ h => h.2 h.1

/-- A collectively compact sequence of symmetric operators converges in operator
norm whenever it converges strongly. Symmetry and compactness of the limit
are derived from the approximating operators. -/
theorem tendsto_operatorNorm_of_collectively_compact_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {Tlim : H →L[ℝ] H}
    (hsym : ∀ n : ℕ, ∀ x y : H, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hc : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : H) 1)))
    (hstrong : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 (Tlim x))) :
    Tendsto T atTop (𝓝 Tlim) := by
  have hlimsym : ∀ x y : H, inner ℝ (Tlim x) y = inner ℝ x (Tlim y) := by
    intro x y
    apply tendsto_nhds_unique ((hstrong x).inner tendsto_const_nhds)
    simpa only [hsym] using tendsto_const_nhds.inner (hstrong y)
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (T n) Tlim := by
    rw [frequently_atTop]
    intro N
    push Not at hbad
    obtain ⟨n, hn, hdist⟩ := hbad N
    exact ⟨n, hn, hdist⟩
  obtain ⟨ψ, hψ, hbadψ⟩ := extraction_of_frequently_atTop hfreq
  have hopen (n : ℕ) : ε / 2 < ‖T (ψ n) - Tlim‖ := by
    have hdist : ε ≤ ‖T (ψ n) - Tlim‖ := by
      simpa only [dist_eq_norm] using hbadψ n
    linarith
  choose x hx hdx using fun n =>
    ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (T (ψ n) - Tlim) (hopen n)
  let K : Set H := closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : H) 1)
  have hTx (n : ℕ) : T (ψ n) (x n) ∈ K := by
    apply subset_closure
    rw [mem_iUnion]
    refine ⟨ψ n, ?_⟩
    refine ⟨x n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hx n).le
  have hTlimx (n : ℕ) : Tlim (x n) ∈ K := by
    apply mem_closure_of_tendsto (hstrong (x n))
    filter_upwards [] with m
    rw [mem_iUnion]
    refine ⟨m, x n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hx n).le
  obtain ⟨a, haK, φ, hφ, ha⟩ := hc.tendsto_subseq hTx
  obtain ⟨b, hbK, θ, hθ, hb⟩ := hc.tendsto_subseq (fun n => hTlimx (φ n))
  let κ : ℕ → ℕ := φ ∘ θ
  have hκ : StrictMono κ := hφ.comp hθ
  have ha' : Tendsto (fun n => T (ψ (κ n)) (x (κ n))) atTop (𝓝 a) := by
    exact ha.comp hθ.tendsto_atTop
  have hb' : Tendsto (fun n => Tlim (x (κ n))) atTop (𝓝 b) := by
    simpa only [κ, Function.comp_def] using hb
  have hdifference : Tendsto
      (fun n => (T (ψ (κ n)) - Tlim) (x (κ n))) atTop (𝓝 (a - b)) := by
    simpa only [sub_apply] using ha'.sub hb'
  have hab : a - b = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    apply tendsto_nhds_unique (hdifference.inner tendsto_const_nhds)
    have hdv : Tendsto (fun n => (T (ψ (κ n)) - Tlim) (a - b)) atTop (𝓝 0) := by
      have ht := (hstrong (a - b)).comp (hψ.comp hκ).tendsto_atTop
      simpa only [Function.comp_def, sub_apply,
        tendsto_sub_nhds_zero_iff] using ht
    have hinner_zero : Tendsto
        (fun n => inner ℝ (x (κ n)) ((T (ψ (κ n)) - Tlim) (a - b)))
        atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      apply squeeze_zero'
      · exact Eventually.of_forall fun n => norm_nonneg _
      · exact Eventually.of_forall fun n => by
          calc
            ‖inner ℝ (x (κ n)) ((T (ψ (κ n)) - Tlim) (a - b))‖
                ≤ ‖x (κ n)‖ * ‖(T (ψ (κ n)) - Tlim) (a - b)‖ := norm_inner_le_norm _ _
            _ ≤ 1 * ‖(T (ψ (κ n)) - Tlim) (a - b)‖ :=
              mul_le_mul_of_nonneg_right (hx (κ n)).le (norm_nonneg _)
            _ = _ := one_mul _
      · simpa only [norm_zero] using hdv.norm
    convert hinner_zero using 1
    funext n
    rw [sub_apply, inner_sub_left, hsym, hlimsym]
    exact (inner_sub_right _ _ _).symm
  have hnormzero : Tendsto
      (fun n => ‖(T (ψ (κ n)) - Tlim) (x (κ n))‖) atTop (𝓝 0) := by
    rw [hab] at hdifference
    simpa only [norm_zero] using hdifference.norm
  have hlower : ∀ n, ε / 2 < ‖(T (ψ (κ n)) - Tlim) (x (κ n))‖ :=
    fun n => hdx (κ n)
  have hevent : ∀ᶠ n in atTop,
      ‖(T (ψ (κ n)) - Tlim) (x (κ n))‖ < ε / 2 := by
    exact (Metric.tendsto_nhds.1 hnormzero (ε / 2) (by linarith)).mono fun n hn => by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hn
  obtain ⟨n, hn, hn'⟩ := (hevent.and (Eventually.of_forall hlower)).exists
  exact (not_lt_of_ge hn'.le) hn

/-- Convergence of all matrix elements of a collectively compact symmetric
operator sequence implies convergence in operator norm. -/
theorem tendsto_operatorNorm_of_collectively_compact_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {Tlim : H →L[ℝ] H}
    (hsym : ∀ n : ℕ, ∀ x y : H, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hc : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : H) 1)))
    (hweak : ∀ x y : H, Tendsto (fun n => inner ℝ (T n x) y) atTop
      (𝓝 (inner ℝ (Tlim x) y))) :
    Tendsto T atTop (𝓝 Tlim) := by
  apply tendsto_operatorNorm_of_collectively_compact_symmetric hsym hc
  intro x
  apply tendsto_of_inner_tendsto_of_isCompact_closure_range _ (hweak x)
  let c : ℝ := max 1 ‖x‖
  let K : Set H := closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : H) 1)
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)
  have hyball : c⁻¹ • x ∈ Metric.closedBall (0 : H) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hcpos)]
    calc
      c⁻¹ * ‖x‖ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (le_max_right 1 ‖x‖) (inv_nonneg.mpr hcpos.le)
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  have hrange : Set.range (fun n => T n x) ⊆ (fun z : H => c • z) '' K := by
    rintro _ ⟨n, rfl⟩
    refine ⟨T n (c⁻¹ • x), ?_, ?_⟩
    · apply subset_closure
      rw [mem_iUnion]
      exact ⟨n, c⁻¹ • x, hyball, rfl⟩
    · change c • T n (c⁻¹ • x) = T n x
      rw [map_smul, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  have himage : IsCompact ((fun z : H => c • z) '' K) :=
    hc.image (continuous_const_smul c)
  exact IsCompact.of_isClosed_subset himage isClosed_closure
    (closure_minimal hrange himage.isClosed)

/-- The common compact image supplies the operator bound used for dense response tests. -/
theorem exists_operatorNorm_bound_of_collectively_compact
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ι → H →L[ℝ] H}
    (hc : IsCompact (closure (⋃ i : ι, (T i) '' Metric.closedBall (0 : H) 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ι, ‖T i‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.exists_pos_norm_le
  refine ⟨C, hC.le, fun i => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC.le
  intro x hx
  apply hbound (T i x)
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨i, x, by simpa only [Metric.mem_closedBall,
    dist_zero_right, hx] using (le_refl (1 : ℝ)), rfl⟩

end SubdiffusiveProcess
