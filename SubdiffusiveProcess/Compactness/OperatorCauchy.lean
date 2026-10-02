import SubdiffusiveProcess.Compactness.OperatorConvergence
open Filter Set
open scoped Topology
/-! Collectively compact symmetric operators are Cauchy in norm when their matrix
elements are Cauchy. No limiting operator is assumed. -/

namespace SubdiffusiveProcess

theorem cauchySeq_operator_of_collectively_compact_inner_cauchy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H}
    (hsym : ∀ n : ℕ, ∀ x y : H, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hc : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : H) 1)))
    (hweak : ∀ x y : H, CauchySeq (fun n => inner ℝ (T n x) y)) :
    CauchySeq T := by
  have hscalar_gap (z w : H) {p q : ℕ → ℕ}
      (hp : Tendsto p atTop atTop) (hq : Tendsto q atTop atTop) :
      Tendsto (fun k => inner ℝ (T (p k) z) w - inner ℝ (T (q k) z) w)
        atTop (𝓝 0) := by
    have hpq : Tendsto (fun k => (p k, q k)) atTop (atTop : Filter (ℕ × ℕ)) := by
      rw [← prod_atTop_atTop_eq]
      exact hp.prodMk hq
    have hd := (cauchySeq_iff_tendsto_dist_atTop_0.mp (hweak z w)).comp
      hpq
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs, Real.dist_eq] using hd
  have horbit (z : H) : CauchySeq (fun k => T k z) := by
    have hzcompact : IsCompact (closure (Set.range (fun k => T k z))) := by
      let c : ℝ := max 1 ‖z‖
      let K : Set H := closure (⋃ k : ℕ, (T k) '' Metric.closedBall (0 : H) 1)
      have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖)
      have hzball : c⁻¹ • z ∈ Metric.closedBall (0 : H) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hcpos)]
        calc
          c⁻¹ * ‖z‖ ≤ c⁻¹ * c :=
            mul_le_mul_of_nonneg_left (le_max_right 1 ‖z‖) (inv_nonneg.mpr hcpos.le)
          _ = 1 := inv_mul_cancel₀ hcpos.ne'
      have hrange : Set.range (fun k => T k z) ⊆ (fun v : H => c • v) '' K := by
        rintro _ ⟨k, rfl⟩
        refine ⟨T k (c⁻¹ • z), ?_, ?_⟩
        · apply subset_closure
          rw [mem_iUnion]
          exact ⟨k, c⁻¹ • z, hzball, rfl⟩
        · change c • T k (c⁻¹ • z) = T k z
          rw [map_smul, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
      have himage : IsCompact ((fun v : H => c • v) '' K) :=
        hc.image (continuous_const_smul c)
      exact IsCompact.of_isClosed_subset himage isClosed_closure
        (closure_minimal hrange himage.isClosed)
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    by_contra hbadz
    push_neg at hbadz
    choose p hp q hq hpq using fun N => hbadz N
    have hp_top : Tendsto p atTop atTop := tendsto_atTop_mono' atTop
      (Eventually.of_forall hp) tendsto_id
    have hq_top : Tendsto q atTop atTop := tendsto_atTop_mono' atTop
      (Eventually.of_forall hq) tendsto_id
    have hp_mem (k : ℕ) : T (p k) z ∈ closure (Set.range (fun j => T j z)) :=
      subset_closure ⟨p k, rfl⟩
    have hq_mem (k : ℕ) : T (q k) z ∈ closure (Set.range (fun j => T j z)) :=
      subset_closure ⟨q k, rfl⟩
    obtain ⟨a, _ha, φ, hφ, ha⟩ := hzcompact.tendsto_subseq hp_mem
    obtain ⟨b, _hb, θ, hθ, hb⟩ := hzcompact.tendsto_subseq (fun k => hq_mem (φ k))
    let κ : ℕ → ℕ := φ ∘ θ
    have ha' : Tendsto (fun k => T (p (κ k)) z) atTop (𝓝 a) :=
      ha.comp hθ.tendsto_atTop
    have hb' : Tendsto (fun k => T (q (κ k)) z) atTop (𝓝 b) := by
      simpa only [κ, Function.comp_apply] using hb
    have hab : a = b := by
      have hi (w : H) : inner ℝ a w = inner ℝ b w := by
        apply sub_eq_zero.mp
        apply tendsto_nhds_unique ((ha'.inner tendsto_const_nhds).sub
          (hb'.inner tendsto_const_nhds))
        exact hscalar_gap z w (hp_top.comp (hφ.comp hθ).tendsto_atTop)
          (hq_top.comp (hφ.comp hθ).tendsto_atTop)
      have hz : inner ℝ (a - b) (a - b) = 0 := by
        rw [inner_sub_left, hi (a - b), sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
    have hdistzero : Tendsto (fun k => dist (T (p (κ k)) z) (T (q (κ k)) z))
        atTop (𝓝 0) := by
      simpa only [hab, dist_self] using ha'.dist hb'
    have hevent : ∀ᶠ k in atTop, dist (T (p (κ k)) z) (T (q (κ k)) z) < δ :=
      (Metric.tendsto_nhds.1 hdistzero δ hδ).mono fun k hk => by
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hk
    obtain ⟨k, hk, hk'⟩ :=
      (hevent.and (Eventually.of_forall fun k => hpq (κ k))).exists
    exact (not_lt_of_ge hk') hk
  rw [Metric.cauchySeq_iff]
  intro ε hε
  by_contra hbad
  push_neg at hbad
  choose m hm n hn hmn using fun N => hbad N
  have hopen (N : ℕ) : ε / 2 < ‖T (m N) - T (n N)‖ := by
    have hd : ε ≤ ‖T (m N) - T (n N)‖ := by
      simpa only [dist_eq_norm] using hmn N
    linarith
  choose x hx hdx using fun N =>
    ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (T (m N) - T (n N)) (hopen N)
  let K : Set H := closure (⋃ k : ℕ, (T k) '' Metric.closedBall (0 : H) 1)
  have hTmx (N : ℕ) : T (m N) (x N) ∈ K := by
    apply subset_closure
    rw [mem_iUnion]
    refine ⟨m N, x N, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hx N).le
  have hTnx (N : ℕ) : T (n N) (x N) ∈ K := by
    apply subset_closure
    rw [mem_iUnion]
    refine ⟨n N, x N, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hx N).le
  obtain ⟨a, _haK, φ, hφ, ha⟩ := hc.tendsto_subseq hTmx
  obtain ⟨b, _hbK, θ, hθ, hb⟩ := hc.tendsto_subseq (fun k => hTnx (φ k))
  let κ : ℕ → ℕ := φ ∘ θ
  have hκ : StrictMono κ := hφ.comp hθ
  have ha' : Tendsto (fun k => T (m (κ k)) (x (κ k))) atTop (𝓝 a) := by
    exact ha.comp hθ.tendsto_atTop
  have hb' : Tendsto (fun k => T (n (κ k)) (x (κ k))) atTop (𝓝 b) := by
    simpa only [κ, Function.comp_apply] using hb
  have hdifference : Tendsto
      (fun k => (T (m (κ k)) - T (n (κ k))) (x (κ k))) atTop (𝓝 (a - b)) := by
    simpa only [ContinuousLinearMap.sub_apply] using ha'.sub hb'
  have hm_top : Tendsto (fun k => m (κ k)) atTop atTop := by
    exact tendsto_atTop_mono' atTop (Eventually.of_forall fun k => hm (κ k))
      hκ.tendsto_atTop
  have hn_top : Tendsto (fun k => n (κ k)) atTop atTop := by
    exact tendsto_atTop_mono' atTop (Eventually.of_forall fun k => hn (κ k))
      hκ.tendsto_atTop
  have hab : a - b = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    apply tendsto_nhds_unique (hdifference.inner tendsto_const_nhds)
    have hdv : Tendsto
        (fun k => (T (m (κ k)) - T (n (κ k))) (a - b)) atTop (𝓝 0) := by
      have hmn_top : Tendsto (fun k => (m (κ k), n (κ k))) atTop
          (atTop : Filter (ℕ × ℕ)) := by
        rw [← prod_atTop_atTop_eq]
        exact hm_top.prodMk hn_top
      have hd := (cauchySeq_iff_tendsto_dist_atTop_0.mp (horbit (a - b))).comp
        hmn_top
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [sub_zero, ContinuousLinearMap.sub_apply, dist_eq_norm] using hd
    have hinner_zero : Tendsto
        (fun k => inner ℝ (x (κ k))
          ((T (m (κ k)) - T (n (κ k))) (a - b))) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      apply squeeze_zero'
      · exact Eventually.of_forall fun k => norm_nonneg _
      · exact Eventually.of_forall fun k => by
          calc
            ‖inner ℝ (x (κ k)) ((T (m (κ k)) - T (n (κ k))) (a - b))‖
                ≤ ‖x (κ k)‖ * ‖(T (m (κ k)) - T (n (κ k))) (a - b)‖ :=
              norm_inner_le_norm _ _
            _ ≤ 1 * ‖(T (m (κ k)) - T (n (κ k))) (a - b)‖ :=
              mul_le_mul_of_nonneg_right (hx (κ k)).le (norm_nonneg _)
            _ = _ := one_mul _
      · simpa only [norm_zero] using hdv.norm
    convert hinner_zero using 1
    funext k
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, hsym, hsym]
    exact (inner_sub_right _ _ _).symm
  have hnormzero : Tendsto
      (fun k => ‖(T (m (κ k)) - T (n (κ k))) (x (κ k))‖) atTop (𝓝 0) := by
    rw [hab] at hdifference
    simpa only [norm_zero] using hdifference.norm
  have hlower : ∀ k, ε / 2 < ‖(T (m (κ k)) - T (n (κ k))) (x (κ k))‖ :=
    fun k => hdx (κ k)
  have hevent : ∀ᶠ k in atTop,
      ‖(T (m (κ k)) - T (n (κ k))) (x (κ k))‖ < ε / 2 := by
    exact (Metric.tendsto_nhds.1 hnormzero (ε / 2) (by linarith)).mono fun k hk => by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hk
  obtain ⟨k, hk, hk'⟩ := (hevent.and (Eventually.of_forall hlower)).exists
  exact (not_lt_of_ge hk'.le) hk

end SubdiffusiveProcess
