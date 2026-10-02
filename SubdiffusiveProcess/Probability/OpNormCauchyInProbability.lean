import Mathlib

/-!
# Operator-norm Cauchy property in probability

Two probabilistic lemmas used in the norm-convergence step of `mfd:prop-killed-inverse`
(paper `mfd:prop-killed-inverse`, Step 1), in their in-probability form.

* `exists_limit_of_cauchy_in_probability`: a sequence of random elements of a complete
  pseudo-metric space that is Cauchy in probability has a measurable limit; it converges almost
  surely along a subsequence and in probability along the whole sequence.  All probabilities are
  outer-measure values, so no measurability of the distance events is required.
* `opNorm_cauchy_in_probability_of_uniformly_compact`: uniformly compact self-adjoint random
  operators whose quadratic forms are Cauchy in probability on a countable dense additive set
  `D` are Cauchy in probability in operator norm.  The proof combines a finite net of the
  compact set, the orthogonal projection onto its (finite-dimensional) span, a finite net of the
  unit ball of that span with centres in `D`, polarisation, and a union bound over the finitely
  many quadratic forms involved.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace SubdiffusiveProcess.Probability

section Completeness

/-- A strictly monotone subsequence along which the Cauchy-in-probability events have
summable probabilities. -/
lemma aux_exists_subseq_summable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Type*} [PseudoMetricSpace F]
    (X : ℕ → Ω → F)
    (hcauchy : ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal rho) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, P {ω | (1 / 2 : ℝ) ^ k ≤ dist (X (φ k) ω) (X (φ (k + 1)) ω)} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  choose N0 hN0 using fun k : ℕ =>
    hcauchy ((1 / 2 : ℝ) ^ k) (by positivity) ((1 / 2 : ℝ) ^ k) (by positivity)
  refine ⟨fun k => k + ∑ i ∈ Finset.range (k + 1), N0 i, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  · intro k
    refine hN0 k _ _ ?_ ?_
    · beta_reduce
      have : N0 k ≤ ∑ i ∈ Finset.range (k + 1), N0 i :=
        Finset.single_le_sum (f := N0) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
      omega
    · beta_reduce
      have : N0 k ≤ ∑ i ∈ Finset.range (k + 1 + 1), N0 i :=
        Finset.single_le_sum (f := N0) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (by omega))
      omega

/-- **Completeness in probability.**  A sequence of random elements of a complete pseudo-metric
space that is Cauchy in probability converges in probability (along the whole sequence) to a
measurable limit, and almost surely along a subsequence.  No measurability of the distance
events is needed: all probabilities are outer-measure values. -/
theorem exists_limit_of_cauchy_in_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Type*} [PseudoMetricSpace F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    (X : ℕ → Ω → F) (hX : ∀ N, Measurable (X N))
    (hcauchy : ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal rho) :
    ∃ Xlim : Ω → F, Measurable Xlim ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => X (φ k) ω) atTop (𝓝 (Xlim ω))) ∧
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
        P {ω | eps ≤ dist (X N ω) (Xlim ω)} ≤ ENNReal.ofReal rho := by
  obtain ⟨φ, hφ, hφP⟩ := aux_exists_subseq_summable (P := P) X hcauchy
  have hsum : ∑' k, P {ω | (1 / 2 : ℝ) ^ k ≤ dist (X (φ k) ω) (X (φ (k + 1)) ω)} ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
      ?_ (ENNReal.tsum_le_tsum hφP)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem hsum
  haveI : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  haveI : Nonempty F := ⟨X 0 (Classical.choice ‹Nonempty Ω›)⟩
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => X (φ k) ω) atTop (𝓝 (limUnder atTop (fun k => X (φ k) ω))) := by
    filter_upwards [hae] with ω hω
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 hω
    have hd : ∀ k : ℕ, dist (X (φ (k + k0)) ω) (X (φ (k + 1 + k0)) ω) ≤ (1 / 2 : ℝ) ^ k := by
      intro k
      have h1 := hk0 (k + k0) (by omega)
      simp only [not_le] at h1
      have h2 : (1 / 2 : ℝ) ^ (k + k0) ≤ (1 / 2 : ℝ) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h3 : φ (k + k0 + 1) = φ (k + 1 + k0) := by rw [Nat.add_right_comm]
      rw [← h3]
      exact (h1.trans_le h2).le
    have hsm : Summable fun k : ℕ => dist (X (φ (k + k0)) ω) (X (φ (k + 1 + k0)) ω) :=
      Summable.of_nonneg_of_le (fun _ => dist_nonneg) hd summable_geometric_two
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
      (cauchySeq_of_summable_dist (f := fun k : ℕ => X (φ (k + k0)) ω) hsm)
    have ha' : Tendsto (fun k => X (φ k) ω) atTop (𝓝 a) :=
      (tendsto_add_atTop_iff_nat (f := fun k => X (φ k) ω) k0).1 ha
    exact tendsto_nhds_limUnder ⟨a, ha'⟩
  have hmeas : AEMeasurable (fun ω => limUnder atTop (fun k => X (φ k) ω)) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun k => (hX (φ k)).aemeasurable) hconv
  refine ⟨hmeas.mk _, hmeas.measurable_mk, φ, hφ, ?_, ?_⟩
  · filter_upwards [hconv, hmeas.ae_eq_mk] with ω h1 h2
    rwa [← h2]
  · intro eps heps rho hrho
    obtain ⟨N0, hN0⟩ := hcauchy (eps / 2) (half_pos heps) rho hrho
    refine ⟨N0, fun N hN => ?_⟩
    set B : ℕ → Set Ω := fun j => {ω | eps / 2 ≤ dist (X N ω) (X (φ j) ω)} with hBdef
    have hB : ∀ j, N0 ≤ j → P (B j) ≤ ENNReal.ofReal rho := fun j hj =>
      hN0 N (φ j) hN (hj.trans (hφ.id_le j))
    have hmono : Monotone fun n : ℕ => ⋂ j ∈ Set.Ici n, B j := fun n m hnm =>
      Set.biInter_subset_biInter_left (Set.Ici_subset_Ici.2 hnm)
    have hL : P (⋃ n : ℕ, ⋂ j ∈ Set.Ici n, B j) ≤ ENNReal.ofReal rho := by
      rw [hmono.measure_iUnion]
      refine iSup_le fun n => ?_
      calc P (⋂ j ∈ Set.Ici n, B j) ≤ P (B (max n N0)) :=
            measure_mono (Set.biInter_subset_of_mem (Set.mem_Ici.2 (le_max_left _ _)))
        _ ≤ ENNReal.ofReal rho := hB _ (le_max_right _ _)
    refine (measure_mono_ae ?_).trans hL
    filter_upwards [hconv, hmeas.ae_eq_mk] with ω h1 h2 hS
    have h1' : Tendsto (fun k => X (φ k) ω) atTop (𝓝 (hmeas.mk _ ω)) := by rwa [← h2]
    have hev : ∀ᶠ j in atTop, dist (X (φ j) ω) (hmeas.mk _ ω) < eps / 2 :=
      Metric.tendsto_nhds.1 h1' (eps / 2) (half_pos heps)
    obtain ⟨n, hn⟩ := eventually_atTop.1 hev
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iInter₂.2 fun j hj => ?_⟩
    have hS' : eps ≤ dist (X N ω) (hmeas.mk _ ω) := hS
    have h4 := dist_triangle (X N ω) (X (φ j) ω) (hmeas.mk _ ω)
    have h5 := hn j hj
    show eps / 2 ≤ dist (X N ω) (X (φ j) ω)
    linarith

end Completeness

section Deterministic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A compact set has a finite `δ`-net with centres in any prescribed dense set. -/
lemma aux_exists_finset_net {S : Set E} (hS : IsCompact S) {D : Set E} (hD : Dense D)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset E, (∀ d ∈ T, d ∈ D) ∧ ∀ x ∈ S, ∃ d ∈ T, dist x d < δ := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun d : D => Metric.ball (d : E) δ)
    (fun _ => Metric.isOpen_ball) (fun x _ => by
      obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x hδ
      exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball.2 hxy⟩)
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro d hd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hd
    exact a.2
  · intro x hx
    have := ht hx
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, hxa⟩ := this
    exact ⟨a, Finset.mem_image_of_mem _ ha, by rwa [Metric.mem_ball] at hxa⟩

/-- The distance from a vector to its orthogonal projection is at most its norm. -/
lemma aux_norm_sub_starProjection_le (V : Submodule ℝ E) [V.HasOrthogonalProjection] (x : E) :
    ‖x - V.starProjection x‖ ≤ ‖x‖ := by
  have h0 : ⟪x - V.starProjection x, V.starProjection x⟫_ℝ = 0 :=
    V.starProjection_inner_eq_zero x _ (V.starProjection_apply_mem x)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  rw [sub_add_cancel] at h
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  linarith only [h, sq_nonneg ‖V.starProjection x‖]

/-- Projection estimate: if `G` is self-adjoint and maps the unit ball into a set within `δ'` of
`V`, then `⟨x, G y⟩ - ⟨P x, G (P y)⟩` is at most `2 δ'` on the unit ball. -/
lemma aux_proj_bilinear (V : Submodule ℝ E) [V.HasOrthogonalProjection] {C : Set E} {δ' : ℝ}
    (hnet : ∀ c ∈ C, ∃ s ∈ V, dist c s < δ') (G : E →L[ℝ] E)
    (hsym : ∀ a b : E, ⟪G a, b⟫_ℝ = ⟪a, G b⟫_ℝ) (hG : ∀ z : E, ‖z‖ ≤ 1 → G z ∈ C)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |⟪x, G y⟫_ℝ - ⟪V.starProjection x, G (V.starProjection y)⟫_ℝ| ≤ 2 * δ' := by
  set Q := V.starProjection with hQ
  have hQx : ‖Q x‖ ≤ 1 := (V.norm_starProjection_apply_le x).trans hx
  have hdec : ⟪x, G y⟫_ℝ - ⟪Q x, G (Q y)⟫_ℝ =
      ⟪x - Q x, G y⟫_ℝ + ⟪G (Q x), y - Q y⟫_ℝ := by
    rw [hsym (Q x) (y - Q y), map_sub, inner_sub_left, inner_sub_right]
    ring
  -- first term
  have h1 : |⟪x - Q x, G y⟫_ℝ| ≤ δ' := by
    obtain ⟨s, hs, hds⟩ := hnet _ (hG y hy)
    have horth : ⟪x - Q x, s⟫_ℝ = 0 := by
      have := V.sub_starProjection_mem_orthogonal x
      rw [Submodule.mem_orthogonal'] at this
      exact this s hs
    have : ⟪x - Q x, G y⟫_ℝ = ⟪x - Q x, G y - s⟫_ℝ := by
      rw [inner_sub_right, horth, sub_zero]
    rw [this]
    calc |⟪x - Q x, G y - s⟫_ℝ| ≤ ‖x - Q x‖ * ‖G y - s‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * δ' := by
        have h1 : ‖x - Q x‖ ≤ 1 := (aux_norm_sub_starProjection_le V x).trans hx
        have h3 : ‖G y - s‖ ≤ δ' := by rw [← dist_eq_norm]; exact hds.le
        exact mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = δ' := one_mul _
  have h2 : |⟪G (Q x), y - Q y⟫_ℝ| ≤ δ' := by
    obtain ⟨s, hs, hds⟩ := hnet _ (hG (Q x) hQx)
    have horth : ⟪s, y - Q y⟫_ℝ = 0 := by
      have := V.sub_starProjection_mem_orthogonal y
      rw [Submodule.mem_orthogonal] at this
      exact this s hs
    have : ⟪G (Q x), y - Q y⟫_ℝ = ⟪G (Q x) - s, y - Q y⟫_ℝ := by
      rw [inner_sub_left, horth, sub_zero]
    rw [this]
    calc |⟪G (Q x) - s, y - Q y⟫_ℝ| ≤ ‖G (Q x) - s‖ * ‖y - Q y‖ := abs_real_inner_le_norm _ _
      _ ≤ δ' * 1 := by
        have h1 : ‖y - Q y‖ ≤ 1 := (aux_norm_sub_starProjection_le V y).trans hy
        have h3 : ‖G (Q x) - s‖ ≤ δ' := by rw [← dist_eq_norm]; exact hds.le
        exact mul_le_mul h3 h1 (norm_nonneg _) ((dist_nonneg).trans hds.le)
      _ = δ' := mul_one _
  rw [hdec]
  calc |⟪x - Q x, G y⟫_ℝ + ⟪G (Q x), y - Q y⟫_ℝ|
      ≤ |⟪x - Q x, G y⟫_ℝ| + |⟪G (Q x), y - Q y⟫_ℝ| := abs_add_le _ _
    _ ≤ 2 * δ' := by linarith

/-- Net estimate: replacing the two arguments of the bilinear form `⟨·, G ·⟩` by `δ₂`-close
vectors changes it by at most `3 R δ₂`, when `G` has operator norm at most `R`. -/
lemma aux_net_bilinear (G : E →L[ℝ] E) {R : ℝ}
    (hR : ∀ z : E, ‖z‖ ≤ 1 → ‖G z‖ ≤ R) {u v d e : E} {δ₂ : ℝ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hd : dist u d ≤ δ₂) (he : dist v e ≤ δ₂) (hδ₂ : δ₂ ≤ 1) :
    |⟪u, G v⟫_ℝ - ⟪d, G e⟫_ℝ| ≤ 3 * R * δ₂ := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (by rw [norm_zero]; exact zero_le_one))
  have hGn : ‖G‖ ≤ R := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hR0 fun z hz => hR z hz.le
  have hd1 : ‖d‖ ≤ 2 := by
    have : ‖d‖ ≤ ‖u‖ + dist u d := by
      have := norm_sub_le u (u - d)
      rw [sub_sub_cancel] at this
      rwa [dist_eq_norm]
    linarith
  have hdec : ⟪u, G v⟫_ℝ - ⟪d, G e⟫_ℝ = ⟪u - d, G v⟫_ℝ + ⟪d, G (v - e)⟫_ℝ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hGv : ‖G v‖ ≤ R := hR v hv
  have hGe : ‖G (v - e)‖ ≤ R * δ₂ := by
    calc ‖G (v - e)‖ ≤ ‖G‖ * ‖v - e‖ := G.le_opNorm _
      _ ≤ R * δ₂ := by
        rw [← dist_eq_norm]
        exact mul_le_mul hGn he dist_nonneg hR0
  have h1 : |⟪u - d, G v⟫_ℝ| ≤ δ₂ * R := by
    calc |⟪u - d, G v⟫_ℝ| ≤ ‖u - d‖ * ‖G v‖ := abs_real_inner_le_norm _ _
      _ ≤ δ₂ * R := by
        rw [← dist_eq_norm]
        exact mul_le_mul hd hGv (norm_nonneg _) ((dist_nonneg).trans hd)
  have h2 : |⟪d, G (v - e)⟫_ℝ| ≤ 2 * (R * δ₂) := by
    calc |⟪d, G (v - e)⟫_ℝ| ≤ ‖d‖ * ‖G (v - e)‖ := abs_real_inner_le_norm _ _
      _ ≤ 2 * (R * δ₂) := mul_le_mul hd1 hGe (norm_nonneg _) (by norm_num)
  rw [hdec]
  calc |⟪u - d, G v⟫_ℝ + ⟪d, G (v - e)⟫_ℝ|
      ≤ |⟪u - d, G v⟫_ℝ| + |⟪d, G (v - e)⟫_ℝ| := abs_add_le _ _
    _ ≤ 3 * R * δ₂ := by linarith only [h1, h2]

/-- **Finite test set.**  For a compact `C` and a dense `D`, there is a finite `T ⊆ D` such that,
for all `x, y` in the unit ball, some pair `d, e ∈ T` approximates the bilinear form `⟨x, G y⟩`
to within `δ`, simultaneously for every self-adjoint `G` mapping the unit ball into `C`. -/
lemma aux_approx_test_set {C : Set E} (hC : IsCompact C) {D : Set E} (hD : Dense D) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ T : Finset E, (∀ d ∈ T, d ∈ D) ∧ ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ∃ d ∈ T, ∃ e ∈ T, ∀ G : E →L[ℝ] E, (∀ a b : E, ⟪G a, b⟫_ℝ = ⟪a, G b⟫_ℝ) →
        (∀ z : E, ‖z‖ ≤ 1 → G z ∈ C) → |⟪x, G y⟫_ℝ - ⟪d, G e⟫_ℝ| ≤ δ := by
  classical
  obtain ⟨S, -, hS⟩ := aux_exists_finset_net hC dense_univ (δ := δ / 4) (by positivity)
  set V : Submodule ℝ E := Submodule.span ℝ (S : Set E) with hV
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_finset ℝ S
  have hnet : ∀ c ∈ C, ∃ s ∈ V, dist c s < δ / 4 := by
    intro c hc
    obtain ⟨s, hsS, hs⟩ := hS c hc
    exact ⟨s, Submodule.subset_span hsS, hs⟩
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  set R₀ : ℝ := max R 0 with hR₀
  have hR0 : 0 ≤ R₀ := le_max_right _ _
  set δ₂ : ℝ := min 1 (δ / (8 * (R₀ + 1))) with hδ₂
  have hδ₂pos : 0 < δ₂ := lt_min one_pos (by positivity)
  have hδ₂1 : δ₂ ≤ 1 := min_le_left _ _
  have hδ₂R : δ₂ * (8 * (R₀ + 1)) ≤ δ :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hK : IsCompact (((↑) : V → E) '' Metric.closedBall (0 : V) 1) :=
    (isCompact_closedBall _ _).image continuous_subtype_val
  obtain ⟨T, hTD, hT⟩ := aux_exists_finset_net hK hD hδ₂pos
  refine ⟨T, hTD, fun x y hx hy => ?_⟩
  have hQmem : ∀ w : E, ‖w‖ ≤ 1 →
      V.starProjection w ∈ ((↑) : V → E) '' Metric.closedBall (0 : V) 1 := by
    intro w hw
    refine ⟨⟨V.starProjection w, V.starProjection_apply_mem w⟩, ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact (V.norm_starProjection_apply_le w).trans hw
  obtain ⟨d, hdT, hd⟩ := hT _ (hQmem x hx)
  obtain ⟨e, heT, he⟩ := hT _ (hQmem y hy)
  refine ⟨d, hdT, e, heT, fun G hsym hG => ?_⟩
  have hGR : ∀ z : E, ‖z‖ ≤ 1 → ‖G z‖ ≤ R₀ := fun z hz =>
    (hR _ (hG z hz)).trans (le_max_left _ _)
  have e1 := aux_proj_bilinear V hnet G hsym hG x y hx hy
  have e2 := aux_net_bilinear G hGR ((V.norm_starProjection_apply_le x).trans hx)
    ((V.norm_starProjection_apply_le y).trans hy) hd.le he.le hδ₂1
  have hsplit : ⟪x, G y⟫_ℝ - ⟪d, G e⟫_ℝ =
      (⟪x, G y⟫_ℝ - ⟪V.starProjection x, G (V.starProjection y)⟫_ℝ) +
        (⟪V.starProjection x, G (V.starProjection y)⟫_ℝ - ⟪d, G e⟫_ℝ) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  linarith only [e1, e2, hδ₂R, hδ₂pos, hδ]

end Deterministic

section Probabilistic

/-- Polarisation for a self-adjoint operator. -/
lemma aux_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E) (hsym : ∀ a b : E, ⟪G a, b⟫_ℝ = ⟪a, G b⟫_ℝ) (d e : E) :
    4 * ⟪d, G e⟫_ℝ = ⟪d + e, G (d + e)⟫_ℝ - ⟪d - e, G (d - e)⟫_ℝ := by
  have h : ⟪e, G d⟫_ℝ = ⟪d, G e⟫_ℝ := by rw [← hsym, real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  linarith

/-- A bilinear bound on the unit ball gives an operator-norm bound. -/
lemma aux_opNorm_le_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → |⟪x, A y⟫_ℝ| ≤ M) : ‖A‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hM fun y hy => ?_
  by_cases hz : A y = 0
  · rw [hz, norm_zero]
    exact hM
  · have hpos : 0 < ‖A y‖ := norm_pos_iff.2 hz
    have hx : ‖(‖A y‖⁻¹ : ℝ) • A y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have := h _ y hx.le hy.le
    have e : ⟪(‖A y‖⁻¹ : ℝ) • A y, A y⟫_ℝ = ‖A y‖ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
        inv_mul_cancel₀ hpos.ne', one_mul]
    rwa [e, abs_of_nonneg (norm_nonneg _)] at this

/-- Finitely many quadratic forms that are Cauchy in probability are jointly Cauchy in
probability (union bound). -/
lemma aux_finite_quad_cauchy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : ℕ → Ω → E →L[ℝ] E) (D : Set E)
    (hquad : ∀ h ∈ D, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} ≤ ENNReal.ofReal rho)
    (H : Finset E) (hH : ∀ h ∈ H, h ∈ D) {eps : ℝ} (heps : 0 < eps) {rho : ℝ} (hrho : 0 < rho) :
    ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
      P {ω | ∃ h ∈ H, eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} ≤ ENNReal.ofReal rho := by
  classical
  choose! N0f hN0f using fun h (hh : h ∈ D) =>
    hquad h hh eps heps (rho / (H.card + 1)) (by positivity)
  refine ⟨H.sup N0f, fun N N' hN hN' => ?_⟩
  have hset : {ω | ∃ h ∈ H, eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} =
      ⋃ h ∈ H, {ω | eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  calc P (⋃ h ∈ H, {ω | eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|})
      ≤ ∑ h ∈ H, P {ω | eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ H, ENNReal.ofReal (rho / (H.card + 1)) :=
        Finset.sum_le_sum fun h hh => hN0f h (hH h hh) N N'
          ((Finset.le_sup hh).trans hN) ((Finset.le_sup hh).trans hN')
    _ = (H.card : ℝ≥0∞) * ENNReal.ofReal (rho / (H.card + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        linarith only [hrho]

end Probabilistic

/-- Operator-norm Cauchy property in probability for uniformly compact self-adjoint random
operators whose quadratic forms are Cauchy in probability on a countable dense set
(the in-probability form of the norm-convergence step of `mfd:prop-killed-inverse`). -/
theorem opNorm_cauchy_in_probability_of_uniformly_compact
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (G : ℕ → Ω → E →L[ℝ] E)
    (hsym : ∀ N ω (x y : E), ⟪G N ω x, y⟫_ℝ = ⟪x, G N ω y⟫_ℝ)
    (Kc : ℕ → Ω → ℝ)
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N, P {ω | Mb < Kc N ω} ≤ ENNReal.ofReal rho)
    (hcomp : ∀ Mb : ℝ, ∃ C : Set E, IsCompact C ∧
      ∀ N ω, Kc N ω ≤ Mb → ∀ x : E, ‖x‖ ≤ 1 → G N ω x ∈ C)
    (D : Set E) (hDdense : Dense D) (hDadd : ∀ a ∈ D, ∀ b ∈ D, a + b ∈ D ∧ a - b ∈ D)
    (hquad : ∀ h ∈ D, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} ≤ ENNReal.ofReal rho) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N', N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ ‖G N ω - G N' ω‖} ≤ ENNReal.ofReal rho := by
  classical
  intro eps heps rho hrho
  obtain ⟨Mb, hMb⟩ := htight (rho / 4) (by positivity)
  obtain ⟨C, hCc, hC⟩ := hcomp Mb
  obtain ⟨T, hTD, hT⟩ := aux_approx_test_set hCc hDdense (δ := eps / 4) (by positivity)
  set H : Finset E := (T ×ˢ T).image (fun p => p.1 + p.2) ∪ (T ×ˢ T).image (fun p => p.1 - p.2)
    with hHdef
  have hHD : ∀ h ∈ H, h ∈ D := by
    intro h hh
    rcases Finset.mem_union.1 hh with hh | hh
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hh
      rw [Finset.mem_product] at hp
      exact (hDadd _ (hTD _ hp.1) _ (hTD _ hp.2)).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hh
      rw [Finset.mem_product] at hp
      exact (hDadd _ (hTD _ hp.1) _ (hTD _ hp.2)).2
  obtain ⟨N0, hN0⟩ := aux_finite_quad_cauchy P G D hquad H hHD (half_pos heps) (half_pos hrho)
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  have hsub : {ω | eps ≤ ‖G N ω - G N' ω‖} ⊆
      ({ω | Mb < Kc N ω} ∪ {ω | Mb < Kc N' ω}) ∪
        {ω | ∃ h ∈ H, eps / 2 ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_exists, not_and,
      not_le] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hnorm : ‖G N ω - G N' ω‖ ≤ 3 * eps / 4 := by
      refine aux_opNorm_le_of_inner (by positivity) fun x y hx hy => ?_
      obtain ⟨d, hd, e, he, hde⟩ := hT x y hx hy
      have hN1 := hde (G N ω) (hsym N ω) (hC N ω h1)
      have hN2 := hde (G N' ω) (hsym N' ω) (hC N' ω h2)
      have hpol : ⟪d, G N ω e⟫_ℝ - ⟪d, G N' ω e⟫_ℝ =
          ((⟪d + e, G N ω (d + e)⟫_ℝ - ⟪d + e, G N' ω (d + e)⟫_ℝ) -
            (⟪d - e, G N ω (d - e)⟫_ℝ - ⟪d - e, G N' ω (d - e)⟫_ℝ)) / 4 := by
        have a1 := aux_polarization (G N ω) (hsym N ω) d e
        have a2 := aux_polarization (G N' ω) (hsym N' ω) d e
        linarith
      have hp := h3 (d + e) (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(d, e),
        Finset.mem_product.2 ⟨hd, he⟩, rfl⟩))
      have hm := h3 (d - e) (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(d, e),
        Finset.mem_product.2 ⟨hd, he⟩, rfl⟩))
      have hmid : |⟪d, G N ω e⟫_ℝ - ⟪d, G N' ω e⟫_ℝ| ≤ eps / 4 := by
        rw [hpol, abs_le]
        rw [abs_lt] at hp hm
        constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
      have hsplit : ⟪x, (G N ω - G N' ω) y⟫_ℝ =
          (⟪x, G N ω y⟫_ℝ - ⟪d, G N ω e⟫_ℝ) + (⟪d, G N ω e⟫_ℝ - ⟪d, G N' ω e⟫_ℝ) -
            (⟪x, G N' ω y⟫_ℝ - ⟪d, G N' ω e⟫_ℝ) := by
        rw [ContinuousLinearMap.sub_apply, inner_sub_right]
        ring
      rw [hsplit]
      rw [abs_le] at hN1 hN2 hmid ⊢
      constructor <;> linarith [hN1.1, hN1.2, hN2.1, hN2.2, hmid.1, hmid.2]
    have := hω
    simp only [Set.mem_setOf_eq] at this
    linarith
  calc P {ω | eps ≤ ‖G N ω - G N' ω‖}
      ≤ P (({ω | Mb < Kc N ω} ∪ {ω | Mb < Kc N' ω}) ∪
        {ω | ∃ h ∈ H, eps / 2 ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|}) := measure_mono hsub
    _ ≤ (P {ω | Mb < Kc N ω} + P {ω | Mb < Kc N' ω}) +
        P {ω | ∃ h ∈ H, eps / 2 ≤ |⟪h, G N ω h⟫_ℝ - ⟪h, G N' ω h⟫_ℝ|} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4)) + ENNReal.ofReal (rho / 2) :=
        add_le_add (add_le_add (hMb N) (hMb N')) (hN0 N N' hN hN')
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end SubdiffusiveProcess.Probability
