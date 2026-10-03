module

public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldPrePrincipal
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldBridge
public import SubdiffusiveProcess.Paper.Foundations.PrefixPrawBridge
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.layer_regularity_moments
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMoment
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldEvenField
public import SubdiffusiveProcess.Analysis.RawLp
public import SubdiffusiveProcess.PrefixMonotoneLp
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualZMeas


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false




noncomputable section LemPrefixLimitActualCoordinateCauchyHelpers



-- ===== PmrGeneric =====
/-!
# Generic probability steps for the raw response coordinate

Cauchy in measure, stability under finite-sum domination and truncation, the
passage "Cauchy in measure + uniform higher moment ⇒ `L^p`-Cauchy", and the
`card^{1/q}` cost of a finite maximum.  No model-specific input.
-/



open MeasureTheory Filter
open scoped ENNReal Topology

namespace Paper

/-- Cauchy in measure along `ℕ`, for real-valued sequences. -/
def aux_prefix_rraw_CauchyInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
    μ {ω | δ ≤ |f n ω - f n' ω|} ≤ ENNReal.ofReal η

theorem aux_prefix_rraw_cim_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (h : TendstoInMeasure μ f atTop g) :
    aux_prefix_rraw_CauchyInMeasure μ f := by
  intro δ hδ η hη
  have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.mp (h _ hδ2)) _ hη2)
  refine ⟨n0, fun n n' hn hn' => ?_⟩
  have hsub : {ω | δ ≤ |f n ω - f n' ω|} ⊆
      {ω | ENNReal.ofReal (δ / 2) ≤ edist (f n ω) (g ω)} ∪
        {ω | ENNReal.ofReal (δ / 2) ≤ edist (f n' ω) (g ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, edist_dist, Real.dist_eq] at hω ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : |f n ω - g ω| < δ / 2 := (ENNReal.ofReal_lt_ofReal_iff'.mp h1).1
    have h2' : |f n' ω - g ω| < δ / 2 := (ENNReal.ofReal_lt_ofReal_iff'.mp h2).1
    have htri : |f n ω - f n' ω| ≤ |f n ω - g ω| + |f n' ω - g ω| := by
      calc |f n ω - f n' ω| = |(f n ω - g ω) - (f n' ω - g ω)| := by ring_nf
        _ ≤ |f n ω - g ω| + |f n' ω - g ω| := abs_sub _ _
    linarith
  calc μ {ω | δ ≤ |f n ω - f n' ω|}
      ≤ μ ({ω | ENNReal.ofReal (δ / 2) ≤ edist (f n ω) (g ω)} ∪
          {ω | ENNReal.ofReal (δ / 2) ≤ edist (f n' ω) (g ω)}) := measure_mono hsub
    _ ≤ μ {ω | ENNReal.ofReal (δ / 2) ≤ edist (f n ω) (g ω)} +
          μ {ω | ENNReal.ofReal (δ / 2) ≤ edist (f n' ω) (g ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add (hn0 n hn) (hn0 n' hn')
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

/-- Eventual almost-everywhere domination by a finite sum of Cauchy-in-measure
sequences gives Cauchy in measure. -/
theorem aux_prefix_rraw_cim_of_sum_dominated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {ι : Type*} (s : Finset ι) (f : ι → ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, aux_prefix_rraw_CauchyInMeasure μ (f i))
    (F : ℕ → Ω → ℝ) (N0 : ℕ)
    (hdom : ∀ n n' : ℕ, N0 ≤ n → N0 ≤ n' → ∀ᵐ ω ∂μ,
      |F n ω - F n' ω| ≤ ∑ i ∈ s, |f i n ω - f i n' ω|) :
    aux_prefix_rraw_CauchyInMeasure μ F := by
  classical
  intro δ hδ η hη
  set c : ℝ := (s.card : ℝ) + 1 with hc
  have hcpos : 0 < c := by positivity
  have hδc : 0 < δ / c := div_pos hδ hcpos
  have hηc : 0 < η / c := div_pos hη hcpos
  have hex : ∀ i ∈ s, ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      μ {ω | δ / c ≤ |f i n ω - f i n' ω|} ≤ ENNReal.ofReal (η / c) :=
    fun i hi => hf i hi (δ / c) hδc (η / c) hηc
  choose n0 hn0 using hex
  let n1 : ℕ := max N0 (s.attach.sup (fun i => n0 i.1 i.2))
  refine ⟨n1, fun n n' hn hn' => ?_⟩
  have hle_i : ∀ i (hi : i ∈ s), n0 i hi ≤ n1 := fun i hi =>
    le_trans (Finset.le_sup (f := fun i : s => n0 i.1 i.2) (Finset.mem_attach s ⟨i, hi⟩))
      (le_max_right _ _)
  have hN0 : N0 ≤ n1 := le_max_left _ _
  have hsub' : ∀ᵐ ω ∂μ, ω ∈ {ω | δ ≤ |F n ω - F n' ω|} →
      ω ∈ (⋃ i ∈ s, {ω | δ / c ≤ |f i n ω - f i n' ω|}) := by
    filter_upwards [hdom n n' (hN0.trans hn) (hN0.trans hn')] with ω hω hmem
    replace hmem : δ ≤ |F n ω - F n' ω| := hmem
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    have hsum : ∑ i ∈ s, |f i n ω - f i n' ω| ≤ ∑ _i ∈ s, δ / c :=
      Finset.sum_le_sum fun i hi => (hcon i hi).le
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hlt : (s.card : ℝ) * (δ / c) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ hcpos]
      nlinarith
    exact absurd (hmem.trans (hω.trans hsum)) (not_le.mpr hlt)
  calc μ {ω | δ ≤ |F n ω - F n' ω|}
      ≤ μ (⋃ i ∈ s, {ω | δ / c ≤ |f i n ω - f i n' ω|}) :=
        measure_mono_ae (hsub'.mono fun ω h => h)
    _ ≤ ∑ i ∈ s, μ {ω | δ / c ≤ |f i n ω - f i n' ω|} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (η / c) := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact hn0 i hi n n' ((hle_i i hi).trans hn) ((hle_i i hi).trans hn')
    _ = ENNReal.ofReal ((s.card : ℝ) * (η / c)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal η := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_div_assoc', div_le_iff₀ hcpos]
      nlinarith

/-- Markov's inequality in the form used for the discounted tail. -/
theorem aux_prefix_rraw_meas_ge_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℝ) (hq : 0 < q) (T : Ω → ℝ) (hT : AEStronglyMeasurable T μ) (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | δ ≤ T ω} ≤
      eLpNorm T (ENNReal.ofReal q) μ ^ q / ENNReal.ofReal δ ^ q := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hmk := mul_meas_ge_le_pow_eLpNorm' μ hq0 ENNReal.ofReal_ne_top (f := T) (ENNReal.ofReal δ)
  rw [ENNReal.toReal_ofReal hq.le] at hmk
  have hsub : {ω | δ ≤ T ω} ⊆ {ω | ENNReal.ofReal δ ≤ ‖T ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hω.trans (le_abs_self _))
  have hpos : ENNReal.ofReal δ ^ q ≠ 0 := by
    have : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr this) ENNReal.ofReal_ne_top).ne'
  have htop : ENNReal.ofReal δ ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop), mul_comm]
  exact (mul_le_mul_right (measure_mono hsub) _).trans hmk

/-- Truncation: if `V` is within `T H` of a Cauchy-in-measure `S H` eventually, and
`T H` is small in `L^q` uniformly in the sequence index for large `H`, then `V` is
Cauchy in measure. -/
theorem aux_prefix_rraw_cim_of_truncation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : ℝ) (hq : 0 < q)
    (V : ℕ → Ω → ℝ) (S T : ℕ → ℕ → Ω → ℝ)
    (hS : ∀ H, aux_prefix_rraw_CauchyInMeasure μ (S H))
    (hVS : ∀ H, ∃ N0 : ℕ, ∀ n, N0 ≤ n → ∀ᵐ ω ∂μ, |V n ω - S H n ω| ≤ T H n ω)
    (hTm : ∀ H n, AEStronglyMeasurable (T H n) μ)
    (hTq : ∀ ε : ℝ, 0 < ε → ∃ H, ∀ n, eLpNorm (T H n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ε) :
    aux_prefix_rraw_CauchyInMeasure μ V := by
  intro δ hδ η hη
  have hδ3 : 0 < δ / 3 := by linarith
  have hη3 : 0 < η / 3 := by linarith
  -- choose `H` so that each tail has `μ {δ/3 ≤ T} ≤ η/3`
  set ε : ℝ := δ / 3 * (η / 3) ^ (1 / q) with hεdef
  have hε : 0 < ε := mul_pos hδ3 (Real.rpow_pos_of_pos hη3 _)
  obtain ⟨H, hH⟩ := hTq ε hε
  have htail : ∀ n, μ {ω | δ / 3 ≤ T H n ω} ≤ ENNReal.ofReal (η / 3) := by
    intro n
    refine (aux_prefix_rraw_meas_ge_le μ q hq (T H n) (hTm H n) (δ / 3) hδ3).trans ?_
    have hpow : eLpNorm (T H n) (ENNReal.ofReal q) μ ^ q ≤ ENNReal.ofReal ε ^ q :=
      ENNReal.rpow_le_rpow (hH n) hq.le
    have hε_eq : ENNReal.ofReal ε ^ q = ENNReal.ofReal (δ / 3) ^ q * ENNReal.ofReal (η / 3) := by
      rw [hεdef, ENNReal.ofReal_mul hδ3.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hη3.le _) hq.le,
        ← Real.rpow_mul hη3.le, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
    have hpos : ENNReal.ofReal (δ / 3) ^ q ≠ 0 := by
      have : ENNReal.ofReal (δ / 3) ≠ 0 := by simpa using hδ3
      exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr this) ENNReal.ofReal_ne_top).ne'
    have htop : ENNReal.ofReal (δ / 3) ^ q ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top
    rw [ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl htop), mul_comm]
    exact hpow.trans hε_eq.le
  obtain ⟨N0, hN0⟩ := hVS H
  obtain ⟨n1, hn1⟩ := hS H (δ / 3) hδ3 (η / 3) hη3
  refine ⟨max N0 n1, fun n n' hn hn' => ?_⟩
  have hsub' : ∀ᵐ ω ∂μ, ω ∈ {ω | δ ≤ |V n ω - V n' ω|} →
      ω ∈ ({ω | δ / 3 ≤ |S H n ω - S H n' ω|} ∪ {ω | δ / 3 ≤ T H n ω}) ∪
        {ω | δ / 3 ≤ T H n' ω} := by
    filter_upwards [hN0 n ((le_max_left _ _).trans hn),
      hN0 n' ((le_max_left _ _).trans hn')] with ω h1 h2 hmem
    replace hmem : δ ≤ |V n ω - V n' ω| := hmem
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨a, b⟩, c⟩ := hcon
    have htri : |V n ω - V n' ω| ≤
        |V n ω - S H n ω| + |S H n ω - S H n' ω| + |V n' ω - S H n' ω| := by
      calc |V n ω - V n' ω|
          = |(V n ω - S H n ω) + (S H n ω - S H n' ω) - (V n' ω - S H n' ω)| := by ring_nf
        _ ≤ |(V n ω - S H n ω) + (S H n ω - S H n' ω)| + |V n' ω - S H n' ω| := abs_sub _ _
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    linarith
  calc μ {ω | δ ≤ |V n ω - V n' ω|}
      ≤ μ (({ω | δ / 3 ≤ |S H n ω - S H n' ω|} ∪ {ω | δ / 3 ≤ T H n ω}) ∪
          {ω | δ / 3 ≤ T H n' ω}) := measure_mono_ae (hsub'.mono fun ω h => h)
    _ ≤ μ {ω | δ / 3 ≤ |S H n ω - S H n' ω|} + μ {ω | δ / 3 ≤ T H n ω} +
          μ {ω | δ / 3 ≤ T H n' ω} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) := by
        gcongr
        · exact hn1 n n' ((le_max_right _ _).trans hn) ((le_max_right _ _).trans hn')
        · exact htail n
        · exact htail n'
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring

/-- Cauchy in measure plus a uniform `L^q` bound with `q > p` gives the `L^p`-Cauchy
property (Hölder on the exceptional set; no limit object is needed). -/
theorem aux_prefix_rraw_Lp_cauchy_of_cim {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : ℝ) (hp : 1 ≤ p) (hpq : p < q) (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ B)
    (hcim : aux_prefix_rraw_CauchyInMeasure μ f) (ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  set e : ℝ := 1 / p - 1 / q with he
  have he0 : 0 < e := by
    rw [he, sub_pos]
    exact one_div_lt_one_div_of_lt hp0 hpq
  set b : ℝ := B.toReal with hb
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hBb : B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hB).symm
  set κ : ℝ := ε / (4 * (b + 1)) with hκ
  have hκ0 : 0 < κ := div_pos hε (by positivity)
  set η : ℝ := κ ^ (1 / e) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hκ0 _
  have hηe : η ^ e = κ := by
    rw [hη, ← Real.rpow_mul hκ0.le, one_div, inv_mul_cancel₀ he0.ne', Real.rpow_one]
  obtain ⟨n0, hn0⟩ := hcim (ε / 2) (by linarith) η hη0
  refine ⟨n0, fun n n' hn hn' => ?_⟩
  set g : Ω → ℝ := fun ω => f n ω - f n' ω with hgdef
  have hg : AEStronglyMeasurable g μ := (hf n).sub (hf n')
  set g' : Ω → ℝ := hg.mk g
  have hg'sm : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hgg' : g =ᵐ[μ] g' := hg.ae_eq_mk
  set A : Set Ω := {ω | ε / 2 ≤ |g' ω|} with hA
  have hAm : MeasurableSet A :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hg'sm.measurable)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hpq.le
  -- the exceptional set is small
  have hμA : μ A ≤ ENNReal.ofReal η := by
    have hAeq : A =ᵐ[μ] {ω | ε / 2 ≤ |g ω|} := by
      filter_upwards [hgg'] with ω hω
      change (ε / 2 ≤ |g' ω|) = (ε / 2 ≤ |g ω|)
      rw [hω]
    rw [measure_congr hAeq]
    exact hn0 n n' hn hn'
  -- `L^q` size of the difference
  have hgq : eLpNorm g' (ENNReal.ofReal q) μ ≤ 2 * ENNReal.ofReal (b + 1) := by
    rw [← eLpNorm_congr_ae hgg']
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := hp1.trans hpqE
    calc eLpNorm g (ENNReal.ofReal q) μ
        ≤ eLpNorm (f n) (ENNReal.ofReal q) μ + eLpNorm (f n') (ENNReal.ofReal q) μ :=
          eLpNorm_sub_le hq1
      _ ≤ B + B := add_le_add (hbound n) (hbound n')
      _ ≤ 2 * ENNReal.ofReal (b + 1) := by
          rw [two_mul]
          have : B ≤ ENNReal.ofReal (b + 1) := by
            rw [hBb]; exact ENNReal.ofReal_le_ofReal (by linarith)
          exact add_le_add this this
  -- split along `A`
  have hsplit : g' = A.indicator g' + Aᶜ.indicator g' := (Set.indicator_self_add_compl A g').symm
  have h1 : eLpNorm (A.indicator g') (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (ε / 2) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hAm]
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict A) hpqE
      hg'sm.aestronglyMeasurable
    rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le,
      Measure.restrict_apply_univ] at hH
    refine hH.trans ?_
    calc eLpNorm g' (ENNReal.ofReal q) (μ.restrict A) * μ A ^ (1 / p - 1 / q)
        ≤ (2 * ENNReal.ofReal (b + 1)) * ENNReal.ofReal η ^ e := by
          gcongr
          exact (eLpNorm_restrict_le _ _ _ _).trans hgq
      _ = ENNReal.ofReal (ε / 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hη0.le he0.le, hηe, hκ,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          ring
  have h2 : eLpNorm (Aᶜ.indicator g') (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (ε / 2) := by
    have hbd : ∀ᵐ ω ∂μ, ‖Aᶜ.indicator g' ω‖ ≤ ε / 2 := by
      refine Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ Aᶜ
      · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]
        simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
        exact hω.le
      · rw [Set.indicator_of_notMem hω, norm_zero]; linarith
    refine (eLpNorm_le_of_ae_bound (hg'sm.indicator hAm.compl).aestronglyMeasurable hbd).trans ?_
    simp
  calc eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ
      = eLpNorm g' (ENNReal.ofReal p) μ := eLpNorm_congr_ae hgg'
    _ = eLpNorm (A.indicator g' + Aᶜ.indicator g') (ENNReal.ofReal p) μ := by
        rw [← hsplit]
    _ ≤ eLpNorm (A.indicator g') (ENNReal.ofReal p) μ +
          eLpNorm (Aᶜ.indicator g') (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

/-- Lipschitz bound for a finite supremum of finite `ENNReal` values. -/
theorem aux_prefix_rraw_abs_toReal_sup_sub_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) (hb : ∀ i, b i ≠ ⊤) :
    |(s.sup a).toReal - (s.sup b).toReal| ≤ ∑ i ∈ s, |(a i).toReal - (b i).toReal| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sup_insert, Finset.sum_insert hi]
    have hsa : s.sup a ≠ ⊤ := by
      rw [← lt_top_iff_ne_top, Finset.sup_lt_iff (by simp)]
      exact fun j _ => lt_top_iff_ne_top.mpr (ha j)
    have hsb : s.sup b ≠ ⊤ := by
      rw [← lt_top_iff_ne_top, Finset.sup_lt_iff (by simp)]
      exact fun j _ => lt_top_iff_ne_top.mpr (hb j)
    rw [ENNReal.toReal_max (ha i) hsa, ENNReal.toReal_max (hb i) hsb]
    refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
    refine max_le ?_ ?_
    · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    · exact ih.trans (le_add_of_nonneg_left (abs_nonneg _))

/-- A finite maximum costs `card^{1/q}` in `L^q`. -/
theorem aux_prefix_rraw_eLpNorm_finset_sup_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ≥0∞)
    (hX : ∀ i, ∀ ω, X i ω ≠ ⊤) (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (q : ℝ) (hq : 0 < q) (B : ℝ≥0∞)
    (hB : ∀ i ∈ s, eLpNorm (fun ω => (X i ω).toReal) (ENNReal.ofReal q) μ ≤ B) :
    eLpNorm (fun ω => (s.sup (fun i => X i ω)).toReal) (ENNReal.ofReal q) μ ≤
      (s.card : ℝ≥0∞) ^ (1 / q) * B := by
  classical
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq.le
  have henorm : ∀ Y : ℝ≥0∞, Y ≠ ⊤ → ‖Y.toReal‖ₑ = Y := by
    intro Y hY
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hY]
  have hsupfin : ∀ ω, s.sup (fun i => X i ω) ≠ ⊤ := by
    intro ω
    rw [← lt_top_iff_ne_top, Finset.sup_lt_iff (by simp)]
    exact fun j _ => lt_top_iff_ne_top.mpr (hX j ω)
  have hsupm : AEMeasurable (fun ω => s.sup (fun i => X i ω)) μ := by
    have hgen : ∀ t : Finset ι, (∀ i ∈ t, AEMeasurable (X i) μ) →
        AEMeasurable (fun ω => t.sup (fun i => X i ω)) μ := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        change AEMeasurable (fun _ : Ω => (⊥ : ℝ≥0∞)) μ
        exact aemeasurable_const
      | @insert i t hi ih =>
        intro hm
        simp only [Finset.sup_insert]
        exact (hm i (Finset.mem_insert_self i t)).sup
          (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
    exact hgen s hXm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top hsupm.ennreal_toReal.aestronglyMeasurable, hqr]
  have hint : ∀ i ∈ s, ∫⁻ ω, X i ω ^ q ∂μ ≤ B ^ q := by
    intro i hi
    have h := hB i hi
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top (hXm i hi).ennreal_toReal.aestronglyMeasurable, hqr] at h
    have h' : (∫⁻ ω, ‖(X i ω).toReal‖ₑ ^ q ∂μ) ≤ B ^ q := by
      have := ENNReal.rpow_le_rpow h hq.le
      rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one] at this
    simpa only [henorm _ (hX i _)] using h'
  have hpt : ∀ ω, ‖(s.sup (fun i => X i ω)).toReal‖ₑ ^ q ≤ ∑ i ∈ s, X i ω ^ q := by
    intro ω
    rw [henorm _ (hsupfin ω)]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simp [ENNReal.zero_rpow_of_pos hq]
    · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup s hs (fun i => X i ω)
      rw [heq]
      exact Finset.single_le_sum (f := fun i => X i ω ^ q) (fun _ _ => zero_le) hi
  calc (∫⁻ ω, ‖(s.sup (fun i => X i ω)).toReal‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ (∫⁻ ω, ∑ i ∈ s, X i ω ^ q ∂μ) ^ (1 / q) := by
        gcongr with ω; exact hpt ω
    _ = (∑ i ∈ s, ∫⁻ ω, X i ω ^ q ∂μ) ^ (1 / q) := by
        rw [lintegral_finset_sum' s (fun i hi => (hXm i hi).pow_const q)]
    _ ≤ (∑ _i ∈ s, B ^ q) ^ (1 / q) := by
        gcongr with i hi; exact hint i hi
    _ = (s.card : ℝ≥0∞) ^ (1 / q) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- Cauchy in measure is stable under a constant factor. -/
theorem aux_prefix_rraw_cim_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (c : ℝ) (hf : aux_prefix_rraw_CauchyInMeasure μ f) :
    aux_prefix_rraw_CauchyInMeasure μ (fun n ω => c * f n ω) := by
  intro δ hδ η hη
  have hc1 : 0 < |c| + 1 := by positivity
  obtain ⟨n0, hn0⟩ := hf (δ / (|c| + 1)) (div_pos hδ hc1) η hη
  refine ⟨n0, fun n n' hn hn' => le_trans (measure_mono ?_) (hn0 n n' hn hn')⟩
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [← mul_sub, abs_mul] at hω
  rw [div_le_iff₀ hc1]
  nlinarith [abs_nonneg c, abs_nonneg (f n ω - f n' ω)]

/-- `L^p`-Cauchy sequences are Cauchy in measure (Markov). -/
theorem aux_prefix_rraw_cim_of_Lp_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 0 < p) (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' →
      eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) :
    aux_prefix_rraw_CauchyInMeasure μ f := by
  intro δ hδ η hη
  set ε : ℝ := δ * η ^ (1 / p) with hεdef
  have hε : 0 < ε := mul_pos hδ (Real.rpow_pos_of_pos hη _)
  obtain ⟨n0, hn0⟩ := h ε hε
  refine ⟨n0, fun n n' hn hn' => ?_⟩
  have hg : AEStronglyMeasurable (fun ω => |f n ω - f n' ω|) μ :=
    (continuous_abs.comp_aestronglyMeasurable ((hf n).sub (hf n')))
  refine (aux_prefix_rraw_meas_ge_le μ p hp _ hg δ hδ).trans ?_
  have hnorm : eLpNorm (fun ω => |f n ω - f n' ω|) (ENNReal.ofReal p) μ =
      eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ :=
    eLpNorm_congr_norm_ae hg ((hf n).sub (hf n')) (Eventually.of_forall fun ω => by simp)
  rw [hnorm]
  have hpow : eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ ^ p ≤
      ENNReal.ofReal ε ^ p := ENNReal.rpow_le_rpow (hn0 n n' hn hn') hp.le
  have hε_eq : ENNReal.ofReal ε ^ p = ENNReal.ofReal δ ^ p * ENNReal.ofReal η := by
    rw [hεdef, ENNReal.ofReal_mul hδ.le, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hη.le _) hp.le,
      ← Real.rpow_mul hη.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hpos : ENNReal.ofReal δ ^ p ≠ 0 := by
    have : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr this) ENNReal.ofReal_ne_top).ne'
  have htop : ENNReal.ofReal δ ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  rw [ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl htop), mul_comm]
  exact hpow.trans hε_eq.le

end Paper

-- ===== PmrRrawCore =====
/-!
# The literal `Rsc` supremum as a discounted maximum of matched-response atoms

For a prefix at sample scale `m` and sample centre `w`, the literal response-score
set of `primitive_scores` clause (4) is re-indexed by relative depth `r = m - n` and
integer offset `k`.  The shallow part (`r ≤ H`) is a fixed finite supremum; the
deep part is bounded by a discounted sum of box maxima.
-/



open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

variable {d : ℕ}

/-- An integer offset as a spatial vector. -/
def aux_prefix_rraw_kvec (k : Fin d → ℤ) : Vec d := fun i => ((k i : ℤ) : ℝ)

/-- The discount of relative depth `r`. -/
def aux_prefix_rraw_c (s : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(s * (r : ℝ) / 8)))

/-- The literal matched-response atom at relative depth `r` and offset `k`. -/
def aux_prefix_rraw_A (M : GMCModel d) (η : PotentialSample d) (m : ℕ) (w : Vec d)
    (r : ℕ) (k : Fin d → ℤ) : ℝ≥0∞ :=
  aux_psf_Jval M (m - r) η (aux_psf_Rpoint (m - r) w k)

open Classical in
/-- The shallow index set: depths `2 ≤ r ≤ H`, offsets in the annuli `2 ≤ t ≤ r`. -/
def aux_prefix_rraw_G (d H : ℕ) : Finset (ℕ × (Fin d → ℤ)) :=
  ((Finset.Icc 2 H) ×ˢ aux_psf_Rindex d H).filter (fun rk => ∃ t : ℕ, 2 ≤ t ∧ t ≤ rk.1 ∧
    aux_prefix_rraw_kvec rk.2 ∈ cube d (t : ℤ) \ cube d ((t : ℤ) - 1))

/-- The shallow finite supremum. -/
def aux_prefix_rraw_shallow (M : GMCModel d) (s : ℝ) (η : PotentialSample d) (m : ℕ)
    (w : Vec d) (H : ℕ) : ℝ≥0∞ :=
  (aux_prefix_rraw_G d H).sup (fun rk => aux_prefix_rraw_c s rk.1 * aux_prefix_rraw_A M η m w rk.1 rk.2)

/-- The deep discounted sum of box maxima. -/
def aux_prefix_rraw_tail (M : GMCModel d) (s : ℝ) (η : PotentialSample d) (m : ℕ)
    (w : Vec d) (H : ℕ) : ℝ≥0∞ :=
  ∑ r ∈ Finset.Ico (H + 1) (m + 1),
    aux_prefix_rraw_c s r * (aux_psf_Rindex d r).sup (fun k => aux_prefix_rraw_A M η m w r k)

/-- The literal `Rsc` set of `primitive_scores` clause (4). -/
def aux_prefix_rraw_Rset (M : GMCModel d) (s : ℝ) (η : PotentialSample d) (m : ℕ)
    (w : Vec d) : ℝ≥0∞ :=
  sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid n (x - w) ∧ x - w ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) * aux_psf_Jval M n η x}

theorem aux_prefix_rraw_smul_mem_cube_iff (v : Vec d) (n : ℕ) (a : ℤ) :
    ((3 : ℝ) ^ n • v ∈ cube d ((n : ℤ) + a)) ↔ v ∈ cube d a := by
  unfold cube
  rw [Homogenization.mem_openCubeSet_originCube_iff, Homogenization.mem_openCubeSet_originCube_iff]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hz : (3 : ℝ) ^ ((n : ℤ) + a) = (3 : ℝ) ^ n * (3 : ℝ) ^ a := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  refine forall_congr' fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, hz]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hc; push_neg at hc; nlinarith
    · by_contra hc; push_neg at hc; nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

theorem aux_prefix_rraw_Rpoint_sub (n : ℕ) (w : Vec d) (k : Fin d → ℤ) :
    aux_psf_Rpoint n w k - w = (3 : ℝ) ^ n • aux_prefix_rraw_kvec k := by
  funext i
  simp [aux_psf_Rpoint, aux_prefix_rraw_kvec]

theorem aux_prefix_rraw_exists_Rpoint (n : ℕ) (w x : Vec d)
    (hgrid : OnTriadicGrid n (x - w)) : ∃ k : Fin d → ℤ, x = aux_psf_Rpoint n w k := by
  choose k hk using hgrid
  refine ⟨k, funext fun i => ?_⟩
  have := hk i
  simp only [Pi.sub_apply] at this
  simp only [aux_psf_Rpoint]
  linarith

theorem aux_prefix_rraw_mem_Rindex (k : Fin d → ℤ) (t R : ℕ) (htR : t ≤ R)
    (hk : aux_prefix_rraw_kvec k ∈ cube d (t : ℤ)) : k ∈ aux_psf_Rindex d R := by
  rw [aux_psf_Rindex, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  unfold cube at hk
  rw [Homogenization.mem_openCubeSet_originCube_iff] at hk
  obtain ⟨h1, h2⟩ := hk i
  simp only [aux_prefix_rraw_kvec, zpow_natCast] at h1 h2
  have htR' : (3 : ℝ) ^ t ≤ (3 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) htR
  have hpos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hcast : (((3 ^ R : ℤ)) : ℝ) = (3 : ℝ) ^ R := by push_cast; rfl
  constructor
  · have : (-(3 ^ R : ℤ) : ℝ) ≤ ((k i : ℤ) : ℝ) := by
      rw [hcast]; linarith
    exact_mod_cast this
  · have : ((k i : ℤ) : ℝ) ≤ ((3 ^ R : ℤ) : ℝ) := by
      rw [hcast]; linarith
    exact_mod_cast this

theorem aux_prefix_rraw_A_ne_top (M : GMCModel d) (η : PotentialSample d) (m : ℕ)
    (w : Vec d) (r : ℕ) (k : Fin d → ℤ) : aux_prefix_rraw_A M η m w r k ≠ ⊤ :=
  aux_psf_Jval_ne_top M _ η _

theorem aux_prefix_rraw_c_ne_top (s : ℝ) (r : ℕ) : aux_prefix_rraw_c s r ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem aux_prefix_rraw_finset_sup_ne_top {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i, f i ≠ ⊤) : S.sup f ≠ ⊤ := by
  rw [← lt_top_iff_ne_top, Finset.sup_lt_iff (by simp)]
  exact fun j _ => lt_top_iff_ne_top.mpr (hf j)

theorem aux_prefix_rraw_shallow_ne_top (M : GMCModel d) (s : ℝ) (η : PotentialSample d)
    (m : ℕ) (w : Vec d) (H : ℕ) : aux_prefix_rraw_shallow M s η m w H ≠ ⊤ :=
  aux_prefix_rraw_finset_sup_ne_top _ _ fun _ =>
    ENNReal.mul_ne_top (aux_prefix_rraw_c_ne_top s _) (aux_prefix_rraw_A_ne_top M η m w _ _)

theorem aux_prefix_rraw_tail_ne_top (M : GMCModel d) (s : ℝ) (η : PotentialSample d)
    (m : ℕ) (w : Vec d) (H : ℕ) : aux_prefix_rraw_tail M s η m w H ≠ ⊤ := by
  refine ENNReal.sum_ne_top.mpr fun r _ => ENNReal.mul_ne_top (aux_prefix_rraw_c_ne_top s r) ?_
  exact aux_prefix_rraw_finset_sup_ne_top _ _ fun k => aux_prefix_rraw_A_ne_top M η m w r k

/-- The shallow part is attained inside the literal set once the prefix is deep enough. -/
theorem aux_prefix_rraw_shallow_le_Rset (M : GMCModel d) (s : ℝ) (η : PotentialSample d)
    (m : ℕ) (w : Vec d) (H : ℕ) (hHm : H ≤ m) :
    aux_prefix_rraw_shallow M s η m w H ≤ aux_prefix_rraw_Rset M s η m w := by
  classical
  refine Finset.sup_le fun rk hrk => ?_
  obtain ⟨r, k⟩ := rk
  simp only [aux_prefix_rraw_G, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hrk
  obtain ⟨⟨⟨h2r, hrH⟩, _⟩, t, h2t, htr, hann⟩ := hrk
  have hrm : r ≤ m := hrH.trans hHm
  set n : ℕ := m - r with hn
  refine le_sSup ⟨n + t, n, by omega, by omega, aux_psf_Rpoint n w k, ?_, ?_, ?_⟩
  · intro i
    exact ⟨k i, by simp [aux_psf_Rpoint]⟩
  · rw [aux_prefix_rraw_Rpoint_sub]
    have h1 : ((n + t : ℕ) : ℤ) = (n : ℤ) + (t : ℤ) := by push_cast; ring
    rw [h1, add_sub_assoc]
    exact ⟨(aux_prefix_rraw_smul_mem_cube_iff _ n _).mpr hann.1,
      fun h => hann.2 ((aux_prefix_rraw_smul_mem_cube_iff _ n _).mp h)⟩
  · have hcast : (m : ℝ) - (n : ℝ) = (r : ℝ) := by
      rw [hn, Nat.cast_sub hrm]; ring
    simp only [aux_prefix_rraw_c, aux_prefix_rraw_A, ← hn, hcast]

/-- Every literal atom is dominated by the shallow supremum or by the deep sum. -/
theorem aux_prefix_rraw_Rset_le (M : GMCModel d) (s : ℝ) (η : PotentialSample d)
    (m : ℕ) (w : Vec d) (H : ℕ) :
    aux_prefix_rraw_Rset M s η m w ≤
      max (aux_prefix_rraw_shallow M s η m w H) (aux_prefix_rraw_tail M s η m w H) := by
  classical
  refine sSup_le ?_
  rintro v ⟨j, n, hjm, hnj, x, hgrid, hann, rfl⟩
  obtain ⟨k, rfl⟩ := aux_prefix_rraw_exists_Rpoint n w x hgrid
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = m - n := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = j - n := ⟨_, rfl⟩
  have hnr : n = m - r := by omega
  have hcast : (m : ℝ) - (n : ℝ) = (r : ℝ) := by
    rw [hr, Nat.cast_sub (by omega : n ≤ m)]
  rw [aux_prefix_rraw_Rpoint_sub] at hann
  have hj1 : ((j : ℕ) : ℤ) = (n : ℤ) + (t : ℤ) := by omega
  rw [hj1, add_sub_assoc] at hann
  have hannk : aux_prefix_rraw_kvec k ∈ cube d (t : ℤ) \ cube d ((t : ℤ) - 1) :=
    ⟨(aux_prefix_rraw_smul_mem_cube_iff _ n _).mp hann.1,
      fun h => hann.2 ((aux_prefix_rraw_smul_mem_cube_iff _ n _).mpr h)⟩
  have hval : ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
      aux_psf_Jval M n η (aux_psf_Rpoint n w k) =
      aux_prefix_rraw_c s r * aux_prefix_rraw_A M η m w r k := by
    rw [hcast, aux_prefix_rraw_c, aux_prefix_rraw_A, ← hnr]
  rw [hval]
  by_cases hrH : r ≤ H
  · refine le_max_of_le_left ?_
    have hmem : (r, k) ∈ aux_prefix_rraw_G d H := by
      simp only [aux_prefix_rraw_G, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, hrH⟩, aux_prefix_rraw_mem_Rindex k t H (by omega) hannk.1⟩,
        t, by omega, by omega, hannk⟩
    have h := Finset.le_sup (f := fun rk : ℕ × (Fin d → ℤ) => aux_prefix_rraw_c s rk.1 *
      aux_prefix_rraw_A M η m w rk.1 rk.2) hmem
    exact h
  · refine le_max_of_le_right ?_
    have hrmem : r ∈ Finset.Ico (H + 1) (m + 1) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hk : k ∈ aux_psf_Rindex d r := aux_prefix_rraw_mem_Rindex k t r (by omega) hannk.1
    calc aux_prefix_rraw_c s r * aux_prefix_rraw_A M η m w r k
        ≤ aux_prefix_rraw_c s r *
            (aux_psf_Rindex d r).sup (fun k => aux_prefix_rraw_A M η m w r k) := by
          have h := Finset.le_sup (f := fun k => aux_prefix_rraw_A M η m w r k) hk
          gcongr
      _ ≤ aux_prefix_rraw_tail M s η m w H := by
          have h := Finset.single_le_sum (f := fun r => aux_prefix_rraw_c s r *
            (aux_psf_Rindex d r).sup (fun k => aux_prefix_rraw_A M η m w r k))
            (fun _ _ => zero_le) hrmem
          exact h

/-- Real-valued sandwich: the literal coordinate is within the deep sum of the shallow
supremum. -/
theorem aux_prefix_rraw_abs_Rset_sub_shallow_le (M : GMCModel d) (s : ℝ)
    (η : PotentialSample d) (m : ℕ) (w : Vec d) (H : ℕ) (hHm : H ≤ m) :
    |(aux_prefix_rraw_Rset M s η m w).toReal - (aux_prefix_rraw_shallow M s η m w H).toReal| ≤
      (aux_prefix_rraw_tail M s η m w H).toReal := by
  have hS := aux_prefix_rraw_shallow_ne_top M s η m w H
  have hT := aux_prefix_rraw_tail_ne_top M s η m w H
  have hle1 := aux_prefix_rraw_shallow_le_Rset M s η m w H hHm
  have hle2 : aux_prefix_rraw_Rset M s η m w ≤
      aux_prefix_rraw_shallow M s η m w H + aux_prefix_rraw_tail M s η m w H :=
    (aux_prefix_rraw_Rset_le M s η m w H).trans (max_le le_self_add le_add_self)
  have hR : aux_prefix_rraw_Rset M s η m w ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hS, hT⟩) hle2
  have h1 := ENNReal.toReal_mono hR hle1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hS, hT⟩) hle2
  rw [ENNReal.toReal_add hS hT] at h2
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- With `H = 0` the shallow part is empty. -/
theorem aux_prefix_rraw_G_zero : aux_prefix_rraw_G d 0 = ∅ := by
  classical
  unfold aux_prefix_rraw_G
  simp

theorem aux_prefix_rraw_Rset_toReal_le_tail_zero (M : GMCModel d) (s : ℝ)
    (η : PotentialSample d) (m : ℕ) (w : Vec d) :
    (aux_prefix_rraw_Rset M s η m w).toReal ≤ (aux_prefix_rraw_tail M s η m w 0).toReal := by
  have h := aux_prefix_rraw_abs_Rset_sub_shallow_le M s η m w 0 (Nat.zero_le m)
  have h0 : aux_prefix_rraw_shallow M s η m w 0 = 0 := by
    simp [aux_prefix_rraw_shallow, aux_prefix_rraw_G_zero]
  rw [h0, ENNReal.toReal_zero, sub_zero] at h
  exact (le_abs_self _).trans h

end Paper

-- ===== PmrRrawBank =====
/-!
# Measurability, transported atom moments, and the discounted tail bound
-/



open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

variable {d : ℕ}

/-- The literal matched-response atom on the bilateral carrier at bilateral scale `l`
and physical position `y`, read at cutoff `N` (zero before the cutoff reaches `l`). -/
def aux_prefix_rraw_atom [NeZero d] (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d) (N : ℕ) (l : ℤ) (y : Vec d)
    (omega : BilateralField d) : ℝ :=
  if 0 ≤ l + (N : ℤ) then
    (aux_psf_Jval M (l + (N : ℤ)).toNat (eta N omega) ((3 : ℝ) ^ N • y)).toReal
  else 0

/-- The sample atom at relative depth `r` is the bilateral atom at scale `-n0-r`. -/
theorem aux_prefix_rraw_A_eq_atom [NeZero d] (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d) (n0 : ℤ) (z : Vec d)
    (N r : ℕ) (k : Fin d → ℤ) (hN : n0 + (r : ℤ) ≤ (N : ℤ)) (omega : BilateralField d) :
    (aux_prefix_rraw_A M (eta N omega) ((N : ℤ) - n0).toNat ((3 : ℝ) ^ N • z) r k).toReal =
      aux_prefix_rraw_atom M eta N (-n0 - r) (z + (3 : ℝ) ^ (-n0 - r) • aux_prefix_rraw_kvec k)
        omega := by
  unfold aux_prefix_rraw_atom aux_prefix_rraw_A
  rw [if_pos (by omega)]
  have hidx : (-n0 - (r : ℤ) + (N : ℤ)).toNat = ((N : ℤ) - n0).toNat - r := by omega
  have hpow : (3 : ℝ) ^ N * (3 : ℝ) ^ (-n0 - (r : ℤ)) = (3 : ℝ) ^ (((N : ℤ) - n0).toNat - r) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [hidx]
  congr 2
  funext i
  simp only [aux_psf_Rpoint, aux_prefix_rraw_kvec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [← hpow]
  ring

theorem aux_prefix_rraw_measurable_finset_sup {δ ι : Type*} [MeasurableSpace δ]
    (S : Finset ι) (f : ι → δ → ℝ≥0∞) (hf : ∀ i ∈ S, Measurable (f i)) :
    Measurable (fun x => S.sup (fun i => f i x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.sup_insert]
    exact (hf i (Finset.mem_insert_self _ _)).sup'
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem aux_prefix_rraw_Jval_measurable [NeZero d] (M : GMCModel d) (n : ℕ) (x : Vec d) :
    Measurable (fun η : PotentialSample d => aux_psf_Jval M n η x) :=
  aux_lem_prefix_limit_actual_J_meas M n x

theorem aux_prefix_rraw_A_measurable [NeZero d] (M : GMCModel d) (m : ℕ) (w : Vec d)
    (r : ℕ) (k : Fin d → ℤ) :
    Measurable (fun η : PotentialSample d => aux_prefix_rraw_A M η m w r k) :=
  aux_prefix_rraw_Jval_measurable M _ _

theorem aux_prefix_rraw_boxsup_measurable [NeZero d] (M : GMCModel d) (m : ℕ) (w : Vec d)
    (r : ℕ) :
    Measurable (fun η : PotentialSample d =>
      (aux_psf_Rindex d r).sup (fun k => aux_prefix_rraw_A M η m w r k)) :=
  aux_prefix_rraw_measurable_finset_sup _ _ fun k _ => aux_prefix_rraw_A_measurable M m w r k

theorem aux_prefix_rraw_shallow_measurable [NeZero d] (M : GMCModel d) (s : ℝ) (m : ℕ)
    (w : Vec d) (H : ℕ) :
    Measurable (fun η : PotentialSample d => aux_prefix_rraw_shallow M s η m w H) :=
  aux_prefix_rraw_measurable_finset_sup _ _ fun rk _ =>
    (aux_prefix_rraw_A_measurable M m w rk.1 rk.2).const_mul _

theorem aux_prefix_rraw_tail_measurable [NeZero d] (M : GMCModel d) (s : ℝ) (m : ℕ)
    (w : Vec d) (H : ℕ) :
    Measurable (fun η : PotentialSample d => aux_prefix_rraw_tail M s η m w H) :=
  Finset.measurable_sum _ fun r _ => (aux_prefix_rraw_boxsup_measurable M m w r).const_mul _

section Transport

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The potential-sample atom bank transported along the common-scale coupling. -/
theorem aux_prefix_rraw_Jval_eta_eLpNorm_le [NeZero d] (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (q b : ℝ)
    (hbank : ∀ (n : ℕ) (x : Vec d),
      eLpNorm (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal b)
    (N n : ℕ) (x : Vec d) :
    eLpNorm (fun omega => (aux_psf_Jval M n (eta N omega) x).toReal)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal b := by
  have hg : Measurable (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal) :=
    ENNReal.measurable_toReal.comp (aux_prefix_rraw_Jval_measurable M n x)
  have hmap := eLpNorm_map_measure (μ := (chaosSampleLaw M).toMeasure)
    (p := ENNReal.ofReal q) hg.aestronglyMeasurable (prefix_eta_aemeasurable M eta hEta N)
  rw [prefix_eta_law M eta hEta N] at hmap
  rw [show (fun omega => (aux_psf_Jval M n (eta N omega) x).toReal) =
      (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal) ∘ eta N from rfl, ← hmap]
  exact hbank n x

/-- A box maximum of transported atoms costs `card^{1/q}`. -/
theorem aux_prefix_rraw_boxsup_eLpNorm_le [NeZero d] (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (q b : ℝ) (hq : 0 < q)
    (hbank : ∀ (n : ℕ) (x : Vec d),
      eLpNorm (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal b)
    (N m : ℕ) (w : Vec d) (r : ℕ) :
    eLpNorm (fun omega => ((aux_psf_Rindex d r).sup
        (fun k => aux_prefix_rraw_A M (eta N omega) m w r k)).toReal)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ((aux_psf_Rindex d r).card : ℝ≥0∞) ^ (1 / q) * ENNReal.ofReal b := by
  refine aux_prefix_rraw_eLpNorm_finset_sup_le (chaosSampleLaw M).toMeasure
    (aux_psf_Rindex d r) (fun k omega => aux_prefix_rraw_A M (eta N omega) m w r k)
    (fun k omega => aux_prefix_rraw_A_ne_top M _ m w r k) ?_ q hq _ ?_
  · intro k _
    exact (aux_prefix_rraw_A_measurable M m w r k).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)
  · intro k _
    exact aux_prefix_rraw_Jval_eta_eLpNorm_le M eta hEta q b hbank N _ _

/-- The deep discounted sum is bounded in `L^q` by the discounted box costs. -/
theorem aux_prefix_rraw_tail_eLpNorm_le [NeZero d] (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (q b : ℝ) (hq : 1 ≤ q)
    (hbank : ∀ (n : ℕ) (x : Vec d),
      eLpNorm (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal b)
    (N m : ℕ) (w : Vec d) (H : ℕ) :
    eLpNorm (fun omega => (aux_prefix_rraw_tail M s (eta N omega) m w H).toReal)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ∑ r ∈ Finset.Ico (H + 1) (m + 1), aux_prefix_rraw_c s r *
        (((aux_psf_Rindex d r).card : ℝ≥0∞) ^ (1 / q) * ENNReal.ofReal b) := by
  have hq0 : 0 < q := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  let g : ℕ → BilateralField d → ℝ := fun r omega =>
    (aux_prefix_rraw_c s r).toReal *
      ((aux_psf_Rindex d r).sup (fun k => aux_prefix_rraw_A M (eta N omega) m w r k)).toReal
  have hfun : (fun omega => (aux_prefix_rraw_tail M s (eta N omega) m w H).toReal) =
      ∑ r ∈ Finset.Ico (H + 1) (m + 1), g r := by
    funext omega
    rw [Finset.sum_apply]
    unfold aux_prefix_rraw_tail
    rw [ENNReal.toReal_sum fun r _ => ENNReal.mul_ne_top (aux_prefix_rraw_c_ne_top s r)
      (aux_prefix_rraw_finset_sup_ne_top _ _ fun k => aux_prefix_rraw_A_ne_top M _ m w r k)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ENNReal.toReal_mul]
  rw [hfun]
  have hgm : ∀ r ∈ Finset.Ico (H + 1) (m + 1),
      AEStronglyMeasurable (g r) (chaosSampleLaw M).toMeasure := by
    intro r _
    exact (((ENNReal.measurable_toReal.comp (aux_prefix_rraw_boxsup_measurable M m w r)).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).const_mul _).aestronglyMeasurable
  refine (eLpNorm_sum_le hq1).trans (Finset.sum_le_sum fun r _ => ?_)
  have hsmul : g r = (aux_prefix_rraw_c s r).toReal • (fun omega =>
      ((aux_psf_Rindex d r).sup (fun k => aux_prefix_rraw_A M (eta N omega) m w r k)).toReal) := by
    funext omega; simp [g, smul_eq_mul]
  rw [hsmul, eLpNorm_const_smul]
  have hc : ‖(aux_prefix_rraw_c s r).toReal‖ₑ = aux_prefix_rraw_c s r := by
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (aux_prefix_rraw_c_ne_top s r)]
  rw [hc]
  gcongr
  exact aux_prefix_rraw_boxsup_eLpNorm_le M eta hEta q b hq0 hbank N m w r

end Transport

/-- The geometric ratio `ρ = 3^{-(s/8 - d/q)}` of the discounted tail. -/
def aux_prefix_rraw_rho (d : ℕ) (s q : ℝ) : ℝ := (3 : ℝ) ^ (-(s / 8 - (d : ℝ) / q))

/-- The tail constant `3^{d/q} / (1 - ρ)`. -/
def aux_prefix_rraw_K (d : ℕ) (s q : ℝ) : ℝ :=
  (3 : ℝ) ^ ((d : ℝ) / q) / (1 - aux_prefix_rraw_rho d s q)

theorem aux_prefix_rraw_rho_pos (d : ℕ) (s q : ℝ) : 0 < aux_prefix_rraw_rho d s q :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem aux_prefix_rraw_rho_lt_one (d : ℕ) (s q : ℝ) (hq : 0 < q)
    (hsq : 8 * (d : ℝ) < s * q) : aux_prefix_rraw_rho d s q < 1 := by
  unfold aux_prefix_rraw_rho
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  have : (d : ℝ) / q < s / 8 := by
    rw [div_lt_div_iff₀ hq (by norm_num)]; linarith
  linarith

theorem aux_prefix_rraw_K_nonneg (d : ℕ) (s q : ℝ) (hq : 0 < q)
    (hsq : 8 * (d : ℝ) < s * q) : 0 ≤ aux_prefix_rraw_K d s q := by
  unfold aux_prefix_rraw_K
  have := aux_prefix_rraw_rho_lt_one d s q hq hsq
  exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)

theorem aux_prefix_rraw_Rindex_card_le (d r : ℕ) :
    (aux_psf_Rindex d r).card ≤ (3 ^ (r + 1)) ^ d := by
  classical
  rw [aux_psf_Rindex, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  apply Nat.pow_le_pow_left
  rw [Int.card_Icc]
  have h : (3 ^ r : ℤ) + 1 - -(3 ^ r : ℤ) = ((2 * 3 ^ r + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast, pow_succ]
  have : 1 ≤ 3 ^ r := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- One discounted box cost is dominated by the geometric profile. -/
theorem aux_prefix_rraw_term_le (d : ℕ) (s q : ℝ) (hq : 0 < q) (r : ℕ) :
    (3 : ℝ) ^ (-(s * (r : ℝ) / 8)) * (((aux_psf_Rindex d r).card : ℕ) : ℝ) ^ (1 / q) ≤
      (3 : ℝ) ^ ((d : ℝ) / q) * aux_prefix_rraw_rho d s q ^ r := by
  have hcard : (((aux_psf_Rindex d r).card : ℕ) : ℝ) ≤ (3 : ℝ) ^ (((r + 1) * d : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_mul]
    exact_mod_cast aux_prefix_rraw_Rindex_card_le d r
  have h1 : (((aux_psf_Rindex d r).card : ℕ) : ℝ) ^ (1 / q) ≤
      (3 : ℝ) ^ ((((r + 1) * d : ℕ) : ℝ) * (1 / q)) := by
    rw [Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)
  have hrho : aux_prefix_rraw_rho d s q ^ r = (3 : ℝ) ^ (-(s / 8 - (d : ℝ) / q) * (r : ℝ)) := by
    rw [aux_prefix_rraw_rho, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc (3 : ℝ) ^ (-(s * (r : ℝ) / 8)) * (((aux_psf_Rindex d r).card : ℕ) : ℝ) ^ (1 / q)
      ≤ (3 : ℝ) ^ (-(s * (r : ℝ) / 8)) * (3 : ℝ) ^ ((((r + 1) * d : ℕ) : ℝ) * (1 / q)) := by
        gcongr
    _ = (3 : ℝ) ^ ((d : ℝ) / q) * aux_prefix_rraw_rho d s q ^ r := by
        rw [hrho, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        field_simp
        ring

/-- The discounted tail from depth `H + 1` is at most `K ρ^{H+1}`, uniformly in `m`. -/
theorem aux_prefix_rraw_tail_numeric (d : ℕ) (s q : ℝ) (hq : 0 < q)
    (hsq : 8 * (d : ℝ) < s * q) (b : ℝ) (hb : 0 ≤ b) (H m : ℕ) :
    ∑ r ∈ Finset.Ico (H + 1) (m + 1), aux_prefix_rraw_c s r *
        (((aux_psf_Rindex d r).card : ℝ≥0∞) ^ (1 / q) * ENNReal.ofReal b) ≤
      ENNReal.ofReal (aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (H + 1) * b) := by
  have hρ0 := aux_prefix_rraw_rho_pos d s q
  have hρ1 := aux_prefix_rraw_rho_lt_one d s q hq hsq
  have hterm : ∀ r ∈ Finset.Ico (H + 1) (m + 1), aux_prefix_rraw_c s r *
      (((aux_psf_Rindex d r).card : ℝ≥0∞) ^ (1 / q) * ENNReal.ofReal b) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (r : ℝ) / 8)) *
        (((aux_psf_Rindex d r).card : ℕ) : ℝ) ^ (1 / q) * b) := by
    intro r _
    rw [aux_prefix_rraw_c, ← ENNReal.ofReal_natCast,
      ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg (fun r _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ∑ r ∈ Finset.Ico (H + 1) (m + 1), (3 : ℝ) ^ (-(s * (r : ℝ) / 8)) *
        (((aux_psf_Rindex d r).card : ℕ) : ℝ) ^ (1 / q) * b
      ≤ ∑ r ∈ Finset.Ico (H + 1) (m + 1),
          (3 : ℝ) ^ ((d : ℝ) / q) * aux_prefix_rraw_rho d s q ^ r * b := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact mul_le_mul_of_nonneg_right (aux_prefix_rraw_term_le d s q hq r) hb
    _ = (3 : ℝ) ^ ((d : ℝ) / q) * b *
          ∑ r ∈ Finset.Ico (H + 1) (m + 1), aux_prefix_rraw_rho d s q ^ r := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring
    _ ≤ (3 : ℝ) ^ ((d : ℝ) / q) * b *
          (aux_prefix_rraw_rho d s q ^ (H + 1) / (1 - aux_prefix_rraw_rho d s q)) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one hρ0.le hρ1
    _ = aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (H + 1) * b := by
        unfold aux_prefix_rraw_K; ring

end Paper

-- ===== Draw prefix =====
/-! Draw (Sum.inl 3) branch of lem_prefix_limit_actual_coordinate_cauchy: accepted pieces
(T4 cutoff invariance, T3 bank/decay, log-card, sqrt-min, eventually-const, add4) followed by the
exact summand definitions of primitive_scores clause (5). Paper 2746–2763. -/



open Filter MeasureTheory Set
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology


namespace Paper

/-- The fourth (gradient-tail) summand of `primitive_scores` clause (5), with the
clause's `normOn` unfolded verbatim. -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 {d : ℕ} (k : ℕ) (w : Vec d)
    (om : PotentialSample d) : ENNReal :=
  ∑' j : ℕ, if k ≤ j then
    ENNReal.ofReal ((3 : ℝ) ^ k) *
      sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
        v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (om j) x)|}
    else 0

/-- HOLE 1. Unscaling a point of the dilated cube. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_cube_unscale_mem {d : ℕ}
    (a k : ℕ) (w y : Vec d)
    (hy : y ∈ translatedCube d ((k + a : ℕ) : ℤ) (((3 : ℝ) ^ a) • w)) :
    ((3 : ℝ) ^ a)⁻¹ • y ∈ translatedCube d (k : ℤ) w := by
  rw [aux_psf_mem_translatedCube_iff] at hy ⊢
  intro i
  have h := hy i
  have hpos : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hpos' : (3 : ℝ) ^ a ≠ 0 := by linarith
  have hsub : (((3 : ℝ) ^ a)⁻¹ • y) i - w i = ((3 : ℝ) ^ a)⁻¹ * (y i - (((3 : ℝ) ^ a) • w) i) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_comm]
    field_simp [hpos']
  rw [hsub, abs_mul, abs_inv, abs_of_pos hpos]
  have hbound : |y i - (((3 : ℝ) ^ a) • w) i| < ((3 : ℝ) ^ k * ((3 : ℝ) ^ a)) / 2 := by
    have h' := h
    simp only [Pi.smul_apply, smul_eq_mul] at h'
    have h_eq : (3 : ℝ) ^ ((k : ℤ) + (a : ℤ)) = ((3 : ℝ) ^ k) * ((3 : ℝ) ^ a) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
    simpa [h_eq] using h'
  calc
    ((3 : ℝ) ^ a)⁻¹ * |y i - (((3 : ℝ) ^ a) • w) i| < ((3 : ℝ) ^ a)⁻¹ * (((3 : ℝ) ^ k * ((3 : ℝ) ^ a)) / 2) :=
      mul_lt_mul_of_pos_left hbound (by positivity)
    _ = ((3 : ℝ) ^ k) / 2 := by
      field_simp [hpos']

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_cube_unscale_mem' {d : ℕ}
    (a k : ℕ) (w y : Vec d)
    (hy : y ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w)) :
    ((3 : ℝ) ^ a)⁻¹ • y ∈ translatedCube d (k : ℤ) w := by
  rw [aux_psf_mem_translatedCube_iff] at hy ⊢
  intro i
  have h := hy i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hne : ((3 : ℝ) ^ a) ≠ 0 := ne_of_gt h3
  have hsplit : (((3 : ℝ) ^ a)⁻¹ • y) i - w i =
      ((3 : ℝ) ^ a)⁻¹ * (y i - (((3 : ℝ) ^ a) • w) i) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hsplit, abs_mul, abs_inv, abs_of_pos h3, zpow_natCast]
  have hz : (3 : ℝ) ^ (((k + a : ℕ) : ℤ)) = ((3 : ℝ) ^ k) * ((3 : ℝ) ^ a) := by
    rw [zpow_natCast, pow_add]
  rw [hz] at h
  have hQP : ((3 : ℝ) ^ a)⁻¹ * ((3 : ℝ) ^ k * ((3 : ℝ) ^ a)) = (3 : ℝ) ^ k := by
    rw [mul_comm ((3 : ℝ) ^ k) ((3 : ℝ) ^ a), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  calc ((3 : ℝ) ^ a)⁻¹ * |y i - (((3 : ℝ) ^ a) • w) i|
      < ((3 : ℝ) ^ a)⁻¹ * (((3 : ℝ) ^ k * ((3 : ℝ) ^ a)) / 2) :=
        mul_lt_mul_of_pos_left h (inv_pos.mpr h3)
    _ = ((3 : ℝ) ^ a)⁻¹ * ((3 : ℝ) ^ k * ((3 : ℝ) ^ a)) / 2 := by
        rw [← mul_div_assoc]
    _ = ((3 : ℝ) ^ k) / 2 := by rw [hQP]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_tsum_guard_shift
    (f : ℕ → ENNReal) (a k : ℕ) :
    (∑' j : ℕ, if k + a ≤ j then f j else 0) =
      ∑' c : ℕ, if k ≤ c then f (c + a) else 0 := by
  have hinj : Function.Injective (fun c : ℕ => c + a) := fun x y h => Nat.add_right_cancel h
  have hsupp : Function.support (fun j : ℕ => if k + a ≤ j then f j else 0) ⊆
      Set.range (fun c : ℕ => c + a) := by
    intro j hj
    by_cases h : k + a ≤ j
    · exact ⟨j - a, Nat.sub_add_cancel (le_trans (Nat.le_add_left a k) h)⟩
    · exfalso
      have hj' : (if k + a ≤ j then f j else 0) ≠ 0 := hj
      have hz : (if k + a ≤ j then f j else 0) = 0 := if_neg h
      exact hj' hz
  have hmain : (∑' c : ℕ, (fun j : ℕ => if k + a ≤ j then f j else 0) (c + a)) =
      ∑' j : ℕ, (if k + a ≤ j then f j else 0) :=
    Function.Injective.tsum_eq (g := fun c : ℕ => c + a) hinj
      (f := fun j : ℕ => if k + a ≤ j then f j else 0) hsupp
  rw [← hmain]
  apply tsum_congr
  intro c
  simp only [Nat.add_le_add_iff_right]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_grad_term_shift {d : ℕ}
    (om1 om2 : PotentialSample d) (a c : ℕ) (y : Vec d)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x) :
    ENNReal.ofReal |euclideanNorm (shellGradient (om2 (c + a)) (((3 : ℝ) ^ a) • y))| =
      ENNReal.ofReal (((3 : ℝ) ^ a)⁻¹) *
        ENNReal.ofReal |euclideanNorm (shellGradient (om1 c) y)| := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hgrad := aux_lem_prefix_limit_actual_coordinate_cauchy_grad_shift om1 om2 a hrel c y
  calc ENNReal.ofReal |euclideanNorm (shellGradient (om2 (c + a)) (((3 : ℝ) ^ a) • y))|
      = ENNReal.ofReal |euclideanNorm (((3 : ℝ) ^ a)⁻¹ • shellGradient (om1 c) y)| := by
        rw [hgrad]
    _ = ENNReal.ofReal |((3 : ℝ) ^ a)⁻¹ * euclideanNorm (shellGradient (om1 c) y)| := by
        rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr h3)]
    _ = ENNReal.ofReal (((3 : ℝ) ^ a)⁻¹ * euclideanNorm (shellGradient (om1 c) y)) := by
        rw [abs_of_nonneg (mul_nonneg (le_of_lt (inv_pos.mpr h3))
          (euclideanNorm_nonneg (shellGradient (om1 c) y)))]
    _ = ENNReal.ofReal (((3 : ℝ) ^ a)⁻¹) *
          ENNReal.ofReal (euclideanNorm (shellGradient (om1 c) y)) :=
        ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr h3))
    _ = ENNReal.ofReal (((3 : ℝ) ^ a)⁻¹) *
          ENNReal.ofReal |euclideanNorm (shellGradient (om1 c) y)| := by
        rw [abs_of_nonneg (euclideanNorm_nonneg (shellGradient (om1 c) y))]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_grad_normOn_shift_sup {d : ℕ}
    (om1 om2 : PotentialSample d) (a k c : ℕ) (w : Vec d)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x) :
    sSup {v : ENNReal | ∃ x : Vec d,
        x ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w) ∧
        v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (om2 (c + a)) x)|} =
      ENNReal.ofReal (((3 : ℝ) ^ a)⁻¹) *
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
          v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (om1 c) x)|} := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hne : ((3 : ℝ) ^ a) ≠ 0 := ne_of_gt h3
  apply le_antisymm
  · rw [ENNReal.mul_sSup]
    refine sSup_le ?_
    intro b hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hy : ((3 : ℝ) ^ a)⁻¹ • x ∈ translatedCube d (k : ℤ) w :=
      aux_lem_prefix_limit_actual_coordinate_cauchy_cube_unscale_mem' a k w x hx
    have hp := aux_lem_prefix_limit_actual_coordinate_cauchy_grad_term_shift om1 om2 a c
      (((3 : ℝ) ^ a)⁻¹ • x) hrel
    have hx' : ((3 : ℝ) ^ a) • (((3 : ℝ) ^ a)⁻¹ • x) = x := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [hx'] at hp
    rw [hp]
    exact le_iSup₂_of_le _ ⟨((3 : ℝ) ^ a)⁻¹ • x, hy, rfl⟩ le_rfl
  · rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    intro b hb
    obtain ⟨y, hy, rfl⟩ := hb
    have hx : ((3 : ℝ) ^ a) • y ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w) := by
      have hmem := aux_lem_prefix_limit_actual_coordinate_cauchy_smul_mem (d := d)
        (a := (k : ℤ)) (w := w) (x := y) a hy
      simpa using hmem
    rw [← aux_lem_prefix_limit_actual_coordinate_cauchy_grad_term_shift om1 om2 a c y hrel]
    exact le_sSup ⟨((3 : ℝ) ^ a) • y, hx, rfl⟩

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_grad_normOn_shift {d : ℕ}
    (om1 om2 : PotentialSample d) (a k c : ℕ) (w : Vec d)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x) :
    ENNReal.ofReal ((3 : ℝ) ^ (k + a)) *
        sSup {v : ENNReal | ∃ x : Vec d,
          x ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w) ∧
          v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (om2 (c + a)) x)|} =
      ENNReal.ofReal ((3 : ℝ) ^ k) *
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
          v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (om1 c) x)|} := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hne : ((3 : ℝ) ^ a) ≠ 0 := ne_of_gt h3
  rw [aux_lem_prefix_limit_actual_coordinate_cauchy_grad_normOn_shift_sup om1 om2 a k c w hrel,
    ← mul_assoc]
  congr 1
  have harith : ((3 : ℝ) ^ (k + a)) * ((3 : ℝ) ^ a)⁻¹ = (3 : ℝ) ^ k := by
    rw [pow_add, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (3 : ℝ) ^ (k + a) by positivity), harith]

/-- HOLE 2. Shifting the summation index of a guarded `ENNReal` series. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_shift {d : ℕ}
    (om1 om2 : PotentialSample d) (a k : ℕ) (w : Vec d)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 (k + a) (((3 : ℝ) ^ a) • w) om2 =
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w om1 := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4
  rw [aux_lem_prefix_limit_actual_coordinate_cauchy_tsum_guard_shift]
  apply tsum_congr
  intro c
  by_cases h : k ≤ c
  · rw [if_pos h, if_pos h]
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_grad_normOn_shift om1 om2 a k c w hrel
  · rw [if_neg h, if_neg h]
/-- CONSUMER: T4 of the
actual Draw coordinate at `(n, z)` is constant for all cutoffs `N ≥ n.toNat`. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_value_const {d : ℕ}
    (omega : BilateralField d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d) (N : ℕ) (hN : n.toNat ≤ N) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega) =
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((n.toNat : ℤ) - n).toNat
        ((3 : ℝ) ^ n.toNat • z) (eta n.toNat omega) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hk : (((n.toNat + a : ℕ) : ℤ) - n).toNat = ((n.toNat : ℤ) - n).toNat + a := by
    have h0 : (0 : ℤ) ≤ (n.toNat : ℤ) - n := by
      have := Int.self_le_toNat n
      omega
    omega
  have hw : (3 : ℝ) ^ (n.toNat + a) • z = ((3 : ℝ) ^ a) • ((3 : ℝ) ^ n.toNat • z) := by
    rw [smul_smul, pow_add, mul_comm]
  have hrel : ∀ (i : ℕ) (x : Vec d),
      eta (n.toNat + a) omega (i + a) (((3 : ℝ) ^ a) • x) = eta n.toNat omega i x :=
    fun i x =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_eta_shift omega eta hEta n.toNat a i x
  rw [hk, hw]
  exact aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_shift
    (eta n.toNat omega) (eta (n.toNat + a) omega) a _ _ hrel



theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_value_guard_const {d : ℕ}
    (omega : BilateralField d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d) (N : ℕ) (hN : n.toNat ≤ N) :
    (if n ≤ (N : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)).toReal else 0) =
      (if n ≤ ((n.toNat : ℕ) : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((n.toNat : ℤ) - n).toNat
          ((3 : ℝ) ^ n.toNat • z) (eta n.toNat omega)).toReal else 0) := by
  have h0 : n ≤ ((n.toNat : ℕ) : ℤ) := Int.self_le_toNat n
  have h1 : n ≤ (N : ℤ) := le_trans h0 (by exact_mod_cast hN)
  rw [if_pos h1, if_pos h0,
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_value_const omega eta hEta n z N hN]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_le_bank {d : ℕ} (s : ℝ) (k : ℕ) (w : Vec d) (om : PotentialSample d) : ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) * sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧ v = ENNReal.ofReal |om 0 x|} ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * aux_prefix_bank_maxObs 0 k w om) := by
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  apply mul_le_mul_right
  apply aux_psf_normOn_le_of_le k w (fun x => om 0 x) (aux_prefix_bank_maxObs 0 k w om)
  intro x hx
  have h := aux_prefix_bank_le_maxObs 0 k (Nat.zero_le k) w x om hx
  have hnn := euclideanNorm_nonneg (shellGradient (om 0) x)
  simp only [pow_zero, one_mul] at h
  linarith

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_rpow_neg_mul_linear_tendsto (s A B : ℝ) (hs : 0 < s) : Tendsto (fun k : ℕ => (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (A + B * (k : ℝ))) atTop (𝓝 0) := by
  set c : ℝ := (s / 8) * Real.log 3 with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    exact mul_pos (div_pos hs (by norm_num)) (Real.log_pos (by norm_num))
  have hcne : c ≠ 0 := ne_of_gt hc
  have hu : Tendsto (fun k : ℕ => c * (k : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hc (tendsto_natCast_atTop_atTop (R := ℝ))
  have h1 : Tendsto (fun k : ℕ => Real.exp (-(c * (k : ℝ)))) atTop (𝓝 0) := by
    exact
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hu
  have h2 : Tendsto (fun k : ℕ => (c * (k : ℝ)) ^ 1 * Real.exp (-(c * (k : ℝ)))) atTop (𝓝 0) := by
    exact
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have h4 : Tendsto (fun k : ℕ => A * Real.exp (-(c * (k : ℝ)))) atTop (𝓝 (A * 0)) :=
    h1.const_mul A
  have h3 : Tendsto (fun k : ℕ => (B / c) * ((c * (k : ℝ)) ^ 1 * Real.exp (-(c * (k : ℝ)))))
      atTop (𝓝 ((B / c) * 0)) :=
    h2.const_mul (B / c)
  have h5 : Tendsto (fun k : ℕ => A * Real.exp (-(c * (k : ℝ)))
        + (B / c) * ((c * (k : ℝ)) ^ 1 * Real.exp (-(c * (k : ℝ)))))
      atTop (𝓝 (A * 0 + (B / c) * 0)) :=
    h4.add h3
  have key : (fun k : ℕ => (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (A + B * (k : ℝ)))
      = (fun k : ℕ => A * Real.exp (-(c * (k : ℝ)))
        + (B / c) * ((c * (k : ℝ)) ^ 1 * Real.exp (-(c * (k : ℝ))))) := by
    funext k
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hexp : Real.log 3 * (-(s / 8) * (k : ℝ)) = -(c * (k : ℝ)) := by
      rw [hc_def]; ring
    rw [hexp, pow_one]
    field_simp
  rw [key]
  simpa using h5

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_log_cells_le (d L : ℕ) : Real.log (2 * ((aux_psf_cells d L).card : ℝ)) ≤ ((d * (L + 1) + 1 : ℕ) : ℝ) * Real.log 3 := by
  rw [aux_psf_cells_card]
  have h : 2 * (2 * 3 ^ L + 1) ^ d ≤ 3 ^ (d * (L + 1) + 1) := by
    have h1 : 2 * 3 ^ L + 1 ≤ 3 ^ (L + 1) := by
      rw [pow_succ]
      have : 1 ≤ 3 ^ L := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)
      nlinarith
    have h2 : (2 * 3 ^ L + 1) ^ d ≤ (3 ^ (L + 1)) ^ d := Nat.pow_le_pow_left h1 d
    rw [← pow_mul] at h2
    rw [mul_comm (L + 1) d] at h2
    rw [pow_succ]
    nlinarith [h2, Nat.zero_le (3 ^ (d * (L + 1)))]
  have hcast : (2 * (2 * 3 ^ L + 1 : ℝ) ^ d) ≤ (3 : ℝ) ^ (d * (L + 1) + 1) := by
    have h' : (2 * (2 * 3 ^ L + 1) ^ d : ℝ) ≤ ((3 : ℕ) ^ (d * (L + 1) + 1) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith [h']
  rw [← Real.log_pow]
  push_cast
  apply Real.log_le_log
  · positivity
  · exact hcast

theorem aux_sqrt_sub_sqrt_le_of_le (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) :
    Real.sqrt y - Real.sqrt x ≤ Real.sqrt (y - x) := by
  have hsub : 0 ≤ y - x := sub_nonneg.mpr h
  have hbound : 0 ≤ Real.sqrt x + Real.sqrt (y - x) :=
    add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (y - x))
  have key : Real.sqrt y ≤ Real.sqrt x + Real.sqrt (y - x) := by
    rw [Real.sqrt_le_left hbound]
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hsub, Real.sqrt_nonneg x, Real.sqrt_nonneg (y - x),
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (y - x))]
  linarith

theorem aux_sqrt_abs_sub_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  rcases le_total x y with h | h
  · have h1 : |Real.sqrt x - Real.sqrt y| = Real.sqrt y - Real.sqrt x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.sqrt_le_sqrt h)), neg_sub]
    have h2 : |x - y| = y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    rw [h1, h2]
    exact aux_sqrt_sub_sqrt_le_of_le x y hx h
  · have h1 : |Real.sqrt x - Real.sqrt y| = Real.sqrt x - Real.sqrt y := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt h))]
    have h2 : |x - y| = x - y := by rw [abs_of_nonneg (sub_nonneg.mpr h)]
    rw [h1, h2]
    exact aux_sqrt_sub_sqrt_le_of_le y x hy h

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_sqrt_min_one_sub (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : |Real.sqrt (min a 1) - Real.sqrt (min b 1)| ≤ Real.sqrt |a - b| := by
  have hx : 0 ≤ min a 1 := le_min ha zero_le_one
  have hy : 0 ≤ min b 1 := le_min hb zero_le_one
  have hxy : |min a 1 - min b 1| ≤ |a - b| := by
    have h := abs_min_sub_min_le_max a 1 b 1
    rw [sub_self, abs_zero] at h
    exact le_trans h (max_le (le_refl _) (abs_nonneg _))
  calc |Real.sqrt (min a 1) - Real.sqrt (min b 1)|
      ≤ Real.sqrt |min a 1 - min b 1| := aux_sqrt_abs_sub_le (min a 1) (min b 1) hx hy
    _ ≤ Real.sqrt |a - b| := Real.sqrt_le_sqrt hxy

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Lp_cauchy_of_eventually_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ) (v : ℕ → Ω → ℝ) (N0 : ℕ) (hconst : ∀ᵐ ω ∂μ, ∀ N : ℕ, N0 ≤ N → v N ω = v N0 ω) (phi : ℕ → ℕ) (hphi : StrictMono phi) (ε : ℝ) (hε : 0 < ε) : ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' → eLpNorm (fun ω => v (phi n) ω - v (phi n') ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε := by
  refine ⟨N0, fun n n' hn hn' => ?_⟩
  have h1 : N0 ≤ phi n := hn.trans (hphi.id_le n)
  have h1' : N0 ≤ phi n' := hn'.trans (hphi.id_le n')
  have hz : (fun ω => v (phi n) ω - v (phi n') ω) =ᵐ[μ] 0 :=
    hconst.mono (fun ω h => by
      simp only [Pi.zero_apply]
      rw [h _ h1, h _ h1', sub_self])
  rw [eLpNorm_congr_ae hz, eLpNorm_zero]
  exact zero_le

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_add4_Lp_cauchy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ) (hp : 1 ≤ p) (v a b c e : ℕ → Ω → ℝ) (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : ∀ n, AEStronglyMeasurable (b n) μ) (hc : ∀ n, AEStronglyMeasurable (c n) μ) (he : ∀ n, AEStronglyMeasurable (e n) μ) (hsum : ∀ n, ∀ᵐ ω ∂μ, v n ω = a n ω + b n ω + c n ω + e n ω) (hca : ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' → eLpNorm (fun ω => a n ω - a n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) (hcb : ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' → eLpNorm (fun ω => b n ω - b n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) (hcc : ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' → eLpNorm (fun ω => c n ω - c n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) (hce : ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' → eLpNorm (fun ω => e n ω - e n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) (ε : ℝ) (hε : 0 < ε) : ∃ n0 : ℕ, ∀ n n' : ℕ, n0 ≤ n → n0 ≤ n' → eLpNorm (fun ω => v n ω - v n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε := by
    have hp1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp
    have hε4 : 0 < ε / 4 := by linarith
    obtain ⟨na, hna⟩ := hca (ε/4) hε4
    obtain ⟨nb, hnb⟩ := hcb (ε/4) hε4
    obtain ⟨nc, hnc⟩ := hcc (ε/4) hε4
    obtain ⟨ne, hne⟩ := hce (ε/4) hε4
    refine ⟨max (max na nb) (max nc ne), ?_⟩
    intro n n' hn hn'
    have hna_n : na ≤ n := le_trans (le_trans (le_max_left na nb) (le_max_left _ _)) hn
    have hna_n' : na ≤ n' := le_trans (le_trans (le_max_left na nb) (le_max_left _ _)) hn'
    have hnb_n : nb ≤ n := le_trans (le_trans (le_max_right na nb) (le_max_left _ _)) hn
    have hnb_n' : nb ≤ n' := le_trans (le_trans (le_max_right na nb) (le_max_left _ _)) hn'
    have hnc_n : nc ≤ n := le_trans (le_trans (le_max_left nc ne) (le_max_right _ _)) hn
    have hnc_n' : nc ≤ n' := le_trans (le_trans (le_max_left nc ne) (le_max_right _ _)) hn'
    have hne_n : ne ≤ n := le_trans (le_trans (le_max_right nc ne) (le_max_right _ _)) hn
    have hne_n' : ne ≤ n' := le_trans (le_trans (le_max_right nc ne) (le_max_right _ _)) hn'
    have hA : eLpNorm (fun ω => a n ω - a n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (ε/4) :=
      hna n n' hna_n hna_n'
    have hB : eLpNorm (fun ω => b n ω - b n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (ε/4) :=
      hnb n n' hnb_n hnb_n'
    have hC : eLpNorm (fun ω => c n ω - c n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (ε/4) :=
      hnc n n' hnc_n hnc_n'
    have hE : eLpNorm (fun ω => e n ω - e n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (ε/4) :=
      hne n n' hne_n hne_n'
    have hAB : AEStronglyMeasurable ((fun ω => a n ω - a n' ω) + (fun ω => b n ω - b n' ω)) μ :=
      ((ha n).sub (ha n')).add ((hb n).sub (hb n'))
    have hCE : AEStronglyMeasurable ((fun ω => c n ω - c n' ω) + (fun ω => e n ω - e n' ω)) μ :=
      ((hc n).sub (hc n')).add ((he n).sub (he n'))
    have hae : (fun ω => v n ω - v n' ω) =ᶠ[ae μ]
        ((fun ω => a n ω - a n' ω) + (fun ω => b n ω - b n' ω))
          + ((fun ω => c n ω - c n' ω) + (fun ω => e n ω - e n' ω)) := by
      filter_upwards [hsum n, hsum n'] with ω hv hv'
      rw [hv, hv']
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [eLpNorm_congr_ae hae]
    calc
      eLpNorm (((fun ω => a n ω - a n' ω) + (fun ω => b n ω - b n' ω))
          + ((fun ω => c n ω - c n' ω) + (fun ω => e n ω - e n' ω))) (ENNReal.ofReal p) μ
          ≤ eLpNorm ((fun ω => a n ω - a n' ω) + (fun ω => b n ω - b n' ω)) (ENNReal.ofReal p) μ
            + eLpNorm ((fun ω => c n ω - c n' ω) + (fun ω => e n ω - e n' ω)) (ENNReal.ofReal p) μ :=
            eLpNorm_add_le hp1
      _ ≤ (eLpNorm (fun ω => a n ω - a n' ω) (ENNReal.ofReal p) μ
            + eLpNorm (fun ω => b n ω - b n' ω) (ENNReal.ofReal p) μ)
            + (eLpNorm (fun ω => c n ω - c n' ω) (ENNReal.ofReal p) μ
            + eLpNorm (fun ω => e n ω - e n' ω) (ENNReal.ofReal p) μ) :=
            add_le_add (eLpNorm_add_le hp1)
                       (eLpNorm_add_le hp1)
      _ ≤ (ENNReal.ofReal (ε/4) + ENNReal.ofReal (ε/4))
            + (ENNReal.ofReal (ε/4) + ENNReal.ofReal (ε/4)) :=
            add_le_add (add_le_add hA hB) (add_le_add hC hE)
      _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ ε/4) (by linarith : (0:ℝ) ≤ ε/4),
                ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ ε/4 + ε/4) (by linarith : (0:ℝ) ≤ ε/4 + ε/4)]
            congr 1
            ring

/-- The third summand of primitive_scores clause (5), normOn unfolded verbatim. -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 {d : ℕ} (s : ℝ) (k : ℕ) (w : Vec d)
    (om : PotentialSample d) : ENNReal :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
    sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
      v = ENNReal.ofReal |om 0 x|}

/-- The second summand of primitive_scores clause (5), normOn unfolded verbatim. -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 {d : ℕ} (s : ℝ) (k : ℕ) (w : Vec d)
    (om : PotentialSample d) : ENNReal :=
  sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
        u = ENNReal.ofReal |shellBlock k j om x|}}

/-- The first summand of primitive_scores clause (5) (discounted capped J-atoms on the
annular triadic grid), with `J` unfolded verbatim. -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 {d : ℕ} [NeZero d] (M : GMCModel d)
    (s : ℝ) (k : ℕ) (z : Vec d) (om : PotentialSample d) : ENNReal :=
  sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
      (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
        u = ENNReal.ofReal (section6Response M l l om x e)}) 1) ^ (1 / 2 : ℝ)}

/-- Clause (5) of primitive_scores splits the Draw score into the four summands. -/
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dsc_eq_sum {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (om : PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Prop)
    (h : primitive_scores d M s eps om Fsc Psc Rsc Dsc Zsc g) (k : ℕ) (z : Vec d) :
    Dsc k z = aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k z om +
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k z om +
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k z om +
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k z om := by
  obtain ⟨_, _, _, _, _, _, _, hD, _⟩ := h
  rw [hD k z]
  rfl

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_toReal_le {d : ℕ} (s : ℝ) (k : ℕ)
    (w : Vec d) (om : PotentialSample d) :
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w om).toReal ≤
      (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * aux_prefix_bank_maxObs 0 k w om := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3
  have h := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_le_bank s k w om
  calc (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
          v = ENNReal.ofReal |om 0 x|}).toReal
      ≤ (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) *
          aux_prefix_bank_maxObs 0 k w om)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * aux_prefix_bank_maxObs 0 k w om :=
        ENNReal.toReal_ofReal
          (mul_nonneg (by positivity) (prefix_bank_maxObs_nonneg 0 k w om))

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_even_moment_log {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N i n : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    let b : ℝ := (q : ℝ) + 1 + Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ))
    (∫⁻ omega : BilateralField d,
      ENNReal.ofReal
        (((aux_prefix_bank_maxObs i n z (eta N omega) /
          aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
          ∂(chaosSampleLaw M).toMeasure) ≤
      2 * ENNReal.ofReal (b ^ q) := by
  dsimp only
  let F : PotentialSample d → ENNReal := fun omega =>
    ENNReal.ofReal (((aux_prefix_bank_maxObs i n z omega / aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
  have hF : Measurable F :=
    ((((prefix_bank_maxObs_measurable i n z).div_const _).pow_const _).pow_const _).ennreal_ofReal
  calc (∫⁻ omega, F (eta N omega) ∂(chaosSampleLaw M).toMeasure)
      = ∫⁻ p, F p ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure :=
        (lintegral_map' hF.aemeasurable (prefix_eta_aemeasurable M eta hEta N)).symm
    _ = ∫⁻ p, F p ∂M.P.toMeasure := by rw [prefix_eta_law M eta hEta N]
    _ ≤ 2 * ENNReal.ofReal (((q : ℝ) + 1 + Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ))) ^ q) := by
        simpa using prefix_bank_even_moment_log M i n z q hq

/-- Capped square root of a matched-response atom (first summand of clause (5)). -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt (a : ℝ≥0∞) : ℝ≥0∞ :=
  (min a 1) ^ (1 / 2 : ℝ)

/-- The T1 discount of relative depth `r`. -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_c1 (s : ℝ) (r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * (r : ℝ)))

/-- The shallow finite supremum of the Draw summand T1 (relative depths `2 ≤ r ≤ H`),
indexed exactly like the Rraw shallow part `aux_prefix_rraw_shallow`. -/
def aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow {d : ℕ} (M : GMCModel d)
    (s : ℝ) (η : PotentialSample d) (m : ℕ) (w : Vec d) (H : ℕ) : ℝ≥0∞ :=
  (aux_prefix_rraw_G d H).sup (fun rk =>
    aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s rk.1 *
      aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt (aux_prefix_rraw_A M η m w rk.1 rk.2))

-- from flash order fg_t1_sup_sub
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_abs_sup'_sub_le {ι : Type*}
    (S : Finset ι) (hS : S.Nonempty) (a b : ι → ℝ) :
    |S.sup' hS a - S.sup' hS b| ≤ ∑ i ∈ S, |a i - b i| := by
  rw [abs_sub_le_iff]
  constructor
  · obtain ⟨i, hi, hia⟩ := Finset.exists_mem_eq_sup' hS a
    have h1 : S.sup' hS a - S.sup' hS b ≤ a i - b i := by
      rw [hia]
      have : b i ≤ S.sup' hS b := Finset.le_sup' b hi
      linarith
    calc S.sup' hS a - S.sup' hS b ≤ a i - b i := h1
      _ ≤ |a i - b i| := le_abs_self _
      _ ≤ ∑ j ∈ S, |a j - b j| :=
          Finset.single_le_sum (f := fun j => |a j - b j|) (fun j _ => abs_nonneg _) hi
  · obtain ⟨i, hi, hib⟩ := Finset.exists_mem_eq_sup' hS b
    have h1 : S.sup' hS b - S.sup' hS a ≤ b i - a i := by
      rw [hib]
      have : a i ≤ S.sup' hS a := Finset.le_sup' a hi
      linarith
    calc S.sup' hS b - S.sup' hS a ≤ b i - a i := h1
      _ ≤ |b i - a i| := le_abs_self _
      _ = |a i - b i| := abs_sub_comm _ _
      _ ≤ ∑ j ∈ S, |a j - b j| :=
          Finset.single_le_sum (f := fun j => |a j - b j|) (fun j _ => abs_nonneg _) hi

-- from flash order fg_t1_tim_sqrt_dom
theorem aux_exists_le_of_abs_le_sum_sqrt {ι : Type*} (S : Finset ι) {ε : ℝ} (hε : 0 < ε)
    {a : ι → ℝ} {z : ℝ} (hz : |z| ≤ ∑ i ∈ S, Real.sqrt (a i)) (hεz : ε ≤ |z|) :
    ∃ i ∈ S, (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ a i := by
  by_contra h
  have hlt : ∀ i ∈ S, a i < (ε / ((S.card : ℝ) + 1)) ^ 2 := by
    intro i hi
    by_contra hlti
    exact h ⟨i, hi, le_of_not_gt hlti⟩
  have hsqrt : ∀ i ∈ S, Real.sqrt (a i) < ε / ((S.card : ℝ) + 1) := by
    intro i hi
    exact (Real.sqrt_lt' (div_pos hε (by positivity))).mpr (hlt i hi)
  have hsum : ∑ i ∈ S, Real.sqrt (a i) < ε := by
    calc ∑ i ∈ S, Real.sqrt (a i) ≤ ∑ _i ∈ S, ε / ((S.card : ℝ) + 1) :=
          Finset.sum_le_sum (fun i hi => le_of_lt (hsqrt i hi))
      _ = (S.card : ℝ) * (ε / ((S.card : ℝ) + 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ < ε := by
            have hpos : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
            have hδ : ((S.card : ℝ) + 1) * (ε / ((S.card : ℝ) + 1)) = ε := by
              rw [mul_comm, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
            have hlt' := mul_lt_mul_of_pos_right (lt_add_one ((S.card : ℝ))) (div_pos hε hpos)
            rwa [hδ] at hlt'
  linarith

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_tim_of_sqrt_dom {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (S : Finset ι)
    (f : ι → ℕ → Ω → ℝ) (g : ι → Ω → ℝ)
    (hf : ∀ i ∈ S, TendstoInMeasure μ (f i) atTop (g i))
    (F : ℕ → Ω → ℝ) (G : Ω → ℝ) (N0 : ℕ)
    (hdom : ∀ n, N0 ≤ n → ∀ᵐ ω ∂μ,
      |F n ω - G ω| ≤ ∑ i ∈ S, Real.sqrt |f i n ω - g i ω|) :
    TendstoInMeasure μ F atTop G := by
    refine (MeasureTheory.tendstoInMeasure_iff_dist (μ := μ)).mpr ?_
    intro ε hε
    have hκpos : (0 : ℝ) < (ε / ((S.card : ℝ) + 1)) ^ 2 := by
      have hpos : (0 : ℝ) < ε / ((S.card : ℝ) + 1) := div_pos hε (by positivity)
      exact pow_pos hpos 2
    have hf_dist : ∀ i ∈ S, Tendsto
        (fun n => μ {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)}) atTop (𝓝 0) := by
      intro i hi
      exact ((MeasureTheory.tendstoInMeasure_iff_dist (μ := μ)).mp (hf i hi)) _ hκpos
    have hsum : Tendsto (fun n => ∑ i ∈ S,
        μ {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)}) atTop (𝓝 0) := by
      have h := tendsto_finset_sum
        (f := fun i n => μ {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)})
        (a := fun _ : ι => (0 : ℝ≥0∞)) S (fun i hi => hf_dist i hi)
      simpa only [Finset.sum_const_zero] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℕ => (0 : ℝ≥0∞))
      (h := fun n => ∑ i ∈ S, μ {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)})
      tendsto_const_nhds hsum ?_ ?_
    · exact Eventually.of_forall (fun n => zero_le)
    · refine eventually_atTop.mpr ⟨N0, fun n hn => ?_⟩
      have hnull : μ {ω : Ω | ¬ |F n ω - G ω| ≤ ∑ i ∈ S, Real.sqrt |f i n ω - g i ω|} = 0 :=
        MeasureTheory.ae_iff.mp (hdom n hn)
      have hsub : {ω : Ω | ε ≤ dist (F n ω) (G ω)} ⊆
          ({ω : Ω | ¬ |F n ω - G ω| ≤ ∑ i ∈ S, Real.sqrt |f i n ω - g i ω|} ∪
            ⋃ i ∈ S, {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)}) := by
        intro ω hω
        by_cases hP : |F n ω - G ω| ≤ ∑ i ∈ S, Real.sqrt |f i n ω - g i ω|
        · have hz : ε ≤ |F n ω - G ω| := by change ε ≤ dist (F n ω) (G ω) at hω; rw [Real.dist_eq] at hω; exact hω
          obtain ⟨i, hiS, hκ⟩ := aux_exists_le_of_abs_le_sum_sqrt S hε hP hz
          refine Set.mem_union_right _ ?_
          rw [Set.mem_iUnion₂]
          exact ⟨i, hiS, by change (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω); rw [Real.dist_eq]; exact hκ⟩
        · exact Set.mem_union_left _ hP
      calc μ {ω : Ω | ε ≤ dist (F n ω) (G ω)}
          ≤ μ ({ω : Ω | ¬ |F n ω - G ω| ≤ ∑ i ∈ S, Real.sqrt |f i n ω - g i ω|} ∪
              ⋃ i ∈ S, {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)}) :=
            measure_mono hsub
        _ ≤ μ {ω : Ω | ¬ |F n ω - G ω| ≤ ∑ i ∈ S, Real.sqrt |f i n ω - g i ω|} +
              μ (⋃ i ∈ S, {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)}) :=
            measure_union_le _ _
        _ ≤ 0 + ∑ i ∈ S, μ {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)} :=
            add_le_add (le_of_eq hnull)
              (measure_biUnion_finset_le S
                (fun i => {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)}))
        _ = ∑ i ∈ S, μ {ω : Ω | (ε / ((S.card : ℝ) + 1)) ^ 2 ≤ dist (f i n ω) (g i ω)} :=
            zero_add _

-- from flash order fg_t1_shallow_le
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_le_Dt1 {d : ℕ} [NeZero d] (M : GMCModel d)
    (s : ℝ) (η : PotentialSample d) (m : ℕ) (w : Vec d) (H : ℕ) (hHm : H ≤ m) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H ≤ aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η := by
  classical
  refine Finset.sup_le fun rk hrk => ?_
  obtain ⟨r, k⟩ := rk
  simp only [aux_prefix_rraw_G, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hrk
  obtain ⟨⟨⟨h2r, hrH⟩, _⟩, t, h2t, htr, hann⟩ := hrk
  have hrm : r ≤ m := hrH.trans hHm
  set n : ℕ := m - r with hn
  refine le_sSup ⟨n + t, n, by omega, by omega, by omega, aux_psf_Rpoint n w k, ?_, ?_, ?_⟩
  · intro i
    exact ⟨k i, by simp [aux_psf_Rpoint]⟩
  · rw [aux_prefix_rraw_Rpoint_sub]
    have h1 : ((n + t : ℕ) : ℤ) = (n : ℤ) + (t : ℤ) := by push_cast; ring
    rw [h1, add_sub_assoc]
    exact ⟨(aux_prefix_rraw_smul_mem_cube_iff _ n _).mpr hann.1,
      fun h => hann.2 ((aux_prefix_rraw_smul_mem_cube_iff _ n _).mp h)⟩
  · have hcast : (m : ℝ) - (n : ℝ) = (r : ℝ) := by
      rw [hn, Nat.cast_sub hrm]; ring
    simp only [aux_lem_prefix_limit_actual_coordinate_cauchy_c1,
      aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt, aux_prefix_rraw_A,
      aux_psf_Jval, ← hn, hcast]

-- from flash order fg_t1_abs_sandwich
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_abs_Dt1_sub_T1shallow_le {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (η : PotentialSample d) (m : ℕ) (w : Vec d) (H : ℕ)
    (hle1 : aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H ≤ aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η)
    (hle2 : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η ≤
      max (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H) (aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s (H + 1))) :
    |(aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η).toReal - (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H).toReal| ≤
      (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)) := by
  set S := aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H with hSdef
  set D := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η with hDdef
  set c : ℝ≥0∞ := aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s (H + 1) with hcdef
  have hcne : c ≠ ⊤ := by rw [hcdef]; exact ENNReal.ofReal_ne_top
  have hcto : c.toReal = (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)) := by
    rw [hcdef, aux_lem_prefix_limit_actual_coordinate_cauchy_c1]
    exact ENNReal.toReal_ofReal (by positivity)
  rcases eq_or_ne S ⊤ with hStop | hsne
  · have hDtop : D = ⊤ := by rw [← top_le_iff, ← hStop]; exact hle1
    rw [hStop, hDtop, ENNReal.toReal_top]
    simp only [sub_self, abs_zero]
    positivity
  · have hDle : D ≤ S + c := hle2.trans (max_le le_self_add le_add_self)
    have hScne : S + c ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hsne, hcne⟩
    have hDne : D ≠ ⊤ := ne_top_of_le_ne_top hScne hDle
    have hSD : S.toReal ≤ D.toReal := ENNReal.toReal_mono hDne hle1
    have hDSc : D.toReal ≤ S.toReal + c.toReal := by
      have h := ENNReal.toReal_mono hScne hDle
      rw [ENNReal.toReal_add hsne hcne] at h
      exact h
    rw [abs_of_nonneg (sub_nonneg.mpr hSD)]
    linarith [hDSc, hcto]

-- from flash order fg_t1_toReal_sup
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_toReal_finset_sup {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ≥0∞) (hf : ∀ i ∈ S, f i ≠ ⊤) :
    (S.sup f).toReal = S.sup' hS (fun i => (f i).toReal) := by
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup S hS f
  rw [hsup]
  apply le_antisymm
  · exact Finset.le_sup' (fun i => (f i).toReal) hi
  · refine Finset.sup'_le hS (fun i => (f i).toReal) (fun j hj => ?_)
    exact ENNReal.toReal_mono (hf i hi) (hsup ▸ Finset.le_sup hj)

-- from flash order fg_t1_capsqrt_real
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt_real_sub_le (c a b : ℝ) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (ha : 0 ≤ a) :
    |c * Real.sqrt (min a 1) - c * Real.sqrt (min (max b 0) 1)| ≤ Real.sqrt |a - b| := by
  have hmax : |a - max b 0| ≤ |a - b| := by
    rcases le_total 0 b with hb | hb
    · rw [max_eq_left hb]
    · rw [max_eq_right hb, sub_zero, abs_of_nonneg ha]
      rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith
  calc |c * Real.sqrt (min a 1) - c * Real.sqrt (min (max b 0) 1)|
      = c * |Real.sqrt (min a 1) - Real.sqrt (min (max b 0) 1)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    _ ≤ |Real.sqrt (min a 1) - Real.sqrt (min (max b 0) 1)| :=
        mul_le_of_le_one_left (abs_nonneg _) hc1
    _ ≤ Real.sqrt |a - max b 0| :=
        aux_lem_prefix_limit_actual_coordinate_cauchy_sqrt_min_one_sub a (max b 0) ha
          (le_max_right b 0)
    _ ≤ Real.sqrt |a - b| := Real.sqrt_le_sqrt hmax

-- from flash order fg_draw_t3_eta_eLpNorm
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_eLpNorm_linear {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (hmom : ∀ (N i n : ℕ) (z : Vec d) (q : ℕ), 1 ≤ q →
      (∫⁻ omega : BilateralField d,
        ENNReal.ofReal
          (((aux_prefix_bank_maxObs i n z (eta N omega) /
            aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
            ∂(chaosSampleLaw M).toMeasure) ≤
        2 * ENNReal.ofReal (((q : ℝ) + 1 +
          Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ))) ^ q))
    (N i n : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n z (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) := by
  have hσ := aux_psf_sigma_pos M
  have hpoint : ∀ omega : BilateralField d,
      ‖aux_prefix_bank_maxObs i n z (eta N omega)‖ ≤
        aux_psf_sigma M *
          ‖aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M‖ := by
    intro omega
    have hb := prefix_bank_maxObs_nonneg i n z (eta N omega)
    have hdiv : 0 ≤ aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M :=
      div_nonneg hb hσ.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb, abs_of_nonneg hdiv,
      mul_div_cancel₀ _ hσ.ne']
  obtain ⟨k0, hk0⟩ := aux_psf_cells_nonempty d (n - i)
  have hcard1 : (1 : ℝ) ≤ ((aux_psf_cells d (n - i)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨k0, hk0⟩
  have hb1 : 1 ≤ (q : ℝ) + 1 +
      Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)) := by
    have hlog : 0 ≤ Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)) :=
      Real.log_nonneg (by linarith)
    have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hY : eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) := by
    have hp0 : ((2 * q : ℕ) : ENNReal) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hptop : ((2 * q : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top (2 * q)
    have hm := ((prefix_bank_maxObs_measurable i n z).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
    have hmdiv : AEStronglyMeasurable (fun omega : BilateralField d =>
        aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M)
        (chaosSampleLaw M).toMeasure := by
      simp only [div_eq_mul_inv]
      exact hm.mul_const _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hmdiv]
    have hrewrite : (∫⁻ omega : BilateralField d,
        ‖aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M‖ₑ ^
          (((2 * q : ℕ) : ENNReal).toReal) ∂(chaosSampleLaw M).toMeasure) =
        ∫⁻ omega : BilateralField d,
          ENNReal.ofReal
            (((aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
          ∂(chaosSampleLaw M).toMeasure := by
      apply lintegral_congr
      intro omega
      exact prefix_even_enorm_identity _
        (div_nonneg (prefix_bank_maxObs_nonneg i n z (eta N omega)) hσ.le) q
    rw [hrewrite]
    refine (ENNReal.rpow_le_rpow (hmom N i n z q hq)
      (div_nonneg zero_le_one ENNReal.toReal_nonneg)).trans ?_
    rw [show (((2 * q : ℕ) : ENNReal).toReal) = ((2 * q : ℕ) : ℝ) by simp]
    exact prefix_even_root_le_linear _ hb1 q hq
  calc
    eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n z (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (aux_psf_sigma M) *
          eLpNorm (fun omega : BilateralField d =>
            aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M)
            ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((prefix_bank_maxObs_measurable i n z).comp_aemeasurable
          (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
        (Filter.Eventually.of_forall hpoint) _
    _ ≤ ENNReal.ofReal (aux_psf_sigma M) *
          ENNReal.ofReal (2 * ((q : ℝ) + 1 +
            Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) := by
      gcongr

-- from flash order fg_draw_dt1_ne_top
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_ne_top {d : ℕ} [NeZero d] (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (z : Vec d) (om : PotentialSample d) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k z om ≠ ⊤ := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  simpa only [aux_psf_Jval] using aux_psf_Dterm1_le_one M s hs k z om

-- from flash order fg_draw_dt2_ne_top
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top {d : ℕ} (s : ℝ) (k : ℕ) (w : Vec d)
    (om : PotentialSample d) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om ≠ ⊤ := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2
  exact ne_top_of_le_ne_top (aux_psf_Dmaj2_ne_top s k w om) (by simpa using aux_psf_Dterm2_le s k w om)

-- from flash order fg_draw_dt3_ne_top
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_ne_top {d : ℕ} (s : ℝ) (k : ℕ) (w : Vec d)
    (om : PotentialSample d) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w om ≠ ⊤ := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_le_bank s k w om)

-- from flash order fg_draw_dt4_ae_ne_top
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_ne_top {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (k : ℕ → ℕ) (w : ℕ → Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 (k N) (w N) (eta N omega) ≠ ⊤ := by
  rw [MeasureTheory.ae_all_iff]
  intro N
  have h1 : ∀ᵐ p ∂(Measure.map (eta N) (chaosSampleLaw M).toMeasure),
      (∑' j : ℕ, aux_psf_Dmaj4 (k N) (w N) j p) ≠ ⊤ := by
    rw [prefix_eta_law M eta hEta N]
    exact aux_psf_Dmaj4_tsum_ae M (k N) (w N)
  filter_upwards [MeasureTheory.ae_of_ae_map (prefix_eta_aemeasurable M eta hEta N) h1]
    with omega hω
  exact ne_top_of_le_ne_top hω (by
    unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4
    exact aux_psf_Dterm4_le (k N) (w N) (eta N omega))

-- from flash order fg_draw_t2_shellblock_shift
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_shellBlock_shift {d : ℕ}
    (om1 om2 : PotentialSample d) (a k j : ℕ)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x)
    (x : Vec d) :
    shellBlock (k + a) (j + a) om2 (((3 : ℝ) ^ a) • x) = shellBlock k j om1 x := by
  unfold shellBlock
  have hs : Finset.Icc (j + a + 1) (k + a) = (Finset.Icc (j + 1) k).map (addRightEmbedding a) := by
    rw [Finset.map_add_right_Icc]
    congr 1
    omega
  rw [hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [addRightEmbedding_apply]
  exact hrel i x

-- from flash order fg_draw_t2_normOn_shift
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_shellBlock_normOn_shift {d : ℕ}
    (om1 om2 : PotentialSample d) (a k j : ℕ) (w : Vec d)
    (hrel : ∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x)
    (hblock : ∀ x : Vec d,
      shellBlock (k + a) (j + a) om2 (((3 : ℝ) ^ a) • x) = shellBlock k j om1 x) :
    sSup {u : ENNReal | ∃ x : Vec d,
        x ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w) ∧
        u = ENNReal.ofReal |shellBlock (k + a) (j + a) om2 x|} =
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
        u = ENNReal.ofReal |shellBlock k j om1 x|} := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hne : ((3 : ℝ) ^ a) ≠ 0 := ne_of_gt h3
  apply le_antisymm
  · refine sSup_le ?_
    rintro u ⟨y, hy, rfl⟩
    have hx : ((3 : ℝ) ^ a)⁻¹ • y ∈ translatedCube d (k : ℤ) w :=
      aux_lem_prefix_limit_actual_coordinate_cauchy_cube_unscale_mem' a k w y hy
    have hy' : ((3 : ℝ) ^ a) • (((3 : ℝ) ^ a)⁻¹ • y) = y := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [← hy', hblock]
    exact le_sSup ⟨((3 : ℝ) ^ a)⁻¹ • y, hx, rfl⟩
  · refine sSup_le ?_
    rintro u ⟨x, hx, rfl⟩
    have hx' : ((3 : ℝ) ^ a) • x ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w) := by
      have hmem := aux_lem_prefix_limit_actual_coordinate_cauchy_smul_mem (d := d)
        (a := (k : ℤ)) (w := w) (x := x) a hx
      simpa [Nat.cast_add] using hmem
    rw [← hblock x]
    exact le_sSup ⟨((3 : ℝ) ^ a) • x, hx', rfl⟩

-- from flash order fg_draw_t2_mono_shift
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_mono_shift {d : ℕ} (s : ℝ)
    (om1 om2 : PotentialSample d) (a k : ℕ) (w : Vec d)
    (hnorm : ∀ j : ℕ, sSup {u : ENNReal | ∃ x : Vec d,
        x ∈ translatedCube d (((k + a : ℕ) : ℤ)) (((3 : ℝ) ^ a) • w) ∧
        u = ENNReal.ofReal |shellBlock (k + a) (j + a) om2 x|} =
      sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
        u = ENNReal.ofReal |shellBlock k j om1 x|}) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om1 ≤ aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s (k + a) (((3 : ℝ) ^ a) • w) om2 := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2
  refine sSup_le ?_
  rintro v ⟨j, hj, rfl⟩
  refine le_sSup ⟨j + a, by omega, ?_⟩
  rw [hnorm j]
  have hd : ((k + a : ℕ) : ℝ) - ((j + a : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by
    push_cast; ring
  rw [hd]

-- from flash order fg_draw_t2_value_mono
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_value_mono {d : ℕ} (s : ℝ)
    (omega : BilateralField d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (hshift : ∀ (om1 om2 : PotentialSample d) (a k : ℕ) (w : Vec d),
      (∀ (i : ℕ) (x : Vec d), om2 (i + a) (((3 : ℝ) ^ a) • x) = om1 i x) →
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om1 ≤ aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s (k + a) (((3 : ℝ) ^ a) • w) om2)
    (hfin : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d), aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om ≠ ⊤)
    (n : ℤ) (z : Vec d) :
    Monotone (fun N : ℕ => if n ≤ (N : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal
      else 0) := by
  intro N N' hNN'
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hNN'
  dsimp only
  by_cases hn : n ≤ (N : ℤ)
  · have hn' : n ≤ ((N + a : ℕ) : ℤ) := by
      have h2 : (N : ℤ) ≤ ((N + a : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_add_right N a
      exact le_trans hn h2
    rw [if_pos hn, if_pos hn']
    have hk : (((N + a : ℕ) : ℤ) - n).toNat = ((N : ℤ) - n).toNat + a := by omega
    have hw : (3 : ℝ) ^ (N + a) • z = ((3 : ℝ) ^ a) • ((3 : ℝ) ^ N • z) := by
      rw [smul_smul, pow_add, mul_comm]
    rw [hk, hw]
    refine ENNReal.toReal_mono (hfin _ _ _) ?_
    exact hshift (eta N omega) (eta (N + a) omega) a _ _
      (fun i x => aux_lem_prefix_limit_actual_coordinate_cauchy_eta_shift omega eta hEta N a i x)
  · rw [if_neg hn]
    split_ifs with h
    · exact ENNReal.toReal_nonneg
    · exact le_refl 0

-- from flash order fg_draw_t2_pointwise
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_toReal_le {d : ℕ} (s : ℝ) (k : ℕ) (w : Vec d)
    (om : PotentialSample d) :
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om).toReal ≤
      ∑ j ∈ Finset.range (k + 1), (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
        ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om := by
  apply ENNReal.toReal_le_of_le_ofReal
  · refine Finset.sum_nonneg (fun j hj => mul_nonneg ?_ ?_)
    · exact Real.rpow_nonneg (by norm_num) _
    · exact Finset.sum_nonneg (fun i hi => prefix_bank_maxObs_nonneg i k w om)
  · unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2
    refine sSup_le ?_
    rintro v hv
    obtain ⟨j, hj, rfl⟩ := hv
    have hinner : sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
        u = ENNReal.ofReal |shellBlock k j om x|} ≤
        ENNReal.ofReal (∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om) := by
      refine sSup_le ?_
      rintro u hu
      obtain ⟨x, hx, rfl⟩ := hu
      refine ENNReal.ofReal_le_ofReal ?_
      have hterm : |shellBlock k j om x| ≤
          ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om := by
        unfold SubdiffusiveProcess.CoarseGrainingVocab.shellBlock
        refine le_trans (Finset.abs_sum_le_sum_abs (fun i => om i x) (Finset.Icc (j + 1) k)) ?_
        exact Finset.sum_le_sum (fun i hi => by
          have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
          have hb := aux_prefix_bank_le_maxObs i k hik w x om hx
          have hg : 0 ≤ (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (om i) x) :=
            mul_nonneg (by positivity) (euclideanNorm_nonneg (shellGradient (om i) x))
          linarith)
      exact hterm
    have hcpos : 0 < (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hjmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hsum_le : (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
        ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om ≤
        ∑ j' ∈ Finset.range (k + 1), (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j' : ℝ))) *
          ∑ i ∈ Finset.Icc (j' + 1) k, aux_prefix_bank_maxObs i k w om :=
      Finset.single_le_sum (s := Finset.range (k + 1))
        (f := fun j' : ℕ => (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j' : ℝ))) *
          ∑ i ∈ Finset.Icc (j' + 1) k, aux_prefix_bank_maxObs i k w om)
        (fun j' _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Finset.sum_nonneg (fun i _ => prefix_bank_maxObs_nonneg i k w om))) hjmem
    calc
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (k : ℤ) w ∧
            u = ENNReal.ofReal |shellBlock k j om x|}
          ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            ENNReal.ofReal (∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om) :=
            mul_le_mul_right hinner _
      _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
            ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om) :=
            (ENNReal.ofReal_mul (le_of_lt hcpos)).symm
      _ ≤ ENNReal.ofReal (∑ j' ∈ Finset.range (k + 1),
            (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j' : ℝ))) *
            ∑ i ∈ Finset.Icc (j' + 1) k, aux_prefix_bank_maxObs i k w om) :=
            ENNReal.ofReal_le_ofReal hsum_le

-- from flash order fg_draw_t2_series
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_rpow_neg_linear_sq_summable (s A B : ℝ) (hs : 0 < s) :
    Summable (fun L : ℕ => (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * (A + B * (L : ℝ)))) := by
  set r : ℝ := (3 : ℝ) ^ (-(s / 8)) with hr_def
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h1lt : (1 : ℝ) < 3 := by norm_num
  have hneg : -(s / 8) < 0 := by linarith
  have hrpos : 0 < r := by
    rw [hr_def]; exact Real.rpow_pos_of_pos h3pos _
  have hrlt : r < 1 := by
    rw [hr_def]; exact Real.rpow_lt_one_of_one_lt_of_neg h1lt hneg
  have hrn : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (le_of_lt hrpos)]; exact hrlt
  have hpow : ∀ L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) = r ^ L := by
    intro L
    rw [Real.rpow_mul (le_of_lt h3pos), ← hr_def, Real.rpow_natCast]
  have hsum : Summable (fun L : ℕ => A * ((L : ℝ) ^ 1 * r ^ L) + B * ((L : ℝ) ^ 2 * r ^ L)) :=
    ((summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrn).mul_left A).add
      ((summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hrn).mul_left B)
  refine hsum.congr (fun L => ?_)
  rw [hpow L]
  ring

-- from flash order fg_draw_t2_inner_eLpNorm
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t2_inner_eLpNorm_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (hbank : ∀ (N i n : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))))
    (N k j : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
        ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((k - j : ℕ) : ℝ) * (aux_psf_sigma M *
        (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3)))) := by
  have h1 : (1 : ℝ≥0∞) ≤ ((2 * q : ℕ) : ENNReal) := by
    have hq' : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by
      have hq'' : (1 : ℕ) ≤ 2 * q := by omega
      exact_mod_cast hq''
    calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((2 * q : ℕ) : ℝ) := ENNReal.ofReal_le_ofReal hq'
      _ = ((2 * q : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast (2 * q)
  have hm : ∀ i ∈ Finset.Icc (j + 1) k,
      AEStronglyMeasurable
        (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega))
        (chaosSampleLaw M).toMeasure :=
    fun i _ => ((prefix_bank_maxObs_measurable i k w).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  have hterm : ∀ i ∈ Finset.Icc (j + 1) k,
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M *
        (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3))) := by
    intro i hi
    have hji : j + 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have hlog : Real.log (2 * ((aux_psf_cells d (k - i)).card : ℝ)) ≤
        ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3 := by
      have hki : k - i + 1 ≤ k - j := by omega
      have hd : d * (k - i + 1) + 1 ≤ d * (k - j) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left d hki) 1
      have hcast : ((d * (k - i + 1) + 1 : ℕ) : ℝ) ≤ ((d * (k - j) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hd
      calc Real.log (2 * ((aux_psf_cells d (k - i)).card : ℝ))
          ≤ ((d * (k - i + 1) + 1 : ℕ) : ℝ) * Real.log 3 :=
            aux_lem_prefix_limit_actual_coordinate_cauchy_log_cells_le d (k - i)
        _ ≤ ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3 :=
            mul_le_mul_of_nonneg_right hcast (Real.log_nonneg (by norm_num))
    calc eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega))
            ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
        ≤ ENNReal.ofReal (aux_psf_sigma M) *
            ENNReal.ofReal (2 * ((q : ℝ) + 1 +
              Real.log (2 * ((aux_psf_cells d (k - i)).card : ℝ)))) :=
          hbank N i k w q hq
      _ ≤ ENNReal.ofReal (aux_psf_sigma M) *
            ENNReal.ofReal (2 * ((q : ℝ) + 1 +
              ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3)) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal (by linarith))
            (ENNReal.ofReal (aux_psf_sigma M))
      _ = ENNReal.ofReal (aux_psf_sigma M *
            (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3))) :=
          (ENNReal.ofReal_mul (le_of_lt (aux_psf_sigma_pos M))).symm
  have hfun_eq : (fun omega : BilateralField d =>
        ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N omega)) =
      ∑ i ∈ Finset.Icc (j + 1) k,
        (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega)) := by
    funext omega
    rw [Finset.sum_apply]
  calc eLpNorm (fun omega : BilateralField d =>
          ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
      = eLpNorm (∑ i ∈ Finset.Icc (j + 1) k,
          (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega)))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure := by rw [hfun_eq]
    _ ≤ ∑ i ∈ Finset.Icc (j + 1) k,
          eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega))
            ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure :=
        eLpNorm_sum_le h1
    _ ≤ ∑ i ∈ Finset.Icc (j + 1) k,
          ENNReal.ofReal (aux_psf_sigma M *
            (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3))) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Icc (j + 1) k).card : ℝ≥0∞) *
          ENNReal.ofReal (aux_psf_sigma M *
            (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (((k - j : ℕ) : ℝ) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3)))) := by
        have hcard : k + 1 - (j + 1) = k - j := by omega
        rw [Nat.card_Icc, hcard, ← ENNReal.ofReal_natCast (k - j),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg (k - j))]

-- from flash order fg_draw_t3_eLpNorm_le
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t3_eLpNorm_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (hbank : ∀ (N i n : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))))
    (N k : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (aux_psf_sigma M *
        (2 * ((q : ℝ) + 1 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)))) := by
  have hσ0 : 0 ≤ aux_psf_sigma M := le_of_lt (aux_psf_sigma_pos M)
  have hc : 0 ≤ (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) := by positivity
  have hpt : ∀ ω : BilateralField d,
      ‖(aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N ω)).toReal‖ ≤
        ‖(3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * aux_prefix_bank_maxObs 0 k w (eta N ω)‖ := by
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (mul_nonneg hc (prefix_bank_maxObs_nonneg 0 k w (eta N ω)))]
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_toReal_le s k w (eta N ω)
  have hbank' : eLpNorm (fun ω : BilateralField d => aux_prefix_bank_maxObs 0 k w (eta N ω))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d k).card : ℝ)))) := by
    simpa only [Nat.sub_zero] using hbank N 0 k w q hq
  have hlog : Real.log (2 * ((aux_psf_cells d k).card : ℝ)) ≤
      ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3 :=
    aux_lem_prefix_limit_actual_coordinate_cauchy_log_cells_le d k
  have hb : 2 * ((q : ℝ) + 1 + Real.log (2 * ((aux_psf_cells d k).card : ℝ))) ≤
      2 * ((q : ℝ) + 1 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3) := by
    linarith
  have hcm : eLpNorm (fun ω : BilateralField d =>
        (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * aux_prefix_bank_maxObs 0 k w (eta N ω))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        eLpNorm (fun ω : BilateralField d => aux_prefix_bank_maxObs 0 k w (eta N ω))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure := by
    rw [← Real.enorm_eq_ofReal hc]
    exact
      eLpNorm_const_smul (𝕜 := ℝ) ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)))
        (fun ω : BilateralField d => aux_prefix_bank_maxObs 0 k w (eta N ω))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
  have hprod : ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        (ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
          Real.log (2 * ((aux_psf_cells d k).card : ℝ))))) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) *
        (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
          Real.log (2 * ((aux_psf_cells d k).card : ℝ)))))) := by
    rw [← ENNReal.ofReal_mul hσ0, ← ENNReal.ofReal_mul hc]
  calc eLpNorm (fun ω : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N ω)).toReal)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
      ≤ eLpNorm (fun ω : BilateralField d =>
          (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * aux_prefix_bank_maxObs 0 k w (eta N ω))
          ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure :=
        eLpNorm_mono
          (((dsc_third_summand_meas s k w).ennreal_toReal).comp_aemeasurable
            (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable hpt
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        eLpNorm (fun ω : BilateralField d => aux_prefix_bank_maxObs 0 k w (eta N ω))
          ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure := hcm
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        (ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
          Real.log (2 * ((aux_psf_cells d k).card : ℝ))))) :=
        mul_le_mul_right hbank' (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))))
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) *
        (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
          ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)))) := by
        rw [hprod]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hσ0) hc)

-- from flash order fg_draw_t4_value_cauchy
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t4_value_Lp_cauchy {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (p : ℝ) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
            (eta (phi k) omega)).toReal else 0) -
        (if n ≤ (phi k' : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z)
            (eta (phi k') omega)).toReal else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  have hconst : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N : ℕ, n.toNat ≤ N →
        (if n ≤ (N : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
            (eta N omega)).toReal else 0) =
        (if n ≤ ((n.toNat : ℕ) : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((n.toNat : ℤ) - n).toNat ((3 : ℝ) ^ n.toNat • z)
            (eta n.toNat omega)).toReal else 0) := by
    filter_upwards [hEta] with omega hω N hN
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_value_guard_const omega eta hω n z N hN
  refine aux_lem_prefix_limit_actual_coordinate_cauchy_Lp_cauchy_of_eventually_const
    (chaosSampleLaw M).toMeasure p
    (fun N omega => if n ≤ (N : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
          (eta N omega)).toReal else 0)
    n.toNat hconst phi hphi eps0 heps0

-- from flash order fg_draw_meas
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N k : ℕ) (w : Vec d) :
    AEStronglyMeasurable (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure ∧
      AEStronglyMeasurable (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure ∧
      AEStronglyMeasurable (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure := by
  refine ⟨?_, ?_, ?_⟩
  · have hm : Measurable (fun om : PotentialSample d =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om) :=
      aux_dsc_block_meas s k w
    exact ((ENNReal.measurable_toReal.comp hm).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  · have hm : Measurable (fun om : PotentialSample d =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w om) :=
      dsc_third_summand_meas s k w
    exact ((ENNReal.measurable_toReal.comp hm).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  · have hm : Measurable (fun om : PotentialSample d =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w om) :=
      dsc_fourth_summand_meas k w
    exact ((ENNReal.measurable_toReal.comp hm).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable

-- from flash order fg_draw_t2_cauchy
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t2_value_Lp_cauchy {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d)
    (hmono : ∀ omega : BilateralField d, (∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      Monotone (fun N : ℕ => if n ≤ (N : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal
        else 0))
    (hmeas : ∀ (N k : ℕ) (w : Vec d), AEStronglyMeasurable (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure)
    (hbound : ∀ q : ℕ, 1 ≤ q → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (N k : ℕ) (w : Vec d),
      eLpNorm (fun omega : BilateralField d =>
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w (eta N omega)).toReal)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤ C)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
            (eta (phi k) omega)).toReal else 0) -
        (if n ≤ (phi k' : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z)
            (eta (phi k') omega)).toReal else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let v : ℕ → BilateralField d → ℝ := fun N omega =>
    if n ≤ (N : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal
      else 0
  let q : ℕ := ⌈p⌉₊
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr
    (Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hp)).ne'
  have hpq : ENNReal.ofReal p ≤ ((2 * q : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have h1 : p ≤ (q : ℝ) := Nat.le_ceil p
    have h2 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    push_cast
    linarith
  obtain ⟨C, hC, hCb⟩ := hbound q hq
  have hv (N : ℕ) : AEStronglyMeasurable (v N) μ := by
    by_cases hn : n ≤ (N : ℤ)
    · simpa only [v, if_pos hn] using hmeas N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
    · simp only [v, if_neg hn]
      exact aestronglyMeasurable_const
  have hbound' (N : ℕ) : eLpNorm (v N) (ENNReal.ofReal p) μ ≤ C := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans ?_
    by_cases hn : n ≤ (N : ℤ)
    · simpa only [v, if_pos hn] using hCb N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
    · simp [v, if_neg hn]
  have hnn : ∀ᵐ omega ∂μ, ∀ k, 0 ≤ v (phi k) omega := by
    refine Eventually.of_forall fun omega k => ?_
    by_cases hn : n ≤ ((phi k : ℕ) : ℤ)
    · simp only [v, if_pos hn]
      exact ENNReal.toReal_nonneg
    · simp only [v, if_neg hn, le_refl]
  have hmono' : ∀ᵐ omega ∂μ, Monotone (fun k => v (phi k) omega) := by
    filter_upwards [hEta] with omega hω
    exact (hmono omega hω).comp hphi.monotone
  simpa only [μ, v] using
    aux_prefix_field_mono_Lp_cauchy μ (fun k => v (phi k)) p hp
      (fun k => hv (phi k)) hnn hmono' C hC (fun k => hbound' (phi k)) eps0 heps0

-- from flash order fg_draw_value_split
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Draw_value_split {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (hf1 : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d), aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k w om ≠ ⊤)
    (hf2 : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d), aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om ≠ ⊤)
    (hf3 : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d), aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w om ≠ ⊤)
    (n : ℤ) (z : Vec d)
    (hf4 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega) ≠ ⊤) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      (if n ≤ (N : ℤ) then
          (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0) =
        (if n ≤ (N : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal else 0) +
        (if n ≤ (N : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal else 0) +
        (if n ≤ (N : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal else 0) +
        (if n ≤ (N : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal else 0) := by
  filter_upwards [hPrimitive, hf4] with omega hP h4
  intro N
  by_cases hn : n ≤ (N : ℤ)
  · simp only [if_pos hn]
    have hD := aux_lem_prefix_limit_actual_coordinate_cauchy_Dsc_eq_sum M s eps (eta N omega)
      (fun m y => F N m y omega) (fun m y => Praw N m y omega) (fun m y => Rraw N m y omega)
      (fun m y => Draw N m y omega) (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)
      (hP N) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
    rw [hD]
    have h1 : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega) ≠ ⊤ := hf1 _ _ _
    have h2 : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega) ≠ ⊤ := hf2 _ _ _
    have h3 : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega) ≠ ⊤ := hf3 _ _ _
    have h4' : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega) ≠ ⊤ := h4 N
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
          ⟨ENNReal.add_ne_top.mpr ⟨h1, h2⟩, h3⟩) h4',
        ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3,
        ENNReal.toReal_add h1 h2]
  · simp only [if_neg hn, add_zero]

-- from flash order fg_draw_t2_uniform
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t2_eLpNorm_uniform {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hpt : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d),
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om).toReal ≤
        ∑ j ∈ Finset.range (k + 1), (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w om)
    (hmeas : ∀ (N k j : ℕ) (w : Vec d), AEStronglyMeasurable (fun omega : BilateralField d =>
        ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N omega)) (chaosSampleLaw M).toMeasure)
    (q : ℕ) (hq : 1 ≤ q)
    (hinner : ∀ (N k j : ℕ) (w : Vec d),
      eLpNorm (fun omega : BilateralField d =>
          ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (((k - j : ℕ) : ℝ) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * (k - j) + 1 : ℕ) : ℝ) * Real.log 3)))))
    (hsum : Summable (fun L : ℕ => (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))))
    (hσ : 0 < aux_psf_sigma M)
    (N k : ℕ) (w : Vec d) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w (eta N omega)).toReal)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (∑' L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))) := by
  let F : ℕ → BilateralField d → ℝ := fun j ω =>
    ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N ω)
  let b : ℕ → ℝ := fun L => (L : ℝ) * (aux_psf_sigma M *
    (2 * ((q : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3)))
  let g : ℕ → ℝ := fun L => (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * b L
  change SubdiffusiveProcess.RawLp.eLpNorm (fun ω : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w (eta N ω)).toReal)
    ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (∑' L : ℕ, g L)
  have hp1 : (1 : ENNReal) ≤ ((2 * q : ℕ) : ENNReal) := by
    have hnat : 1 ≤ 2 * q := by omega
    first
      | exact_mod_cast hnat
      | rw [← Nat.cast_one, Nat.cast_le]; exact hnat
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := le_of_lt (Real.log_pos (by norm_num))
  have hb_nonneg : ∀ L : ℕ, 0 ≤ b L := by
    intro L
    have h1 : (0 : ℝ) ≤ ((d * L + 1 : ℕ) : ℝ) * Real.log 3 :=
      mul_nonneg (Nat.cast_nonneg _) hlog3
    have h2 : (0 : ℝ) ≤ (q : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3 := by
      have hq' : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    exact mul_nonneg (Nat.cast_nonneg L) (mul_nonneg hσ.le (mul_nonneg (by norm_num) h2))
  have hg_nonneg : ∀ L : ℕ, 0 ≤ g L := fun L =>
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
      (-(s / 8) * (L : ℝ)))) (hb_nonneg L)
  have hfun : (fun ω : BilateralField d => ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω)
      = ∑ j ∈ Finset.range (k + 1), (fun ω : BilateralField d =>
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω) := by
    funext ω
    simp only [Finset.sum_apply]
  have hrefl : (∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j))
      = ∑ L ∈ Finset.range (k + 1), g L := by
    rw [← Finset.sum_range_reflect g (k + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hkj : k + 1 - 1 - j = k - j := by omega
    rw [hkj]
    show (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j)
      = (3 : ℝ) ^ (-(s / 8) * (((k - j : ℕ) : ℝ))) * b (k - j)
    rw [Nat.cast_sub hjle]
  have h1 : SubdiffusiveProcess.RawLp.eLpNorm (fun ω : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w (eta N ω)).toReal)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
      ≤ eLpNorm (fun ω : BilateralField d => ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure := by
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (by
      rw [hfun]
      exact Finset.aestronglyMeasurable_sum _ (fun j _ => (hmeas N k j w).const_mul _))]
    apply SubdiffusiveProcess.RawLp.eLpNorm_mono_ae
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs]
    exact (hpt k w (eta N ω)).trans (le_abs_self _)
  have h2 : eLpNorm (fun ω : BilateralField d => ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
      ≤ ∑ j ∈ Finset.range (k + 1), eLpNorm (fun ω : BilateralField d =>
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure := by
    rw [hfun]
    exact eLpNorm_sum_le hp1
  have h3 : (∑ j ∈ Finset.range (k + 1), eLpNorm (fun ω : BilateralField d =>
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure)
      ≤ ∑ j ∈ Finset.range (k + 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (-(s / 8) * ((k : ℝ) - (j : ℝ))))
    have hsm : (fun ω : BilateralField d =>
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * F j ω)
        = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) • F j := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsm, eLpNorm_const_smul ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) (F j)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure, Real.enorm_eq_ofReal hc0]
    calc ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          eLpNorm (F j) ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
        ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          ENNReal.ofReal (b (k - j)) :=
          mul_le_mul_right (hinner N k j w)
            (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))))
      _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j)) :=
          (ENNReal.ofReal_mul hc0).symm
  have h4 : (∑ j ∈ Finset.range (k + 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j)))
      = ENNReal.ofReal (∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j)) := by
    have hterm : ∀ j ∈ Finset.range (k + 1),
        0 ≤ (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j) := by
      intro j hj
      exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
        (-(s / 8) * ((k : ℝ) - (j : ℝ))))) (hb_nonneg (k - j))
    exact (ENNReal.ofReal_sum_of_nonneg hterm).symm
  have h5 : ENNReal.ofReal (∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) * b (k - j))
      = ENNReal.ofReal (∑ L ∈ Finset.range (k + 1), g L) := by rw [hrefl]
  have h6 : ENNReal.ofReal (∑ L ∈ Finset.range (k + 1), g L)
      ≤ ENNReal.ofReal (∑' L : ℕ, g L) := ENNReal.ofReal_le_ofReal
        (Summable.sum_le_tsum (Finset.range (k + 1)) (fun L _ => hg_nonneg L) hsum)
  exact h1.trans (h2.trans (h3.trans ((le_of_eq h4).trans ((le_of_eq h5).trans h6))))

-- from flash order fg_draw_t3_tendsto
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t3_value_tendsto_zero {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (ht3 : ∀ (N k : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
      eLpNorm (fun omega : BilateralField d =>
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)))))
    (hmeas : ∀ (N k : ℕ) (w : Vec d), AEStronglyMeasurable (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure)
    (n : ℤ) (z : Vec d) (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun N : ℕ => eLpNorm (fun omega : BilateralField d =>
        if n ≤ (N : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (eta N omega)).toReal
        else 0) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0) := by
  classical
  have hq : 1 ≤ Nat.ceil p := by
    have h1 : (1 : ℝ) ≤ ((Nat.ceil p : ℕ) : ℝ) := le_trans hp (Nat.le_ceil p)
    exact_mod_cast h1
  have hpq : ENNReal.ofReal p ≤ ((2 * Nat.ceil p : ℕ) : ENNReal) := by
    have h1 : ENNReal.ofReal p ≤ (Nat.ceil p : ENNReal) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (Nat.le_ceil p)
    have h2 : (Nat.ceil p : ENNReal) ≤ ((2 * Nat.ceil p : ℕ) : ENNReal) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      have hc : (0 : ℝ) ≤ (Nat.ceil p : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_trans h1 h2
  have hAB : ∀ k : ℕ,
      aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3))
        = aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3))
          + aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3)) * (k : ℝ) := by
    intro k
    push_cast
    ring
  have hkN : Tendsto (fun N : ℕ => ((N : ℤ) - n).toNat) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b + n.toNat, fun N hN => ?_⟩
    have h2 : n ≤ ((n.toNat : ℕ) : ℤ) := Int.self_le_toNat n
    have h4 : (((b + n.toNat : ℕ)) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    push_cast at h4
    have h1 : (b : ℤ) ≤ (N : ℤ) - n := by omega
    have h5 : (0 : ℤ) ≤ (N : ℤ) - n := by omega
    have h6 : (b : ℤ) ≤ (((N : ℤ) - n).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg h5]
      exact h1
    exact_mod_cast h6
  have hcomp : Tendsto (fun N : ℕ =>
      (3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
        (aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3))
          + aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3)) * (((N : ℤ) - n).toNat : ℝ)))
      atTop (𝓝 0) := by
    have hg := aux_lem_prefix_limit_actual_coordinate_cauchy_rpow_neg_mul_linear_tendsto s
      (aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3)))
      (aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3))) hs
    simpa only [Function.comp_def] using hg.comp hkN
  have hcompE : Tendsto (fun N : ℕ =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
        (aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3))
          + aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3)) * (((N : ℤ) - n).toNat : ℝ))))
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hcomp
    rwa [ENNReal.ofReal_zero] at h
  have hbound : ∀ N : ℕ,
      eLpNorm (fun omega : BilateralField d =>
          if n ≤ (N : ℤ) then
            (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
              ((3 : ℝ) ^ N • z) (eta N omega)).toReal
          else 0) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
          (aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3))
            + aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3)) * (((N : ℤ) - n).toNat : ℝ))) := by
    intro N
    by_cases h : n ≤ (N : ℤ)
    · have hz : (fun omega : BilateralField d =>
            if n ≤ (N : ℤ) then
              (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
                ((3 : ℝ) ^ N • z) (eta N omega)).toReal
            else 0) =ᵐ[(chaosSampleLaw M).toMeasure]
          (fun omega : BilateralField d =>
            (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
              ((3 : ℝ) ^ N • z) (eta N omega)).toReal) := by
        filter_upwards with omega
        exact if_pos h
      rw [eLpNorm_congr_ae hz]
      calc
        eLpNorm (fun omega : BilateralField d =>
            (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
              ((3 : ℝ) ^ N • z) (eta N omega)).toReal)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
          ≤ eLpNorm (fun omega : BilateralField d =>
              (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
                ((3 : ℝ) ^ N • z) (eta N omega)).toReal)
              ((2 * Nat.ceil p : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure :=
            eLpNorm_le_eLpNorm_of_exponent_le hpq
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
              (aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 +
                ((d * (((N : ℤ) - n).toNat + 1) + 1 : ℕ) : ℝ) * Real.log 3)))) :=
            ht3 N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) (Nat.ceil p) hq
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
              (aux_psf_sigma M * (2 * ((Nat.ceil p : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3))
                + aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3)) *
                  (((N : ℤ) - n).toNat : ℝ))) :=
            ENNReal.ofReal_le_ofReal (by rw [hAB ((N : ℤ) - n).toNat])
    · have hz : (fun omega : BilateralField d =>
            if n ≤ (N : ℤ) then
              (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
                ((3 : ℝ) ^ N • z) (eta N omega)).toReal
            else 0) =ᵐ[(chaosSampleLaw M).toMeasure] (0 : BilateralField d → ℝ) := by
        filter_upwards with omega
        exact if_neg h
      rw [eLpNorm_congr_ae hz, eLpNorm_zero]
      exact zero_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcompE ?_ ?_
  · exact Filter.Eventually.of_forall (fun N => zero_le)
  · exact Filter.Eventually.of_forall hbound

-- from flash order fg_draw_t2_cauchy_full
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t2_value_Lp_cauchy_full {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
            (eta (phi k) omega)).toReal else 0) -
        (if n ≤ (phi k' : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z)
            (eta (phi k') omega)).toReal else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  apply aux_lem_prefix_limit_actual_coordinate_cauchy_t2_value_Lp_cauchy
    M s eta hEta n z ?_ ?_ ?_ phi hphi p hp eps0 heps0
  · intro omega hω
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_value_mono s omega eta hω
      (fun om1 om2 a k w hrel =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_mono_shift s om1 om2 a k w
          (fun j => aux_lem_prefix_limit_actual_coordinate_cauchy_shellBlock_normOn_shift
            om1 om2 a k j w hrel
            (aux_lem_prefix_limit_actual_coordinate_cauchy_shellBlock_shift om1 om2 a k j hrel)))
      (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top s k w om) n z
  · intro N k w
    exact (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable
      M s eta hEta N k w).1
  · intro q hq
    have hbank : ∀ (N i n : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
        eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n w (eta N omega))
          ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
            Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) :=
      fun N i n w q hq =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_eLpNorm_linear M eta hEta
          (fun N i n w q hq =>
            aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_even_moment_log
              M eta hEta N i n w q hq) N i n w q hq
    have hsum : Summable (fun L : ℕ => (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) *
        ((L : ℝ) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))) := by
      refine (aux_lem_prefix_limit_actual_coordinate_cauchy_rpow_neg_linear_sq_summable s
        (aux_psf_sigma M * (2 * ((q : ℝ) + 1 + Real.log 3)))
        (aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3))) hs).congr (fun L => ?_)
      push_cast
      ring
    refine ⟨ENNReal.ofReal (∑' L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) *
        ((L : ℝ) * (aux_psf_sigma M *
          (2 * ((q : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))),
      ENNReal.ofReal_ne_top, ?_⟩
    intro N k w
    erw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable
        M s eta hEta N k w).1]
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_t2_eLpNorm_uniform M s eta
      (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_toReal_le s k w om)
      (fun N k j w => by
        have hfun : (fun omega : BilateralField d =>
            ∑ i ∈ Finset.Icc (j + 1) k, aux_prefix_bank_maxObs i k w (eta N omega)) =
            ∑ i ∈ Finset.Icc (j + 1) k,
              (fun omega : BilateralField d => aux_prefix_bank_maxObs i k w (eta N omega)) := by
          funext omega
          rw [Finset.sum_apply]
        rw [hfun]
        exact Finset.aestronglyMeasurable_sum (Finset.Icc (j + 1) k) (fun i _ =>
          ((prefix_bank_maxObs_measurable i k w).comp_aemeasurable
            (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable))
      q hq
      (fun N k j w => aux_lem_prefix_limit_actual_coordinate_cauchy_t2_inner_eLpNorm_le
        M eta hEta hbank N k j w q hq)
      hsum (aux_psf_sigma_pos M) N k w

-- from flash order fg_draw_t3_cauchy_full
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t3_value_Lp_cauchy_full {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
            (eta (phi k) omega)).toReal else 0) -
        (if n ≤ (phi k' : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z)
            (eta (phi k') omega)).toReal else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  have hbank : ∀ (N i n : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) :=
    fun N i n w q hq =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_eLpNorm_linear M eta hEta
        (aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_even_moment_log M eta hEta)
        N i n w q hq
  have hmeasT : ∀ (N k : ℕ) (w : Vec d),
      AEStronglyMeasurable (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal)
        (chaosSampleLaw M).toMeasure := fun N k w =>
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable M s eta hEta
      N k w).2.1
  have ht3 : ∀ (N k : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
      eLpNorm (fun omega : BilateralField d =>
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal)
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (aux_psf_sigma M *
        (2 * ((q : ℝ) + 1 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)))) :=
    fun N k w q hq =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_t3_eLpNorm_le M s eta hEta hbank N k w q hq
  have hT := aux_lem_prefix_limit_actual_coordinate_cauchy_t3_value_tendsto_zero
    M s hs eta ht3 hmeasT n z p hp
  refine aux_prefix_limit_cauchy_of_tendsto (chaosSampleLaw M).toMeasure p hp
    (fun k omega => if n ≤ (phi k : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((phi k : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) (eta (phi k) omega)).toReal else 0)
    (fun _ => 0) ?_ aestronglyMeasurable_const ?_ eps0 heps0
  · intro k
    by_cases hn : n ≤ (phi k : ℤ)
    · simpa only [if_pos hn] using
        hmeasT (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
    · simp only [if_neg hn]
      exact aestronglyMeasurable_const
  · simp only [sub_zero]
    exact hT.comp hphi.tendsto_atTop

-- from flash order fg_t1_dt1_le
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_le_max {d : ℕ} [NeZero d] (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) (η : PotentialSample d) (m : ℕ) (w : Vec d) (H : ℕ) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η ≤
      max (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H) (aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s (H + 1)) := by
  classical
  refine sSup_le ?_
  rintro v ⟨j, l, hjl, hlk, hlj, x, hgrid, hann, rfl⟩
  obtain ⟨k, rfl⟩ := aux_prefix_rraw_exists_Rpoint l w x hgrid
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = m - l := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = j - l := ⟨_, rfl⟩
  have hcast : (m : ℝ) - (l : ℝ) = (r : ℝ) := by
    rw [hr, Nat.cast_sub (by omega : l ≤ m)]
  rw [aux_prefix_rraw_Rpoint_sub] at hann
  have hj1 : ((j : ℕ) : ℤ) = (l : ℤ) + (t : ℤ) := by omega
  rw [hj1, add_sub_assoc] at hann
  have hannk : aux_prefix_rraw_kvec k ∈ cube d (t : ℤ) \ cube d ((t : ℤ) - 1) :=
    ⟨(aux_prefix_rraw_smul_mem_cube_iff _ l _).mp hann.1,
      fun h => hann.2 ((aux_prefix_rraw_smul_mem_cube_iff _ l _).mpr h)⟩
  have hval : ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ)))) *
      (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
        u = ENNReal.ofReal (section6Response M l l η (aux_psf_Rpoint l w k) e)}) 1) ^
        (1 / 2 : ℝ) =
      aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r *
        aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt (aux_prefix_rraw_A M η m w r k) := by
    have hml : m - r = l := by omega
    unfold aux_lem_prefix_limit_actual_coordinate_cauchy_c1
      aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt aux_prefix_rraw_A aux_psf_Jval
    rw [hml, hcast]
  rw [hval]
  by_cases hrH : r ≤ H
  · have hmem : (r, k) ∈ aux_prefix_rraw_G d H := by
      simp only [aux_prefix_rraw_G, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, hrH⟩, aux_prefix_rraw_mem_Rindex k t H (by omega) hannk.1⟩,
        t, by omega, by omega, hannk⟩
    have hsup : aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H =
        (aux_prefix_rraw_G d H).sup (fun rk : ℕ × (Fin d → ℤ) =>
          aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s rk.1 *
            aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
              (aux_prefix_rraw_A M η m w rk.1 rk.2)) := rfl
    rw [hsup]
    have hle := Finset.le_sup (f := fun rk : ℕ × (Fin d → ℤ) =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s rk.1 *
        aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
          (aux_prefix_rraw_A M η m w rk.1 rk.2)) hmem
    exact le_max_of_le_left hle
  · refine le_max_of_le_right ?_
    have hHr : H + 1 ≤ r := by omega
    have hcap : aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
        (aux_prefix_rraw_A M η m w r k) ≤ 1 := by
      unfold aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
      exact ENNReal.rpow_le_one (min_le_right _ 1) (by norm_num)
    have hstep1 : aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r *
        aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt (aux_prefix_rraw_A M η m w r k) ≤
        aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r := by
      calc aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r *
            aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt (aux_prefix_rraw_A M η m w r k)
          ≤ aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r * 1 :=
            mul_le_mul_right hcap _
        _ = aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r := mul_one _
    have hstep2 : aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s r ≤
        aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s (H + 1) := by
      unfold aux_lem_prefix_limit_actual_coordinate_cauchy_c1
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      have h1 : ((H + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hHr
      exact mul_le_mul_of_nonpos_left h1 (by linarith)
    exact hstep1.trans hstep2

-- from flash order fg_t1_meas
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_aestronglyMeasurable {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N k : ℕ) (w : Vec d) :
    AEStronglyMeasurable (fun omega : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure := by
    exact (((ENNReal.measurable_toReal.comp
    (aux_lem_prefix_limit_actual_Dsc_first_meas M s k w)).comp_aemeasurable
    (prefix_eta_aemeasurable M eta hEta N))).aestronglyMeasurable

-- from flash order fg_t1_lp_cauchy
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t1_value_Lp_cauchy_of_cim {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ)
    (hmeas : ∀ (N k : ℕ) (w : Vec d), AEStronglyMeasurable (fun omega : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k w (eta N omega)).toReal) (chaosSampleLaw M).toMeasure)
    (hle1 : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d), aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k w om ≤ 1)
    (hcim : aux_prefix_rraw_CauchyInMeasure (chaosSampleLaw M).toMeasure
      (fun i omega => (if n ≤ (phi i : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z)
            (eta (phi i) omega)).toReal else 0)))
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
            (eta (phi k) omega)).toReal else 0) -
        (if n ≤ (phi k' : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z)
            (eta (phi k') omega)).toReal else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  set f : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi i : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi i) • z) (eta (phi i) omega)).toReal
    else 0 with hf_def
  have hf : ∀ i, AEStronglyMeasurable (f i) (chaosSampleLaw M).toMeasure := by
    intro i
    by_cases h : n ≤ (phi i : ℤ)
    · rw [hf_def]
      simp only [h, if_true]
      exact hmeas _ _ _
    · rw [hf_def]
      simp only [h, if_false]
      exact aestronglyMeasurable_const
  have hbound : ∀ i, eLpNorm (f i) (ENNReal.ofReal (p+1)) (chaosSampleLaw M).toMeasure ≤ 1 := by
    intro i
    have hbd : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ‖f i omega‖ ≤ 1 := by
      refine Eventually.of_forall fun omega => ?_
      by_cases h : n ≤ (phi i : ℤ)
      · rw [hf_def]
        simp only [h, if_true]
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
          (by simpa using hle1 ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z) (eta (phi i) omega))
      · rw [hf_def]
        simp only [h, if_false]
        rw [norm_zero]
        norm_num
    calc eLpNorm (f i) (ENNReal.ofReal (p+1)) (chaosSampleLaw M).toMeasure
        ≤ (chaosSampleLaw M).toMeasure Set.univ ^ (ENNReal.ofReal (p+1)).toReal⁻¹ *
            ENNReal.ofReal 1 := eLpNorm_le_of_ae_bound (hf i) hbd
      _ = 1 := by
          rw [measure_univ, ENNReal.one_rpow, ENNReal.ofReal_one, one_mul]
  exact aux_prefix_rraw_Lp_cauchy_of_cim (chaosSampleLaw M).toMeasure p (p+1) hp (by linarith)
    f hf 1 ENNReal.one_ne_top hbound hcim eps0 heps0

-- from flash order fg_t1_toReal_atoms
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_toReal_eq_atoms {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d) (n : ℤ) (z : Vec d) (N H : ℕ)
    (hN : n + (H : ℤ) ≤ (N : ℤ)) (hne : (aux_prefix_rraw_G d H).Nonempty)
    (omega : BilateralField d) :
    (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta N omega) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) H).toReal =
      (aux_prefix_rraw_G d H).sup' hne (fun rk => (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) *
        Real.sqrt (min (aux_prefix_rraw_atom M eta N (-n - (rk.1 : ℤ))
          (z + (3 : ℝ) ^ (-n - (rk.1 : ℤ)) • aux_prefix_rraw_kvec rk.2) omega) 1)) := by
  classical
  have hcap : ∀ a : ℝ≥0∞, aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt a ≠ ⊤ := by
    intro a
    unfold aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (ENNReal.rpow_le_one (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2))
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow
  rw [aux_lem_prefix_limit_actual_coordinate_cauchy_toReal_finset_sup (aux_prefix_rraw_G d H) hne
    (fun rk => aux_lem_prefix_limit_actual_coordinate_cauchy_c1 s rk.1 *
      aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
        (aux_prefix_rraw_A M (eta N omega) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) rk.1 rk.2))
    (fun rk _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcap _))]
  refine Finset.sup'_congr hne rfl ?_
  intro rk hrk
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_c1
    aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt
  have hrH : rk.1 ≤ H := by
    have h := hrk
    simp only [aux_prefix_rraw_G, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
    exact h.1.1.2
  have hNr : n + (rk.1 : ℤ) ≤ (N : ℤ) := by
    have h' : ((rk.1 : ℕ) : ℤ) ≤ ((H : ℕ) : ℤ) := by exact_mod_cast hrH
    omega
  have hA : aux_prefix_rraw_A M (eta N omega) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) rk.1 rk.2 ≠ ⊤ :=
    aux_prefix_rraw_A_ne_top M _ _ _ _ _
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) by positivity),
    ← ENNReal.toReal_rpow, ENNReal.toReal_min hA ENNReal.one_ne_top, ENNReal.toReal_one,
    aux_prefix_rraw_A_eq_atom M eta n z N rk.1 rk.2 hNr omega, Real.sqrt_eq_rpow]

-- from flash order fg_t1_shallow_tim
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_tendstoInMeasure {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d) (n : ℤ) (z : Vec d)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (htoReal : ∀ (N H : ℕ), n + (H : ℤ) ≤ (N : ℤ) → ∀ (hne : (aux_prefix_rraw_G d H).Nonempty)
      (omega : BilateralField d),
      (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta N omega) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) H).toReal =
        (aux_prefix_rraw_G d H).sup' hne (fun rk => (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) *
          Real.sqrt (min (aux_prefix_rraw_atom M eta N (-n - (rk.1 : ℤ))
          (z + (3 : ℝ) ^ (-n - (rk.1 : ℤ)) • aux_prefix_rraw_kvec rk.2) omega) 1)))
    (H : ℕ) :
    ∃ Gl : BilateralField d → ℝ, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun i omega => if n ≤ (phi i : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta (phi i) omega) ((phi i : ℤ) - n).toNat
          ((3 : ℝ) ^ (phi i) • z) H).toReal else 0) atTop Gl := by
  let F : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta (phi i) omega)
        ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ phi i • z) H).toReal
    else 0
  change ∃ Gl : BilateralField d → ℝ,
    TendstoInMeasure (chaosSampleLaw M).toMeasure F atTop Gl
  choose lim hlim using hAtoms
  rcases (aux_prefix_rraw_G d H).eq_empty_or_nonempty with hE | hne
  · have hT : ∀ (N : ℕ) (om : PotentialSample d),
        aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s om ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) H = 0 := by
      intro N om
      unfold aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow
      rw [hE]
      exact Finset.sup_empty.trans ENNReal.bot_eq_zero
    have hF0 : ∀ i (om : BilateralField d), F i om = 0 := by
      intro i om
      dsimp only [F]
      by_cases h : n ≤ (phi i : ℤ)
      · rw [if_pos h, hT (phi i) (eta (phi i) om), ENNReal.toReal_zero]
      · rw [if_neg h]
    refine ⟨fun _ => 0, ?_⟩
    refine tendstoInMeasure_iff_dist.mpr fun ε hε => ?_
    have hgoal : Tendsto (fun i => (chaosSampleLaw M).toMeasure
        {x : BilateralField d | ε ≤ dist (F i x) 0}) atTop (𝓝 0) := by
      have hzero : (fun i => (chaosSampleLaw M).toMeasure
          {x : BilateralField d | ε ≤ dist (F i x) 0}) = fun _ => 0 := by
        funext i
        have hset : {x : BilateralField d | ε ≤ dist (F i x) 0} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Set.mem_setOf_eq] at hx
          rw [hF0 i x, dist_self] at hx
          exact absurd hx (not_le.mpr hε)
        rw [hset, measure_empty]
      rw [hzero]
      exact tendsto_const_nhds
    exact hgoal
  · let S : Finset (ℕ × (Fin d → ℤ)) := aux_prefix_rraw_G d H
    let f : (ℕ × (Fin d → ℤ)) → ℕ → BilateralField d → ℝ := fun rk i om =>
      aux_prefix_rraw_atom M eta (phi i) (-n - (rk.1 : ℤ))
        (z + (3 : ℝ) ^ (-n - (rk.1 : ℤ)) • aux_prefix_rraw_kvec rk.2) om
    let g : (ℕ × (Fin d → ℤ)) → BilateralField d → ℝ := fun rk om =>
      lim (-n - (rk.1 : ℤ)) rk.2 om
    let Glim : BilateralField d → ℝ := fun om =>
      S.sup' hne (fun rk => (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) *
        Real.sqrt (min (max (g rk om) 0) 1))
    refine ⟨Glim, ?_⟩
    have hf : ∀ rk ∈ S, TendstoInMeasure (chaosSampleLaw M).toMeasure (f rk) atTop (g rk) := by
      intro rk _
      dsimp only [f, g]
      exact hlim (-n - (rk.1 : ℤ)) rk.2
    have hdom : ∀ i : ℕ, (n + (H : ℤ)).toNat ≤ i →
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        |F i om - Glim om| ≤ ∑ rk ∈ S, Real.sqrt |f rk i om - g rk om| := by
      intro i hi
      have hle : n + (H : ℤ) ≤ (phi i : ℤ) := by
        have h2 : n + (H : ℤ) ≤ (((n + (H : ℤ)).toNat : ℕ) : ℤ) := Int.self_le_toNat _
        have h3 : ((n + (H : ℤ)).toNat : ℕ) ≤ phi i := le_trans hi (hphi.id_le i)
        have h4 : (((n + (H : ℤ)).toNat : ℕ) : ℤ) ≤ (phi i : ℤ) := by exact_mod_cast h3
        linarith
      have hnle : n ≤ (phi i : ℤ) := by
        have hH0 : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
        linarith
      refine Eventually.of_forall fun om => ?_
      dsimp only [F, Glim, S, f, g]
      rw [if_pos hnle, htoReal (phi i) H hle hne om]
      have h1 := aux_lem_prefix_limit_actual_coordinate_cauchy_abs_sup'_sub_le
        (aux_prefix_rraw_G d H) hne
        (fun rk : ℕ × (Fin d → ℤ) => (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) *
          Real.sqrt (min (aux_prefix_rraw_atom M eta (phi i) (-n - (rk.1 : ℤ))
            (z + (3 : ℝ) ^ (-n - (rk.1 : ℤ)) • aux_prefix_rraw_kvec rk.2) om) 1))
        (fun rk : ℕ × (Fin d → ℤ) => (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) *
          Real.sqrt (min (max (lim (-n - (rk.1 : ℤ)) rk.2 om) 0) 1))
      refine h1.trans ?_
      refine Finset.sum_le_sum fun rk _ => ?_
      have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) := by positivity
      have hc1 : (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ)) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
        have h0 : (0 : ℝ) ≤ (rk.1 : ℝ) := Nat.cast_nonneg _
        nlinarith [hs]
      have ha0 : (0 : ℝ) ≤ aux_prefix_rraw_atom M eta (phi i) (-n - (rk.1 : ℤ))
          (z + (3 : ℝ) ^ (-n - (rk.1 : ℤ)) • aux_prefix_rraw_kvec rk.2) om := by
        unfold aux_prefix_rraw_atom
        split_ifs with hh
        · exact ENNReal.toReal_nonneg
        · exact le_refl 0
      exact aux_lem_prefix_limit_actual_coordinate_cauchy_capsqrt_real_sub_le
        ((3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ))) _ _ hc0 hc1 ha0
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_tim_of_sqrt_dom
      (chaosSampleLaw M).toMeasure S f g hf F Glim ((n + (H : ℤ)).toNat) hdom

-- from flash order fg_t1_value_cim
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t1_value_cim {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d) (n : ℤ) (z : Vec d)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hshallow : ∀ H : ℕ, ∃ Gl : BilateralField d → ℝ, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun i omega => if n ≤ (phi i : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta (phi i) omega) ((phi i : ℤ) - n).toNat
          ((3 : ℝ) ^ (phi i) • z) H).toReal else 0) atTop Gl)
    (hsand : ∀ (η : PotentialSample d) (m : ℕ) (w : Vec d) (H : ℕ), H ≤ m →
      |(aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s m w η).toReal - (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s η m w H).toReal| ≤
        (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ))) :
    aux_prefix_rraw_CauchyInMeasure (chaosSampleLaw M).toMeasure
      (fun i omega => if n ≤ (phi i : ℤ) then
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z)
          (eta (phi i) omega)).toReal else 0) := by
  refine aux_prefix_rraw_cim_of_truncation (chaosSampleLaw M).toMeasure 1 one_pos
    (fun i omega => if n ≤ (phi i : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi i : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi i) • z) (eta (phi i) omega)).toReal else 0)
    (fun H i omega => if n ≤ (phi i : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta (phi i) omega)
        ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z) H).toReal else 0)
    (fun H _ _ => (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)))
    ?hS ?hVS ?hTm ?hTq
  case hS =>
    intro H
    obtain ⟨Gl, hGl⟩ := hshallow H
    exact aux_prefix_rraw_cim_of_tendstoInMeasure _ _ Gl hGl
  case hVS =>
    intro H
    refine ⟨(n + H).toNat, fun i hi => ?_⟩
    have hNle : (n + H : ℤ) ≤ (i : ℤ) :=
      (Int.self_le_toNat (n + H)).trans (by exact_mod_cast hi)
    have hphi_ge : (i : ℤ) ≤ (phi i : ℤ) := by exact_mod_cast hphi.id_le i
    have h1 : n ≤ (phi i : ℤ) := by omega
    have hz : (0 : ℤ) ≤ (phi i : ℤ) - n := by omega
    have h2 : H ≤ ((phi i : ℤ) - n).toNat := by
      rw [Int.le_toNat hz]
      push_cast
      omega
    refine Eventually.of_forall fun omega => ?_
    rw [if_pos h1]
    rw [if_pos h1]
    exact hsand (eta (phi i) omega) ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z) H h2
  case hTm =>
    intro H i
    exact aestronglyMeasurable_const
  case hTq =>
    intro ε hε
    have hlim : Tendsto (fun H : ℕ => (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      have hr : (3 : ℝ) ^ (-(s / 2)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hpow : Tendsto (fun k : ℕ => ((3 : ℝ) ^ (-(s / 2))) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) _) hr
      have hcomp : Tendsto (fun H : ℕ => ((3 : ℝ) ^ (-(s / 2))) ^ (H + 1)) atTop (𝓝 0) :=
        hpow.comp (tendsto_add_atTop_nat 1)
      have heq : (fun H : ℕ => (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)))
          = fun H : ℕ => ((3 : ℝ) ^ (-(s / 2))) ^ (H + 1) := by
        funext H
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      rw [heq]
      exact hcomp
    obtain ⟨H0, hH0⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
    refine ⟨H0, fun i => ?_⟩
    have hbd : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
        ‖(3 : ℝ) ^ (-(s / 2) * ((H0 + 1 : ℕ) : ℝ))‖ ≤ ε :=
      Eventually.of_forall fun _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (hH0 H0 le_rfl).le
    refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const hbd).trans ?_
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), inv_one, ENNReal.rpow_one,
      measure_univ, one_mul]

-- from flash order fg_t1_full
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t1_value_Lp_cauchy_full {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
            (eta (phi k) omega)).toReal else 0) -
        (if n ≤ (phi k' : ℤ) then
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z)
            (eta (phi k') omega)).toReal else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  refine aux_lem_prefix_limit_actual_coordinate_cauchy_t1_value_Lp_cauchy_of_cim M s eta n z phi
    ?_ ?_ ?_ p hp eps0 heps0
  · exact aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_aestronglyMeasurable M s eta hEta
  · intro k w om
    exact aux_psf_Dterm1_le_one M s hs k w om
  · exact aux_lem_prefix_limit_actual_coordinate_cauchy_t1_value_cim M s hs eta n z phi hphi
      (fun H =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_tendstoInMeasure M s hs eta n z phi hphi
          hAtoms
          (fun N H hN hne om =>
            aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_toReal_eq_atoms
              M s eta n z N H hN hne om)
          H)
      (fun η m w H hH =>
        aux_lem_prefix_limit_actual_coordinate_cauchy_abs_Dt1_sub_T1shallow_le M s η m w H
          (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_le_Dt1 M s η m w H hH)
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_le_max M s hs η m w H))

-- from flash order fg_draw_final
theorem aux_prefix_exact_Draw_value_Lp_cauchy_of_atoms {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (p : ℝ) (hp : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (Draw (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega).toReal
          else 0) -
        (if n ≤ (phi k' : ℤ) then
          (Draw (phi k') ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z) omega).toReal
          else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  have hsplit := aux_lem_prefix_limit_actual_coordinate_cauchy_Draw_value_split M s eps eta
    F Praw Rraw Draw Z rawGood hPrimitive
    (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_ne_top M s hs k w om)
    (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top s k w om)
    (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_ne_top s k w om)
    n z
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_ne_top M eta hEta
      (fun N => ((N : ℤ) - n).toNat) (fun N => (3 : ℝ) ^ N • z))
  refine aux_lem_prefix_limit_actual_coordinate_cauchy_add4_Lp_cauchy
    (chaosSampleLaw M).toMeasure p hp
    (fun k (omega : BilateralField d) => if n ≤ (phi k : ℤ) then
      (Draw (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega).toReal else 0)
    (fun k (omega : BilateralField d) => if n ≤ (phi k : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((phi k : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) (eta (phi k) omega)).toReal else 0)
    (fun k (omega : BilateralField d) => if n ≤ (phi k : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((phi k : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) (eta (phi k) omega)).toReal else 0)
    (fun k (omega : BilateralField d) => if n ≤ (phi k : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((phi k : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) (eta (phi k) omega)).toReal else 0)
    (fun k (omega : BilateralField d) => if n ≤ (phi k : ℤ) then
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((phi k : ℤ) - n).toNat
        ((3 : ℝ) ^ (phi k) • z) (eta (phi k) omega)).toReal else 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ eps0 heps0
  · intro k
    by_cases h : n ≤ (phi k : ℤ)
    · simpa only [if_pos h] using
        aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_aestronglyMeasurable M s eta hEta
          (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)
    · simp only [if_neg h]
      exact aestronglyMeasurable_const
  · intro k
    by_cases h : n ≤ (phi k : ℤ)
    · simpa only [if_pos h] using
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable M s eta hEta
          (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)).1
    · simp only [if_neg h]
      exact aestronglyMeasurable_const
  · intro k
    by_cases h : n ≤ (phi k : ℤ)
    · simpa only [if_pos h] using
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable M s eta hEta
          (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)).2.1
    · simp only [if_neg h]
      exact aestronglyMeasurable_const
  · intro k
    by_cases h : n ≤ (phi k : ℤ)
    · simpa only [if_pos h] using
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable M s eta hEta
          (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z)).2.2
    · simp only [if_neg h]
      exact aestronglyMeasurable_const
  · intro k
    filter_upwards [hsplit] with omega hω
    exact hω (phi k)
  · intro ε hε
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_t1_value_Lp_cauchy_full
      M s hs eta hEta n z phi hphi hAtoms p hp ε hε
  · intro ε hε
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_t2_value_Lp_cauchy_full
      M s hs eta hEta n z phi hphi p hp ε hε
  · intro ε hε
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_t3_value_Lp_cauchy_full
      M s hs eta hEta n z phi hphi p hp ε hε
  · intro ε hε
    exact aux_lem_prefix_limit_actual_coordinate_cauchy_t4_value_Lp_cauchy
      M eta hEta n z phi hphi p ε hε

end Paper

-- ===== PmrRrawBridge (verbatim) =====






open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

variable {d : ℕ} [NeZero d]
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Core: the raw response coordinate along `phi` is Cauchy in measure, measurable,
and uniformly bounded in `L^q`, given the atom input and an atom bank at order `q`. -/
theorem aux_prefix_rraw_value_cim_core (M : GMCModel d)
    (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (q b : ℝ) (hq1 : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q) (hb : 0 ≤ b)
    (hbank : ∀ (n : ℕ) (x : Vec d),
      eLpNorm (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal b) :
    let V : ℕ → BilateralField d → ℝ := fun i omega =>
      if n ≤ (phi i : ℤ) then
        (Rraw (phi i) ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z) omega).toReal else 0
    aux_prefix_rraw_CauchyInMeasure (chaosSampleLaw M).toMeasure V ∧
      (∀ i, AEStronglyMeasurable (V i) (chaosSampleLaw M).toMeasure) ∧
      (∀ i, eLpNorm (V i) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (0 + 1) * b)) := by
  intro V0
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hq0 : 0 < q := by linarith
  let mN : ℕ → ℕ := fun N => ((N : ℤ) - n).toNat
  let wN : ℕ → Vec d := fun N => (3 : ℝ) ^ N • z
  let V : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then (Rraw (phi i) (mN (phi i)) (wN (phi i)) omega).toReal else 0
  let S : ℕ → ℕ → BilateralField d → ℝ := fun H i omega =>
    (aux_prefix_rraw_shallow M s (eta (phi i) omega) (mN (phi i)) (wN (phi i)) H).toReal
  let T : ℕ → ℕ → BilateralField d → ℝ := fun H i omega =>
    (aux_prefix_rraw_tail M s (eta (phi i) omega) (mN (phi i)) (wN (phi i)) H).toReal
  -- the literal clause (4) identification, almost surely and for every cutoff
  have hgood : ∀ᵐ omega ∂μ, ∀ N,
      Rraw N (mN N) (wN N) omega = aux_prefix_rraw_Rset M s (eta N omega) (mN N) (wN N) := by
    filter_upwards [hPrimitive] with omega hω N
    obtain ⟨_, _, _, _, _, _, hR, _⟩ := hω N
    exact hR _ _
  have hdeep : ∀ H i, (n + (H : ℤ)).toNat ≤ i → n + (H : ℤ) ≤ (phi i : ℤ) := by
    intro H i hi
    have h1 : i ≤ phi i := hphi.id_le i
    have h2 : n + (H : ℤ) ≤ ((n + (H : ℤ)).toNat : ℤ) := Int.self_le_toNat _
    omega
  -- truncation: `V` is within the deep sum of the shallow supremum
  have hVS : ∀ H, ∃ N0 : ℕ, ∀ i, N0 ≤ i → ∀ᵐ omega ∂μ, |V i omega - S H i omega| ≤ T H i omega := by
    intro H
    refine ⟨(n + (H : ℤ)).toNat, fun i hi => ?_⟩
    have hd := hdeep H i hi
    filter_upwards [hgood] with omega hω
    have hn : n ≤ (phi i : ℤ) := by omega
    have hHm : H ≤ mN (phi i) := by simp only [mN]; omega
    simp only [V, S, T, if_pos hn, hω]
    exact aux_prefix_rraw_abs_Rset_sub_shallow_le M s _ _ _ H hHm
  -- the shallow supremum is Cauchy in measure (finitely many convergent atoms)
  have hS : ∀ H, aux_prefix_rraw_CauchyInMeasure μ (S H) := by
    intro H
    let f : ℕ × (Fin d → ℤ) → ℕ → BilateralField d → ℝ := fun rk i omega =>
      aux_prefix_rraw_atom M eta (phi i) (-n - (rk.1 : ℤ))
        (z + (3 : ℝ) ^ (-n - (rk.1 : ℤ)) • aux_prefix_rraw_kvec rk.2) omega
    have hf : ∀ rk ∈ aux_prefix_rraw_G d H, aux_prefix_rraw_CauchyInMeasure μ (f rk) := by
      intro rk _
      obtain ⟨lim, hlim⟩ := hAtoms (-n - (rk.1 : ℤ)) rk.2
      exact aux_prefix_rraw_cim_of_tendstoInMeasure μ (f rk) lim hlim
    refine aux_prefix_rraw_cim_of_sum_dominated μ (aux_prefix_rraw_G d H) f hf (S H)
      (n + (H : ℤ)).toNat fun i i' hi hi' => Eventually.of_forall fun omega => ?_
    have hdi := hdeep H i hi
    have hdi' := hdeep H i' hi'
    refine (aux_prefix_rraw_abs_toReal_sup_sub_le _ _ _
      (fun _ => ENNReal.mul_ne_top (aux_prefix_rraw_c_ne_top s _) (aux_prefix_rraw_A_ne_top M _ _ _ _ _))
      (fun _ => ENNReal.mul_ne_top (aux_prefix_rraw_c_ne_top s _) (aux_prefix_rraw_A_ne_top M _ _ _ _ _))).trans ?_
    refine Finset.sum_le_sum fun rk hrk => ?_
    have hrH : rk.1 ≤ H := by
      classical
      simp only [aux_prefix_rraw_G, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hrk
      exact hrk.1.1.2
    have hA := aux_prefix_rraw_A_eq_atom M eta n z (phi i) rk.1 rk.2 (by omega) omega
    have hA' := aux_prefix_rraw_A_eq_atom M eta n z (phi i') rk.1 rk.2 (by omega) omega
    simp only [f]
    rw [← hA, ← hA', ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have hc1 : (aux_prefix_rraw_c s rk.1).toReal ≤ 1 := by
      rw [aux_prefix_rraw_c, ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : 0 ≤ s * (rk.1 : ℝ) / 8 := by positivity
      linarith
    exact mul_le_of_le_one_left (abs_nonneg _) hc1
  -- measurability
  have hTm : ∀ H i, AEStronglyMeasurable (T H i) μ := by
    intro H i
    exact ((ENNReal.measurable_toReal.comp (aux_prefix_rraw_tail_measurable M s _ _ H)).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta (phi i))).aestronglyMeasurable
  have hVm : ∀ i, AEStronglyMeasurable (V i) μ := by
    intro i
    by_cases hn : n ≤ (phi i : ℤ)
    · simpa only [V, if_pos hn] using
        (aux_lem_prefix_limit_actual_Rraw_aemeas M s eps μ eta
          (fun N => prefix_eta_aemeasurable M eta hEta N)
          F Praw Rraw Draw Z rawGood hPrimitive (phi i) (mN (phi i)) (wN (phi i))).aestronglyMeasurable
    · simp only [V, if_neg hn]
      exact aestronglyMeasurable_const
  -- the uniform tail bound
  have hTbound : ∀ H i, eLpNorm (T H i) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (H + 1) * b) := by
    intro H i
    exact (aux_prefix_rraw_tail_eLpNorm_le M s eta hEta q b hq1 hbank (phi i) _ _ H).trans
      (aux_prefix_rraw_tail_numeric d s q hq0 hsq b hb H _)
  have hTq : ∀ ε : ℝ, 0 < ε → ∃ H, ∀ i,
      eLpNorm (T H i) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal ε := by
    intro ε hε
    have hρ0 := aux_prefix_rraw_rho_pos d s q
    have hρ1 := aux_prefix_rraw_rho_lt_one d s q hq0 hsq
    have hlim : Tendsto (fun H : ℕ =>
        aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (H + 1) * b) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp (tendsto_add_atTop_nat 1)
      simpa using (h.const_mul (aux_prefix_rraw_K d s q)).mul_const b
    obtain ⟨H, hH⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    exact ⟨H, fun i => (hTbound H i).trans (ENNReal.ofReal_le_ofReal hH.le)⟩
  -- the uniform higher moment of the coordinate
  have hVbound : ∀ i, eLpNorm (V i) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (0 + 1) * b) := by
    intro i
    refine le_trans ?_ (hTbound 0 i)
    refine eLpNorm_mono_ae_real (hVm i) ?_
    filter_upwards [hgood] with omega hω
    have hT0 : 0 ≤ T 0 i omega := ENNReal.toReal_nonneg
    by_cases hn : n ≤ (phi i : ℤ)
    · simp only [V, if_pos hn, hω, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact aux_prefix_rraw_Rset_toReal_le_tail_zero M s _ _ _
    · simp only [V, if_neg hn, norm_zero]
      exact hT0
  have hcim : aux_prefix_rraw_CauchyInMeasure μ V :=
    aux_prefix_rraw_cim_of_truncation μ q hq0 V S T hS hVS hTm hTq
  exact ⟨hcim, hVm, hVbound⟩



theorem aux_prefix_exact_Rraw_value_Lp_cauchy_of_atoms_core (M : GMCModel d)
    (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (p q b : ℝ) (hp1 : 1 ≤ p) (hpq : p < q) (hsq : 8 * (d : ℝ) < s * q) (hb : 0 ≤ b)
    (hbank : ∀ (n : ℕ) (x : Vec d),
      eLpNorm (fun η : PotentialSample d => (aux_psf_Jval M n η x).toReal)
        (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal b)
    (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (Rraw (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega).toReal
          else 0) -
        (if n ≤ (phi k' : ℤ) then
          (Rraw (phi k') ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z) omega).toReal
          else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  obtain ⟨hcim, hVm, hVbound⟩ := aux_prefix_rraw_value_cim_core M s eps hs eta hEta
    F Praw Rraw Draw Z rawGood hPrimitive n z phi hphi hAtoms q b (by linarith) hsq hb hbank
  exact aux_prefix_rraw_Lp_cauchy_of_cim (chaosSampleLaw M).toMeasure p q hp1 hpq _ hVm _
    ENNReal.ofReal_ne_top hVbound hcim eps0 heps0

/-- The moment order: above every requested moment and above the entropy margin
`8d/s` of the discount `3^{-s r/8}`. -/
def aux_prefix_rraw_q (d : ℕ) (s : ℝ) (moments : Finset ℝ) : ℝ :=
  2 + |16 * (d : ℝ) / s| + ∑ p ∈ moments, |p|

theorem aux_prefix_rraw_two_le_q (d : ℕ) (s : ℝ) (moments : Finset ℝ) :
    2 ≤ aux_prefix_rraw_q d s moments := by
  unfold aux_prefix_rraw_q
  have := Finset.sum_nonneg (fun p (_ : p ∈ moments) => abs_nonneg p)
  have := abs_nonneg (16 * (d : ℝ) / s)
  linarith

theorem aux_prefix_rraw_one_le_q (d : ℕ) (s : ℝ) (moments : Finset ℝ) :
    1 ≤ aux_prefix_rraw_q d s moments :=
  le_trans (by norm_num) (aux_prefix_rraw_two_le_q d s moments)

theorem aux_prefix_rraw_lt_q (d : ℕ) (s : ℝ) (moments : Finset ℝ) (p : ℝ)
    (hp : p ∈ insert 1 moments) : p < aux_prefix_rraw_q d s moments := by
  have h2 := aux_prefix_rraw_two_le_q d s moments
  rcases Finset.mem_insert.mp hp with rfl | hp
  · linarith
  · unfold aux_prefix_rraw_q
    have h1 : |p| ≤ ∑ p ∈ moments, |p| :=
      Finset.single_le_sum (f := fun p => |p|) (fun p _ => abs_nonneg p) hp
    have := abs_nonneg (16 * (d : ℝ) / s)
    linarith [le_abs_self p]

theorem aux_prefix_rraw_margin (d : ℕ) (s : ℝ) (hs : 0 < s) (moments : Finset ℝ) :
    8 * (d : ℝ) < s * aux_prefix_rraw_q d s moments := by
  have hq : 16 * (d : ℝ) / s + 2 ≤ aux_prefix_rraw_q d s moments := by
    unfold aux_prefix_rraw_q
    have := Finset.sum_nonneg (fun p (_ : p ∈ moments) => abs_nonneg p)
    have := le_abs_self (16 * (d : ℝ) / s)
    linarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc 8 * (d : ℝ) < 16 * (d : ℝ) + 2 * s := by linarith
    _ = s * (16 * (d : ℝ) / s + 2) := by field_simp
    _ ≤ s * aux_prefix_rraw_q d s moments := mul_le_mul_of_nonneg_left hq hs.le

/-- The landed atom bank, packaged. -/
theorem aux_prefix_rraw_bank_spec (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ q : ℝ, 1 ≤ q → ∃ δ0 : ℝ, 0 < δ0 ∧
        ∀ (M : GMCModel d), 0 < M.delta → M.delta ≤ δ0 →
          ∀ (n : ℕ) (x : Vec d),
          eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega x).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) :=
  aux_psf_exists_Jval_spatial_moment_small_disorder d

/-- The bank constant `C`. -/
def aux_prefix_rraw_C (d : ℕ) : ℝ :=
  Classical.choose (Classical.choose_spec (aux_prefix_rraw_bank_spec d))

theorem aux_prefix_rraw_C_spec (d : ℕ) :
    0 < aux_prefix_rraw_C d ∧
      ∀ q : ℝ, 1 ≤ q → ∃ δ0 : ℝ, 0 < δ0 ∧
        ∀ (M : GMCModel d), 0 < M.delta → M.delta ≤ δ0 →
          ∀ (n : ℕ) (x : Vec d),
          eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega x).toReal)
            (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (aux_prefix_rraw_C d * q * Real.log (2 + q) * M.delta ^ 2) :=
  (Classical.choose_spec (Classical.choose_spec (aux_prefix_rraw_bank_spec d))).2

/-- The disorder threshold of the raw response coordinate; it depends only on
`d`, `s` and the requested finite moment set, and precedes the model. -/
def aux_prefix_rraw_delta0 (d : ℕ) (s : ℝ) (moments : Finset ℝ) : ℝ :=
  Classical.choose ((aux_prefix_rraw_C_spec d).2 (aux_prefix_rraw_q d s moments)
    (aux_prefix_rraw_one_le_q d s moments))

theorem aux_prefix_rraw_delta0_spec (d : ℕ) (s : ℝ) (moments : Finset ℝ) :
    0 < aux_prefix_rraw_delta0 d s moments ∧
      ∀ (M : GMCModel d), 0 < M.delta → M.delta ≤ aux_prefix_rraw_delta0 d s moments →
        ∀ (n : ℕ) (x : Vec d),
        eLpNorm (fun omega : PotentialSample d => (aux_psf_Jval M n omega x).toReal)
          (ENNReal.ofReal (aux_prefix_rraw_q d s moments)) M.P.toMeasure ≤
          ENNReal.ofReal (aux_prefix_rraw_C d * aux_prefix_rraw_q d s moments *
            Real.log (2 + aux_prefix_rraw_q d s moments) * M.delta ^ 2) :=
  Classical.choose_spec ((aux_prefix_rraw_C_spec d).2 (aux_prefix_rraw_q d s moments)
    (aux_prefix_rraw_one_le_q d s moments))

theorem aux_prefix_rraw_delta0_pos (d : ℕ) (s : ℝ) (moments : Finset ℝ) :
    0 < aux_prefix_rraw_delta0 d s moments :=
  (aux_prefix_rraw_delta0_spec d s moments).1

/-- CONDITIONAL on `hAtoms`.  The exact frozen raw response coordinate (`Sum.inl 2`),
read along `phi`, is Cauchy in `L^p` for every `p ∈ insert 1 moments`, below the
threshold `aux_prefix_rraw_delta0 d s moments`. -/
theorem aux_prefix_exact_Rraw_value_Lp_cauchy_of_atoms (M : GMCModel d)
    (s eps : ℝ) (hs : 0 < s) (moments : Finset ℝ)
    (hM : M.delta ≤ aux_prefix_rraw_delta0 d s moments)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (p : ℝ) (hp : p ∈ insert 1 moments) (hp1 : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          (Rraw (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega).toReal
          else 0) -
        (if n ≤ (phi k' : ℤ) then
          (Rraw (phi k') ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z) omega).toReal
          else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hbank := (aux_prefix_rraw_delta0_spec d s moments).2 M hdelta hM
  have hq2 := aux_prefix_rraw_two_le_q d s moments
  have hb : 0 ≤ aux_prefix_rraw_C d * aux_prefix_rraw_q d s moments *
      Real.log (2 + aux_prefix_rraw_q d s moments) * M.delta ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (aux_prefix_rraw_C_spec d).1.le (by linarith))
      (Real.log_nonneg (by linarith))) (sq_nonneg _)
  exact aux_prefix_exact_Rraw_value_Lp_cauchy_of_atoms_core M s eps hs eta hEta
    F Praw Rraw Draw Z rawGood hPrimitive n z phi hphi hAtoms p
    (aux_prefix_rraw_q d s moments) _ hp1 (aux_prefix_rraw_lt_q d s moments p hp)
    (aux_prefix_rraw_margin d s hs moments) hb hbank eps0 heps0

/-- CONDITIONAL on `hAtoms`: Cauchy in measure of the raw response coordinate below
the threshold `aux_prefix_rraw_delta0 d s moments` (used by the ramped score `Z`). -/
theorem aux_prefix_rraw_value_cim_of_atoms (M : GMCModel d)
    (s eps : ℝ) (hs : 0 < s) (moments : Finset ℝ)
    (hM : M.delta ≤ aux_prefix_rraw_delta0 d s moments)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim) :
    aux_prefix_rraw_CauchyInMeasure (chaosSampleLaw M).toMeasure (fun i omega =>
      if n ≤ (phi i : ℤ) then
        (Rraw (phi i) ((phi i : ℤ) - n).toNat ((3 : ℝ) ^ (phi i) • z) omega).toReal else 0) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hbank := (aux_prefix_rraw_delta0_spec d s moments).2 M hdelta hM
  have hq2 := aux_prefix_rraw_two_le_q d s moments
  have hb : 0 ≤ aux_prefix_rraw_C d * aux_prefix_rraw_q d s moments *
      Real.log (2 + aux_prefix_rraw_q d s moments) * M.delta ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (aux_prefix_rraw_C_spec d).1.le (by linarith))
      (Real.log_nonneg (by linarith))) (sq_nonneg _)
  exact (aux_prefix_rraw_value_cim_core M s eps hs eta hEta F Praw Rraw Draw Z rawGood
    hPrimitive n z phi hphi hAtoms _ _ (by linarith) (aux_prefix_rraw_margin d s hs moments)
    hb hbank).1

end Paper


-- ===== PmrZBridge (verbatim) =====






open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess

namespace Paper

/-- The extended ramp is `1/(b-a)`-Lipschitz on finite arguments. -/
theorem aux_prefix_rraw_eramp_lip (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (X Y : ℝ≥0∞)
    (hX : X ≠ ⊤) (hY : Y ≠ ⊤) :
    |(min (1 : ℝ≥0∞) ((X - ENNReal.ofReal a) / ENNReal.ofReal (b - a))).toReal -
      (min (1 : ℝ≥0∞) ((Y - ENNReal.ofReal a) / ENNReal.ofReal (b - a))).toReal| ≤
      1 / (b - a) * |X.toReal - Y.toReal| := by
  have hba : 0 < b - a := by linarith
  have key : ∀ W : ℝ≥0∞, W ≠ ⊤ →
      (min (1 : ℝ≥0∞) ((W - ENNReal.ofReal a) / ENNReal.ofReal (b - a))).toReal =
        max (min 1 ((W.toReal - a) / (b - a))) 0 := by
    intro W hW
    conv_lhs => rw [← ENNReal.ofReal_toReal hW]
    rw [← ENNReal.ofReal_sub _ ha, ← ENNReal.ofReal_div_of_pos hba, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_mono.map_min, ENNReal.toReal_ofReal']
  rw [key X hX, key Y hY]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), ← sub_div, abs_div,
    abs_of_pos hba, div_eq_mul_one_div, mul_comm]
  ring_nf
  exact le_rfl

variable {d : ℕ} [NeZero d]
variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- CONDITIONAL on `hAtoms`.  The exact frozen ramped bad score (`Sum.inl 4`), read along
`phi`, is Cauchy in `L^p` for every `p ≥ 1`, below `min` of the product and response
thresholds. -/
theorem aux_prefix_exact_Z_value_Lp_cauchy_of_atoms (M : GMCModel d)
    (s eps : ℝ) (hs : 0 < s) (heps : 0 < eps) (moments : Finset ℝ)
    (hM : M.delta ≤ min (aux_prefix_praw_delta0 d s moments) (aux_prefix_rraw_delta0 d s moments))
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : Vec d) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hAtoms : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun i omega => aux_prefix_rraw_atom M eta (phi i) l
          (z + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim)
    (p : ℝ) (hp1 : 1 ≤ p) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ n0 : ℕ, ∀ k k' : ℕ, n0 ≤ k → n0 ≤ k' →
      eLpNorm (fun omega : BilateralField d =>
        (if n ≤ (phi k : ℤ) then
          Z (phi k) ((phi k : ℤ) - n).toNat ((3 : ℝ) ^ (phi k) • z) omega
          else 0) -
        (if n ≤ (phi k' : ℤ) then
          Z (phi k') ((phi k' : ℤ) - n).toNat ((3 : ℝ) ^ (phi k') • z) omega
          else 0))
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal eps0 := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let mN : ℕ → ℕ := fun N => ((N : ℤ) - n).toNat
  let wN : ℕ → Vec d := fun N => (3 : ℝ) ^ N • z
  let Fv : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then (F (phi i) (mN (phi i)) (wN (phi i)) omega).toReal else 0
  let Pv : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then (Praw (phi i) (mN (phi i)) (wN (phi i)) omega).toReal else 0
  let Rv : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then (Rraw (phi i) (mN (phi i)) (wN (phi i)) omega).toReal else 0
  let Zv : ℕ → BilateralField d → ℝ := fun i omega =>
    if n ≤ (phi i : ℤ) then Z (phi i) (mN (phi i)) (wN (phi i)) omega else 0
  have hEtaMeas : ∀ N, AEMeasurable (eta N) μ := fun N => prefix_eta_aemeasurable M eta hEta N
  have hMP : M.delta ≤ aux_prefix_praw_delta0 d s moments := hM.trans (min_le_left _ _)
  have hMR : M.delta ≤ aux_prefix_rraw_delta0 d s moments := hM.trans (min_le_right _ _)
  -- the three constituent coordinates are Cauchy in measure
  have hFm : ∀ i, AEStronglyMeasurable (Fv i) μ := by
    intro i
    by_cases hn : n ≤ (phi i : ℤ)
    · simpa only [Fv, if_pos hn] using (aux_lem_prefix_limit_actual_Fsc_raw_aemeas M s eps μ eta
        hEtaMeas F Praw Rraw Draw Z rawGood hPrimitive (phi i) _ _).aestronglyMeasurable
    · simp only [Fv, if_neg hn]; exact aestronglyMeasurable_const
  have hPm : ∀ i, AEStronglyMeasurable (Pv i) μ := by
    intro i
    by_cases hn : n ≤ (phi i : ℤ)
    · simpa only [Pv, if_pos hn] using (aux_lem_prefix_limit_actual_Praw_raw_aemeas M s eps μ eta
        hEtaMeas F Praw Rraw Draw Z rawGood hPrimitive (phi i) _ _).aestronglyMeasurable
    · simp only [Pv, if_neg hn]; exact aestronglyMeasurable_const
  have hFc : aux_prefix_rraw_CauchyInMeasure μ Fv :=
    aux_prefix_rraw_cim_of_Lp_cauchy μ 1 one_pos Fv hFm fun ε hε =>
      aux_prefix_exact_Fsc_value_Lp_cauchy M s eps hs eta hEta F Praw Rraw Draw Z rawGood
        hPrimitive n z phi hphi 1 le_rfl ε hε
  have hPc : aux_prefix_rraw_CauchyInMeasure μ Pv :=
    aux_prefix_rraw_cim_of_Lp_cauchy μ 1 one_pos Pv hPm fun ε hε =>
      aux_prefix_exact_Praw_value_Lp_cauchy M s eps hs moments hMP eta hEta
        F Praw Rraw Draw Z rawGood hPrimitive n z phi hphi 1 (Finset.mem_insert_self 1 moments)
        le_rfl ε hε
  have hRc : aux_prefix_rraw_CauchyInMeasure μ Rv :=
    aux_prefix_rraw_value_cim_of_atoms M s eps hs moments hMR eta hEta F Praw Rraw Draw Z
      rawGood hPrimitive n z phi hphi hAtoms
  -- Lipschitz constants of the three ramps
  set c1 : ℝ := 1 / (eps - eps / 2) with hc1
  set c2 : ℝ := 1 / ((12 : ℝ) - 6) with hc2
  set c3 : ℝ := 1 / (eps ^ 2 - eps ^ 2 / 4) with hc3
  let f : Fin 3 → ℕ → BilateralField d → ℝ :=
    ![fun i omega => c1 * Fv i omega, fun i omega => c2 * Pv i omega,
      fun i omega => c3 * Rv i omega]
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin 3)), aux_prefix_rraw_CauchyInMeasure μ (f j) := by
    intro j _
    fin_cases j
    · exact aux_prefix_rraw_cim_const_mul μ Fv c1 hFc
    · exact aux_prefix_rraw_cim_const_mul μ Pv c2 hPc
    · exact aux_prefix_rraw_cim_const_mul μ Rv c3 hRc
  -- almost surely: the ramp formula, the bound, and finiteness at every cutoff
  have hFfin : ∀ᵐ omega ∂μ, ∀ N, F N (mN N) (wN N) omega ≠ ⊤ :=
    ae_all_iff.mpr fun N => prefix_eta_raw_Fsc_ae_finite M s eps hs eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N _ _
  have hPfin : ∀ᵐ omega ∂μ, ∀ N, Praw N (mN N) (wN N) omega ≠ ⊤ :=
    ae_all_iff.mpr fun N => aux_prefix_praw_actual_ae_finite M s eps hs moments hMP eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N _ _
  have hZform : ∀ᵐ omega ∂μ, ∀ N,
      Rraw N (mN N) (wN N) omega ≠ ⊤ ∧
      Z N (mN N) (wN N) omega =
        (min (1 : ENNReal) ((F N (mN N) (wN N) omega - ENNReal.ofReal (eps / 2)) /
          ENNReal.ofReal (eps - eps / 2))).toReal +
        (min (1 : ENNReal) ((Praw N (mN N) (wN N) omega - ENNReal.ofReal 6) /
          ENNReal.ofReal ((12 : ℝ) - 6))).toReal +
        (min (1 : ENNReal) ((Rraw N (mN N) (wN N) omega - ENNReal.ofReal (eps ^ 2 / 4)) /
          ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal ∧
      0 ≤ Z N (mN N) (wN N) omega ∧ Z N (mN N) (wN N) omega ≤ 3 := by
    filter_upwards [hPrimitive] with omega hω N
    have hprim := hω N
    have hRfin : Rraw N (mN N) (wN N) omega ≠ ⊤ := by
      obtain ⟨_, _, _, _, _, _, hR, _⟩ := hprim
      have hRset : Rraw N (mN N) (wN N) omega =
          aux_prefix_rraw_Rset M s (eta N omega) (mN N) (wN N) := hR _ _
      rw [hRset]
      exact aux_psf_Rsc_ne_top M s (mN N) (wN N) (eta N omega)
    rw [Paper.primitive_scores] at hprim
    obtain ⟨_, _, _, _, _, _, _, _, _, hZ, _⟩ := hprim
    obtain ⟨hZeq, hZ0, hZ3⟩ := hZ (mN N) (wN N)
    dsimp only at hZeq
    exact ⟨hRfin, hZeq, hZ0, hZ3⟩
  have hdeep : ∀ i, n.toNat ≤ i → n ≤ (phi i : ℤ) := by
    intro i hi
    have h1 : i ≤ phi i := hphi.id_le i
    have h2 : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n
    omega
  have hZc : aux_prefix_rraw_CauchyInMeasure μ Zv := by
    refine aux_prefix_rraw_cim_of_sum_dominated μ Finset.univ f hf Zv n.toNat
      fun i i' hi hi' => ?_
    filter_upwards [hZform, hFfin, hPfin] with omega hZ hF hP
    have hn := hdeep i hi
    have hn' := hdeep i' hi'
    obtain ⟨hR1, hZ1, -, -⟩ := hZ (phi i)
    obtain ⟨hR2, hZ2, -, -⟩ := hZ (phi i')
    have e1 := aux_prefix_rraw_eramp_lip (eps / 2) eps (by positivity) (by linarith)
      _ _ (hF (phi i)) (hF (phi i'))
    have e2 := aux_prefix_rraw_eramp_lip 6 12 (by norm_num) (by norm_num)
      _ _ (hP (phi i)) (hP (phi i'))
    have e3 := aux_prefix_rraw_eramp_lip (eps ^ 2 / 4) (eps ^ 2) (by positivity)
      (by nlinarith [sq_pos_of_pos heps]) _ _ hR1 hR2
    simp only [Fin.sum_univ_three, f, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Zv, Fv, Pv, Rv,
      if_pos hn, if_pos hn']
    rw [hZ1, hZ2, ← mul_sub, ← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_mul]
    have hc1n : |c1| = c1 := abs_of_pos (by rw [hc1]; apply one_div_pos.mpr; linarith)
    have hc2n : |c2| = c2 := abs_of_pos (by rw [hc2]; norm_num)
    have hc3n : |c3| = c3 := abs_of_pos (by
      rw [hc3]; apply one_div_pos.mpr; nlinarith [sq_pos_of_pos heps])
    rw [hc1n, hc2n, hc3n]
    have htri : ∀ a b c a' b' c' : ℝ,
        |(a + b + c) - (a' + b' + c')| ≤ |a - a'| + |b - b'| + |c - c'| := by
      intro a b c a' b' c'
      calc |(a + b + c) - (a' + b' + c')| = |(a - a') + (b - b') + (c - c')| := by ring_nf
        _ ≤ |(a - a') + (b - b')| + |c - c'| := abs_add_le _ _
        _ ≤ |a - a'| + |b - b'| + |c - c'| := by gcongr; exact abs_add_le _ _
    refine (htri _ _ _ _ _ _).trans ?_
    gcongr
  -- the uniform bound `|Z| ≤ 3`
  have hZm : ∀ i, AEStronglyMeasurable (Zv i) μ := by
    intro i
    by_cases hn : n ≤ (phi i : ℤ)
    · simpa only [Zv, if_pos hn] using (actual_Z_aemeas M s eps μ eta hEtaMeas
        F Praw Rraw Draw Z rawGood hPrimitive (phi i) _ _).aestronglyMeasurable
    · simp only [Zv, if_neg hn]; exact aestronglyMeasurable_const
  have hZb : ∀ i, eLpNorm (Zv i) (ENNReal.ofReal (p + 1)) μ ≤ ENNReal.ofReal 3 := by
    intro i
    have hbd : ∀ᵐ omega ∂μ, ‖Zv i omega‖ ≤ 3 := by
      filter_upwards [hZform] with omega hZ
      obtain ⟨-, -, hZ0, hZ3⟩ := hZ (phi i)
      by_cases hn : n ≤ (phi i : ℤ)
      · simp only [Zv, if_pos hn, Real.norm_eq_abs, abs_of_nonneg hZ0]; exact hZ3
      · simp only [Zv, if_neg hn, norm_zero]; norm_num
    refine (eLpNorm_le_of_ae_bound (hZm i) hbd).trans ?_
    simp
  exact aux_prefix_rraw_Lp_cauchy_of_cim μ p (p + 1) hp1 (by linarith) Zv hZm _
    ENNReal.ofReal_ne_top hZb hZc eps0 heps0

end Paper

end LemPrefixLimitActualCoordinateCauchyHelpers

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper



theorem lem_prefix_limit_actual_coordinate_cauchy
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I)
    (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d)
    (moments : Finset ℝ) (hmom : ∀ p ∈ moments, 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
    ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
    ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n))
    (Pos : Type) [Countable Pos]
    (level : Pos → ℤ) (centre : Pos → SpatialCoordinates d)
    (phi : ℕ → ℕ) (hphi : StrictMono phi),
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun n z omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) z
        else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) z
    let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun N n z omega => kappa ((N : ℤ) - n).toNat / kappa N *
        Real.exp (H omega z + retained n z omega)
    let Test := Fin 5 ⊕ (Fin T × (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)))
    let value : ℕ → ℤ → SpatialCoordinates d → Test → BilateralField d → ℝ :=
      fun N n z test omega =>
        Sum.elim
          (fun j => if n ≤ (N : ℤ) then
            let m := ((N : ℤ) - n).toNat
            let w := (3 : ℝ) ^ N • z
            if j = 0 then (F N m w omega).toReal
            else if j = 1 then (Praw N m w omega).toReal
            else if j = 2 then (Rraw N m w omega).toReal
            else if j = 3 then (Draw N m w omega).toReal
            else Z N m w omega
          else 0)
          (fun ij =>
            let i := ij.1
            let m := n + offset i
            let w := z + ((3 : ℝ) ^ (-n)) • shift i
            let r := (3 : ℝ) ^ (-m)
            let aN := Lane4.cutoffPositiveCoefficient M H omega N w (sidePos m)
            let ref := reference N m w omega
            if n ≤ (N : ℤ) ∧ m ≤ (N : ℤ) then
              Sum.elim
                (fun j => if j = 0 then I.lam w r (sidePos m) aN w r sigma 2 / ref
                  else if j = 1 then I.Lam w r (sidePos m) aN w r sigma 2 / ref
                  else ref / I.lam w r (sidePos m) aN w r sigma 2)
                (Sum.elim
                  (fun ab => if ab.1 then
                    (Homogenization.Book.Ch02.sigmaCoarse
                      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                      ((I.chart w r (sidePos m) aN w r).coeffOn
                        (Homogenization.originCube d 0))) ab.2.1 ab.2.2 / ref
                    else ref * (Homogenization.Book.Ch02.sigmaStarInvCoarse
                      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                      ((I.chart w r (sidePos m) aN w r).coeffOn
                        (Homogenization.originCube d 0))) ab.2.1 ab.2.2)
                  (fun j => if j = 0 then I.err w r (sidePos m) aN w r ref s 2
                    else reference N n z omega / ref)) ij.2
            else 0) test
    ∀ (hResponse :
      (∀ p ∈ insert 1 moments, ∃ q : ℝ, p < q ∧
        ∃ B : ℝ≥0∞, ∀ (pos : Pos) (j : ℤ) (i : Fin T)
          (rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)) (N : ℕ),
          MemLp
              (fun omega =>
                value N (level pos + j) (centre pos)
                  (Sum.inr (i, rt)) omega)
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
            eLpNorm
                (fun omega =>
                  value N (level pos + j) (centre pos)
                    (Sum.inr (i, rt)) omega)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ B) ∧
      (∀ p ∈ insert 1 moments, ∀ (pos : Pos) (j : ℤ) (i : Fin T)
          (rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)),
          ∃ lim : BilateralField d → ℝ,
            AEStronglyMeasurable lim (chaosSampleLaw M).toMeasure ∧
            Tendsto
              (fun n =>
                eLpNorm
                  (fun omega =>
                    value (phi n) (level pos + j) (centre pos)
                      (Sum.inr (i, rt)) omega - lim omega)
                  (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
              atTop (𝓝 0))),
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∀ p ∈ insert 1 moments, ∀ pos j test (ε : ℝ), 0 < ε →
      ∃ n₀ : ℕ, ∀ n n' : ℕ, n₀ ≤ n → n₀ ≤ n' →
        eLpNorm (fun omega =>
          value (phi (psi n)) (level pos + j) (centre pos) test omega -
            value (phi (psi n')) (level pos + j) (centre pos) test omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal ε
    := by
  have hExtract0 := lem_prefix_limit_atom_extraction d hd I _Poincare _Extension
    _Perturbation _Sobolev D
  obtain ⟨deltaA, hdA, hExtract⟩ := hExtract0
  refine ⟨min (min (aux_prefix_praw_delta0 d s moments) (aux_prefix_rraw_delta0 d s moments))
    deltaA, lt_min (lt_min (aux_prefix_praw_delta0_pos d s hs.1 moments)
      (aux_prefix_rraw_delta0_pos d s moments)) hdA, ?_⟩
  intro M hMmin Rm hRmC Sreg _It H hH eta hEta F Praw Rraw Draw Z rawGood
    hPrimitive sidePos Pos _ level centre phi hphi
  have hMPR : M.delta ≤ min (aux_prefix_praw_delta0 d s moments)
      (aux_prefix_rraw_delta0 d s moments) := hMmin.trans (min_le_left _ _)
  have hM : M.delta ≤ aux_prefix_praw_delta0 d s moments := hMPR.trans (min_le_left _ _)
  have hMR : M.delta ≤ aux_prefix_rraw_delta0 d s moments := hMPR.trans (min_le_right _ _)
  have hMA : M.delta ≤ deltaA := hMmin.trans (min_le_right _ _)
  intro kappa retained reference Test value hResponse
  -- Joint extraction, inside `phi`, of the zero-infrared response atoms that the raw scores
  -- Rraw, Draw and Z read (paper 2749--2751 via mfd:prop-response-compact).
  obtain ⟨psi, hpsi, hAtoms⟩ : ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∀ (pos : Pos) (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun i omega =>
            if 0 ≤ l + ((phi (psi i) : ℕ) : ℤ) then
              (aux_psf_Jval M (l + ((phi (psi i) : ℕ) : ℤ)).toNat (eta (phi (psi i)) omega)
                ((3 : ℝ) ^ (phi (psi i)) •
                  (centre pos + (3 : ℝ) ^ l • (fun c => ((k c : ℤ) : ℝ))))).toReal
            else 0) atTop lim :=
    hExtract M hMA Rm Sreg _It eta hEta Pos centre phi hphi
  refine ⟨psi, hpsi, ?_⟩
  intro p hp pos jz test eps0 heps0
  obtain ⟨hbank, hconv⟩ := hResponse
  have hp1 : (1 : ℝ) ≤ p := by
    rcases Finset.mem_insert.mp hp with h | h
    · exact le_of_eq h.symm
    · exact hmom p h
  have hphipsi : StrictMono (phi ∘ psi) := hphi.comp hpsi
  rcases test with jj | ⟨i, rt⟩
  · by_cases hj : jj = 0
    · subst hj
      exact aux_prefix_exact_Fsc_value_Lp_cauchy M s eps hs.1 eta hEta
        F Praw Rraw Draw Z rawGood hPrimitive
        (level pos + jz) (centre pos) (phi ∘ psi) hphipsi p hp1 eps0 heps0
    · by_cases hj1 : jj = 1
      · subst hj1
        exact aux_prefix_exact_Praw_value_Lp_cauchy M s eps hs.1 moments hM eta hEta
          F Praw Rraw Draw Z rawGood hPrimitive (level pos + jz) (centre pos) (phi ∘ psi)
          hphipsi p hp hp1 eps0 heps0
      · -- Raw coordinates 2–4 (Rraw, Draw, Z) read the zero-infrared atoms extracted above
        -- (paper 2746--2763, primitive_scores clauses (4)--(6)).
        have hAt : ∀ (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (fun i omega => aux_prefix_rraw_atom M eta ((phi ∘ psi) i) l
                (centre pos + (3 : ℝ) ^ l • aux_prefix_rraw_kvec k) omega) atTop lim :=
          fun l k => hAtoms pos l k
        by_cases hj2 : jj = 2
        · subst hj2
          exact aux_prefix_exact_Rraw_value_Lp_cauchy_of_atoms M s eps hs.1 moments hMR eta
            hEta F Praw Rraw Draw Z rawGood hPrimitive (level pos + jz) (centre pos)
            (phi ∘ psi) hphipsi hAt p hp hp1 eps0 heps0
        · by_cases hj3 : jj = 3
          · subst hj3
            exact aux_prefix_exact_Draw_value_Lp_cauchy_of_atoms M s eps hs.1 eta hEta
              F Praw Rraw Draw Z rawGood hPrimitive (level pos + jz) (centre pos)
              (phi ∘ psi) hphipsi hAt p hp1 eps0 heps0
          · have hj4 : jj = 4 := by
              have key : ∀ x : Fin 5, ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → x = 4 := by
                decide
              exact key jj hj hj1 hj2 hj3
            subst hj4
            exact aux_prefix_exact_Z_value_Lp_cauchy_of_atoms M s eps hs.1 heps.1 moments hMPR
              eta hEta F Praw Rraw Draw Z rawGood hPrimitive (level pos + jz) (centre pos)
              (phi ∘ psi) hphipsi hAt p hp1 eps0 heps0
  · -- Response coordinates (`Sum.inr`): `hResponse` along `phi`, composed with `psi`.
    obtain ⟨q, _hpq, B, hB⟩ := hbank p hp
    obtain ⟨limit, hlimmeas, hlimtend⟩ := hconv p hp pos jz i rt
    exact aux_prefix_limit_cauchy_of_tendsto (chaosSampleLaw M).toMeasure p hp1
      (fun n omega => value (phi (psi n)) (level pos + jz) (centre pos) (Sum.inr (i, rt)) omega)
      limit (fun n => (hB pos jz i rt (phi (psi n))).1.aestronglyMeasurable) hlimmeas
      (hlimtend.comp hpsi.tendsto_atTop) eps0 heps0

end Paper
