module

public import SubdiffusiveProcess.Paper.lem_local_normalizations_regroup
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Sobolev.H1.BasicLemmas
public import SubdiffusiveProcess.Paper.lem_local_normalizations_common_smooth
public import SubdiffusiveProcess.Paper.lem_local_normalizations_common_affine
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_dirichlet_response
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_gluing
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_layer_norms
public import SubdiffusiveProcess.Paper.lem_15
public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lem_17
public import SubdiffusiveProcess.Paper.lem_compact_responses
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.lem_local_normalizations_full_cutoff
public import Mathlib
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.lem_extension_trace_class_transport
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_smooth_net
public import SubdiffusiveProcess.Paper.lem_finite_trace_holder_beta_bound
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Paper.in_deterministic_matrix_bounds
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.Probability.ConditionalPullback
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section LNHelpers
open scoped Pointwise ContDiff

-- ===== from LNRatio.lean =====

/-- Every cluster value of `c` along a subsequence satisfies `X = e * Y` a.s. -/
theorem aux_lem_local_normalizations_ratio_cluster
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (c : ℕ → ℝ) (X Y : ℕ → Ω → ℝ) (Xl Yl : Ω → ℝ)
    (hX : TendstoInMeasure μ X atTop Xl) (hY : TendstoInMeasure μ Y atTop Yl)
    (N0 : ℕ) (hid : ∀ N, N0 ≤ N → ∀ᵐ om ∂μ, X N om = c N * Y N om)
    (ψ : ℕ → ℕ) (hψt : Tendsto ψ atTop atTop) (e : ℝ)
    (hce : Tendsto (c ∘ ψ) atTop (𝓝 e)) :
    ∀ᵐ om ∂μ, Xl om = e * Yl om := by
  have hXψ : TendstoInMeasure μ (fun n => X (ψ n)) atTop Xl := hX.comp hψt
  obtain ⟨ns, hns, hXns⟩ := hXψ.exists_seq_tendsto_ae
  have hYψ : TendstoInMeasure μ (fun n => Y (ψ (ns n))) atTop Yl :=
    hY.comp (hψt.comp hns.tendsto_atTop)
  obtain ⟨ms, hms, hYms⟩ := hYψ.exists_seq_tendsto_ae
  have hall : ∀ᵐ om ∂μ, ∀ N : ℕ, N0 ≤ N → X N om = c N * Y N om := by
    rw [ae_all_iff]
    intro N
    by_cases hN : N0 ≤ N
    · filter_upwards [hid N hN] with om hom _ using hom
    · exact ae_of_all _ fun om h => absurd h hN
  filter_upwards [hXns, hYms, hall] with om hXo hYo hallo
  let k : ℕ → ℕ := fun n => ψ (ns (ms n))
  have hk : Tendsto k atTop atTop :=
    hψt.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
  have hXk : Tendsto (fun n => X (k n) om) atTop (𝓝 (Xl om)) :=
    hXo.comp hms.tendsto_atTop
  have hck : Tendsto (fun n => c (k n)) atTop (𝓝 e) :=
    hce.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
  have hprod : Tendsto (fun n => c (k n) * Y (k n) om) atTop (𝓝 (e * Yl om)) :=
    hck.mul hYo
  have heq : (fun n => X (k n) om) =ᶠ[atTop] (fun n => c (k n) * Y (k n) om) := by
    filter_upwards [hk.eventually_ge_atTop N0] with n hn using hallo (k n) hn
  exact tendsto_nhds_unique (hXk.congr' heq) hprod

/-- **Scalar ratio limit.** A deterministic sequence in a compact positive
interval that relates two sequences converging in probability, the second
to an a.s. positive limit, converges to a positive constant. -/
theorem aux_lem_local_normalizations_ratio_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [NeZero μ]
    (c : ℕ → ℝ) (a b : ℝ) (ha : 0 < a) (hc : ∀ N, c N ∈ Icc a b)
    (X Y : ℕ → Ω → ℝ) (Xl Yl : Ω → ℝ)
    (hX : TendstoInMeasure μ X atTop Xl) (hY : TendstoInMeasure μ Y atTop Yl)
    (N0 : ℕ) (hid : ∀ N, N0 ≤ N → ∀ᵐ om ∂μ, X N om = c N * Y N om)
    (hYpos : ∀ᵐ om ∂μ, 0 < Yl om) :
    ∃ e : ℝ, 0 < e ∧ Tendsto c atTop (𝓝 e) ∧ ∀ᵐ om ∂μ, Xl om = e * Yl om := by
  have hK : IsCompact (Icc a b) := isCompact_Icc
  -- any two cluster values coincide
  have huniq : ∀ (ψ₁ ψ₂ : ℕ → ℕ) (e₁ e₂ : ℝ), Tendsto ψ₁ atTop atTop →
      Tendsto ψ₂ atTop atTop →
      Tendsto (c ∘ ψ₁) atTop (𝓝 e₁) → Tendsto (c ∘ ψ₂) atTop (𝓝 e₂) → e₁ = e₂ := by
    intro ψ₁ ψ₂ e₁ e₂ h₁ h₂ hc₁ hc₂
    have hE₁ := aux_lem_local_normalizations_ratio_cluster μ c X Y Xl Yl hX hY N0 hid
      ψ₁ h₁ e₁ hc₁
    have hE₂ := aux_lem_local_normalizations_ratio_cluster μ c X Y Xl Yl hX hY N0 hid
      ψ₂ h₂ e₂ hc₂
    have hev : ∀ᵐ om ∂μ, e₁ = e₂ := by
      filter_upwards [hE₁, hE₂, hYpos] with om h1 h2 hp
      have h := h1.symm.trans h2
      exact mul_right_cancel₀ hp.ne' h
    by_contra hne
    have hnull : μ Set.univ = 0 := by
      have h0 : μ {om | e₁ = e₂}ᶜ = 0 := hev
      simpa [hne] using h0
    exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp hnull)
  obtain ⟨e, he, φ, hφ, hcφ⟩ := hK.tendsto_subseq hc
  refine ⟨e, lt_of_lt_of_le ha he.1, ?_, ?_⟩
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨e', _, φ', hφ', hcφ'⟩ := hK.tendsto_subseq (fun n => hc (ns n))
    have hee' : e' = e := huniq (ns ∘ φ') φ e' e (hns.comp hφ'.tendsto_atTop)
      hφ.tendsto_atTop (by simpa [Function.comp_def] using hcφ') hcφ
    refine ⟨φ', ?_⟩
    rw [← hee']
    simpa [Function.comp_def] using hcφ'
  · exact aux_lem_local_normalizations_ratio_cluster μ c X Y Xl Yl hX hY N0 hid φ
      hφ.tendsto_atTop e hcφ

/-- The ratio is eventually bounded above: otherwise the product would blow up on the
positive-limit event. -/
theorem aux_lem_local_normalizations_ratio_bdd
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [NeZero μ]
    (c : ℕ → ℝ) (X Y : ℕ → Ω → ℝ) (Xl Yl : Ω → ℝ)
    (hX : TendstoInMeasure μ X atTop Xl) (hY : TendstoInMeasure μ Y atTop Yl)
    (N0 : ℕ) (hid : ∀ N, N0 ≤ N → ∀ᵐ om ∂μ, X N om = c N * Y N om)
    (hYpos : ∀ᵐ om ∂μ, 0 < Yl om) :
    ∃ b : ℝ, ∃ N1 : ℕ, ∀ N, N1 ≤ N → c N ≤ b := by
  by_contra hnot
  push Not at hnot
  have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop, (n : ℝ) < c k := by
    intro n
    rw [frequently_atTop]
    intro N1
    obtain ⟨N, hN, hc⟩ := hnot n N1
    exact ⟨N, hN, hc⟩
  obtain ⟨φ, hφ, hφc⟩ := Filter.extraction_forall_of_frequently hfreq
  have hcφ : Tendsto (fun n => c (φ n)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => (hφc n).le) tendsto_natCast_atTop_atTop
  obtain ⟨ns, hns, hXns⟩ := (hX.comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hYms⟩ :=
    (hY.comp (hφ.tendsto_atTop.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ om ∂μ, ∀ N : ℕ, N0 ≤ N → X N om = c N * Y N om := by
    rw [ae_all_iff]
    intro N
    by_cases hN : N0 ≤ N
    · filter_upwards [hid N hN] with om hom _ using hom
    · exact ae_of_all _ fun om h => absurd h hN
  have hfalse : ∀ᵐ om ∂μ, False := by
    filter_upwards [hXns, hYms, hall, hYpos] with om hXo hYo hallo hpos
    let k : ℕ → ℕ := fun n => φ (ns (ms n))
    have hk : Tendsto k atTop atTop :=
      hφ.tendsto_atTop.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
    have hXk : Tendsto (fun n => X (k n) om) atTop (𝓝 (Xl om)) := hXo.comp hms.tendsto_atTop
    have hck : Tendsto (fun n => c (k n)) atTop atTop :=
      hcφ.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
    have hprod : Tendsto (fun n => c (k n) * Y (k n) om) atTop atTop :=
      hck.atTop_mul_pos hpos hYo
    have heq : (fun n => X (k n) om) =ᶠ[atTop] (fun n => c (k n) * Y (k n) om) := by
      filter_upwards [hk.eventually_ge_atTop N0] with n hn using hallo (k n) hn
    exact not_tendsto_atTop_of_tendsto_nhds hXk (hprod.congr' heq.symm)
  have hnull : μ Set.univ = 0 := by
    rw [ae_iff] at hfalse
    simpa using hfalse
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp hnull)

/-- **Scalar ratio limit with a lower bound only.** -/
theorem aux_lem_local_normalizations_ratio_limit_lb
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [NeZero μ]
    (c : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (N0 : ℕ) (hc : ∀ N, N0 ≤ N → a ≤ c N)
    (X Y : ℕ → Ω → ℝ) (Xl Yl : Ω → ℝ)
    (hX : TendstoInMeasure μ X atTop Xl) (hY : TendstoInMeasure μ Y atTop Yl)
    (hid : ∀ N, N0 ≤ N → ∀ᵐ om ∂μ, X N om = c N * Y N om)
    (hYpos : ∀ᵐ om ∂μ, 0 < Yl om) :
    ∃ e : ℝ, 0 < e ∧ Tendsto c atTop (𝓝 e) ∧ ∀ᵐ om ∂μ, Xl om = e * Yl om := by
  obtain ⟨b, N1, hb⟩ := aux_lem_local_normalizations_ratio_bdd μ c X Y Xl Yl hX hY N0 hid hYpos
  set N2 := max N0 N1
  have hshift : Tendsto (fun N => N + N2) atTop atTop := tendsto_add_atTop_nat N2
  obtain ⟨e, he, hce, hXe⟩ := aux_lem_local_normalizations_ratio_limit μ
    (fun N => c (N + N2)) a b ha
    (fun N => ⟨hc _ (by omega), hb _ (by omega)⟩)
    (fun N => X (N + N2)) (fun N => Y (N + N2)) Xl Yl (hX.comp hshift) (hY.comp hshift) 0
    (fun N _ => hid _ (by omega)) hYpos
  exact ⟨e, he, (tendsto_add_atTop_iff_nat N2).1 hce, hXe⟩

-- ===== from LNSemi.lean =====

/-! ### Elementary real inequalities -/

theorem aux_lem_local_normalizations_abs_sqrt_sub_le (a b : ℝ) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this b a (le_of_not_ge hab)
  have hsab : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
  rw [abs_of_nonneg (sub_nonneg.2 hsab), abs_of_nonneg (sub_nonneg.2 hab)]
  rcases le_or_gt b 0 with hb | hb
  · rw [Real.sqrt_eq_zero'.2 hb, sub_zero]
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [sub_le_iff_le_add]
    rw [Real.sqrt_le_left]
    · have h1 := Real.sq_sqrt (sub_nonneg.2 hab)
      have h2 := Real.sq_sqrt hb.le
      nlinarith [Real.sqrt_nonneg (a - b), Real.sqrt_nonneg b]
    · positivity

/-- `√(x+y)`-subadditivity of a symmetric positive semidefinite bilinear form. -/
theorem aux_lem_local_normalizations_sqrt_form_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hsymm : ∀ x y, F x y = F y x) (hpos : ∀ x, 0 ≤ F x x)
    (x y : E) :
    Real.sqrt (F (x + y) (x + y)) ≤ Real.sqrt (F x x) + Real.sqrt (F y y) := by
  have hcs : F x y ≤ Real.sqrt (F x x) * Real.sqrt (F y y) := by
    -- discriminant argument
    have hq : ∀ t : ℝ, 0 ≤ F x x - 2 * t * F x y + t ^ 2 * F y y := by
      intro t
      have := hpos (x - t • y)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] at this
      rw [hsymm y x] at this
      nlinarith [this]
    rcases (hpos y).lt_or_eq with hy | hy
    · have h := hq (F x y / F y y)
      have hsq : F x y ^ 2 ≤ F x x * F y y := by
        field_simp at h
        nlinarith [h, hy]
      calc F x y ≤ |F x y| := le_abs_self _
        _ = Real.sqrt (F x y ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (F x x * F y y) := Real.sqrt_le_sqrt hsq
        _ = _ := Real.sqrt_mul (hpos x) _
    · have hxy : F x y = 0 := by
        by_contra hne
        have h := hq ((F x x + 1) / (2 * F x y))
        rw [← hy] at h
        have h2 : 2 * ((F x x + 1) / (2 * F x y)) * F x y = F x x + 1 := by
          field_simp
        nlinarith [h, h2]
      rw [hxy]; positivity
  rw [Real.sqrt_le_left (by positivity)]
  simp only [map_add, LinearMap.add_apply]
  rw [hsymm y x]
  nlinarith [Real.sq_sqrt (hpos x), Real.sq_sqrt (hpos y), hcs]

/-! ### Joint almost-sure subsequence for a countable family -/

theorem aux_lem_local_normalizations_joint_subseq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (F : ℕ → ℕ → Ω → ℝ) (L : ℕ → Ω → ℝ)
    (hF : ∀ i, TendstoInMeasure μ (fun N => F N i) atTop (L i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ om ∂μ, ∀ i, Tendsto (fun n => F (φ n) i om) atTop (𝓝 (L i om)) := by
  -- the combined distance
  let w : ℕ → ℝ := fun i => (1 / 2 : ℝ) ^ i
  have hw : Summable w := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let G : ℕ → Ω → ℝ := fun N om => ∑' i, w i * min 1 |F N i om - L i om|
  have hterm_nn : ∀ N om i, 0 ≤ w i * min 1 |F N i om - L i om| := fun N om i =>
    mul_nonneg (by positivity) (le_min zero_le_one (abs_nonneg _))
  have hterm_le : ∀ N om i, w i * min 1 |F N i om - L i om| ≤ w i := fun N om i =>
    mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  have hsum : ∀ N om, Summable (fun i => w i * min 1 |F N i om - L i om|) := fun N om =>
    Summable.of_nonneg_of_le (hterm_nn N om) (hterm_le N om) hw
  have hG : TendstoInMeasure μ G atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    -- choose the truncation level
    obtain ⟨I, hI⟩ : ∃ I : ℕ, 2 * (1 / 2 : ℝ) ^ I < ε / 2 := by
      obtain ⟨I, hI⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < ε / 4)
        (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨I, by linarith⟩
    have hsub : ∀ N, {om | ε ≤ dist (G N om) 0} ⊆
        ⋃ i ∈ Finset.range I, {om | ε / 4 ≤ dist (F N i om) (L i om)} := by
      intro N om hom
      by_contra hno
      simp only [Set.mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hno
      simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hom
      have hsplit := ((hsum N om).sum_add_tsum_nat_add I).symm
      have hhead : ∑ i ∈ Finset.range I, w i * min 1 |F N i om - L i om| ≤
          ∑ i ∈ Finset.range I, w i * (ε / 4) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hno i hi
        rw [Real.dist_eq] at this
        exact (min_le_right _ _).trans this.le
      have hgeo : ∑ i ∈ Finset.range I, w i * (ε / 4) ≤ 2 * (ε / 4) := by
        rw [← Finset.sum_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := sum_geometric_two_le I
        simpa [w] using this
      have htail : ∑' i, w (i + I) * min 1 |F N (i + I) om - L (i + I) om| ≤
          2 * (1 / 2 : ℝ) ^ I := by
        calc ∑' i, w (i + I) * min 1 |F N (i + I) om - L (i + I) om|
            ≤ ∑' i, w (i + I) := by
              apply Summable.tsum_le_tsum (fun i => hterm_le N om (i + I))
                ((summable_nat_add_iff I).2 (hsum N om)) ((summable_nat_add_iff I).2 hw)
          _ = 2 * (1 / 2 : ℝ) ^ I := by
              simp only [w, pow_add]
              rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
              ring
      have hGnn : 0 ≤ G N om := tsum_nonneg (hterm_nn N om)
      rw [abs_of_nonneg hGnn] at hom
      have : G N om < ε := by
        change ∑' i, w i * min 1 |F N i om - L i om| < ε
        rw [hsplit]
        linarith
      linarith
    have hfin : Tendsto (fun N => ∑ i ∈ Finset.range I,
        μ {om | ε / 4 ≤ dist (F N i om) (L i om)}) atTop (𝓝 0) := by
      rw [show (0 : ENNReal) = ∑ i ∈ Finset.range I, (0 : ENNReal) by simp]
      exact tendsto_finsetSum _ (fun i _ => (tendstoInMeasure_iff_dist.1 (hF i)) (ε / 4)
        (by linarith))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfin
      (fun N => zero_le) (fun N => ?_)
    exact (measure_mono (hsub N)).trans (measure_biUnion_finset_le _ _)
  obtain ⟨φ, hφ, hae⟩ := hG.exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae] with om hom i
  have hwi : 0 < w i := by positivity
  -- each term tends to zero
  have hti : Tendsto (fun n => w i * min 1 |F (φ n) i om - L i om|) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => hterm_nn _ _ _) (fun n => ?_) hom
    exact (hsum (φ n) om).le_tsum i (fun j _ => hterm_nn _ _ _)
  have hmin : Tendsto (fun n => min 1 |F (φ n) i om - L i om|) atTop (𝓝 0) := by
    have := hti.const_mul (w i)⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hwi.ne'] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hev : ∀ᶠ n in atTop, min 1 |F (φ n) i om - L i om| < 1 :=
    hmin.eventually (gt_mem_nhds (by norm_num))
  refine hmin.congr' ?_
  filter_upwards [hev] with n hn
  rw [Real.norm_eq_abs]
  rcases le_total 1 |F (φ n) i om - L i om| with h | h
  · rw [min_eq_left h] at hn; exact absurd hn (lt_irrefl _)
  · exact min_eq_right h

/-! ### The good event of bounded-constant times -/

theorem aux_lem_local_normalizations_eventually_large {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (Rb : ℝ) (η : ENNReal)
    (hK : ∀ N, μ {om | Rb < K N om} ≤ η) :
    μ {om | ∀ᶠ n in atTop, Rb < K (φ n) om} ≤ η := by
  have hset : {om | ∀ᶠ n in atTop, Rb < K (φ n) om} =
      ⋃ n0 : ℕ, ⋂ n ≥ n0, {om | Rb < K (φ n) om} := by
    ext om
    simp only [mem_ofPred_eq, eventually_atTop, Set.mem_iUnion, Set.mem_iInter]
  rw [hset]
  have hmono : Monotone (fun n0 : ℕ => ⋂ n ≥ n0, {om | Rb < K (φ n) om}) := by
    intro a b hab om hom
    simp only [Set.mem_iInter] at hom ⊢
    exact fun n hn => hom n (hab.trans hn)
  rw [hmono.measure_iUnion]
  refine iSup_le fun n0 => ?_
  refine (measure_mono ?_).trans (hK (φ n0))
  intro om hom
  simp only [Set.mem_iInter] at hom
  exact hom n0 le_rfl

/-! ### Deterministic Cauchy transfer -/

/-- A real sequence uniformly approximable by convergent sequences converges. -/
theorem aux_lem_local_normalizations_conv_of_approx (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ)
    (hb : ∀ i, ∃ x, Tendsto (b i) atTop (𝓝 x))
    (happrox : ∀ ε > 0, ∃ i, ∀ n, |a n - b i n| ≤ ε) :
    ∃ x, Tendsto a atTop (𝓝 x) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨i, hi⟩ := happrox (ε / 3) (by positivity)
  obtain ⟨x, hx⟩ := hb i
  have hc := (hx.cauchySeq)
  rw [Metric.cauchySeq_iff] at hc
  obtain ⟨N, hN⟩ := hc (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hi m
  have h2 := hi n
  have h3 := hN m hm n hn
  rw [Real.dist_eq] at h3 ⊢
  have e1 : |a m - a n| ≤ |a m - b i m| + |b i m - b i n| + |a n - b i n| := by
    have := abs_sub_le (a m) (b i m) (a n)
    have := abs_sub_le (b i m) (b i n) (a n)
    rw [abs_sub_comm (b i n) (a n)] at this
    linarith
  linarith

/-! ### Pointwise seminorm estimates -/

theorem aux_lem_local_normalizations_sqrtQ_lip
    {V : Type*} [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) (nrm : V → ℝ)
    (q : V → ℝ)
    (htri : ∀ g h, g ∈ W → h ∈ W → Real.sqrt (q (g + h)) ≤ Real.sqrt (q g) + Real.sqrt (q h))
    (hsmul : ∀ (c : ℝ) g, g ∈ W → q (c • g) = c ^ 2 * q g)
    (R : ℝ) (hbound : ∀ g, g ∈ W → q g ≤ R * nrm g ^ 2)
    (g h : V) (hg : g ∈ W) (hh : h ∈ W) :
    |Real.sqrt (q g) - Real.sqrt (q h)| ≤ Real.sqrt R * |nrm (g - h)| := by
  have hgh : g - h ∈ W := W.sub_mem hg hh
  have hhg : h - g ∈ W := W.sub_mem hh hg
  have hsym : q (h - g) = q (g - h) := by
    rw [show h - g = (-1 : ℝ) • (g - h) by simp, hsmul _ _ hgh]; ring
  have hup : Real.sqrt (q (g - h)) ≤ Real.sqrt R * |nrm (g - h)| := by
    by_cases hR : 0 ≤ R
    · rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hR]
      exact Real.sqrt_le_sqrt (hbound _ hgh)
    · have h0 : q (g - h) ≤ 0 := (hbound _ hgh).trans
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hR) (sq_nonneg _))
      rw [Real.sqrt_eq_zero'.2 h0]; positivity
  have h1 : Real.sqrt (q g) ≤ Real.sqrt (q h) + Real.sqrt (q (g - h)) := by
    have := htri h (g - h) hh hgh
    rwa [add_sub_cancel] at this
  have h2 : Real.sqrt (q h) ≤ Real.sqrt (q g) + Real.sqrt (q (g - h)) := by
    have := htri g (h - g) hg hhg
    rwa [add_sub_cancel, hsym] at this
  rw [abs_le]
  constructor <;> linarith

/-! ### Enumerating the bounded-constant times -/

/-- The least integer level at which the constants are infinitely often bounded. -/
def aux_lem_local_normalizations_Rom {Ω : Type*} (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ)
    (om : Ω) : ℕ := by
  classical
  exact if h : ∃ R : ℕ, ∃ᶠ n in atTop, K (φ n) om ≤ R then Nat.find h else 0

/-- The times of `φ` at which the constant is below that level. -/
def aux_lem_local_normalizations_seq {Ω : Type*} (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ)
    (om : Ω) (n : ℕ) : ℕ :=
  φ (Nat.nth (fun m => K (φ m) om ≤ aux_lem_local_normalizations_Rom K φ om) n)

theorem aux_lem_local_normalizations_seq_spec {Ω : Type*} (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (om : Ω) (h : ∃ R : ℕ, ∃ᶠ n in atTop, K (φ n) om ≤ R) :
    Tendsto (fun n => Nat.nth (fun m => K (φ m) om ≤
        aux_lem_local_normalizations_Rom K φ om) n) atTop atTop ∧
      StrictMono (aux_lem_local_normalizations_seq K φ om) ∧
      (∀ n, K (aux_lem_local_normalizations_seq K φ om n) om ≤
        aux_lem_local_normalizations_Rom K φ om) ∧
      (∀ R : ℕ, R < aux_lem_local_normalizations_Rom K φ om →
        ∀ᶠ n in atTop, (R : ℝ) < K (φ n) om) := by
  classical
  have hR : aux_lem_local_normalizations_Rom K φ om = Nat.find h := by
    simp [aux_lem_local_normalizations_Rom, h]
  have hfreq : ∃ᶠ n in atTop, K (φ n) om ≤ aux_lem_local_normalizations_Rom K φ om := by
    rw [hR]; exact Nat.find_spec h
  have hinf : (ofPred (fun m => K (φ m) om ≤ aux_lem_local_normalizations_Rom K φ om)).Infinite :=
    Nat.frequently_atTop_iff_infinite.1 hfreq
  have hmono := Nat.nth_strictMono hinf
  refine ⟨hmono.tendsto_atTop, hφ.comp hmono, fun n => Nat.nth_mem_of_infinite hinf n, ?_⟩
  intro R hRlt
  rw [hR] at hRlt
  have hnot := Nat.find_min h hRlt
  rw [not_frequently] at hnot
  filter_upwards [hnot] with n hn
  exact lt_of_not_ge hn

/-! ### The good event and the pointwise limit -/

/-- The good event: infinitely often bounded constants, joint convergence on the
catalogue, and the extension bound at every cutoff. -/
def aux_lem_local_normalizations_good {Ω V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ) (K : ℕ → Ω → ℝ)
    (φ : ℕ → ℕ) (D : ℕ → V) (L : ℕ → Ω → ℝ) (om : Ω) : Prop :=
  (∃ R : ℕ, ∃ᶠ n in atTop, K (φ n) om ≤ R) ∧
    (∀ i, Tendsto (fun n => Q (φ n) om (D i)) atTop (𝓝 (L i om))) ∧
    (∀ N g, g ∈ W → Q N om g ≤ K N om * nrm g ^ 2)

theorem aux_lem_local_normalizations_good_lip {Ω V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ) (K : ℕ → Ω → ℝ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : ℕ → V) (L : ℕ → Ω → ℝ)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (om : Ω) (hgood : aux_lem_local_normalizations_good W nrm Q K φ D L om)
    (n : ℕ) (g h : V) (hg : g ∈ W) (hh : h ∈ W) :
    |Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om g) -
        Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om h)| ≤
      Real.sqrt (aux_lem_local_normalizations_Rom K φ om) * |nrm (g - h)| := by
  obtain ⟨hR, -, hbd⟩ := hgood
  have hspec := aux_lem_local_normalizations_seq_spec K φ hφ om hR
  set s := aux_lem_local_normalizations_seq K φ om n
  apply aux_lem_local_normalizations_sqrtQ_lip W nrm (Q s om)
    (fun g h hg hh => hQtri s om g h hg hh) (fun c g hg => hQsmul s om c g hg)
    (aux_lem_local_normalizations_Rom K φ om) _ g h hg hh
  intro f hf
  exact (hbd s f hf).trans (mul_le_mul_of_nonneg_right (hspec.2.2.1 n) (sq_nonneg _))

theorem aux_lem_local_normalizations_good_tendsto {Ω V : Type*} [AddCommGroup V]
    [Module ℝ V]
    (W : Submodule ℝ V) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ) (K : ℕ → Ω → ℝ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : ℕ → V) (hDW : ∀ i, D i ∈ W) (L : ℕ → Ω → ℝ)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (hdense : ∀ g ∈ W, ∀ ε > 0, ∃ i, |nrm (g - D i)| ≤ ε)
    (om : Ω) (hgood : aux_lem_local_normalizations_good W nrm Q K φ D L om) :
    (∀ i, Tendsto (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om (D i)))
        atTop (𝓝 (Real.sqrt (L i om)))) ∧
      ∀ g ∈ W, ∃ x, Tendsto
        (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om g)) atTop (𝓝 x) := by
  have hspec := aux_lem_local_normalizations_seq_spec K φ hφ om hgood.1
  have hD : ∀ i, Tendsto (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n)
      om (D i))) atTop (𝓝 (Real.sqrt (L i om))) := by
    intro i
    have h := (hgood.2.1 i).comp hspec.1
    exact (Real.continuous_sqrt.tendsto _).comp h
  refine ⟨hD, fun g hg => ?_⟩
  apply aux_lem_local_normalizations_conv_of_approx _
    (fun i n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om (D i)))
    (fun i => ⟨_, hD i⟩)
  intro ε hε
  set R := aux_lem_local_normalizations_Rom K φ om
  obtain ⟨i, hi⟩ := hdense g hg (ε / (Real.sqrt R + 1)) (by positivity)
  refine ⟨i, fun n => ?_⟩
  have hl := aux_lem_local_normalizations_good_lip W nrm Q K φ hφ D L hQtri hQsmul om hgood n
    g (D i) hg (hDW i)
  calc _ ≤ Real.sqrt R * |nrm (g - D i)| := hl
    _ ≤ (Real.sqrt R + 1) * (ε / (Real.sqrt R + 1)) := by
        apply mul_le_mul (by linarith) hi (abs_nonneg _) (by positivity)
    _ = ε := by field_simp

/-- The limiting root response on the good event (junk `0` elsewhere), read
through a linear projection onto `W`. -/
def aux_lem_local_normalizations_pfun {Ω V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (π : V →ₗ[ℝ] W) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ)
    (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (D : ℕ → V) (L : ℕ → Ω → ℝ) (om : Ω) (g : V) : ℝ := by
  classical
  exact if aux_lem_local_normalizations_good W nrm Q K φ D L om then
    limUnder atTop
      (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om (π g : V)))
  else 0

section pfun

variable {Ω V : Type*} [AddCommGroup V] [Module ℝ V]
  (W : Submodule ℝ V) (π : V →ₗ[ℝ] W) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ)
  (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (D : ℕ → V) (L : ℕ → Ω → ℝ)

theorem aux_lem_local_normalizations_pfun_tendsto (hφ : StrictMono φ) (hDW : ∀ i, D i ∈ W)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (hdense : ∀ g ∈ W, ∀ ε > 0, ∃ i, |nrm (g - D i)| ≤ ε)
    (om : Ω) (hgood : aux_lem_local_normalizations_good W nrm Q K φ D L om) (g : V) :
    Tendsto (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om (π g : V)))
      atTop (𝓝 (aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g)) := by
  classical
  obtain ⟨x, hx⟩ := (aux_lem_local_normalizations_good_tendsto W nrm Q K φ hφ D hDW L
    hQtri hQsmul hdense om hgood).2 (π g : V) (π g).property
  have hdef : aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g =
      limUnder atTop
        (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om (π g : V))) := by
    simp [aux_lem_local_normalizations_pfun, hgood]
  rw [hdef]
  exact tendsto_nhds_limUnder ⟨x, hx⟩

theorem aux_lem_local_normalizations_pfun_add_le (hφ : StrictMono φ) (hDW : ∀ i, D i ∈ W)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (hdense : ∀ g ∈ W, ∀ ε > 0, ∃ i, |nrm (g - D i)| ≤ ε) (om : Ω) (g h : V) :
    aux_lem_local_normalizations_pfun W π nrm Q K φ D L om (g + h) ≤
      aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g +
        aux_lem_local_normalizations_pfun W π nrm Q K φ D L om h := by
  classical
  by_cases hgood : aux_lem_local_normalizations_good W nrm Q K φ D L om
  · have t := fun f => aux_lem_local_normalizations_pfun_tendsto W π nrm Q K φ D L hφ hDW
      hQtri hQsmul hdense om hgood f
    refine le_of_tendsto_of_tendsto' (t (g + h)) ((t g).add (t h)) (fun n => ?_)
    rw [map_add, Submodule.coe_add]
    exact hQtri _ _ _ _ (π g).property (π h).property
  · simp [aux_lem_local_normalizations_pfun, hgood]

theorem aux_lem_local_normalizations_pfun_smul (hφ : StrictMono φ) (hDW : ∀ i, D i ∈ W)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (hdense : ∀ g ∈ W, ∀ ε > 0, ∃ i, |nrm (g - D i)| ≤ ε) (om : Ω) (c : ℝ) (g : V) :
    aux_lem_local_normalizations_pfun W π nrm Q K φ D L om (c • g) =
      ‖c‖ * aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g := by
  classical
  by_cases hgood : aux_lem_local_normalizations_good W nrm Q K φ D L om
  · have t := fun f => aux_lem_local_normalizations_pfun_tendsto W π nrm Q K φ D L hφ hDW
      hQtri hQsmul hdense om hgood f
    have h1 := t (c • g)
    have h2 := (t g).const_mul ‖c‖
    refine tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall fun n => ?_))
    simp only
    rw [map_smul, Submodule.coe_smul, hQsmul _ _ _ _ (π g).property,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
  · simp [aux_lem_local_normalizations_pfun, hgood]

end pfun

section pfunprops

variable {Ω V : Type*} [AddCommGroup V] [Module ℝ V]
  (W : Submodule ℝ V) (π : V →ₗ[ℝ] W) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ)
  (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (D : ℕ → V) (L : ℕ → Ω → ℝ)

theorem aux_lem_local_normalizations_pfun_props (hφ : StrictMono φ) (hDW : ∀ i, D i ∈ W)
    (hπ : ∀ g ∈ W, (π g : V) = g)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (hdense : ∀ g ∈ W, ∀ ε > 0, ∃ i, |nrm (g - D i)| ≤ ε)
    (om : Ω) (hgood : aux_lem_local_normalizations_good W nrm Q K φ D L om) :
    (∀ i, aux_lem_local_normalizations_pfun W π nrm Q K φ D L om (D i) = Real.sqrt (L i om)) ∧
    (∀ g h, g ∈ W → h ∈ W →
      |aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g -
        aux_lem_local_normalizations_pfun W π nrm Q K φ D L om h| ≤
      Real.sqrt (aux_lem_local_normalizations_Rom K φ om) * |nrm (g - h)|) ∧
    (∀ g, g ∈ W → 0 ≤ aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g ∧
      aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g ≤
        Real.sqrt (aux_lem_local_normalizations_Rom K φ om) * |nrm g|) := by
  have t := fun f => aux_lem_local_normalizations_pfun_tendsto W π nrm Q K φ D L hφ hDW
    hQtri hQsmul hdense om hgood f
  have tW : ∀ g ∈ W, Tendsto
      (fun n => Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om g)) atTop
      (𝓝 (aux_lem_local_normalizations_pfun W π nrm Q K φ D L om g)) := by
    intro g hg
    have := t g
    rwa [hπ g hg] at this
  have hlip := aux_lem_local_normalizations_good_lip W nrm Q K φ hφ D L hQtri hQsmul om hgood
  refine ⟨fun i => ?_, fun g h hg hh => ?_, fun g hg => ⟨?_, ?_⟩⟩
  · exact tendsto_nhds_unique (tW (D i) (hDW i))
      ((aux_lem_local_normalizations_good_tendsto W nrm Q K φ hφ D hDW L hQtri hQsmul
        hdense om hgood).1 i)
  · have hlim := ((tW g hg).sub (tW h hh)).abs
    exact le_of_tendsto' hlim (fun n => hlip n g h hg hh)
  · exact ge_of_tendsto' (tW g hg) (fun n => Real.sqrt_nonneg _)
  · have h0 : ∀ n, Q (aux_lem_local_normalizations_seq K φ om n) om 0 = 0 := by
      intro n
      have := hQsmul (aux_lem_local_normalizations_seq K φ om n) om 0 0 W.zero_mem
      simpa using this
    have hle : ∀ n, Real.sqrt (Q (aux_lem_local_normalizations_seq K φ om n) om g) ≤
        Real.sqrt (aux_lem_local_normalizations_Rom K φ om) * |nrm g| := by
      intro n
      have := hlip n g 0 hg W.zero_mem
      rw [h0, Real.sqrt_zero, sub_zero, sub_zero] at this
      exact (le_abs_self _).trans this
    exact le_of_tendsto' (tW g hg) hle

end pfunprops

theorem aux_lem_local_normalizations_good_ae {Ω V : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ)
    (K : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (D : ℕ → V) (L : ℕ → Ω → ℝ)
    (hKbound : ∀ᵐ om ∂μ, ∀ N g, g ∈ W → Q N om g ≤ K N om * nrm g ^ 2)
    (hKtight : ∀ η : ENNReal, 0 < η → ∃ Rb : ℕ, ∀ N, μ {om | (Rb : ℝ) < K N om} ≤ η)
    (hjoint : ∀ᵐ om ∂μ, ∀ i, Tendsto (fun n => Q (φ n) om (D i)) atTop (𝓝 (L i om))) :
    ∀ᵐ om ∂μ, aux_lem_local_normalizations_good W nrm Q K φ D L om := by
  have hR : ∀ᵐ om ∂μ, ∃ R : ℕ, ∃ᶠ n in atTop, K (φ n) om ≤ R := by
    rw [ae_iff]
    apply le_antisymm _ (zero_le)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨Rb, hRb⟩ := hKtight (ε : ENNReal) (by exact_mod_cast hε)
    refine (measure_mono ?_).trans ((aux_lem_local_normalizations_eventually_large μ K φ
      (Rb : ℝ) ε hRb).trans (by simp))
    intro om hom
    simp only [mem_ofPred_eq, not_exists, not_frequently] at hom ⊢
    filter_upwards [hom Rb] with n hn
    exact lt_of_not_ge hn
  filter_upwards [hR, hjoint, hKbound] with om h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- Pointwise core of the convergence estimate. -/
theorem aux_lem_local_normalizations_pointwise_close
    (q p pD sL sQD Rb Rom nrmg nrmgD ρ δ B : ℝ)
    (hq : 0 ≤ q) (hp : 0 ≤ p) (hRom : Rom ≤ Rb) (hρ : 0 < ρ)
    (hB : B = Real.sqrt Rb * |nrmg|)
    (hρδ : ρ * (ρ + 2 * B) < δ)
    (hpD : pD = sL)
    (hsmall : |nrmgD| ≤ ρ / (3 * (Real.sqrt Rb + 1)))
    (h1 : |Real.sqrt q - sQD| ≤ Real.sqrt Rb * |nrmgD|)
    (h2 : |sQD - sL| < ρ / 3)
    (h3 : |p - pD| ≤ Real.sqrt Rom * |nrmgD|)
    (h4 : p ≤ Real.sqrt Rom * |nrmg|) :
    |q - p ^ 2| < δ := by
  have hsR : Real.sqrt Rom ≤ Real.sqrt Rb := Real.sqrt_le_sqrt hRom
  have hs0 : 0 ≤ Real.sqrt Rb := Real.sqrt_nonneg _
  have hkey : Real.sqrt Rb * |nrmgD| < ρ / 3 := by
    calc Real.sqrt Rb * |nrmgD| ≤ Real.sqrt Rb * (ρ / (3 * (Real.sqrt Rb + 1))) :=
          mul_le_mul_of_nonneg_left hsmall hs0
      _ < ρ / 3 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hkey' : Real.sqrt Rom * |nrmgD| < ρ / 3 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsR (abs_nonneg _)) hkey
  have hclose : |Real.sqrt q - p| < ρ := by
    have e : Real.sqrt q - p = (Real.sqrt q - sQD) + (sQD - sL) + (pD - p) := by
      rw [hpD]; ring
    rw [e]
    calc |(Real.sqrt q - sQD) + (sQD - sL) + (pD - p)|
        ≤ |Real.sqrt q - sQD| + |sQD - sL| + |pD - p| := by
          have := abs_add_le ((Real.sqrt q - sQD) + (sQD - sL)) (pD - p)
          have := abs_add_le (Real.sqrt q - sQD) (sQD - sL)
          linarith
      _ < ρ := by rw [abs_sub_comm pD p]; linarith
  have hpB : p ≤ B := by
    rw [hB]; exact h4.trans (mul_le_mul_of_nonneg_right hsR (abs_nonneg _))
  have hsq : q = Real.sqrt q ^ 2 := (Real.sq_sqrt hq).symm
  have hfac : q - p ^ 2 = (Real.sqrt q - p) * (Real.sqrt q + p) := by
    have : (Real.sqrt q - p) * (Real.sqrt q + p) = Real.sqrt q ^ 2 - p ^ 2 := by ring
    rw [this, ← hsq]
  rw [hfac, abs_mul]
  have hs : 0 ≤ Real.sqrt q + p := by positivity
  rw [abs_of_nonneg hs]
  have hsq_le : Real.sqrt q + p ≤ ρ + 2 * B := by
    have := (abs_lt.1 hclose).2
    linarith
  calc |Real.sqrt q - p| * (Real.sqrt q + p) ≤ ρ * (ρ + 2 * B) :=
        mul_le_mul hclose.le hsq_le hs hρ.le
    _ < δ := hρδ

/-- **Random seminorm limit.** -/
theorem aux_lem_local_normalizations_seminorm_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (W : Submodule ℝ V) (nrm : V → ℝ) (Q : ℕ → Ω → V → ℝ)
    (hQnn : ∀ N om g, 0 ≤ Q N om g)
    (hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h))
    (hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g)
    (K : ℕ → Ω → ℝ)
    (hKbound : ∀ᵐ om ∂μ, ∀ N g, g ∈ W → Q N om g ≤ K N om * nrm g ^ 2)
    (hKtight : ∀ η : ENNReal, 0 < η → ∃ Rb : ℕ, ∀ N, μ {om | (Rb : ℝ) < K N om} ≤ η)
    (D : ℕ → V) (hDW : ∀ i, D i ∈ W)
    (hdense : ∀ g ∈ W, ∀ ε > 0, ∃ i, |nrm (g - D i)| ≤ ε)
    (L : ℕ → Ω → ℝ)
    (hconvD : ∀ i, TendstoInMeasure μ (fun N om => Q N om (D i)) atTop (L i)) :
    ∃ R : Ω → Seminorm ℝ V,
      (∀ g ∈ W, TendstoInMeasure μ (fun N om => Q N om g) atTop (fun om => (R om g) ^ 2)) ∧
      (∀ᵐ om ∂μ, ∃ Kc : ℝ, 0 < Kc ∧ ∀ g ∈ W, (R om g) ^ 2 ≤ Kc * nrm g ^ 2) := by
  classical
  obtain ⟨φ, hφ, hjoint⟩ := aux_lem_local_normalizations_joint_subseq μ
    (fun N i om => Q N om (D i)) L hconvD
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  set π : V →ₗ[ℝ] W := W.projectionOnto W' hW' with hπdef
  have hπ : ∀ g ∈ W, (π g : V) = g := fun g hg => by
    simpa only [hπdef] using! congrArg Subtype.val
      (Submodule.projectionOnto_apply_left hW' ⟨g, hg⟩)
  have hgood := aux_lem_local_normalizations_good_ae μ W nrm Q K φ D L hKbound hKtight hjoint
  set pf := aux_lem_local_normalizations_pfun W π nrm Q K φ D L with hpf
  let R : Ω → Seminorm ℝ V := fun om => Seminorm.of (pf om)
    (aux_lem_local_normalizations_pfun_add_le W π nrm Q K φ D L hφ hDW hQtri hQsmul hdense om)
    (aux_lem_local_normalizations_pfun_smul W π nrm Q K φ D L hφ hDW hQtri hQsmul hdense om)
  have hR : ∀ om g, R om g = pf om g := fun om g => rfl
  refine ⟨R, fun g hg => ?_, ?_⟩
  · -- convergence in probability
    rw [tendstoInMeasure_iff_dist]
    intro δ hδ
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨ε', hε', hε'η⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal (3 * ε') ≤ η := by
      rcases eq_or_ne η ⊤ with h | h
      · exact ⟨1, one_pos, by simp [h]⟩
      · refine ⟨η.toReal / 3, by
          have := ENNReal.toReal_pos hη.ne' h; positivity, ?_⟩
        rw [show 3 * (η.toReal / 3) = η.toReal by ring, ENNReal.ofReal_toReal h]
    obtain ⟨Rb, hRb⟩ := hKtight (ENNReal.ofReal ε') (ENNReal.ofReal_pos.2 hε')
    set B := Real.sqrt Rb * |nrm g| with hB
    set ρ := min 1 (δ / (2 * (2 * B + 1))) with hρdef
    have hB0 : 0 ≤ B := by positivity
    have hρ : 0 < ρ := lt_min one_pos (by positivity)
    have hρδ : ρ * (ρ + 2 * B) < δ := by
      have h1 : ρ ≤ 1 := min_le_left _ _
      have h2 : ρ ≤ δ / (2 * (2 * B + 1)) := min_le_right _ _
      calc ρ * (ρ + 2 * B) ≤ (δ / (2 * (2 * B + 1))) * (1 + 2 * B) :=
            mul_le_mul h2 (by linarith) (by positivity) (by positivity)
        _ = δ / 2 := by field_simp; ring
        _ < δ := by linarith
    obtain ⟨i, hi⟩ := hdense g hg (ρ / (3 * (Real.sqrt Rb + 1))) (by positivity)
    -- square roots of the catalogue responses converge in probability
    have hsq : Tendsto (fun N => μ {om | ρ / 3 ≤ dist (Real.sqrt (Q N om (D i)))
        (Real.sqrt (L i om))}) atTop (𝓝 0) := by
      have h := (tendstoInMeasure_iff_dist.1 (hconvD i)) ((ρ / 3) ^ 2) (by positivity)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
        (fun N => zero_le) (fun N => measure_mono fun om hom => ?_)
      simp only [mem_ofPred_eq, Real.dist_eq] at hom ⊢
      have := aux_lem_local_normalizations_abs_sqrt_sub_le (Q N om (D i)) (L i om)
      have h3 : ρ / 3 ≤ Real.sqrt |Q N om (D i) - L i om| := hom.trans this
      calc (ρ / 3) ^ 2 ≤ Real.sqrt |Q N om (D i) - L i om| ^ 2 :=
            pow_le_pow_left₀ (by positivity) h3 2
        _ = |Q N om (D i) - L i om| := Real.sq_sqrt (abs_nonneg _)
    have hev := (ENNReal.tendsto_nhds_zero.1 hsq) (ENNReal.ofReal ε')
      (ENNReal.ofReal_pos.2 hε')
    filter_upwards [hev] with N hN
    -- the exceptional sets
    have hlarge : μ {om | aux_lem_local_normalizations_good W nrm Q K φ D L om ∧
        Rb < aux_lem_local_normalizations_Rom K φ om} ≤ ENNReal.ofReal ε' := by
      refine (measure_mono fun om hom => ?_).trans
        (aux_lem_local_normalizations_eventually_large μ K φ (Rb : ℝ) _ hRb)
      exact (aux_lem_local_normalizations_seq_spec K φ hφ om hom.1.1).2.2.2 Rb hom.2
    have hnull : μ {om | ¬ aux_lem_local_normalizations_good W nrm Q K φ D L om} = 0 := by
      simpa [ae_iff] using hgood
    have hsub : {om | δ ≤ dist (Q N om g) ((R om g) ^ 2)} ⊆
        {om | ¬ aux_lem_local_normalizations_good W nrm Q K φ D L om} ∪
        {om | aux_lem_local_normalizations_good W nrm Q K φ D L om ∧
          Rb < aux_lem_local_normalizations_Rom K φ om} ∪
        {om | (Rb : ℝ) < K N om} ∪
        {om | ρ / 3 ≤ dist (Real.sqrt (Q N om (D i))) (Real.sqrt (L i om))} := by
      intro om hom
      by_contra hno
      simp only [Set.mem_union, mem_ofPred_eq, not_or, not_not, not_and, not_lt,
        not_le] at hno
      obtain ⟨⟨⟨hg1, hg2⟩, hK⟩, hc⟩ := hno
      have hRom := hg2 hg1
      have props := aux_lem_local_normalizations_pfun_props W π nrm Q K φ D L hφ hDW hπ
        hQtri hQsmul hdense om hg1
      simp only [mem_ofPred_eq, Real.dist_eq, hR] at hom
      have hlipN := aux_lem_local_normalizations_sqrtQ_lip W nrm (Q N om)
        (fun g h hg hh => hQtri N om g h hg hh) (fun c g hg => hQsmul N om c g hg) (Rb : ℝ)
        (fun f hf => (hg1.2.2 N f hf).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _)))
        g (D i) hg (hDW i)
      rw [Real.dist_eq] at hc
      have := aux_lem_local_normalizations_pointwise_close (Q N om g) (pf om g) (pf om (D i))
        (Real.sqrt (L i om)) (Real.sqrt (Q N om (D i))) Rb
        (aux_lem_local_normalizations_Rom K φ om) (nrm g) (nrm (g - D i)) ρ δ B
        (hQnn N om g) (props.2.2 g hg).1 (by exact_mod_cast hRom) hρ hB hρδ
        (props.1 i) hi hlipN hc (props.2.1 g (D i) hg (hDW i)) (props.2.2 g hg).2
      linarith
    calc μ {om | δ ≤ dist (Q N om g) ((R om g) ^ 2)}
        ≤ μ ({om | ¬ aux_lem_local_normalizations_good W nrm Q K φ D L om} ∪
        {om | aux_lem_local_normalizations_good W nrm Q K φ D L om ∧
          Rb < aux_lem_local_normalizations_Rom K φ om} ∪
        {om | (Rb : ℝ) < K N om} ∪
        {om | ρ / 3 ≤ dist (Real.sqrt (Q N om (D i))) (Real.sqrt (L i om))}) :=
          measure_mono hsub
      _ ≤ 0 + ENNReal.ofReal ε' + ENNReal.ofReal ε' + ENNReal.ofReal ε' := by
          refine (measure_union_le _ _).trans (add_le_add ?_ hN)
          refine (measure_union_le _ _).trans (add_le_add ?_ (hRb N))
          refine (measure_union_le _ _).trans (add_le_add hnull.le hlarge)
      _ = ENNReal.ofReal (3 * ε') := by
          rw [zero_add, ← ENNReal.ofReal_add hε'.le hε'.le,
            ← ENNReal.ofReal_add (by positivity) hε'.le]
          ring_nf
      _ ≤ η := hε'η
  · filter_upwards [hgood] with om hom
    refine ⟨aux_lem_local_normalizations_Rom K φ om + 1, by positivity, fun g hg => ?_⟩
    have props := aux_lem_local_normalizations_pfun_props W π nrm Q K φ D L hφ hDW hπ
      hQtri hQsmul hdense om hom
    obtain ⟨h0, h1⟩ := props.2.2 g hg
    rw [hR]
    calc pf om g ^ 2 ≤ (Real.sqrt (aux_lem_local_normalizations_Rom K φ om) * |nrm g|) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = (aux_lem_local_normalizations_Rom K φ om) * nrm g ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), sq_abs]
      _ ≤ _ := by nlinarith [sq_nonneg (nrm g)]

-- ===== from LNStruct.lean =====



def aux_lem_local_normalizations_T {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨cubeDilation z 0 ((3 : ℝ) ^ (-(k : ℤ))),
    continuous_cubeDilation z 0 ((3 : ℝ) ^ (-(k : ℤ)))⟩



def aux_lem_local_normalizations_Theta {d : ℕ} (k : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j : ℤ => (omega (j - (k : ℤ))).comp (aux_lem_local_normalizations_T k z)

/-- The retained coarse potential `G_k`. -/
def aux_lem_local_normalizations_Gc {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))

theorem aux_lem_local_normalizations_T_zero {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    aux_lem_local_normalizations_T k z 0 = z := by
  funext i
  simp [aux_lem_local_normalizations_T, cubeDilation]

theorem aux_lem_local_normalizations_Theta_eq_zoom {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) :
    aux_lem_local_normalizations_Theta (d := d) k z =
      aux_lem_extension_cell_moment_zoom (k : ℤ) z := by
  funext omega j
  ext x
  rw [aux_lem_extension_cell_moment_zoom_apply]
  simp only [aux_lem_local_normalizations_Theta, aux_lem_local_normalizations_T,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  congr 1
  funext i
  simp [cubeDilation, Pi.smul_apply, smul_eq_mul, add_comm]

/-- **Clause 5.** `Θ_{k,z}` preserves the common-scale layer law. -/
theorem aux_lem_local_normalizations_Theta_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_lem_local_normalizations_Theta k z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  rw [aux_lem_local_normalizations_Theta_eq_zoom]
  exact aux_lem_extension_cell_moment_zoom_measurePreserving M (k : ℤ) z

theorem aux_lem_local_normalizations_Theta_apply {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) (j : ℤ)
    (y : SpatialCoordinates d) :
    aux_lem_local_normalizations_Theta k z omega j y =
      omega (j - (k : ℤ)) (aux_lem_local_normalizations_T k z y) := rfl

/-- The infrared partial sums of the zoomed field split into the retained
coarse layers and the anchored tail of the original field. -/
theorem aux_lem_local_normalizations_partialSum_Theta {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) (L : ℕ) :
    infraredPartialSum (aux_lem_local_normalizations_Theta k z omega) (L + k) =
      ((∑ j ∈ Finset.range k, omega (-(j : ℤ))).comp
          (aux_lem_local_normalizations_T k z) -
        ContinuousMap.const _ ((∑ j ∈ Finset.range k, omega (-(j : ℤ))) z)) +
      ((infraredPartialSum omega L).comp (aux_lem_local_normalizations_T k z) -
        ContinuousMap.const _ ((infraredPartialSum omega L) z)) := by
  have hT0 := aux_lem_local_normalizations_T_zero (d := d) k z
  ext x
  simp only [infraredPartialSum, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    ContinuousMap.add_apply, aux_lem_local_normalizations_Theta_apply, hT0]
  rw [add_comm L k, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have hidx : Int.ofNat (k - 1 - n + 1) - (k : ℤ) = -((n : ℕ) : ℤ) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hidx]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hidx : (Int.ofNat (k + n + 1) - (k : ℤ)) = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring
    rw [hidx]
    ring

/-- **Clause 6.** The infrared field of the zoomed layers is the retained
coarse potential, reanchored at `z`. -/
theorem aux_lem_local_normalizations_H_Theta {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H) (k : ℕ) (z : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      H (aux_lem_local_normalizations_Theta k z omega) =
        (aux_lem_local_normalizations_Gc H k omega).comp
            (aux_lem_local_normalizations_T k z) -
          ContinuousMap.const _ (aux_lem_local_normalizations_Gc H k omega z) := by
  have hMP := aux_lem_local_normalizations_Theta_measurePreserving M k z
  have hpull := hMP.quasiMeasurePreserving.ae HI.2
  filter_upwards [HI.2, hpull] with omega hom hTom
  set T := aux_lem_local_normalizations_T (d := d) k z with hT
  set F : C(SpatialCoordinates d, ℝ) := ∑ j ∈ Finset.range k, omega (-(j : ℤ)) with hF
  -- the shifted sequence of partial sums of the zoomed field
  have hshift : Tendsto
      (fun L => infraredPartialSum (aux_lem_local_normalizations_Theta k z omega) (L + k))
      atTop (𝓝 (H (aux_lem_local_normalizations_Theta k z omega))) :=
    (tendsto_add_atTop_iff_nat k).2 hTom
  have hcont : Continuous (fun G : C(SpatialCoordinates d, ℝ) =>
      (F.comp T - ContinuousMap.const _ (F z)) +
        (G.comp T - ContinuousMap.const _ (G z))) := by
    refine continuous_const.add ?_
    exact (ContinuousMap.compRightContinuousMap ℝ T).continuous.sub
      (ContinuousMap.const'.continuous.comp (continuous_eval_const z))
  have hlim : Tendsto
      (fun L => infraredPartialSum (aux_lem_local_normalizations_Theta k z omega) (L + k))
      atTop (𝓝 ((F.comp T - ContinuousMap.const _ (F z)) +
        ((H omega).comp T - ContinuousMap.const _ ((H omega) z)))) := by
    have h := (hcont.tendsto (H omega)).comp hom
    refine h.congr' (Eventually.of_forall fun L => ?_)
    simp only [Function.comp_apply]
    rw [aux_lem_local_normalizations_partialSum_Theta]
  rw [tendsto_nhds_unique hshift hlim]
  ext x
  simp only [aux_lem_local_normalizations_Gc, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    hF]
  ring

-- ===== from LNScale.lean =====



def aux_lem_local_normalizations_Lset {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) : Set ℝ :=
  {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
      (U : SpatialCoordinates d → ℝ),
    ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
    ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
    (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = g x) ∧
    e = sobolevCoefficientForm a u.val u.val}

theorem aux_lem_local_normalizations_dil_mem_closed {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (y : SpatialCoordinates d)
    (hy : y ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :
    cubeDilation z 0 r y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
  change y ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) at hy
  change cubeDilation z 0 r y ∈ Metric.closedBall z (r / 2)
  have hT : cubeDilation z 0 r y = z + r • y := by
    funext i; simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  rw [hT, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr]
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  nlinarith

theorem aux_lem_local_normalizations_inv_mem_closed {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (x : SpatialCoordinates d)
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    cubeDilation 0 z r⁻¹ x ∈
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
  change x ∈ Metric.closedBall z (r / 2) at hx
  change cubeDilation 0 z r⁻¹ x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2)
  have hT : cubeDilation 0 z r⁻¹ x = r⁻¹ • (x - z) := by
    funext i; simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  rw [hT, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  rw [inv_mul_le_iff₀ hr]
  linarith

theorem aux_lem_local_normalizations_dil_frontier {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (y : SpatialCoordinates d)
    (hy : y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) :
    cubeDilation z 0 r y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  change y ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) at hy
  change cubeDilation z 0 r y ∈ frontier (Metric.ball z (r / 2))
  rw [frontier_ball _ (by norm_num)] at hy
  rw [frontier_ball _ (by positivity)]
  have hT : cubeDilation z 0 r y = z + r • y := by
    funext i; simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  rw [hT, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr]
  rw [mem_sphere_iff_norm, sub_zero] at hy
  rw [hy]; ring

theorem aux_lem_local_normalizations_inv_frontier {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (x : SpatialCoordinates d)
    (hx : x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d))) :
    cubeDilation 0 z r⁻¹ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := by
  change x ∈ frontier (Metric.ball z (r / 2)) at hx
  change cubeDilation 0 z r⁻¹ x ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
  rw [frontier_ball _ (by positivity)] at hx
  rw [frontier_ball _ (by norm_num)]
  have hT : cubeDilation 0 z r⁻¹ x = r⁻¹ • (x - z) := by
    funext i; simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  rw [hT, mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]
  rw [mem_sphere_iff_norm] at hx
  rw [hx]; field_simp

theorem aux_lem_local_normalizations_dil_inv {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (x : SpatialCoordinates d) :
    cubeDilation z 0 r (cubeDilation 0 z r⁻¹ x) = x := by
  funext i; simp [cubeDilation]; field_simp; ring

theorem aux_lem_local_normalizations_inv_dil {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (y : SpatialCoordinates d) :
    cubeDilation 0 z r⁻¹ (cubeDilation z 0 r y) = y := by
  funext i; simp [cubeDilation]; field_simp

/-- Almost-everywhere statements transfer exactly between the cube and the
unit cube along the dilation. -/
theorem aux_lem_local_normalizations_ae_iff {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (p : SpatialCoordinates d → Prop) :
    (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), p x) ↔
      ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), p (cubeDilation z 0 r y) := by
  have hmap := map_cubeDilation_restrict z 0 hr one_pos
  have hemb : MeasurableEmbedding (cubeDilation z 0 r) :=
    (cubeDilationEquiv z 0 hr.ne').measurableEmbedding
  have hc : ENNReal.ofReal |(r ^ d)⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  rw [← hemb.ae_map_iff, hmap, Measure.ae_ennreal_smul_measure_iff hc]

/-- The unit-cube coefficient scaled by a positive constant. -/
def aux_lem_local_normalizations_smulCoeff {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (c : ℝ) (hc : 0 < c) (b : PositiveCoefficient Ω) : PositiveCoefficient Ω :=
  ⟨c • b.val, by
    obtain ⟨m, hm, hbm⟩ := b.property
    refine ⟨c * m, mul_pos hc hm, ?_⟩
    filter_upwards [hbm, Lp.coeFn_smul c b.val] with x hx hsx
    rw [hsx, Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hx hc.le⟩

theorem aux_lem_local_normalizations_smulCoeff_coeFn {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (c : ℝ) (hc : 0 < c) (b : PositiveCoefficient Ω) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (aux_lem_local_normalizations_smulCoeff c hc b).val x = c * b.val x := by
  filter_upwards [Lp.coeFn_smul c b.val] with x hx
  change (c • b.val) x = _
  rw [hx, Pi.smul_apply, smul_eq_mul]

theorem aux_lem_local_normalizations_smulCoeff_form {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (c : ℝ) (hc : 0 < c) (b : PositiveCoefficient Ω)
    (u v : SobolevData Ω) :
    sobolevCoefficientForm (aux_lem_local_normalizations_smulCoeff c hc b) u v =
      c * sobolevCoefficientForm b u v := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [aux_lem_local_normalizations_smulCoeff_coeFn c hc b] with x hx
  rw [hx]; ring

/-- **Deterministic dilation of the variational response.** -/
theorem aux_lem_local_normalizations_Lset_dilation {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (c : ℝ) (hc : 0 < c)
    (hab : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), a.val (cubeDilation z 0 r y) = c * b.val y)
    (g : SpatialCoordinates d → ℝ) :
    aux_lem_local_normalizations_Lset z r hr a g =
      (fun e => (r ^ ((d : ℝ) - 2) * c) * e) ''
        aux_lem_local_normalizations_Lset 0 1 one_pos b (g ∘ cubeDilation z 0 r) := by
  let bc := aux_lem_local_normalizations_smulCoeff c hc b
  have hbc : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), bc.val y = a.val (cubeDilation z 0 r y) := by
    filter_upwards [hab, aux_lem_local_normalizations_smulCoeff_coeFn c hc b] with y h1 h2
    rw [h2, h1]
  have hqmp := lane4_dilation_quasi_measure_preserving d z 0 r hr one_pos
  ext e
  constructor
  · rintro ⟨u, U, hUc, huU, hUb, rfl⟩
    obtain ⟨w, hwval, -⟩ :=
      aux_lem_as_regularity_affine_transport_weak_pullback d z 0 r hr one_pos u
    refine ⟨sobolevCoefficientForm b w.val w.val, ⟨w, U ∘ cubeDilation z 0 r, ?_, ?_, ?_, rfl⟩, ?_⟩
    · exact hUc.comp (continuous_cubeDilation z 0 r).continuousOn
        (fun y hy => aux_lem_local_normalizations_dil_mem_closed z hr y hy)
    · have hpull := hqmp.ae huU
      filter_upwards [hwval, hpull] with y h1 h2
      rw [h1]; exact h2
    · intro y hy
      exact hUb _ (aux_lem_local_normalizations_dil_frontier z hr y hy)
    · have hs := aux_lem_as_regularity_affine_transport_form_scaling d z 0 r hr one_pos
        a bc u u w w hbc hwval hwval
      rw [hs, aux_lem_local_normalizations_smulCoeff_form]
      ring
  · rintro ⟨e', ⟨w, W, hWc, hwW, hWb, rfl⟩, rfl⟩
    obtain ⟨u, huval⟩ :=
      aux_lem_as_regularity_affine_transport_weak_pushforward d z 0 r hr one_pos w
    refine ⟨u, W ∘ cubeDilation 0 z r⁻¹, ?_, ?_, ?_, ?_⟩
    · exact hWc.comp (continuous_cubeDilation 0 z r⁻¹).continuousOn
        (fun x hx => aux_lem_local_normalizations_inv_mem_closed z hr x hx)
    · refine (aux_lem_local_normalizations_ae_iff z hr
        (fun x => ((u.val).1 : SpatialCoordinates d → ℝ) x =
          (W ∘ cubeDilation 0 z r⁻¹) x)).2 ?_
      filter_upwards [huval, hwW] with y h1 h2
      rw [Function.comp_apply, aux_lem_local_normalizations_inv_dil z hr, ← h1, h2]
    · intro x hx
      have h := hWb _ (aux_lem_local_normalizations_inv_frontier z hr x hx)
      rw [Function.comp_apply, h, Function.comp_apply,
        aux_lem_local_normalizations_dil_inv z hr]
    · have hs := aux_lem_as_regularity_affine_transport_form_scaling d z 0 r hr one_pos
        a bc u u w w hbc (by filter_upwards [huval] with y h using h)
        (by filter_upwards [huval] with y h using h)
      rw [hs, aux_lem_local_normalizations_smulCoeff_form]
      ring

theorem aux_lem_local_normalizations_sInf_dilation {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (c : ℝ) (hc : 0 < c)
    (hab : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), a.val (cubeDilation z 0 r y) = c * b.val y)
    (g : SpatialCoordinates d → ℝ) :
    sInf (aux_lem_local_normalizations_Lset z r hr a g) =
      r ^ ((d : ℝ) - 2) * c *
        sInf (aux_lem_local_normalizations_Lset 0 1 one_pos b (g ∘ cubeDilation z 0 r)) := by
  rw [aux_lem_local_normalizations_Lset_dilation z r hr a b c hc hab g]
  have hlam : 0 ≤ r ^ ((d : ℝ) - 2) * c := by positivity
  have himg : (fun e => (r ^ ((d : ℝ) - 2) * c) * e) ''
      aux_lem_local_normalizations_Lset 0 1 one_pos b (g ∘ cubeDilation z 0 r) =
      (r ^ ((d : ℝ) - 2) * c) •
        aux_lem_local_normalizations_Lset 0 1 one_pos b (g ∘ cubeDilation z 0 r) := by
    rw [← Set.image_smul]; rfl
  rw [himg, Real.sInf_smul_of_nonneg hlam, smul_eq_mul]

/-- The actual coefficient agrees a.e. on the cube with the cutoff formula. -/
theorem aux_lem_local_normalizations_cutoff_coeFn {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hr).val x =
        cutoffCoefficient M H omega N x := by
  let : Fact (((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hnorm := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr)
    (cutoffCoefficientCM M H omega N z hr) (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hnorm, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxm
  simpa [cutoffPositiveCoefficient, cutoffCoefficientCM] using hx hxm

/-- The deterministic normalization `κ_N`. -/
def aux_lem_local_normalizations_kap {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N

theorem aux_lem_local_normalizations_kap_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    0 < aux_lem_local_normalizations_kap M N :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)

/-- The cutoff potential of the zoomed field is the original cutoff potential
minus the retained constant `G_k(z)`. -/
theorem aux_lem_local_normalizations_pot_identity {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hH : H (aux_lem_local_normalizations_Theta k z omega) =
      (aux_lem_local_normalizations_Gc H k omega).comp
          (aux_lem_local_normalizations_T k z) -
        ContinuousMap.const _ (aux_lem_local_normalizations_Gc H k omega z))
    (N : ℕ) (hkN : k ≤ N) (y : SpatialCoordinates d) :
    cutoffPotential H omega N (aux_lem_local_normalizations_T k z y) =
      cutoffPotential H (aux_lem_local_normalizations_Theta k z omega) (N - k) y +
        aux_lem_local_normalizations_Gc H k omega z := by
  unfold cutoffPotential
  rw [hH]
  have hsplit : N + 1 = k + (N - k + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, aux_lem_local_normalizations_Gc,
    ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    aux_lem_local_normalizations_Theta_apply]
  simp only [Int.ofNat_eq_natCast]
  have hsum : ∑ x ∈ Finset.range (N - k + 1),
      omega (-((k + x : ℕ) : ℤ)) (aux_lem_local_normalizations_T k z y) =
      ∑ x ∈ Finset.range (N - k + 1),
        omega (-(x : ℤ) - (k : ℤ)) (aux_lem_local_normalizations_T k z y) :=
    Finset.sum_congr rfl (fun j _ => by congr 2; push_cast; ring)
  rw [hsum]
  ring

/-- Pointwise coefficient identity on the infrared event. -/
theorem aux_lem_local_normalizations_coef_identity {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hH : H (aux_lem_local_normalizations_Theta k z omega) =
      (aux_lem_local_normalizations_Gc H k omega).comp
          (aux_lem_local_normalizations_T k z) -
        ContinuousMap.const _ (aux_lem_local_normalizations_Gc H k omega z))
    (N : ℕ) (hkN : k ≤ N) (y : SpatialCoordinates d) :
    cutoffCoefficient M H omega N (aux_lem_local_normalizations_T k z y) =
      (aux_lem_local_normalizations_kap M (N - k) / aux_lem_local_normalizations_kap M N *
          Real.exp (aux_lem_local_normalizations_Gc H k omega z)) *
        cutoffCoefficient M H (aux_lem_local_normalizations_Theta k z omega) (N - k) y := by
  have hpot := aux_lem_local_normalizations_pot_identity H k z omega hH N hkN y
  have hN : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by
    rw [Nat.cast_sub hkN]
  unfold cutoffCoefficient aux_lem_local_normalizations_kap
  rw [hpot, hN]
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hB := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = _root_.SubdiffusiveProcess.Model.tauSq M.P := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P =
      cutoffPotential H (aux_lem_local_normalizations_Theta k z omega) (N - k) y := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = aux_lem_local_normalizations_Gc H k omega z := ⟨_, rfl⟩
  rw [← hτ, ← hP, ← hG]
  have e1 : Real.exp (P + G - ((N : ℝ) + 1) * τ) =
      Real.exp (((N : ℝ) - k + 1) * τ) * Real.exp G *
        Real.exp (P - ((N : ℝ) - k + 1) * τ) / Real.exp (((N : ℝ) + 1) * τ) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [e1]
  field_simp

theorem aux_lem_local_normalizations_rscale_rpow (d k : ℕ) :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) = (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) := by
  rw [show ((3 : ℝ) ^ (-(k : ℤ))) = (3 : ℝ) ^ (-(k : ℝ)) by
    rw [← Real.rpow_intCast]; push_cast; rfl]
  rw [← Real.rpow_mul (by norm_num)]
  congr 1; ring

/-- **Clause 7a.** Exact finite-cutoff scaling of the actual variational response. -/
theorem aux_lem_local_normalizations_finite_scaling {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H) (k : ℕ) (z : SpatialCoordinates d)
    (hrk : 0 < (3 : ℝ) ^ (-(k : ℤ))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, k ≤ N →
      ∀ g : SpatialCoordinates d → ℝ,
        sInf (aux_lem_local_normalizations_Lset z ((3 : ℝ) ^ (-(k : ℤ))) hrk
            (cutoffPositiveCoefficient M H omega N z hrk) g) =
          (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
            (aux_lem_local_normalizations_kap M (N - k) /
              aux_lem_local_normalizations_kap M N) *
            Real.exp (aux_lem_local_normalizations_Gc H k omega z) *
            sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
              (cutoffPositiveCoefficient M H (aux_lem_local_normalizations_Theta k z omega)
                (N - k) 0 one_pos)
              (g ∘ aux_lem_local_normalizations_T k z)) := by
  filter_upwards [aux_lem_local_normalizations_H_Theta M H HI k z] with omega hH
  intro N hkN g
  set c := aux_lem_local_normalizations_kap M (N - k) / aux_lem_local_normalizations_kap M N *
    Real.exp (aux_lem_local_normalizations_Gc H k omega z) with hc_def
  have hc : 0 < c := mul_pos (div_pos (aux_lem_local_normalizations_kap_pos M _)
    (aux_lem_local_normalizations_kap_pos M _)) (Real.exp_pos _)
  have hab : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hrk).val
          (cubeDilation z 0 ((3 : ℝ) ^ (-(k : ℤ))) y) =
        c * (cutoffPositiveCoefficient M H (aux_lem_local_normalizations_Theta k z omega)
          (N - k) 0 one_pos).val y := by
    have hA := (aux_lem_local_normalizations_ae_iff z hrk _).1
      (aux_lem_local_normalizations_cutoff_coeFn M H omega N z hrk)
    filter_upwards [hA, aux_lem_local_normalizations_cutoff_coeFn M H
      (aux_lem_local_normalizations_Theta k z omega) (N - k) 0 one_pos] with y h1 h2
    rw [h1, h2]
    exact aux_lem_local_normalizations_coef_identity M H k z omega hH N hkN y
  have h := aux_lem_local_normalizations_sInf_dilation z _ hrk _ _ c hc hab g
  rw [h, aux_lem_local_normalizations_rscale_rpow, hc_def]
  have hT : (g ∘ cubeDilation z 0 ((3 : ℝ) ^ (-(k : ℤ)))) =
      g ∘ aux_lem_local_normalizations_T k z := rfl
  rw [hT]
  ring

-- ===== from LNUnit.lean =====

variable {d : ℕ}

theorem aux_lem_local_normalizations_Lset_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    ∀ e ∈ aux_lem_local_normalizations_Lset z r hr a g, 0 ≤ e := by
  rintro e ⟨u, U, -, -, -, rfl⟩
  exact sobolevCoefficientForm_nonneg a u.val

theorem aux_lem_local_normalizations_sInf_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    0 ≤ sInf (aux_lem_local_normalizations_Lset z r hr a g) :=
  Real.sInf_nonneg (aux_lem_local_normalizations_Lset_nonneg z r hr a g)

theorem aux_lem_local_normalizations_Lset_bdd (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    BddBelow (aux_lem_local_normalizations_Lset z r hr a g) :=
  ⟨0, aux_lem_local_normalizations_Lset_nonneg z r hr a g⟩

/-- Competitors scale with the datum. -/
theorem aux_lem_local_normalizations_Lset_smul_mem (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) (c : ℝ) (e : ℝ)
    (he : e ∈ aux_lem_local_normalizations_Lset z r hr a g) :
    c ^ 2 * e ∈ aux_lem_local_normalizations_Lset z r hr a (c • g) := by
  obtain ⟨u, U, hUc, huU, hUb, rfl⟩ := he
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨c • u.val, (weakSobolevGraph (centeredCube z r hr)).smul_mem c u.property⟩
  refine ⟨v, c • U, hUc.const_smul c, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c u.val.1, huU] with x h1 h2
    change ((c • u.val.1 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x = _
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply]
  · intro x hx
    simp only [Pi.smul_apply, hUb x hx]
  · change c ^ 2 * sobolevCoefficientForm a u.val u.val =
      sobolevCoefficientForm a (c • u.val) (c • u.val)
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

/-- **Exact homogeneity.** -/
theorem aux_lem_local_normalizations_sInf_smul (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) (c : ℝ) :
    sInf (aux_lem_local_normalizations_Lset z r hr a (c • g)) =
      c ^ 2 * sInf (aux_lem_local_normalizations_Lset z r hr a g) := by
  rcases eq_or_ne c 0 with rfl | hc
  · -- the zero datum has the zero competitor
    have h0 : (0 : ℝ) ∈ aux_lem_local_normalizations_Lset z r hr a ((0 : ℝ) • g) := by
      refine ⟨0, 0, continuousOn_const, ?_, ?_, ?_⟩
      · filter_upwards [Lp.coeFn_zero ℝ 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))] with x hx
        exact hx
      · intro x _; simp
      · simp
    have hle := csInf_le (aux_lem_local_normalizations_Lset_bdd z r hr a _) h0
    have hge := aux_lem_local_normalizations_sInf_nonneg z r hr a ((0 : ℝ) • g)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    linarith
  · have hset : aux_lem_local_normalizations_Lset z r hr a (c • g) =
        (c ^ 2) • aux_lem_local_normalizations_Lset z r hr a g := by
      ext e
      constructor
      · intro he
        have h := aux_lem_local_normalizations_Lset_smul_mem z r hr a (c • g) c⁻¹ e he
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
        refine Set.mem_smul_set.2 ⟨c⁻¹ ^ 2 * e, h, ?_⟩
        simp only [smul_eq_mul]
        field_simp
      · intro he
        obtain ⟨e', he', rfl⟩ := Set.mem_smul_set.1 he
        exact aux_lem_local_normalizations_Lset_smul_mem z r hr a g c e' he'
    rw [hset, Real.sInf_smul_of_nonneg (sq_nonneg c), smul_eq_mul]

/-- `√`-subadditivity of the continuous bilinear energy. -/
theorem aux_lem_local_normalizations_sqrt_clm_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (F : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ x y, F x y = F y x)
    (hpos : ∀ x, 0 ≤ F x x) (x y : E) :
    Real.sqrt (F (x + y) (x + y)) ≤ Real.sqrt (F x x) + Real.sqrt (F y y) :=
  aux_lem_local_normalizations_sqrt_form_add F.toLinearMap₁₂ hsymm hpos x y

/-- Competitors add. -/
theorem aux_lem_local_normalizations_Lset_add_le (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g h : SpatialCoordinates d → ℝ) (e₁ e₂ : ℝ)
    (he₁ : e₁ ∈ aux_lem_local_normalizations_Lset z r hr a g)
    (he₂ : e₂ ∈ aux_lem_local_normalizations_Lset z r hr a h) :
    Real.sqrt (sInf (aux_lem_local_normalizations_Lset z r hr a (g + h))) ≤
      Real.sqrt e₁ + Real.sqrt e₂ := by
  obtain ⟨u₁, U₁, hU₁c, hu₁, hU₁b, rfl⟩ := he₁
  obtain ⟨u₂, U₂, hU₂c, hu₂, hU₂b, rfl⟩ := he₂
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u₁.val + u₂.val, (weakSobolevGraph (centeredCube z r hr)).add_mem u₁.property u₂.property⟩
  have hmem : sobolevCoefficientForm a v.val v.val ∈
      aux_lem_local_normalizations_Lset z r hr a (g + h) := by
    refine ⟨v, U₁ + U₂, hU₁c.add hU₂c, ?_, ?_, rfl⟩
    · filter_upwards [Lp.coeFn_add u₁.val.1 u₂.val.1, hu₁, hu₂] with x h0 h1 h2
      change ((u₁.val.1 + u₂.val.1 : DomainL2 (centeredCube z r hr)) :
        SpatialCoordinates d → ℝ) x = _
      rw [h0, Pi.add_apply, h1, h2, Pi.add_apply]
    · intro x hx
      simp only [Pi.add_apply, hU₁b x hx, hU₂b x hx]
  calc Real.sqrt (sInf (aux_lem_local_normalizations_Lset z r hr a (g + h)))
      ≤ Real.sqrt (sobolevCoefficientForm a v.val v.val) :=
        Real.sqrt_le_sqrt (csInf_le (aux_lem_local_normalizations_Lset_bdd z r hr a _) hmem)
    _ ≤ _ := aux_lem_local_normalizations_sqrt_clm_add (sobolevCoefficientForm a)
        (sobolevCoefficientForm_symm a) (sobolevCoefficientForm_nonneg a) u₁.val u₂.val

/-- **`√`-subadditivity** of the actual response for data with competitors. -/
theorem aux_lem_local_normalizations_sInf_tri (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g h : SpatialCoordinates d → ℝ)
    (hg : (aux_lem_local_normalizations_Lset z r hr a g).Nonempty)
    (hh : (aux_lem_local_normalizations_Lset z r hr a h).Nonempty) :
    Real.sqrt (sInf (aux_lem_local_normalizations_Lset z r hr a (g + h))) ≤
      Real.sqrt (sInf (aux_lem_local_normalizations_Lset z r hr a g)) +
        Real.sqrt (sInf (aux_lem_local_normalizations_Lset z r hr a h)) := by
  set A := sInf (aux_lem_local_normalizations_Lset z r hr a g)
  set B := sInf (aux_lem_local_normalizations_Lset z r hr a h)
  have hbound : ∀ n : ℕ, Real.sqrt (sInf (aux_lem_local_normalizations_Lset z r hr a (g + h))) ≤
      Real.sqrt (A + 1 / ((n : ℝ) + 1)) + Real.sqrt (B + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨e₁, he₁, hlt₁⟩ := Real.lt_sInf_add_pos hg hε
    obtain ⟨e₂, he₂, hlt₂⟩ := Real.lt_sInf_add_pos hh hε
    exact (aux_lem_local_normalizations_Lset_add_le z r hr a g h e₁ e₂ he₁ he₂).trans
      (add_le_add (Real.sqrt_le_sqrt hlt₁.le) (Real.sqrt_le_sqrt hlt₂.le))
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (A + 1 / ((n : ℝ) + 1)) +
      Real.sqrt (B + 1 / ((n : ℝ) + 1))) atTop (𝓝 (Real.sqrt A + Real.sqrt B)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hA0 : Tendsto (fun n : ℕ => A + 1 / ((n : ℝ) + 1)) atTop (𝓝 A) := by
      simpa using (tendsto_const_nhds (x := A)).add h0
    have hB0 : Tendsto (fun n : ℕ => B + 1 / ((n : ℝ) + 1)) atTop (𝓝 B) := by
      simpa using (tendsto_const_nhds (x := B)).add h0
    exact ((Real.continuous_sqrt.tendsto A).comp hA0).add
      ((Real.continuous_sqrt.tendsto B).comp hB0)
  exact ge_of_tendsto' hlim hbound

/-- Admissible competitors exist for every Hölder datum on the unit cube. -/
theorem aux_lem_local_normalizations_Lset_nonempty {hd : 2 ≤ d}
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (g : SpatialCoordinates d → ℝ)
    (hg : IsHolderOn beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) g) :
    ∃ (b : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
      (U : SpatialCoordinates d → ℝ), Continuous U ∧
      ((b : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))] U ∧
      (∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), U x = g x) ∧
      sobolevCoefficientForm a b.val b.val ∈
        aux_lem_local_normalizations_Lset 0 1 one_pos a g := by
  obtain ⟨b, U, hUc, hbU, hUg, -⟩ :=
    Sf.traceRightInverse beta hbeta 0 1 one_pos rfl g hg
  exact ⟨b, U, hUc, hbU, hUg, ⟨b, U, hUc.continuousOn, hbU, hUg, rfl⟩⟩

theorem aux_lem_local_normalizations_rescaled_unit (g : SpatialCoordinates d → ℝ) :
    rescaledDatum (0 : SpatialCoordinates d) 1 g = g := by
  funext y
  simp [rescaledDatum]

-- ===== from LNUnit2.lean =====

variable {d : ℕ}



theorem aux_lem_local_normalizations_smooth_class
    (beta : ℝ) (hbeta1 : beta ≤ 1)
    (z : SpatialCoordinates d) (r : ℝ)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi) :
    IsCellBoundaryClass beta z r phi := by
  set G : SpatialCoordinates d → ℝ := rescaledDatum z r phi with hG
  have hGsmooth : ContDiff ℝ 1 G := by
    have haff : ContDiff ℝ 1 (fun y : SpatialCoordinates d => fun i => z i + r * y i) := by
      apply contDiff_pi.2
      intro i
      exact contDiff_const.add (contDiff_const.mul (contDiff_apply ℝ ℝ i))
    exact (hphi.of_le (by exact_mod_cast le_top)).comp haff
  set B : Set (SpatialCoordinates d) := closedBall (0 : SpatialCoordinates d) (1 / 2) with hB
  have hSB : frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) ⊆ B := by
    refine frontier_subset_closure.trans ?_
    change closure (ball (0 : SpatialCoordinates d) (1 / 2)) ⊆ B
    exact closure_ball_subset_closedBall
  have hBcpt : IsCompact B := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hBcpt.exists_bound_of_continuousOn
    ((hGsmooth.continuous_fderiv (by norm_num)).continuousOn (s := B))
  have hLip : ∀ x ∈ B, ∀ y ∈ B, |G x - G y| ≤ C * dist x y := by
    intro x hx y hy
    have h := (convex_closedBall (0 : SpatialCoordinates d) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hGsmooth.differentiable (by norm_num) w) (fun w hw => hC w hw) hy hx
    rw [Real.norm_eq_abs, ← dist_eq_norm] at h
    exact h
  have hdist_le : ∀ x y : SpatialCoordinates d,
      dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    intro x y
    refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun j => ?_
    rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j))
  have heucl_le : ∀ x ∈ B, ∀ y ∈ B,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d := by
    intro x hx y hy
    apply Real.sqrt_le_sqrt
    have hxy : dist x y ≤ 1 := by
      calc dist x y ≤ dist x 0 + dist y 0 := dist_triangle_right x y 0
        _ ≤ 1 / 2 + 1 / 2 := add_le_add (mem_closedBall.1 hx) (mem_closedBall.1 hy)
        _ = 1 := by norm_num
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          have hj : |x j - y j| ≤ 1 := by
            have := (dist_le_pi_dist x y j).trans hxy
            rwa [Real.dist_eq] at this
          have h0 : 0 ≤ |x j - y j| := abs_nonneg _
          calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
            _ ≤ 1 ^ 2 := pow_le_pow_left₀ h0 hj 2
            _ = 1 := one_pow 2
      _ = d := by simp
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self (by norm_num)))
  constructor
  · refine ⟨C * (Real.sqrt d) ^ (1 - beta), ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hdpos : 0 < dist x y := dist_pos.2 hxy
    have hepos : 0 < e := hdpos.trans_le (hdist_le x y)
    have hnum : |G x - G y| ≤ C * e :=
      (hLip x (hSB hx) y (hSB hy)).trans (mul_le_mul_of_nonneg_left (hdist_le x y) hC0)
    have hepow : 0 < e ^ beta := Real.rpow_pos_of_pos hepos beta
    calc |G x - G y| / e ^ beta ≤ C * e / e ^ beta :=
          div_le_div_of_nonneg_right hnum hepow.le
      _ = C * e ^ (1 - beta) := by
          rw [Real.rpow_sub hepos, Real.rpow_one, mul_div_assoc]
      _ ≤ C * (Real.sqrt d) ^ (1 - beta) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact Real.rpow_le_rpow hepos.le (heucl_le x (hSB hx) y (hSB hy)) (by linarith)
  · obtain ⟨M, hM⟩ := hBcpt.exists_bound_of_continuousOn hGsmooth.continuous.continuousOn
    refine ⟨M, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa [Real.norm_eq_abs] using hM x (hSB hx)

/-- The boundary class is closed under addition. -/
theorem aux_lem_local_normalizations_class_add (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    {f g : SpatialCoordinates d → ℝ}
    (hf : IsCellBoundaryClass beta z r f) (hg : IsCellBoundaryClass beta z r g) :
    IsCellBoundaryClass beta z r (f + g) := by
  obtain ⟨⟨Mf, hMf⟩, ⟨Af, hAf⟩⟩ := hf
  obtain ⟨⟨Mg, hMg⟩, ⟨Ag, hAg⟩⟩ := hg
  have hres : rescaledDatum z r (f + g) =
      fun y => rescaledDatum z r f y + rescaledDatum z r g y := by
    funext y; simp [rescaledDatum]
  refine ⟨⟨Mf + Mg, ?_⟩, ⟨Af + Ag, ?_⟩⟩
  · rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    rw [hres]
    have h1 := hMf ⟨x, hx, y, hy, hxy, rfl⟩
    have h2 := hMg ⟨x, hx, y, hy, hxy, rfl⟩
    set e := (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta
    have he : 0 ≤ e := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc |rescaledDatum z r f x + rescaledDatum z r g x -
          (rescaledDatum z r f y + rescaledDatum z r g y)| / e
        ≤ (|rescaledDatum z r f x - rescaledDatum z r f y| +
            |rescaledDatum z r g x - rescaledDatum z r g y|) / e := by
          apply div_le_div_of_nonneg_right _ he
          have := abs_add_le (rescaledDatum z r f x - rescaledDatum z r f y)
            (rescaledDatum z r g x - rescaledDatum z r g y)
          calc _ = |(rescaledDatum z r f x - rescaledDatum z r f y) +
                (rescaledDatum z r g x - rescaledDatum z r g y)| := by ring_nf
            _ ≤ _ := this
      _ = |rescaledDatum z r f x - rescaledDatum z r f y| / e +
            |rescaledDatum z r g x - rescaledDatum z r g y| / e := add_div _ _ _
      _ ≤ Mf + Mg := add_le_add h1 h2
  · rintro v ⟨x, hx, rfl⟩
    rw [hres]
    exact (abs_add_le _ _).trans (add_le_add (hAf ⟨x, hx, rfl⟩) (hAg ⟨x, hx, rfl⟩))

/-- The boundary class is closed under scalar multiplication. -/
theorem aux_lem_local_normalizations_class_smul (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (c : ℝ) {f : SpatialCoordinates d → ℝ} (hf : IsCellBoundaryClass beta z r f) :
    IsCellBoundaryClass beta z r (c • f) := by
  rcases le_total 0 c with hc | hc
  · have := aux_lem_finite_trace_tests_IsCellBoundaryClass_smul beta z r c hc hf
    simpa [Pi.smul_def, smul_eq_mul] using this
  · have h1 := aux_lem_finite_trace_tests_IsCellBoundaryClass_smul beta z r (-c)
      (by linarith) hf
    have h2 := aux_lem_finite_trace_smooth_net_IsCellBoundaryClass_neg beta z r h1
    have heq : (fun x => -(-c * f x)) = c • f := by funext x; simp [Pi.smul_apply]
    rwa [heq] at h2

/-- The Hölder boundary class of a cell, as a submodule. -/
def aux_lem_local_normalizations_classW (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ) :
    Submodule ℝ (SpatialCoordinates d → ℝ) where
  carrier := {g | IsCellBoundaryClass beta z r g}
  add_mem' hf hg := aux_lem_local_normalizations_class_add beta z r hf hg
  zero_mem' := by
    -- the zero datum has zero ratios
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · rintro v ⟨x, -, y, -, -, rfl⟩; simp [rescaledDatum]
    · rintro v ⟨x, -, rfl⟩; simp [rescaledDatum]
  smul_mem' c f hf := aux_lem_local_normalizations_class_smul beta z r c hf

theorem aux_lem_local_normalizations_quot_nonneg (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) : 0 ≤ cellBoundaryQuotientNorm beta z r g :=
  aux_lem_finite_trace_tests_quotient_nonneg beta _ _

/-- Exponent monotonicity of the quotient norms on the unit cube. -/
theorem aux_lem_local_normalizations_norm_mono (hd : 2 ≤ d) (beta' beta : ℝ)
    (hb' : 1 / 2 < beta') (hbb : beta' < beta) (hb : beta < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
      IsCellBoundaryClass beta' 0 1 g ∧
        cellBoundaryQuotientNorm beta' 0 1 g ≤ C * cellBoundaryQuotientNorm beta 0 1 g := by
  obtain ⟨C, hC, hmono⟩ := lem_finite_trace_holder_beta_bound d hd beta' beta hb' hbb hb
  refine ⟨C, hC, fun g hg => ?_⟩
  set t := cellBoundaryQuotientNorm beta 0 1 g with ht
  have ht0 : 0 ≤ t := aux_lem_local_normalizations_quot_nonneg _ _ _ _
  -- scaled copies have unit norm
  have hscaled : ∀ s : ℝ, 0 < s → s * t ≤ 1 →
      IsCellBoundaryClass beta' 0 1 g ∧ s * cellBoundaryQuotientNorm beta' 0 1 g ≤ C := by
    intro s hs hst
    have hcl := aux_lem_finite_trace_tests_IsCellBoundaryClass_smul beta 0 1 s hs.le hg
    have hn : cellBoundaryQuotientNorm beta 0 1 (fun x => s * g x) ≤ 1 := by
      rw [aux_lem_finite_trace_tests_cellBoundaryQuotientNorm_smul beta 0 1 s hs g]
      exact hst
    obtain ⟨hcl', hn'⟩ := hmono _ hcl hn
    rw [aux_lem_finite_trace_tests_cellBoundaryQuotientNorm_smul beta' 0 1 s hs g] at hn'
    refine ⟨?_, hn'⟩
    have := aux_lem_finite_trace_tests_IsCellBoundaryClass_smul beta' 0 1 s⁻¹
      (inv_nonneg.2 hs.le) hcl'
    simpa [← mul_assoc, inv_mul_cancel₀ hs.ne'] using this
  rcases ht0.lt_or_eq with htpos | ht0'
  · obtain ⟨h1, h2⟩ := hscaled t⁻¹ (inv_pos.2 htpos) (by rw [inv_mul_cancel₀ htpos.ne'])
    refine ⟨h1, ?_⟩
    have := mul_le_mul_of_nonneg_left h2 htpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul, mul_comm] at this
  · refine ⟨(hscaled 1 one_pos (by rw [← ht0']; norm_num)).1, ?_⟩
    rw [← ht0', mul_zero]
    by_contra hpos
    push Not at hpos
    obtain ⟨-, h2⟩ := hscaled ((C + 1) / cellBoundaryQuotientNorm beta' 0 1 g)
      (div_pos (by linarith) hpos) (by rw [← ht0', mul_zero]; norm_num)
    rw [div_mul_cancel₀ _ hpos.ne'] at h2
    linarith

theorem aux_lem_local_normalizations_holderRatio_congr (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (f g : SpatialCoordinates d → ℝ)
    (hfg : ∀ x ∈ S, f x = g x) :
    holderRatioSet beta S f = holderRatioSet beta S g := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [hfg x hx, hfg y hy]⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [hfg x hx, hfg y hy]⟩

/-- The Hölder seminorm of a class member is below its quotient norm. -/
theorem aux_lem_local_normalizations_holder_le_quot (beta : ℝ)
    (g : SpatialCoordinates d → ℝ) :
    holderSeminorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) g ≤ cellBoundaryQuotientNorm beta 0 1 g := by
  unfold cellBoundaryQuotientNorm quotientCBetaNorm
  rw [aux_lem_local_normalizations_rescaled_unit]
  refine le_csInf ⟨_, 0, rfl⟩ ?_
  rintro v ⟨c, rfl⟩
  unfold cAlphaNorm
  have h1 : 0 ≤ sSup {v : ℝ | ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), v = |g x - c|} := by
    apply Real.sSup_nonneg
    rintro v ⟨x, -, rfl⟩
    exact abs_nonneg _
  have h2 : holderSeminorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) (fun x => g x - c) =
      holderSeminorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) g := by
    unfold holderSeminorm
    rw [aux_lem_finite_trace_holder_beta_bound_holderRatio_const_sub]
  linarith

open scoped Distributions in
/-- Continuous-datum competitors `b + ψ`. -/
theorem aux_lem_local_normalizations_cont_competitor
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x)
    (ψ : 𝓓(centeredCube z r hr, ℝ)) :
    sobolevCoefficientForm a (b.val + smoothSobolevData ψ) (b.val + smoothSobolevData ψ) ∈
      aux_lem_local_normalizations_Lset z r hr a g := by
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨b.val + smoothSobolevData ψ,
      (weakSobolevGraph (centeredCube z r hr)).add_mem b.property (smoothSobolevData_mem ψ)⟩
  refine ⟨u, fun x => G x + ψ x, ?_, ?_, ?_, rfl⟩
  · exact hGc.add ψ.contDiff.continuous.continuousOn
  · filter_upwards [Lp.coeFn_add b.val.1 (testL2 ψ), hb, testL2_coeFn ψ] with x hadd hbx hψx
    change ((b.val.1 + testL2 ψ : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = G x + ψ x
    rw [hadd, Pi.add_apply, hbx, hψx]
  · intro x hx
    have hxnot : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      have hopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        (centeredCube z r hr).isOpen
      rw [hopen.frontier_eq] at hx
      exact hx.2
    have hψ0 : ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxnot (ψ.tsupport_subset h))
    simp only [hψ0, add_zero, hGg x hx]

/-- The actual response is at most the Sobolev Dirichlet response of any continuous
realization of the datum. -/
theorem aux_lem_local_normalizations_sInf_le_response
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    sInf (aux_lem_local_normalizations_Lset z r hr a g) ≤
      dirichletResponse (killedResponseSpace hP) a b := by
  have hmem : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈
      killedSobolevGraph (centeredCube z r hr) :=
    dirichletMinimizer_mem_affine (killedResponseSpace hP) a b
  have hcl : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈ closure
      ((LinearMap.range (smoothSobolevDataLinear (Ω := centeredCube z r hr)) :
        Submodule ℝ (SobolevData (centeredCube z r hr))) :
          Set (SobolevData (centeredCube z r hr))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose ψ hψ using hxmem
  have hψ' : ∀ n, smoothSobolevData (ψ n) = x n := hψ
  have hconv : Tendsto (fun n => b.val + smoothSobolevData (ψ n)) atTop
      (𝓝 (dirichletMinimizer (killedResponseSpace hP) a b).val) := by
    have h1 : Tendsto (fun n => b.val + x n) atTop
        (𝓝 (b.val + ((dirichletMinimizer (killedResponseSpace hP) a b).val - b.val))) :=
      tendsto_const_nhds.add hxlim
    rw [add_sub_cancel] at h1
    simpa only [hψ'] using h1
  have hform : Continuous (fun u : SobolevData (centeredCube z r hr) =>
      sobolevCoefficientForm a u u) :=
    (sobolevCoefficientForm a).continuous₂.comp (continuous_id.prodMk continuous_id)
  have hlim : Tendsto (fun n => sobolevCoefficientForm a (b.val + smoothSobolevData (ψ n))
      (b.val + smoothSobolevData (ψ n))) atTop
      (𝓝 (dirichletResponse (killedResponseSpace hP) a b)) := (hform.tendsto _).comp hconv
  refine ge_of_tendsto' hlim (fun n => ?_)
  exact csInf_le (aux_lem_local_normalizations_Lset_bdd z r hr a g)
    (aux_lem_local_normalizations_cont_competitor z r hr a b g G hGc hb hGg (ψ n))

/-- The converse comparison: every continuous-boundary competitor is admissible
for the killed response, so the Dirichlet minimum is below the boundary infimum. -/
theorem aux_lem_local_normalizations_response_le_sInf
    (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    dirichletResponse (killedResponseSpace hP) a b ≤
      sInf (aux_lem_local_normalizations_Lset z r hr a g) := by
  have hne : (aux_lem_local_normalizations_Lset z r hr a g).Nonempty := by
    exact ⟨sobolevCoefficientForm a b.val b.val, ⟨b, G, hGc, hb, hGg, rfl⟩⟩
  apply le_csInf hne
  rintro e ⟨u, U, hUc, huU, hUb, rfl⟩
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val - b.val, (weakSobolevGraph (centeredCube z r hr)).sub_mem u.property b.property⟩
  have hvrep : ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (U - G) := by
    filter_upwards [Lp.coeFn_sub u.val.1 b.val.1, huU, hb] with x hsub hxu hbx
    change ((u.val.1 - b.val.1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = U x - G x
    rw [hsub, Pi.sub_apply, hxu, hbx]
  have hvzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (U - G) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hUb x hx, hGg x hx, sub_self]
  have hvk : (v : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr) :=
    lem_extension_trace_class_transport hd z r hr v (U - G) (hUc.sub hGc) hvrep hvzero
  let w : (killedResponseSpace hP).space := ⟨v.val, hvk⟩
  have hsum : b.val + w.val = u.val := by
    change b.val + (u.val - b.val) = u.val
    abel
  have hleast := dirichletResponse_isLeast (killedResponseSpace hP) a b
  have hle := hleast.2 ⟨w, rfl⟩
  change dirichletResponse (killedResponseSpace hP) a b ≤
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) at hle
  rw [hsum] at hle
  exact hle

theorem aux_lem_local_normalizations_unit_poincare (hd : 2 ≤ d) :
    ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖ := by
  have : NeZero d := ⟨by omega⟩
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    refine ⟨(centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen, ⟨1, one_pos, ?_⟩, ?_⟩
    · intro x hx i
      have hx' : dist x 0 < 1 / 2 := hx
      have hi : |x i| ≤ dist x 0 := by
        have := dist_le_pi_dist x 0 i
        simpa [Real.dist_eq] using this
      linarith
    · exact convex_ball (0 : SpatialCoordinates d) (1 / 2)
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos) hgeom).1

/-- **Unit-cube extension bound** (eq:mfd-2 at `r = 1`), for the actual response. -/
theorem aux_lem_local_normalizations_unit_ext_bound (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta' : ℝ) (hb' : beta' ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : PositiveCoefficient
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (g : SpatialCoordinates d → ℝ),
      IsCellBoundaryClass beta' 0 1 g →
      sInf (aux_lem_local_normalizations_Lset 0 1 one_pos a g) ≤
        C * Jc.Lam 0 1 one_pos a 0 1 ((beta' - 1 / 2) / 4) 2 *
          (cellBoundaryQuotientNorm beta' 0 1 g) ^ 2 := by
  have hext := (lem_extension d hd Jc Xc Sf).1 beta' hb'
  obtain ⟨C, hC, hbound⟩ := hext
  refine ⟨C, hC, fun a g hg => ?_⟩
  have hgH : IsHolderOn beta' (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) g := by
    have h := hg.1
    rwa [aux_lem_local_normalizations_rescaled_unit] at h
  obtain ⟨b, U, hUc, hbU, hUg, -⟩ := Sf.traceRightInverse beta' hb' 0 1 one_pos rfl g hgH
  have hP := aux_lem_local_normalizations_unit_poincare (d := d) hd
  have hUH : IsHolderOn beta' (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) U := by
    unfold IsHolderOn
    rw [aux_lem_local_normalizations_holderRatio_congr beta' _ U g hUg]
    exact hgH
  have hsemi : holderSeminorm beta' (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) U = holderSeminorm beta'
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) g := by
    unfold holderSeminorm
    rw [aux_lem_local_normalizations_holderRatio_congr beta' _ U g hUg]
  have h1 := aux_lem_local_normalizations_sInf_le_response 0 1 one_pos hP a b g U
    hUc.continuousOn hbU hUg
  have h2 := hbound 0 1 one_pos le_rfl hP a U b hUc.continuousOn hUH hbU
  rw [hsemi, Real.one_rpow, Real.one_rpow, one_mul, mul_one] at h2
  have hq := aux_lem_local_normalizations_holder_le_quot beta' g
  have hH0 : 0 ≤ holderSeminorm beta' (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) g := by
    apply Real.sSup_nonneg
    rintro v ⟨x, -, y, -, -, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hLam : 0 ≤ C * Jc.Lam 0 1 one_pos a 0 1 ((beta' - 1 / 2) / 4) 2 :=
    mul_nonneg hC.le (Jc.Lam_pos _ _ _ _ _ _ _ _).le
  calc sInf (aux_lem_local_normalizations_Lset 0 1 one_pos a g)
      ≤ C * Jc.Lam 0 1 one_pos a 0 1 ((beta' - 1 / 2) / 4) 2 *
          holderSeminorm beta' (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d))) g ^ 2 := h1.trans h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hq 2) hLam

-- ===== from LNUnit3.lean =====

variable {d : ℕ}

/-- Uniform `L¹` bounds give tightness at integer levels (Markov). -/
theorem aux_lem_local_normalizations_tight_of_L1 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (K : ℕ → Ω → ℝ) (Cb : ℝ)
    (_hK : ∀ N, AEStronglyMeasurable (K N) μ)
    (hB : ∀ N, eLpNorm (K N) 1 μ ≤ ENNReal.ofReal Cb) :
    ∀ η : ℝ≥0∞, 0 < η → ∃ Rb : ℕ, ∀ N, μ {om | (Rb : ℝ) < K N om} ≤ η := by
  intro η hη
  rcases eq_or_ne η ⊤ with htop | htop
  · exact ⟨0, fun N => by rw [htop]; exact le_top⟩
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨Rb, hRb⟩ := exists_nat_gt (max Cb 0 / η.toReal)
  have hRbpos : (0 : ℝ) < Rb := lt_of_le_of_lt (by positivity) hRb
  refine ⟨Rb, fun N => ?_⟩
  have hM := mul_meas_ge_le_pow_eLpNorm' μ (f := K N) (p := 1) one_ne_zero ENNReal.one_ne_top
    (Rb : ℝ≥0∞)
  simp only [ENNReal.toReal_one, ENNReal.rpow_one] at hM
  have hsub : {om | (Rb : ℝ) < K N om} ⊆ {om | (Rb : ℝ≥0∞) ≤ ‖K N om‖ₑ} := by
    intro om hom
    simp only [mem_ofPred_eq] at hom ⊢
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hom.le.trans (le_abs_self _))
  have hRbne : (Rb : ℝ≥0∞) ≠ 0 := by exact_mod_cast hRbpos.ne'
  have hμ : μ {om | (Rb : ℝ≥0∞) ≤ ‖K N om‖ₑ} ≤ ENNReal.ofReal Cb / Rb := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hRbne) (Or.inl (ENNReal.natCast_ne_top Rb)),
      mul_comm]
    exact hM.trans (hB N)
  refine (measure_mono hsub).trans (hμ.trans ?_)
  rw [ENNReal.div_le_iff hRbne (ENNReal.natCast_ne_top Rb), ← ENNReal.ofReal_toReal htop,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hηr.le]
  apply ENNReal.ofReal_le_ofReal
  have := (div_lt_iff₀ hηr).1 hRb
  nlinarith [le_max_left Cb 0]

/-- **eq:mfd-3 at the unit root**: the cutoff coarse ellipticity of the unit cube
is dominated by a tight family, with the disorder threshold fixed before the model. -/
theorem aux_lem_local_normalizations_unit_K (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta' : ℝ) (hb' : beta' ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          Jc.Lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) 0 1
            ((beta' - 1 / 2) / 4) 2 ≤ K N om) ∧
        (∀ η : ℝ≥0∞, 0 < η → ∃ Rb : ℕ, ∀ N,
          (chaosSampleLaw M).toMeasure {om | (Rb : ℝ) < K N om} ≤ η) := by
  have hgrid := (lem_extension d hd Jc Xc Sf).2 1 1 one_pos le_rfl beta' hb'
  obtain ⟨delta0, hdelta0, hgrid⟩ := hgrid
  refine ⟨delta0, hdelta0, fun M Rm H HI hδ => ?_⟩
  have h := hgrid M Rm H HI hδ 0 1 one_pos 1 (fun _ => 0)
  obtain ⟨K, Cb, hmem, hnorm, hae⟩ := h
  refine ⟨K, ?_, ?_⟩
  · filter_upwards [hae] with om hom N
    have h1 := hom N 0 0 (fun _ => 0) (Nat.zero_le N) (by
      intro x hx
      have hw : (fun i => ((fun _ : Fin 1 => (0 : SpatialCoordinates d)) 0) i +
          (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * (((fun _ : Fin d => (0 : ℤ)) i : ℤ) : ℝ)) =
          (0 : SpatialCoordinates d) := by funext i; simp
      have hr : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
      change x ∈ Metric.ball _ _ at hx
      change x ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2)
      rw [hw, hr] at hx
      exact hx)
    have hw : (fun i => ((fun _ : Fin 1 => (0 : SpatialCoordinates d)) 0) i +
        (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * (((fun _ : Fin d => (0 : ℤ)) i : ℤ) : ℝ)) =
        (0 : SpatialCoordinates d) := by funext i; simp
    have hr : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
    rw [hw, hr, Real.one_rpow, mul_one] at h1
    have hlam := Jc.lam_pos 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) 0 1
      ((beta' - 1 / 2) / 4) 2
    have : 0 ≤ (Jc.lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) 0 1
      ((beta' - 1 / 2) / 4) 2)⁻¹ := (inv_pos.2 hlam).le
    linarith
  · have hB : ∀ N, eLpNorm (K N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb := by
      intro N
      have := hnorm N
      simpa using this
    exact aux_lem_local_normalizations_tight_of_L1 _ K Cb
      (fun N => (hmem N).aestronglyMeasurable) hB

/-- **Countable smooth catalogue** dense for the `β'` quotient norm on the `β` class
(`lem_finite_trace_smooth_net`, scaled). -/
theorem aux_lem_local_normalizations_catalogue (hd : 2 ≤ d) (beta' beta : ℝ)
    (hb' : 1 / 2 < beta') (hbb : beta' < beta) (hb : beta < 1) :
    ∃ D : ℕ → (SpatialCoordinates d → ℝ), (∀ i, ContDiff ℝ ∞ (D i)) ∧
      ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        ∀ ε > 0, ∃ i, |cellBoundaryQuotientNorm beta' 0 1 (g - D i)| ≤ ε := by
  classical
  obtain ⟨Cn, -, -, hnet⟩ := lem_finite_trace_smooth_net d hd beta' beta hb' hbb hb
  choose Hs hHs using fun m : ℕ => hnet (1 / ((m : ℝ) + 1)) (by positivity)
  let S : Set (SpatialCoordinates d → ℝ) :=
    insert 0 (⋃ m : ℕ, ⋃ n : ℕ, (fun h => (n : ℝ) • h) '' ((Hs m : Finset _) : Set _))
  have hScount : S.Countable := by
    refine Set.Countable.insert _ (Set.countable_iUnion fun m => Set.countable_iUnion fun n => ?_)
    exact ((Hs m).finite_toSet.image _).countable
  obtain ⟨D, hD⟩ := hScount.exists_eq_range ⟨0, Set.mem_insert _ _⟩
  refine ⟨D, fun i => ?_, fun g hg ε hε => ?_⟩
  · have hi : D i ∈ S := hD ▸ Set.mem_range_self i
    rcases hi with h0 | hi
    · rw [h0]; exact contDiff_const
    · simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hi
      obtain ⟨m, n, h, hh, hDi⟩ := hi
      rw [← hDi]
      exact ((hHs m).1 h hh).1.const_smul (n : ℝ)
  · set t := cellBoundaryQuotientNorm beta 0 1 g
    have ht0 : 0 ≤ t := aux_lem_local_normalizations_quot_nonneg _ _ _ _
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt ht0 hn
    obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) / ε)
    have hm' : (n : ℝ) * (1 / ((m : ℝ) + 1)) ≤ ε := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      have := (div_lt_iff₀ hε).1 hm
      nlinarith
    -- the rescaled datum has unit norm
    set g' : SpatialCoordinates d → ℝ := fun x => (n : ℝ)⁻¹ * g x
    have hg' : IsCellBoundaryClass beta 0 1 g' :=
      aux_lem_finite_trace_tests_IsCellBoundaryClass_smul beta 0 1 _ (by positivity) hg
    have hg'n : cellBoundaryQuotientNorm beta 0 1 g' ≤ 1 := by
      rw [aux_lem_finite_trace_tests_cellBoundaryQuotientNorm_smul beta 0 1 _
        (inv_pos.2 hn0) g, inv_mul_le_iff₀ hn0, mul_one]
      exact hn.le
    obtain ⟨h, hh, hgh⟩ := (hHs m).2 g' hg' hg'n
    have hmem : (n : ℝ) • h ∈ S := by
      refine Set.mem_insert_of_mem _ ?_
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
      exact ⟨m, n, h, hh, rfl⟩
    rw [hD] at hmem
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, ?_⟩
    rw [hi]
    have heq : g - (n : ℝ) • h = fun x => (n : ℝ) * (g' x - h x) := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, g']
      field_simp
    rw [heq, aux_lem_finite_trace_tests_cellBoundaryQuotientNorm_smul beta' 0 1 _ hn0,
      abs_of_nonneg (mul_nonneg hn0.le (aux_lem_local_normalizations_quot_nonneg _ _ _ _))]
    exact (mul_le_mul_of_nonneg_left hgh hn0.le).trans hm'

/-- **The unit-cube limiting response seminorm.**  Given convergence in probability of
the actual response for every smooth datum on the unit cube (the determining traces of
`mfd:lem-local-normalizations`), the limit extends to a random seminorm with convergence for every
`C^β` datum and an almost-sure `C^β` extension bound. -/
theorem aux_lem_local_normalizations_unit_RL (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hb : 1 / 2 < beta) (hb1 : beta < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      (∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g → ∃ L : BilateralField d → ℝ,
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N om => sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
            (cutoffPositiveCoefficient M H om N 0 one_pos) g)) atTop L) →
      ∃ RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ),
        (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun N om => sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
              (cutoffPositiveCoefficient M H om N 0 one_pos) g)) atTop
            (fun om => (RL0 om g) ^ 2)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
            (RL0 om g) ^ 2 ≤ K * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) := by
  classical
  set beta' : ℝ := (1 / 2 + beta) / 2 with hbeta'
  have hb'1 : 1 / 2 < beta' := by rw [hbeta']; linarith
  have hb'2 : beta' < beta := by rw [hbeta']; linarith
  have hb'I : beta' ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨hb'1, by linarith⟩
  have hbI : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨hb, hb1⟩
  obtain ⟨delta0, hdelta0, hKall⟩ := aux_lem_local_normalizations_unit_K hd Jc Xc Sf beta' hb'I
  obtain ⟨C, hC, hext⟩ := aux_lem_local_normalizations_unit_ext_bound hd Jc Xc Sf beta' hb'I
  obtain ⟨Cm, hCm, hmono⟩ := aux_lem_local_normalizations_norm_mono hd beta' beta hb'1 hb'2 hb1
  obtain ⟨D, hDs, hdense⟩ := aux_lem_local_normalizations_catalogue hd beta' beta hb'1 hb'2 hb1
  refine ⟨delta0, hdelta0, fun M Rm H HI hδ hconv => ?_⟩
  obtain ⟨K, hKae, hKtight⟩ := hKall M Rm H HI hδ
  set μ := (chaosSampleLaw M).toMeasure
  set Q : ℕ → BilateralField d → (SpatialCoordinates d → ℝ) → ℝ := fun N om g =>
    sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
      (cutoffPositiveCoefficient M H om N 0 one_pos) g) with hQ
  set W := aux_lem_local_normalizations_classW (d := d) beta 0 1
  have hW : ∀ g, g ∈ W ↔ IsCellBoundaryClass beta 0 1 g := fun g => Iff.rfl
  have hne : ∀ N om g, g ∈ W → (aux_lem_local_normalizations_Lset 0 1 one_pos
      (cutoffPositiveCoefficient M H om N 0 one_pos) g).Nonempty := by
    intro N om g hg
    have hgH : IsHolderOn beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) g := by
      have h := ((hW g).1 hg).1
      rwa [aux_lem_local_normalizations_rescaled_unit] at h
    obtain ⟨b, U, -, -, -, hmem⟩ := aux_lem_local_normalizations_Lset_nonempty Sf beta hbI
      (cutoffPositiveCoefficient M H om N 0 one_pos) g hgH
    exact ⟨_, hmem⟩
  have hQnn : ∀ N om g, 0 ≤ Q N om g := fun N om g =>
    aux_lem_local_normalizations_sInf_nonneg _ _ _ _ _
  have hQtri : ∀ N om g h, g ∈ W → h ∈ W →
      Real.sqrt (Q N om (g + h)) ≤ Real.sqrt (Q N om g) + Real.sqrt (Q N om h) :=
    fun N om g h hg hh => aux_lem_local_normalizations_sInf_tri _ _ _ _ g h
      (hne N om g hg) (hne N om h hh)
  have hQsmul : ∀ N om (c : ℝ) g, g ∈ W → Q N om (c • g) = c ^ 2 * Q N om g :=
    fun N om c g _ => aux_lem_local_normalizations_sInf_smul _ _ _ _ g c
  have hKbound : ∀ᵐ om ∂μ, ∀ N g, g ∈ W →
      Q N om g ≤ (C * K N om) * cellBoundaryQuotientNorm beta' 0 1 g ^ 2 := by
    filter_upwards [hKae] with om hom N g hg
    have h1 := hext (cutoffPositiveCoefficient M H om N 0 one_pos) g ((hmono g hg).1)
    calc Q N om g ≤ C * Jc.Lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) 0 1
          ((beta' - 1 / 2) / 4) 2 * cellBoundaryQuotientNorm beta' 0 1 g ^ 2 := h1
      _ ≤ (C * K N om) * cellBoundaryQuotientNorm beta' 0 1 g ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left (hom N) hC.le
  have hKtight' : ∀ η : ℝ≥0∞, 0 < η → ∃ Rb : ℕ, ∀ N, μ {om | (Rb : ℝ) < C * K N om} ≤ η := by
    intro η hη
    obtain ⟨Rb, hRb⟩ := hKtight η hη
    refine ⟨Nat.ceil (C * Rb), fun N => (measure_mono fun om hom => ?_).trans (hRb N)⟩
    simp only [mem_ofPred_eq] at hom ⊢
    have h1 : C * (Rb : ℝ) < C * K N om := lt_of_le_of_lt (Nat.le_ceil _) hom
    exact lt_of_mul_lt_mul_left h1 hC.le
  have hDW : ∀ i, D i ∈ W := fun i =>
    (hW _).2 (aux_lem_local_normalizations_smooth_class beta hb1.le 0 1 (D i) (hDs i))
  choose L hL using fun i => hconv (D i) (hDs i)
  obtain ⟨R, hRconv, hRbound⟩ := aux_lem_local_normalizations_seminorm_limit μ W
    (cellBoundaryQuotientNorm beta' 0 1) Q hQnn hQtri hQsmul (fun N om => C * K N om)
    hKbound hKtight' D hDW (fun g hg ε hε => hdense g ((hW g).1 hg) ε hε) L hL
  refine ⟨R, fun g hg => hRconv g ((hW g).2 hg), ?_⟩
  filter_upwards [hRbound] with om hom
  obtain ⟨Kc, hKc, hKcb⟩ := hom
  refine ⟨Kc * Cm ^ 2, by positivity, fun g hg => ?_⟩
  have h1 := hKcb g ((hW g).2 hg)
  have h2 := (hmono g hg).2
  have h0 := aux_lem_local_normalizations_quot_nonneg beta' 0 1 g
  calc (R om g) ^ 2 ≤ Kc * cellBoundaryQuotientNorm beta' 0 1 g ^ 2 := h1
    _ ≤ Kc * (Cm * cellBoundaryQuotientNorm beta 0 1 g) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 2) hKc.le
    _ = Kc * Cm ^ 2 * cellBoundaryQuotientNorm beta 0 1 g ^ 2 := by ring

-- ===== from LNPos.lean =====

variable {d : ℕ}

/-- The public Chapter 2 domain of the unit cube. -/
def aux_lem_local_normalizations_unitDomain (d : ℕ) : Homogenization.Book.Ch02.Domain d :=
  Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0)

theorem aux_lem_local_normalizations_unitDomain_set :
    (aux_lem_local_normalizations_unitDomain d : Set (Homogenization.Vec d)) =
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ (0 : ℤ) := by positivity
  have h := _root_.SubdiffusiveProcess.EllipticRegularity.centeredCube_zero_eq_openCubeSet_originCube
    (d := d) (0 : ℤ) hr
  have h1 : (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (0 : ℤ)) hr :
      Set (SpatialCoordinates d)) =
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    change Metric.ball (0 : SpatialCoordinates d) ((3 : ℝ) ^ (0 : ℤ) / 2) =
      Metric.ball (0 : SpatialCoordinates d) (1 / 2)
    simp
  rw [aux_lem_local_normalizations_unitDomain, Homogenization.Book.Ch02.cubeDomain_coe,
    ← h, h1]

/-- The affine Dirichlet response is the coarse quadratic form (the public Chapter 2
variational identity, as in `cor_37`). -/
theorem aux_lem_local_normalizations_affine_eq_sigma
    (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (U : Homogenization.Book.Ch02.Domain d)
    (hUOm : (U : Set (Homogenization.Vec d)) = (Om : Set (SpatialCoordinates d)))
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (a : SpatialCoordinates d → ℝ)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (aP : PositiveCoefficient Om)
    (haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) :
    affineDirichletResponse hOm hP aP p / volume.real (Om : Set (SpatialCoordinates d)) =
      Homogenization.vecDot p
        (Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaCoarse U data.toCoeffOn) p) := by
  obtain ⟨S, hdom, hne⟩ := U
  change S = (Om : Set (SpatialCoordinates d)) at hUOm
  subst hUOm
  have htheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
    _ data.toCoeffOn data.isSymmetric
  have hnu := htheory.dirichlet_value_by_sigma p
  rw [_root_.SubdiffusiveProcess.EllipticRegularity.symmetricDirichletNu_eq_affineDirichletResponse
    hdom hne data hOm hP aP haP hvol] at hnu
  have hv : volume.real (Om : Set (SpatialCoordinates d)) ≠ 0 := ne_of_gt hvol
  calc affineDirichletResponse hOm hP aP p / volume.real (Om : Set (SpatialCoordinates d))
      = 2 * (affineDirichletResponse hOm hP aP p /
          (2 * volume.real (Om : Set (SpatialCoordinates d)))) := by field_simp
    _ = _ := by rw [hnu]; ring

/-- Every continuous competitor with affine boundary values costs at least the affine
Dirichlet response. -/
theorem aux_lem_local_normalizations_sInf_ge_affine (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (p : Fin d → ℝ)
    (hne : (aux_lem_local_normalizations_Lset z r hr a
      (fun x => ∑ i : Fin d, p i * x i)).Nonempty) :
    affineDirichletResponse (centeredCube_isBounded z hr) hP a p ≤
      sInf (aux_lem_local_normalizations_Lset z r hr a (fun x => ∑ i : Fin d, p i * x i)) := by
  apply le_csInf hne
  rintro e ⟨u, U, hU, huU, hbdry, rfl⟩
  let b := affineSobolev (centeredCube_isBounded z hr) p 0
  let phi : SpatialCoordinates d → ℝ := fun x => ∑ i : Fin d, p i * x i
  have hphi : Continuous phi := continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_apply i)
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val - b.val, (weakSobolevGraph (centeredCube z r hr)).sub_mem u.property b.property⟩
  have hvU : ContinuousOn (U - phi) (closedCube z r hr : Set (SpatialCoordinates d)) :=
    hU.sub hphi.continuousOn
  have hvrep : ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (U - phi) := by
    filter_upwards [Lp.coeFn_sub u.val.1 b.val.1, huU,
      affineL2_coeFn (centeredCube_isBounded z hr) p 0] with x hsub hxu hxb
    change ((u.val.1 - b.val.1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = U x - phi x
    rw [hsub, Pi.sub_apply, hxu]
    change U x - (affineL2 (centeredCube_isBounded z hr) p 0 : SpatialCoordinates d → ℝ) x = _
    rw [hxb, affineSlope_apply, add_zero]
  have hvzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (U - phi) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hbdry x hx, phi, sub_self]
  have hvk : (v : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr) :=
    lem_extension_trace_class_transport hd z r hr v (U - phi) hvU hvrep hvzero
  let w : (killedResponseSpace hP).space := ⟨v.val, hvk⟩
  have hsum : b.val + w.val = u.val := by
    change b.val + (u.val - b.val) = u.val
    abel
  have hleast := dirichletResponse_isLeast (killedResponseSpace hP) a b
  have hle := hleast.2 ⟨w, rfl⟩
  change dirichletResponse (killedResponseSpace hP) a b ≤
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) at hle
  rw [hsum] at hle
  exact hle

theorem aux_lem_local_normalizations_unit_volume :
    volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      1 := by
  rw [measureReal_def, centeredCube_volume]
  simp

/-- **Coarse lower bound at finite cutoff**: the actual affine response on the unit cube
dominates `λ_{s,2}(Q₀; A_N) |p|²`. -/
theorem aux_lem_local_normalizations_affine_ge_lam (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖)
    (p : Fin d → ℝ) :
    Jc.lam 0 1 one_pos (cutoffPositiveCoefficient M H omega N 0 one_pos) 0 1 s 2 *
        (p ⬝ᵥ p) ≤
      affineDirichletResponse (centeredCube_isBounded 0 one_pos) hP
        (cutoffPositiveCoefficient M H omega N 0 one_pos) p := by
  have : NeZero d := ⟨by omega⟩
  set a := cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) one_pos
  have hsub : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) :=
    subset_rfl
  have hlamEq := Jc.lam_eq 0 1 one_pos a 0 1 one_pos hsub s hs 2 (by norm_num)
  have hq := aux_in_deterministic_matrix_bounds_quad_ge (Homogenization.originCube d 0)
    (Jc.chart 0 1 one_pos a 0 1) hs.1 aux_in_deterministic_matrix_bounds_two_admissible p
  rw [← hlamEq] at hq
  set data := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H omega N)
    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
  have hset := aux_lem_local_normalizations_unitDomain_set (d := d)
  have hopen : Homogenization.openCubeSet (Homogenization.originCube d 0) =
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [← hset, aux_lem_local_normalizations_unitDomain, Homogenization.Book.Ch02.cubeDomain_coe]
  have hAE : Homogenization.Book.Ch02.CoeffOn.AEEq
      ((Jc.chart 0 1 one_pos a 0 1).coeffOn (Homogenization.originCube d 0))
      data.toCoeffOn := by
    unfold Homogenization.Book.Ch02.CoeffOn.AEEq
    change ((Jc.chart 0 1 one_pos a 0 1).coeffOn
      (Homogenization.originCube d 0)).toCoeffField =ᵐ[volume.restrict
        (Homogenization.openCubeSet (Homogenization.originCube d 0))]
      data.toCoeffOn.toCoeffField
    have hc := Jc.chart_eq 0 1 one_pos a 0 1 one_pos hsub (Homogenization.originCube d 0)
      subset_rfl
    have hcoe := aux_lem_local_normalizations_cutoff_coeFn M H omega N
      (0 : SpatialCoordinates d) one_pos
    rw [hopen] at hc ⊢
    filter_upwards [hc, hcoe] with x h1 h2
    rw [h1]
    have hx : (fun i => (0 : SpatialCoordinates d) i + 1 * x i) = x := by
      funext i; simp
    rw [hx, h2]
    rfl
  have hσ := Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq hAE
  have haff := aux_lem_local_normalizations_affine_eq_sigma
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos)
    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0)) hset
    (centeredCube_isBounded 0 one_pos) hP
    (cutoffCoefficient M H omega N) data a
    (aux_lem_local_normalizations_cutoff_coeFn M H omega N 0 one_pos)
    (by rw [aux_lem_local_normalizations_unit_volume]; norm_num) p
  rw [aux_lem_local_normalizations_unit_volume, div_one] at haff
  rw [haff]
  rw [hσ] at hq
  simpa [Homogenization.vecDot, Homogenization.matVecMul, dotProduct, Matrix.mulVec] using hq

/-- A probability limit of responses bounded below by `c / K_N` with tight `K_N` is
almost surely positive. -/
theorem aux_lem_local_normalizations_pos_of_lower {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (L : Ω → ℝ) (hX : TendstoInMeasure μ X atTop L)
    (K : ℕ → Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (hlow : ∀ᵐ om ∂μ, ∀ N, 0 < K N om ∧ c / K N om ≤ X N om)
    (hK : ∀ η : ℝ≥0∞, 0 < η → ∃ Rb : ℕ, ∀ N, μ {om | (Rb : ℝ) < K N om} ≤ η) :
    ∀ᵐ om ∂μ, 0 < L om := by
  rw [ae_iff]
  apply le_antisymm _ (zero_le)
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  obtain ⟨Rb, hRb⟩ := hK η (by exact_mod_cast hη)
  set R : ℝ := (Rb : ℝ) + 1
  have hR : 0 < R := by positivity
  set ε : ℝ := c / (2 * R)
  have hε : 0 < ε := by positivity
  have hdist := (tendstoInMeasure_iff_dist.1 hX) ε hε
  have hbad : μ {om | ¬ (∀ N, 0 < K N om ∧ c / K N om ≤ X N om)} = 0 := by
    simpa [ae_iff] using hlow
  -- for every N the non-positive set is covered by three small sets
  have hcover : ∀ N, μ {om | ¬ 0 < L om} ≤
      μ {om | ε ≤ dist (X N om) (L om)} + (η : ℝ≥0∞) := by
    intro N
    have hsub : {om | ¬ 0 < L om} ⊆ {om | ε ≤ dist (X N om) (L om)} ∪
        ({om | (Rb : ℝ) < K N om} ∪ {om | ¬ (∀ N, 0 < K N om ∧ c / K N om ≤ X N om)}) := by
      intro om hom
      by_contra hno
      simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le, not_lt, not_not] at hno hom
      obtain ⟨h1, h2, h3⟩ := hno
      obtain ⟨hKpos, hXlow⟩ := h3 N
      rw [Real.dist_eq] at h1
      have hXsmall : X N om < ε := by
        have := (abs_lt.1 h1).2
        linarith
      have hKle : K N om ≤ R := by linarith
      have : c / R ≤ c / K N om := div_le_div_of_nonneg_left hc.le hKpos hKle
      have hcR : ε < c / R := by
        change c / (2 * R) < c / R
        rw [div_lt_div_iff₀ (by positivity) hR]
        nlinarith
      linarith
    calc μ {om | ¬ 0 < L om} ≤ μ ({om | ε ≤ dist (X N om) (L om)} ∪
          ({om | (Rb : ℝ) < K N om} ∪ {om | ¬ (∀ N, 0 < K N om ∧ c / K N om ≤ X N om)})) :=
          measure_mono hsub
      _ ≤ μ {om | ε ≤ dist (X N om) (L om)} + (μ {om | (Rb : ℝ) < K N om} +
          μ {om | ¬ (∀ N, 0 < K N om ∧ c / K N om ≤ X N om)}) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ μ {om | ε ≤ dist (X N om) (L om)} + (η : ℝ≥0∞) := by
          rw [hbad, add_zero]
          exact add_le_add le_rfl (hRb N)
  have hlim : Tendsto (fun N => μ {om | ε ≤ dist (X N om) (L om)} + (η : ℝ≥0∞)) atTop
      (𝓝 (0 + (η : ℝ≥0∞))) := hdist.add tendsto_const_nhds
  rw [zero_add] at hlim
  have := ge_of_tendsto' hlim hcover
  simpa using this

/-- eq:mfd-3 at the unit root, lower half: the inverse coarse lower ellipticity of the
unit cube is dominated by a tight family, threshold fixed before the model. -/
theorem aux_lem_local_normalizations_unit_Klam (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta' : ℝ) (hb' : beta' ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          (Jc.lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) 0 1
            ((beta' - 1 / 2) / 4) 2)⁻¹ ≤ K N om) ∧
        (∀ η : ℝ≥0∞, 0 < η → ∃ Rb : ℕ, ∀ N,
          (chaosSampleLaw M).toMeasure {om | (Rb : ℝ) < K N om} ≤ η) := by
  have hgrid := (lem_extension d hd Jc Xc Sf).2 1 1 one_pos le_rfl beta' hb'
  obtain ⟨delta0, hdelta0, hgrid⟩ := hgrid
  refine ⟨delta0, hdelta0, fun M Rm H HI hδ => ?_⟩
  have h := hgrid M Rm H HI hδ 0 1 one_pos 1 (fun _ => 0)
  obtain ⟨K, Cb, hmem, hnorm, hae⟩ := h
  refine ⟨K, ?_, ?_⟩
  · filter_upwards [hae] with om hom N
    have h1 := hom N 0 0 (fun _ => 0) (Nat.zero_le N) (by
      intro x hx
      have hw : (fun i => ((fun _ : Fin 1 => (0 : SpatialCoordinates d)) 0) i +
          (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * (((fun _ : Fin d => (0 : ℤ)) i : ℤ) : ℝ)) =
          (0 : SpatialCoordinates d) := by funext i; simp
      have hr : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
      change x ∈ Metric.ball _ _ at hx
      change x ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2)
      rw [hw, hr] at hx
      exact hx)
    have hw : (fun i => ((fun _ : Fin 1 => (0 : SpatialCoordinates d)) 0) i +
        (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) * (((fun _ : Fin d => (0 : ℤ)) i : ℤ) : ℝ)) =
        (0 : SpatialCoordinates d) := by funext i; simp
    have hr : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
    rw [hw, hr, Real.one_rpow, mul_one] at h1
    have hLam := Jc.Lam_pos 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) 0 1
      ((beta' - 1 / 2) / 4) 2
    linarith
  · have hB : ∀ N, eLpNorm (K N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb := by
      intro N
      have := hnorm N
      simpa using this
    exact aux_lem_local_normalizations_tight_of_L1 _ K Cb
      (fun N => (hmem N).aestronglyMeasurable) hB

theorem aux_lem_local_normalizations_aff_mem (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (p : Fin d → ℝ) :
    (aux_lem_local_normalizations_Lset z r hr a (fun x => ∑ i : Fin d, p i * x i)).Nonempty := by
  refine ⟨_, affineSobolev (centeredCube_isBounded z hr) p 0,
    fun x => ∑ i : Fin d, p i * x i,
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).continuousOn,
    ?_, fun x _ => rfl, rfl⟩
  filter_upwards [affineL2_coeFn (centeredCube_isBounded z hr) p 0] with x hx
  change (affineL2 (centeredCube_isBounded z hr) p 0 : SpatialCoordinates d → ℝ) x = _
  rw [hx, affineSlope_apply, add_zero]

/-- **Unit-cube positivity (clause 4 at the unit cube)**: every probability limit of the
actual nonconstant affine responses on the unit cube is almost surely positive. -/
theorem aux_lem_local_normalizations_unit_pos (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ p : Fin d → ℝ, p ≠ 0 → ∀ L : BilateralField d → ℝ,
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N om => sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
            (cutoffPositiveCoefficient M H om N 0 one_pos)
            (fun x : SpatialCoordinates d => ∑ i : Fin d, p i * x i))) atTop L →
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, 0 < L om := by
  have hb : (3 / 4 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨delta0, hdelta0, hK⟩ := aux_lem_local_normalizations_unit_Klam hd Jc Xc Sf (3 / 4) hb
  refine ⟨delta0, hdelta0, fun M Rm H HI hδ p hp L hL => ?_⟩
  obtain ⟨K, hKae, hKt⟩ := hK M Rm H HI hδ
  have hP := aux_lem_local_normalizations_unit_poincare (d := d) hd
  have hs : ((3 / 4 : ℝ) - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hc : 0 < p ⬝ᵥ p := by
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h
      push Not at h
      exact hp (funext h)
    simp only [dotProduct]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (p j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  refine aux_lem_local_normalizations_pos_of_lower _ _ L hL K (p ⬝ᵥ p) hc ?_ hKt
  filter_upwards [hKae] with om hom N
  set a := cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) one_pos
  have hlam := Jc.lam_pos 0 1 one_pos a 0 1 (((3 / 4 : ℝ) - 1 / 2) / 4) 2
  have hKN : (Jc.lam 0 1 one_pos a 0 1 (((3 / 4 : ℝ) - 1 / 2) / 4) 2)⁻¹ ≤ K N om := hom N
  have hKpos : 0 < K N om := lt_of_lt_of_le (inv_pos.2 hlam) hKN
  refine ⟨hKpos, ?_⟩
  have h1 := aux_lem_local_normalizations_affine_ge_lam hd Jc M H om N _ hs hP p
  have h2 := aux_lem_local_normalizations_sInf_ge_affine hd 0 1 one_pos hP a p
    (aux_lem_local_normalizations_aff_mem 0 1 one_pos a p)
  have hlamK : (K N om)⁻¹ ≤ Jc.lam 0 1 one_pos a 0 1 (((3 / 4 : ℝ) - 1 / 2) / 4) 2 := by
    rw [inv_le_comm₀ hKpos hlam]; exact hKN
  calc p ⬝ᵥ p / K N om = (K N om)⁻¹ * (p ⬝ᵥ p) := by ring
    _ ≤ Jc.lam 0 1 one_pos a 0 1 (((3 / 4 : ℝ) - 1 / 2) / 4) 2 * (p ⬝ᵥ p) :=
        mul_le_mul_of_nonneg_right hlamK hc.le
    _ ≤ _ := h1.trans h2

-- ===== from LNBig.lean =====

variable {d : ℕ}

/-- The chart `y ↦ z + 3^m y`. -/
def aux_lem_local_normalizations_Tbig (m : ℕ) (z : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨cubeDilation z 0 ((3 : ℝ) ^ (m : ℤ)), continuous_cubeDilation z 0 ((3 : ℝ) ^ (m : ℤ))⟩

/-- The zoom-out `Θ'_{m,z}`. -/
def aux_lem_local_normalizations_Thetabig (m : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j : ℤ => (omega (j + (m : ℤ))).comp (aux_lem_local_normalizations_Tbig m z)

/-- The random constant of the zoom-out. -/
def aux_lem_local_normalizations_Cbig (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℕ) (omega : BilateralField d) (z : SpatialCoordinates d) : ℝ :=
  H omega z - ∑ l ∈ Finset.range m, omega ((l : ℤ) + 1) z

theorem aux_lem_local_normalizations_Tbig_zero (m : ℕ) (z : SpatialCoordinates d) :
    aux_lem_local_normalizations_Tbig m z 0 = z := by
  funext i; simp [aux_lem_local_normalizations_Tbig, cubeDilation]

theorem aux_lem_local_normalizations_Thetabig_apply (m : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) (j : ℤ) (y : SpatialCoordinates d) :
    aux_lem_local_normalizations_Thetabig m z omega j y =
      omega (j + (m : ℤ)) (aux_lem_local_normalizations_Tbig m z y) := rfl

theorem aux_lem_local_normalizations_Thetabig_eq_zoom (m : ℕ) (z : SpatialCoordinates d) :
    aux_lem_local_normalizations_Thetabig (d := d) m z =
      aux_lem_extension_cell_moment_zoom (-(m : ℤ)) z := by
  funext omega j
  ext x
  rw [aux_lem_extension_cell_moment_zoom_apply]
  simp only [aux_lem_local_normalizations_Thetabig, aux_lem_local_normalizations_Tbig,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, sub_neg_eq_add, neg_neg]
  congr 1
  funext i
  simp [cubeDilation, Pi.smul_apply, smul_eq_mul, add_comm]

theorem aux_lem_local_normalizations_Thetabig_measurePreserving
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_lem_local_normalizations_Thetabig m z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  rw [aux_lem_local_normalizations_Thetabig_eq_zoom]
  exact aux_lem_extension_cell_moment_zoom_measurePreserving M (-(m : ℤ)) z

/-- Real-sum identity behind the zoom-out partial sums. -/
theorem aux_lem_local_normalizations_sum_shift (a b c : ℕ → ℝ) (m L : ℕ) :
    ∑ n ∈ Finset.range L, (a (m + n) - b (m + n)) =
      ((∑ n ∈ Finset.range (m + L), (a n - c n)) -
          (∑ n ∈ Finset.range (m + L), (b n - c n))) -
        ((∑ n ∈ Finset.range m, (a n - c n)) - (∑ n ∈ Finset.range m, (b n - c n))) := by
  rw [Finset.sum_range_add (fun n => a n - c n) m L,
    Finset.sum_range_add (fun n => b n - c n) m L]
  have : ∑ n ∈ Finset.range L, (a (m + n) - b (m + n)) =
      ∑ n ∈ Finset.range L, (a (m + n) - c (m + n)) -
        ∑ n ∈ Finset.range L, (b (m + n) - c (m + n)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [this]
  ring

/-- Partial sums of the zoomed-out field. -/
theorem aux_lem_local_normalizations_partialSum_Thetabig (m : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) (L : ℕ) :
    infraredPartialSum (aux_lem_local_normalizations_Thetabig m z omega) L =
      ((infraredPartialSum omega (m + L)).comp (aux_lem_local_normalizations_Tbig m z) -
          ContinuousMap.const _ ((infraredPartialSum omega (m + L)) z)) -
        ((infraredPartialSum omega m).comp (aux_lem_local_normalizations_Tbig m z) -
          ContinuousMap.const _ ((infraredPartialSum omega m) z)) := by
  have hT0 := aux_lem_local_normalizations_Tbig_zero (d := d) m z
  ext x
  simp only [infraredPartialSum, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    aux_lem_local_normalizations_Thetabig_apply, hT0]
  have key := aux_lem_local_normalizations_sum_shift
    (fun n => omega (Int.ofNat (n + 1)) (aux_lem_local_normalizations_Tbig m z x))
    (fun n => omega (Int.ofNat (n + 1)) z) (fun n => omega (Int.ofNat (n + 1)) 0) m L
  rw [← key]
  apply Finset.sum_congr rfl
  intro n _
  have hidx : Int.ofNat (n + 1) + (m : ℤ) = Int.ofNat (m + n + 1) := by
    simp only [Int.ofNat_eq_natCast]; push_cast; ring
  rw [hidx]

/-- **Infrared identity for the zoom-out.** -/
theorem aux_lem_local_normalizations_H_Thetabig
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H) (m : ℕ) (z : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      H (aux_lem_local_normalizations_Thetabig m z omega) =
        ((H omega).comp (aux_lem_local_normalizations_Tbig m z) -
            ContinuousMap.const _ (H omega z)) -
          ((infraredPartialSum omega m).comp (aux_lem_local_normalizations_Tbig m z) -
            ContinuousMap.const _ ((infraredPartialSum omega m) z)) := by
  have hMP := aux_lem_local_normalizations_Thetabig_measurePreserving M m z
  have hpull := hMP.quasiMeasurePreserving.ae HI.2
  filter_upwards [HI.2, hpull] with omega hom hTom
  set T := aux_lem_local_normalizations_Tbig (d := d) m z
  set F : C(SpatialCoordinates d, ℝ) := infraredPartialSum omega m
  have hcont : Continuous (fun G : C(SpatialCoordinates d, ℝ) =>
      (G.comp T - ContinuousMap.const _ (G z)) - (F.comp T - ContinuousMap.const _ (F z))) := by
    refine Continuous.sub ?_ continuous_const
    exact (ContinuousMap.compRightContinuousMap ℝ T).continuous.sub
      (ContinuousMap.const'.continuous.comp (continuous_eval_const z))
  have hshift : Tendsto (fun L => infraredPartialSum omega (m + L)) atTop (𝓝 (H omega)) := by
    have := (tendsto_add_atTop_iff_nat m).2 hom
    simpa only [add_comm] using this
  have hlim : Tendsto
      (fun L => infraredPartialSum (aux_lem_local_normalizations_Thetabig m z omega) L)
      atTop (𝓝 (((H omega).comp T - ContinuousMap.const _ (H omega z)) -
        (F.comp T - ContinuousMap.const _ (F z)))) := by
    have h := (hcont.tendsto (H omega)).comp hshift
    refine h.congr' (Eventually.of_forall fun L => ?_)
    simp only [Function.comp_apply]
    rw [aux_lem_local_normalizations_partialSum_Thetabig]
  exact tendsto_nhds_unique hTom hlim

/-- The cutoff potential under the zoom-out. -/
theorem aux_lem_local_normalizations_pot_identity_big
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (m : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hH : H (aux_lem_local_normalizations_Thetabig m z omega) =
        ((H omega).comp (aux_lem_local_normalizations_Tbig m z) -
            ContinuousMap.const _ (H omega z)) -
          ((infraredPartialSum omega m).comp (aux_lem_local_normalizations_Tbig m z) -
            ContinuousMap.const _ ((infraredPartialSum omega m) z)))
    (N : ℕ) (y : SpatialCoordinates d) :
    cutoffPotential H omega N (aux_lem_local_normalizations_Tbig m z y) =
      cutoffPotential H (aux_lem_local_normalizations_Thetabig m z omega) (N + m) y +
        aux_lem_local_normalizations_Cbig H m omega z := by
  set T := aux_lem_local_normalizations_Tbig (d := d) m z
  unfold cutoffPotential aux_lem_local_normalizations_Cbig
  rw [hH]
  simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply,
    ContinuousMap.const_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    aux_lem_local_normalizations_Thetabig_apply, infraredPartialSum]
  have hsplit : N + m + 1 = m + (N + 1) := by omega
  rw [hsplit, Finset.sum_range_add (fun j => omega (-Int.ofNat j + (m : ℤ)) (T y)) m (N + 1)]
  have h1 : ∑ x ∈ Finset.range m, omega (-Int.ofNat x + (m : ℤ)) (T y) =
      ∑ l ∈ Finset.range m, omega (Int.ofNat (l + 1)) (T y) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    congr 2
    simp only [Int.ofNat_eq_natCast]
    omega
  have h2 : ∑ x ∈ Finset.range (N + 1), omega (-Int.ofNat (m + x) + (m : ℤ)) (T y) =
      ∑ x ∈ Finset.range (N + 1), omega (-Int.ofNat x) (T y) :=
    Finset.sum_congr rfl (fun j _ => by
      congr 2; simp only [Int.ofNat_eq_natCast]; push_cast; ring)
  have h3 : ∑ l ∈ Finset.range m, omega ((l : ℤ) + 1) z =
      ∑ l ∈ Finset.range m, omega (Int.ofNat (l + 1)) z :=
    Finset.sum_congr rfl (fun l _ => by
      congr 2)
  rw [h1, h2, h3]
  simp only [Finset.sum_sub_distrib]
  ring

/-- Pointwise coefficient identity for the zoom-out. -/
theorem aux_lem_local_normalizations_coef_identity_big
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (m : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hH : H (aux_lem_local_normalizations_Thetabig m z omega) =
        ((H omega).comp (aux_lem_local_normalizations_Tbig m z) -
            ContinuousMap.const _ (H omega z)) -
          ((infraredPartialSum omega m).comp (aux_lem_local_normalizations_Tbig m z) -
            ContinuousMap.const _ ((infraredPartialSum omega m) z)))
    (N : ℕ) (y : SpatialCoordinates d) :
    cutoffCoefficient M H omega N (aux_lem_local_normalizations_Tbig m z y) =
      (aux_lem_local_normalizations_kap M (N + m) / aux_lem_local_normalizations_kap M N *
          Real.exp (aux_lem_local_normalizations_Cbig H m omega z)) *
        cutoffCoefficient M H (aux_lem_local_normalizations_Thetabig m z omega) (N + m) y := by
  have hpot := aux_lem_local_normalizations_pot_identity_big H m z omega hH N y
  unfold cutoffCoefficient aux_lem_local_normalizations_kap
  rw [hpot]
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hB := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + m)
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = _root_.SubdiffusiveProcess.Model.tauSq M.P := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P =
      cutoffPotential H (aux_lem_local_normalizations_Thetabig m z omega) (N + m) y :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = aux_lem_local_normalizations_Cbig H m omega z := ⟨_, rfl⟩
  rw [← hτ, ← hP, ← hG]
  push_cast
  have e1 : Real.exp (P + G - ((N : ℝ) + 1) * τ) =
      Real.exp (((N : ℝ) + m + 1) * τ) * Real.exp G *
        Real.exp (P - ((N : ℝ) + m + 1) * τ) / Real.exp (((N : ℝ) + 1) * τ) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [e1]
  field_simp

theorem aux_lem_local_normalizations_rscale_big_rpow (d m : ℕ) :
    ((3 : ℝ) ^ (m : ℤ)) ^ ((d : ℝ) - 2) = (3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) := by
  rw [show ((3 : ℝ) ^ (m : ℤ)) = (3 : ℝ) ^ (m : ℝ) by
    rw [← Real.rpow_intCast]; push_cast; rfl]
  rw [← Real.rpow_mul (by norm_num)]
  congr 1; ring

/-- **Finite-cutoff scaling on large triadic cubes.** -/
theorem aux_lem_local_normalizations_finite_scaling_big
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H) (m : ℕ) (z : SpatialCoordinates d)
    (hrm : 0 < (3 : ℝ) ^ (m : ℤ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ g : SpatialCoordinates d → ℝ,
        sInf (aux_lem_local_normalizations_Lset z ((3 : ℝ) ^ (m : ℤ)) hrm
            (cutoffPositiveCoefficient M H omega N z hrm) g) =
          (3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) *
            (aux_lem_local_normalizations_kap M (N + m) /
              aux_lem_local_normalizations_kap M N) *
            Real.exp (aux_lem_local_normalizations_Cbig H m omega z) *
            sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
              (cutoffPositiveCoefficient M H (aux_lem_local_normalizations_Thetabig m z omega)
                (N + m) 0 one_pos)
              (g ∘ aux_lem_local_normalizations_Tbig m z)) := by
  filter_upwards [aux_lem_local_normalizations_H_Thetabig M H HI m z] with omega hH
  intro N g
  set c := aux_lem_local_normalizations_kap M (N + m) / aux_lem_local_normalizations_kap M N *
    Real.exp (aux_lem_local_normalizations_Cbig H m omega z) with hc_def
  have hc : 0 < c := mul_pos (div_pos (aux_lem_local_normalizations_kap_pos M _)
    (aux_lem_local_normalizations_kap_pos M _)) (Real.exp_pos _)
  have hab : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hrm).val
          (cubeDilation z 0 ((3 : ℝ) ^ (m : ℤ)) y) =
        c * (cutoffPositiveCoefficient M H (aux_lem_local_normalizations_Thetabig m z omega)
          (N + m) 0 one_pos).val y := by
    have hA := (aux_lem_local_normalizations_ae_iff z hrm _).1
      (aux_lem_local_normalizations_cutoff_coeFn M H omega N z hrm)
    filter_upwards [hA, aux_lem_local_normalizations_cutoff_coeFn M H
      (aux_lem_local_normalizations_Thetabig m z omega) (N + m) 0 one_pos] with y h1 h2
    rw [h1, h2]
    exact aux_lem_local_normalizations_coef_identity_big M H m z omega hH N y
  have h := aux_lem_local_normalizations_sInf_dilation z _ hrm _ _ c hc hab g
  rw [h, aux_lem_local_normalizations_rscale_big_rpow, hc_def]
  have hT : (g ∘ cubeDilation z 0 ((3 : ℝ) ^ (m : ℤ))) =
      g ∘ aux_lem_local_normalizations_Tbig m z := rfl
  rw [hT]
  ring

-- ===== from LNMeas.lean =====

variable {d : ℕ}

/-- Measurability of the actual response in the environment (reproved from the proof
body of `lem_local_normalizations_full_cutoff`). -/
theorem aux_lem_local_normalizations_Lam_aesm
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (μ : Measure (BilateralField d)) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (g : SpatialCoordinates d → ℝ) :
    AEStronglyMeasurable (fun om => sInf (aux_lem_local_normalizations_Lset z r hr
      (cutoffPositiveCoefficient M H om N z hr) g)) μ := by
  let : MeasureTheory.IsSeparable
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := inferInstance
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let : SecondCountableTopology (DomainL2 (centeredCube z r hr)) := inferInstance
  let : SecondCountableTopology (Fin d → DomainL2 (centeredCube z r hr)) := inferInstance
  let : SecondCountableTopology (SobolevData (centeredCube z r hr)) := inferInstance
  let A : Set (weakSobolevGraph (centeredCube z r hr)) :=
    {u | ∃ (U : SpatialCoordinates d → ℝ),
      ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
      ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = g x)}
  let f : weakSobolevGraph (centeredCube z r hr) → BilateralField d → ℝ :=
    fun u om => sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr) u.val u.val
  have hfcont : ∀ om, Continuous (fun u => f u om) := by
    intro om
    fun_prop
  have hfbdd : ∀ om, BddBelow ((fun u => f u om) '' A) := by
    intro om
    refine ⟨0, ?_⟩
    rintro e ⟨u, hu, rfl⟩
    exact sobolevCoefficientForm_nonneg (cutoffPositiveCoefficient M H om N z hr) u.val
  have hfmeas : ∀ u, u ∈ A → AEStronglyMeasurable (f u) μ := by
    intro u _
    exact aux_lem_local_normalizations_full_cutoff_energy_meas M H hH μ N z hr u
  have hfinf := aux_lem_local_normalizations_full_cutoff_sInf_meas μ A f hfcont hfbdd hfmeas
  have hEq : (fun om => sInf (aux_lem_local_normalizations_Lset z r hr
      (cutoffPositiveCoefficient M H om N z hr) g)) =
      (fun om => sInf ((fun u => f u om) '' A)) := by
    funext om
    congr 1
    ext e
    constructor
    · rintro ⟨u, U, hU, hAE, hbd, rfl⟩
      exact ⟨u, ⟨U, hU, hAE, hbd⟩, rfl⟩
    · rintro ⟨u, ⟨U, hU, hAE, hbd⟩, rfl⟩
      exact ⟨u, U, hU, hAE, hbd, rfl⟩
  rw [hEq]
  exact hfinf

/-- Convergence in probability is preserved by a measure-preserving change of environment. -/
theorem aux_lem_local_normalizations_tim_comp_mp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (Θ : Ω → Ω) (hΘ : MeasurePreserving Θ μ μ)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (h : TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ (fun N om => f N (Θ om)) atTop (fun om => g (Θ om)) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun N => zero_le) (fun N => ?_)
  set A := {x | ε ≤ edist (f N x) (g x)}
  calc μ {x | ε ≤ edist (f N (Θ x)) (g (Θ x))} = μ (Θ ⁻¹' A) := rfl
    _ ≤ μ (Θ ⁻¹' toMeasurable μ A) := measure_mono (Set.preimage_mono (subset_toMeasurable μ A))
    _ = μ (toMeasurable μ A) := hΘ.measure_preimage (measurableSet_toMeasurable μ A).nullMeasurableSet
    _ = μ A := measure_toMeasurable A

/-- Convergence in probability under deterministic rescaling and a fixed random factor. -/
theorem aux_lem_local_normalizations_tim_scale {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Yl : Ω → ℝ) (hY : TendstoInMeasure μ Y atTop Yl)
    (hYm : ∀ N, AEStronglyMeasurable (Y N) μ)
    (c : ℕ → ℝ) (cinf : ℝ) (hc : Tendsto c atTop (𝓝 cinf))
    (F : Ω → ℝ) (hF : AEStronglyMeasurable F μ) :
    TendstoInMeasure μ (fun N om => c N * F om * Y N om) atTop
      (fun om => cinf * F om * Yl om) := by
  have hm : ∀ N, AEStronglyMeasurable (fun om => c N * F om * Y N om) μ := fun N =>
    (aestronglyMeasurable_const.mul hF).mul (hYm N)
  rw [exists_seq_tendstoInMeasure_atTop_iff hm]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (hY.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with om hom
  have hcn : Tendsto (fun i => c (ns (ns' i))) atTop (𝓝 cinf) :=
    hc.comp (hns.tendsto_atTop.comp hns'.tendsto_atTop)
  exact (hcn.mul tendsto_const_nhds).mul hom

-- ===== from LNAsm1.lean =====

variable {d : ℕ}

/-- The actual finite-cutoff response. -/
def aux_lem_local_normalizations_Lam
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) (omega : BilateralField d)
    (g : SpatialCoordinates d → ℝ) : ℝ :=
  sInf (aux_lem_local_normalizations_Lset z r hr (cutoffPositiveCoefficient M H omega N z hr) g)

theorem aux_lem_local_normalizations_Lam_eq_response
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x)
    (ha : a = cutoffPositiveCoefficient M H omega N z hr) :
    aux_lem_local_normalizations_Lam M H z r hr N omega g =
      dirichletResponse (killedResponseSpace hP) a b := by
  unfold aux_lem_local_normalizations_Lam
  exact le_antisymm
    (by simpa [ha] using
      (aux_lem_local_normalizations_sInf_le_response z r hr hP a b g G hGc hb hGg))
    (by simpa [ha] using
      (aux_lem_local_normalizations_response_le_sInf hd z r hr hP a b g G hGc hb hGg))

/-- Constants have zero energy against every datum. -/
theorem aux_lem_local_normalizations_form_const (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (v : SobolevData (centeredCube z r hr)) (c : ℝ) :
    sobolevCoefficientForm a v (affineSobolevData (centeredCube_isBounded z hr) 0 c) = 0 := by
  rw [sobolevCoefficientForm_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      a.val x * (v.2 i x * (affineSobolevData (centeredCube_isBounded z hr) 0 c).2 i x) = 0 := by
    filter_upwards [domainConstantL2_coeFn (Ω := centeredCube z r hr) ((0 : Fin d → ℝ) i)]
      with x hx
    change a.val x * (v.2 i x * (domainConstantL2 (Ω := centeredCube z r hr)
      ((0 : Fin d → ℝ) i)) x) = 0
    rw [hx]; simp
  rw [integral_congr_ae h, integral_zero]

theorem aux_lem_local_normalizations_Lset_shift_mem (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) (c : ℝ) (e : ℝ)
    (he : e ∈ aux_lem_local_normalizations_Lset z r hr a g) :
    e ∈ aux_lem_local_normalizations_Lset z r hr a (fun x => g x + c) := by
  obtain ⟨u, U, hUc, huU, hUb, rfl⟩ := he
  let k := affineSobolev (centeredCube_isBounded z hr) 0 c
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val + k.val, (weakSobolevGraph (centeredCube z r hr)).add_mem u.property k.property⟩
  refine ⟨v, fun x => U x + c, hUc.add continuousOn_const, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add u.val.1 k.val.1, huU,
      affineL2_coeFn (centeredCube_isBounded z hr) 0 c] with x h0 h1 h2
    change ((u.val.1 + k.val.1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = _
    rw [h0, Pi.add_apply, h1]
    change U x + (affineL2 (centeredCube_isBounded z hr) 0 c : SpatialCoordinates d → ℝ) x = _
    rw [h2, affineSlope_apply]; simp
  · intro x hx; simp [hUb x hx]
  · change sobolevCoefficientForm a u.val u.val =
      sobolevCoefficientForm a (u.val + k.val) (u.val + k.val)
    simp only [map_add, add_apply]
    rw [sobolevCoefficientForm_symm a k.val u.val]
    have h1 := aux_lem_local_normalizations_form_const z r hr a u.val c
    have h2 := aux_lem_local_normalizations_form_const z r hr a k.val c
    change sobolevCoefficientForm a u.val (affineSobolevData _ 0 c) = 0 at h1
    change sobolevCoefficientForm a k.val (affineSobolevData _ 0 c) = 0 at h2
    change _ = _ + sobolevCoefficientForm a u.val (affineSobolevData _ 0 c) +
      (sobolevCoefficientForm a u.val (affineSobolevData _ 0 c) +
        sobolevCoefficientForm a k.val (affineSobolevData _ 0 c))
    rw [h1, h2]; ring

/-- **Constants are invisible** to the actual response. -/
theorem aux_lem_local_normalizations_sInf_shift (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) (c : ℝ) :
    sInf (aux_lem_local_normalizations_Lset z r hr a (fun x => g x + c)) =
      sInf (aux_lem_local_normalizations_Lset z r hr a g) := by
  congr 1
  ext e
  constructor
  · intro he
    have := aux_lem_local_normalizations_Lset_shift_mem z r hr a _ (-c) e he
    simpa using this
  · exact aux_lem_local_normalizations_Lset_shift_mem z r hr a g c e

/-! ### Triadic scales -/

theorem aux_lem_local_normalizations_triadic_cases (r : ℝ) (h : ∃ j : ℤ, r = (3 : ℝ) ^ j) :
    (∃ k : ℕ, r = (3 : ℝ) ^ (-(k : ℤ))) ∨ (∃ m : ℕ, 1 ≤ m ∧ r = (3 : ℝ) ^ (m : ℤ)) := by
  obtain ⟨j, rfl⟩ := h
  rcases le_or_gt j 0 with hj | hj
  · left
    refine ⟨j.natAbs, ?_⟩
    congr 1
    omega
  · right
    refine ⟨j.natAbs, by omega, ?_⟩
    congr 1
    omega

theorem aux_lem_local_normalizations_zpow_inj {k k' : ℤ}
    (h : (3 : ℝ) ^ k = (3 : ℝ) ^ k') : k = k' :=
  zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) h

/-! ### The transported limiting seminorm -/

/-- The small-cube seminorm transported from the unit cube. -/
def aux_lem_local_normalizations_RLsmall
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ) (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    Seminorm ℝ (SpatialCoordinates d → ℝ) :=
  (Real.toNNReal (Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
      Real.exp (aux_lem_local_normalizations_Gc H k omega z)))) •
    (RL0 (aux_lem_local_normalizations_Theta k z omega)).comp
      (LinearMap.funLeft ℝ ℝ (aux_lem_local_normalizations_T k z))

/-- The large-cube seminorm transported from the unit cube. -/
def aux_lem_local_normalizations_RLbig
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ) (m : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    Seminorm ℝ (SpatialCoordinates d → ℝ) :=
  (Real.toNNReal (Real.sqrt ((3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) / e m *
      Real.exp (aux_lem_local_normalizations_Cbig H m omega z)))) •
    (RL0 (aux_lem_local_normalizations_Thetabig m z omega)).comp
      (LinearMap.funLeft ℝ ℝ (aux_lem_local_normalizations_Tbig m z))

/-- **The limiting response seminorm** on every cube (zero off triadic sides). -/
def aux_lem_local_normalizations_RL
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ)
    (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r) (omega : BilateralField d) :
    Seminorm ℝ (SpatialCoordinates d → ℝ) := by
  classical
  exact if h : ∃ k : ℕ, r = (3 : ℝ) ^ (-(k : ℤ)) then
      aux_lem_local_normalizations_RLsmall RL0 H e (Nat.find h) z omega
    else if h' : ∃ m : ℕ, r = (3 : ℝ) ^ (m : ℤ) then
      aux_lem_local_normalizations_RLbig RL0 H e (Nat.find h') z omega
    else 0

theorem aux_lem_local_normalizations_RL_small
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ)
    (z : SpatialCoordinates d) (k : ℕ) (hr : 0 < (3 : ℝ) ^ (-(k : ℤ)))
    (omega : BilateralField d) :
    aux_lem_local_normalizations_RL RL0 H e z ((3 : ℝ) ^ (-(k : ℤ))) hr omega =
      aux_lem_local_normalizations_RLsmall RL0 H e k z omega := by
  classical
  have h : ∃ k' : ℕ, (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ (-(k' : ℤ)) := ⟨k, rfl⟩
  have hfind : Nat.find h = k := by
    have hs := Nat.find_spec h
    have := aux_lem_local_normalizations_zpow_inj hs
    omega
  simp only [aux_lem_local_normalizations_RL, dite_eq_left h, hfind]

theorem aux_lem_local_normalizations_RL_big
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ)
    (z : SpatialCoordinates d) (m : ℕ) (hm : 1 ≤ m) (hr : 0 < (3 : ℝ) ^ (m : ℤ))
    (omega : BilateralField d) :
    aux_lem_local_normalizations_RL RL0 H e z ((3 : ℝ) ^ (m : ℤ)) hr omega =
      aux_lem_local_normalizations_RLbig RL0 H e m z omega := by
  classical
  have hn : ¬ ∃ k : ℕ, (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ (-(k : ℤ)) := by
    rintro ⟨k, hk⟩
    have := aux_lem_local_normalizations_zpow_inj hk
    omega
  have h : ∃ m' : ℕ, (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ (m' : ℤ) := ⟨m, rfl⟩
  have hfind : Nat.find h = m := by
    have hs := Nat.find_spec h
    have := aux_lem_local_normalizations_zpow_inj hs
    omega
  simp only [aux_lem_local_normalizations_RL, dite_eq_right hn, dite_eq_left h, hfind]

theorem aux_lem_local_normalizations_RLsmall_sq
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ) (k : ℕ) (hek : 0 < e k)
    (z : SpatialCoordinates d) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) :
    (aux_lem_local_normalizations_RLsmall RL0 H e k z omega g) ^ 2 =
      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
        Real.exp (aux_lem_local_normalizations_Gc H k omega z) *
        (RL0 (aux_lem_local_normalizations_Theta k z omega)
          (g ∘ aux_lem_local_normalizations_T k z)) ^ 2 := by
  have hA : 0 ≤ (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
      Real.exp (aux_lem_local_normalizations_Gc H k omega z) := by positivity
  simp only [aux_lem_local_normalizations_RLsmall, smul_apply, Seminorm.comp_apply,
    NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt hA]
  rfl

theorem aux_lem_local_normalizations_RLbig_sq
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ) (m : ℕ) (hem : 0 < e m)
    (z : SpatialCoordinates d) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) :
    (aux_lem_local_normalizations_RLbig RL0 H e m z omega g) ^ 2 =
      (3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) / e m *
        Real.exp (aux_lem_local_normalizations_Cbig H m omega z) *
        (RL0 (aux_lem_local_normalizations_Thetabig m z omega)
          (g ∘ aux_lem_local_normalizations_Tbig m z)) ^ 2 := by
  have hA : 0 ≤ (3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) / e m *
      Real.exp (aux_lem_local_normalizations_Cbig H m omega z) := by positivity
  simp only [aux_lem_local_normalizations_RLbig, smul_apply, Seminorm.comp_apply,
    NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  rw [mul_pow, Real.sq_sqrt hA]
  rfl

-- ===== from LNAsm2.lean =====

variable {d : ℕ}

theorem aux_lem_local_normalizations_rescaled_transfer (z : SpatialCoordinates d) (r : ℝ)
    (g : SpatialCoordinates d → ℝ) :
    rescaledDatum (0 : SpatialCoordinates d) 1 (g ∘ cubeDilation z 0 r) = rescaledDatum z r g := by
  funext y
  simp only [rescaledDatum, Function.comp_apply]
  congr 1
  funext i
  simp [cubeDilation]

theorem aux_lem_local_normalizations_class_transfer (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) :
    IsCellBoundaryClass beta 0 1 (g ∘ cubeDilation z 0 r) ↔ IsCellBoundaryClass beta z r g := by
  unfold IsCellBoundaryClass
  rw [aux_lem_local_normalizations_rescaled_transfer]

theorem aux_lem_local_normalizations_norm_transfer (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) :
    cellBoundaryQuotientNorm beta 0 1 (g ∘ cubeDilation z 0 r) =
      cellBoundaryQuotientNorm beta z r g := by
  unfold cellBoundaryQuotientNorm
  rw [aux_lem_local_normalizations_rescaled_transfer]

theorem aux_lem_local_normalizations_Gc_meas
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (k : ℕ)
    (z : SpatialCoordinates d) :
    Measurable (fun om => aux_lem_local_normalizations_Gc H k om z) := by
  have heq : (fun om => aux_lem_local_normalizations_Gc H k om z) =
      fun om => H om z + ∑ j ∈ Finset.range k, om (-(j : ℤ)) z := by
    funext om
    simp [aux_lem_local_normalizations_Gc]
  rw [heq]
  refine ((continuous_eval_const z).measurable.comp hH).add ?_
  exact Finset.measurable_sum _ fun j _ =>
    (continuous_eval_const z).measurable.comp (measurable_pi_apply _)

theorem aux_lem_local_normalizations_Cbig_meas
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (m : ℕ)
    (z : SpatialCoordinates d) :
    Measurable (fun om => aux_lem_local_normalizations_Cbig H m om z) := by
  unfold aux_lem_local_normalizations_Cbig
  refine ((continuous_eval_const z).measurable.comp hH).sub ?_
  exact Finset.measurable_sum _ fun j _ =>
    (continuous_eval_const z).measurable.comp (measurable_pi_apply _)

section clause2

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **Clause 2 on small triadic cubes.** -/
theorem aux_lem_local_normalizations_conv_small
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (beta : ℝ) (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (e : ℕ → ℝ)
    (he : ∀ k, 0 < e k ∧ Tendsto (fun N => aux_lem_local_normalizations_kap M (N - k) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 (e k)))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-(k : ℤ)))
    (g : SpatialCoordinates d → ℝ) (hg : IsCellBoundaryClass beta z ((3 : ℝ) ^ (-(k : ℤ))) g) :
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N om => aux_lem_local_normalizations_Lam M H z ((3 : ℝ) ^ (-(k : ℤ))) hr N om g)
      atTop (fun om => (aux_lem_local_normalizations_RLsmall RL0 H e k z om g) ^ 2) := by
  set μ := (chaosSampleLaw M).toMeasure
  set T := aux_lem_local_normalizations_T (d := d) k z
  set Θ := aux_lem_local_normalizations_Theta (d := d) k z
  have hMP : MeasurePreserving Θ μ μ := aux_lem_local_normalizations_Theta_measurePreserving M k z
  have hgT : IsCellBoundaryClass beta 0 1 (g ∘ T) :=
    (aux_lem_local_normalizations_class_transfer beta z _ g).2 hg
  have hY : TendstoInMeasure μ
      (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos (N - k) (Θ om) (g ∘ T))
      atTop (fun om => (RL0 (Θ om) (g ∘ T)) ^ 2) :=
    (aux_lem_local_normalizations_tim_comp_mp μ Θ hMP _ _ (hRL0conv _ hgT)).comp
      (tendsto_sub_atTop_nat k)
  have hYm : ∀ N, AEStronglyMeasurable
      (fun om => aux_lem_local_normalizations_Lam M H 0 1 one_pos (N - k) (Θ om) (g ∘ T)) μ :=
    fun N => (aux_lem_local_normalizations_Lam_aesm M H HI.1 μ (N - k) 0 1 one_pos
      (g ∘ T)).comp_measurePreserving hMP
  have hF : AEStronglyMeasurable (fun om => (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
      Real.exp (aux_lem_local_normalizations_Gc H k om z)) μ :=
    (measurable_const.mul (Real.measurable_exp.comp
      (aux_lem_local_normalizations_Gc_meas H HI.1 k z))).aestronglyMeasurable
  have hsc := aux_lem_local_normalizations_tim_scale μ _ _ hY hYm _ (e k) (he k).2 _ hF
  refine hsc.congr' ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop k] with N hN
    filter_upwards [aux_lem_local_normalizations_finite_scaling M H HI k z hr] with om hom
    have h := hom N hN g
    change _ = aux_lem_local_normalizations_Lam M H z ((3 : ℝ) ^ (-(k : ℤ))) hr N om g
    unfold aux_lem_local_normalizations_Lam
    rw [h]
    ring
  · exact ae_of_all _ fun om => by
      dsimp only
      rw [aux_lem_local_normalizations_RLsmall_sq RL0 H e k (he k).1]
      ring

/-- **Clause 2 on large triadic cubes.** -/
theorem aux_lem_local_normalizations_conv_big
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (beta : ℝ) (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (e : ℕ → ℝ)
    (he : ∀ k, 0 < e k ∧ Tendsto (fun N => aux_lem_local_normalizations_kap M (N - k) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 (e k)))
    (m : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (m : ℤ))
    (g : SpatialCoordinates d → ℝ) (hg : IsCellBoundaryClass beta z ((3 : ℝ) ^ (m : ℤ)) g) :
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N om => aux_lem_local_normalizations_Lam M H z ((3 : ℝ) ^ (m : ℤ)) hr N om g)
      atTop (fun om => (aux_lem_local_normalizations_RLbig RL0 H e m z om g) ^ 2) := by
  set μ := (chaosSampleLaw M).toMeasure
  set T := aux_lem_local_normalizations_Tbig (d := d) m z
  set Θ := aux_lem_local_normalizations_Thetabig (d := d) m z
  have hMP : MeasurePreserving Θ μ μ :=
    aux_lem_local_normalizations_Thetabig_measurePreserving M m z
  have hgT : IsCellBoundaryClass beta 0 1 (g ∘ T) :=
    (aux_lem_local_normalizations_class_transfer beta z _ g).2 hg
  have hY : TendstoInMeasure μ
      (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos (N + m) (Θ om) (g ∘ T))
      atTop (fun om => (RL0 (Θ om) (g ∘ T)) ^ 2) :=
    (aux_lem_local_normalizations_tim_comp_mp μ Θ hMP _ _ (hRL0conv _ hgT)).comp
      (tendsto_add_atTop_nat m)
  have hYm : ∀ N, AEStronglyMeasurable
      (fun om => aux_lem_local_normalizations_Lam M H 0 1 one_pos (N + m) (Θ om) (g ∘ T)) μ :=
    fun N => (aux_lem_local_normalizations_Lam_aesm M H HI.1 μ (N + m) 0 1 one_pos
      (g ∘ T)).comp_measurePreserving hMP
  have hF : AEStronglyMeasurable (fun om => (3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) *
      Real.exp (aux_lem_local_normalizations_Cbig H m om z)) μ :=
    (measurable_const.mul (Real.measurable_exp.comp
      (aux_lem_local_normalizations_Cbig_meas H HI.1 m z))).aestronglyMeasurable
  -- the deterministic ratio `κ_{N+m}/κ_N → 1/e(m)`
  have hcm : Tendsto (fun N => aux_lem_local_normalizations_kap M (N + m) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 (e m)⁻¹) := by
    have h1 := ((he m).2.comp (tendsto_add_atTop_nat m)).inv₀ (he m).1.ne'
    refine h1.congr' (Eventually.of_forall fun N => ?_)
    simp only [Function.comp_apply, Nat.add_sub_cancel, inv_div]
  have hsc := aux_lem_local_normalizations_tim_scale μ _ _ hY hYm _ _ hcm _ hF
  refine hsc.congr' ?_ ?_
  · refine Eventually.of_forall fun N => ?_
    filter_upwards [aux_lem_local_normalizations_finite_scaling_big M H HI m z hr] with om hom
    have h := hom N g
    change _ = aux_lem_local_normalizations_Lam M H z ((3 : ℝ) ^ (m : ℤ)) hr N om g
    unfold aux_lem_local_normalizations_Lam
    rw [h]
    ring
  · exact ae_of_all _ fun om => by
      dsimp only
      rw [aux_lem_local_normalizations_RLbig_sq RL0 H e m (he m).1]
      simp only [div_eq_mul_inv]
      ring

end clause2

-- ===== from LNAsm3.lean =====

variable {d : ℕ}

/-- The affine datum of slope `p`. -/
def aux_lem_local_normalizations_aff (p : Fin d → ℝ) : SpatialCoordinates d → ℝ :=
  fun x => ∑ i : Fin d, p i * x i

theorem aux_lem_local_normalizations_aff_smooth (p : Fin d → ℝ) :
    ContDiff ℝ ∞ (aux_lem_local_normalizations_aff p) := by
  unfold aux_lem_local_normalizations_aff
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (contDiff_apply ℝ ℝ i)

theorem aux_lem_local_normalizations_aff_comp (p : Fin d → ℝ) (z : SpatialCoordinates d)
    (r : ℝ) :
    aux_lem_local_normalizations_aff p ∘ cubeDilation z 0 r =
      fun y => aux_lem_local_normalizations_aff (r • p) y + ∑ i : Fin d, p i * z i := by
  funext y
  simp only [aux_lem_local_normalizations_aff, Function.comp_apply, cubeDilation,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

section clauses

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
  (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
  (H : BilateralField d → C(SpatialCoordinates d, ℝ))
  (beta : ℝ) (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))

/-- Unit-cube positivity survives adding constants (constants are invisible). -/
theorem aux_lem_local_normalizations_unit_pos_shift (hbeta1 : beta ≤ 1)
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (hpos : ∀ p : Fin d → ℝ, p ≠ 0 → ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (aux_lem_local_normalizations_aff p)) ^ 2)
    (p : Fin d → ℝ) (hp : p ≠ 0) (c : ℝ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (fun y => aux_lem_local_normalizations_aff p y + c)) ^ 2 := by
  have h1 := hRL0conv (fun y => aux_lem_local_normalizations_aff p y + c)
    (aux_lem_local_normalizations_smooth_class beta hbeta1 0 1 _
      ((aux_lem_local_normalizations_aff_smooth p).add (contDiff_const (c := c))))
  have h2 := hRL0conv _ (aux_lem_local_normalizations_smooth_class beta hbeta1 0 1 _
    (aux_lem_local_normalizations_aff_smooth p))
  have h1' : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om
        (aux_lem_local_normalizations_aff p)) atTop
      (fun om => (RL0 om (fun y => aux_lem_local_normalizations_aff p y + c)) ^ 2) := by
    refine h1.congr (fun N => ae_of_all _ fun om => ?_) EventuallyEq.rfl
    exact aux_lem_local_normalizations_sInf_shift 0 1 one_pos _ _ c
  have huniq := tendstoInMeasure_ae_unique h1' h2
  filter_upwards [huniq, hpos p hp] with om h3 h4
  rw [h3]; exact h4

/-- **Clause 3 on small triadic cubes.** -/
theorem aux_lem_local_normalizations_bound_small
    (hRL0bd : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ g, IsCellBoundaryClass beta 0 1 g →
        (RL0 om g) ^ 2 ≤ K * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2)
    (e : ℕ → ℝ) (he : ∀ k, 0 < e k) (k : ℕ) (z : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ g, IsCellBoundaryClass beta z ((3 : ℝ) ^ (-(k : ℤ))) g →
        (aux_lem_local_normalizations_RLsmall RL0 H e k z om g) ^ 2 ≤
          K * (cellBoundaryQuotientNorm beta z ((3 : ℝ) ^ (-(k : ℤ))) g) ^ 2 := by
  have hMP := aux_lem_local_normalizations_Theta_measurePreserving M k z
  filter_upwards [hMP.quasiMeasurePreserving.ae hRL0bd] with om hom
  obtain ⟨K, hK, hKb⟩ := hom
  set A := (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
    Real.exp (aux_lem_local_normalizations_Gc H k om z)
  have hA : 0 < A := by have := he k; positivity
  refine ⟨A * K, mul_pos hA hK, fun g hg => ?_⟩
  rw [aux_lem_local_normalizations_RLsmall_sq RL0 H e k (he k)]
  have hgT := (aux_lem_local_normalizations_class_transfer beta z _ g).2 hg
  have h := hKb _ hgT
  rw [aux_lem_local_normalizations_norm_transfer] at h
  calc A * (RL0 (aux_lem_local_normalizations_Theta k z om)
        (g ∘ aux_lem_local_normalizations_T k z)) ^ 2
      ≤ A * (K * cellBoundaryQuotientNorm beta z ((3 : ℝ) ^ (-(k : ℤ))) g ^ 2) :=
        mul_le_mul_of_nonneg_left h hA.le
    _ = _ := by ring

/-- **Clause 3 on large triadic cubes.** -/
theorem aux_lem_local_normalizations_bound_big
    (hRL0bd : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ g, IsCellBoundaryClass beta 0 1 g →
        (RL0 om g) ^ 2 ≤ K * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2)
    (e : ℕ → ℝ) (he : ∀ k, 0 < e k) (m : ℕ) (z : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ g, IsCellBoundaryClass beta z ((3 : ℝ) ^ (m : ℤ)) g →
        (aux_lem_local_normalizations_RLbig RL0 H e m z om g) ^ 2 ≤
          K * (cellBoundaryQuotientNorm beta z ((3 : ℝ) ^ (m : ℤ)) g) ^ 2 := by
  have hMP := aux_lem_local_normalizations_Thetabig_measurePreserving M m z
  filter_upwards [hMP.quasiMeasurePreserving.ae hRL0bd] with om hom
  obtain ⟨K, hK, hKb⟩ := hom
  set A := (3 : ℝ) ^ (((d : ℝ) - 2) * (m : ℝ)) / e m *
    Real.exp (aux_lem_local_normalizations_Cbig H m om z)
  have hA : 0 < A := by have := he m; positivity
  refine ⟨A * K, mul_pos hA hK, fun g hg => ?_⟩
  rw [aux_lem_local_normalizations_RLbig_sq RL0 H e m (he m)]
  have hgT := (aux_lem_local_normalizations_class_transfer beta z _ g).2 hg
  have h := hKb _ hgT
  rw [aux_lem_local_normalizations_norm_transfer] at h
  calc A * (RL0 (aux_lem_local_normalizations_Thetabig m z om)
        (g ∘ aux_lem_local_normalizations_Tbig m z)) ^ 2
      ≤ A * (K * cellBoundaryQuotientNorm beta z ((3 : ℝ) ^ (m : ℤ)) g ^ 2) :=
        mul_le_mul_of_nonneg_left h hA.le
    _ = _ := by ring

/-- **Clause 4 on small triadic cubes.** -/
theorem aux_lem_local_normalizations_pos_small (hbeta1 : beta ≤ 1)
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (hpos : ∀ p : Fin d → ℝ, p ≠ 0 → ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (aux_lem_local_normalizations_aff p)) ^ 2)
    (e : ℕ → ℝ) (he : ∀ k, 0 < e k) (k : ℕ) (z : SpatialCoordinates d)
    (p : Fin d → ℝ) (hp : p ≠ 0) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (aux_lem_local_normalizations_RLsmall RL0 H e k z om
        (aux_lem_local_normalizations_aff p)) ^ 2 := by
  have hMP := aux_lem_local_normalizations_Theta_measurePreserving M k z
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hq : ((3 : ℝ) ^ (-(k : ℤ))) • p ≠ 0 := smul_ne_zero hr.ne' hp
  have h := aux_lem_local_normalizations_unit_pos_shift M H beta RL0 hbeta1 hRL0conv hpos _ hq
    (∑ i : Fin d, p i * z i)
  filter_upwards [hMP.quasiMeasurePreserving.ae h] with om hom
  rw [aux_lem_local_normalizations_RLsmall_sq RL0 H e k (he k)]
  have hcomp : aux_lem_local_normalizations_aff p ∘ aux_lem_local_normalizations_T k z =
      fun y => aux_lem_local_normalizations_aff (((3 : ℝ) ^ (-(k : ℤ))) • p) y +
        ∑ i : Fin d, p i * z i :=
    aux_lem_local_normalizations_aff_comp p z _
  rw [hcomp]
  have := he k
  positivity

/-- **Clause 4 on large triadic cubes.** -/
theorem aux_lem_local_normalizations_pos_big (hbeta1 : beta ≤ 1)
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (hpos : ∀ p : Fin d → ℝ, p ≠ 0 → ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (aux_lem_local_normalizations_aff p)) ^ 2)
    (e : ℕ → ℝ) (he : ∀ k, 0 < e k) (m : ℕ) (z : SpatialCoordinates d)
    (p : Fin d → ℝ) (hp : p ≠ 0) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (aux_lem_local_normalizations_RLbig RL0 H e m z om
        (aux_lem_local_normalizations_aff p)) ^ 2 := by
  have hMP := aux_lem_local_normalizations_Thetabig_measurePreserving M m z
  have hr : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  have hq : ((3 : ℝ) ^ (m : ℤ)) • p ≠ 0 := smul_ne_zero hr.ne' hp
  have h := aux_lem_local_normalizations_unit_pos_shift M H beta RL0 hbeta1 hRL0conv hpos _ hq
    (∑ i : Fin d, p i * z i)
  filter_upwards [hMP.quasiMeasurePreserving.ae h] with om hom
  rw [aux_lem_local_normalizations_RLbig_sq RL0 H e m (he m)]
  have hcomp : aux_lem_local_normalizations_aff p ∘ aux_lem_local_normalizations_Tbig m z =
      fun y => aux_lem_local_normalizations_aff (((3 : ℝ) ^ (m : ℤ)) • p) y +
        ∑ i : Fin d, p i * z i :=
    aux_lem_local_normalizations_aff_comp p z _
  rw [hcomp]
  have := he m
  positivity

end clauses

theorem aux_lem_local_normalizations_T_zero_zero :
    (aux_lem_local_normalizations_T (d := d) 0 0 : SpatialCoordinates d → SpatialCoordinates d) =
      id := by
  funext y i
  simp [aux_lem_local_normalizations_T, cubeDilation]

theorem aux_lem_local_normalizations_Theta_zero_zero (omega : BilateralField d) :
    aux_lem_local_normalizations_Theta 0 0 omega = omega := by
  funext j
  ext y
  rw [aux_lem_local_normalizations_Theta_apply]
  have : (aux_lem_local_normalizations_T (d := d) 0 0) y = y := by
    rw [show ((aux_lem_local_normalizations_T (d := d) 0 0) y) =
      (aux_lem_local_normalizations_T (d := d) 0 0 : SpatialCoordinates d → SpatialCoordinates d) y
      from rfl, aux_lem_local_normalizations_T_zero_zero]; rfl
  rw [this]; simp

theorem aux_lem_local_normalizations_RL_one
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (e : ℕ → ℝ)
    (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (omega : BilateralField d) :
    aux_lem_local_normalizations_RL RL0 H e z 1 h1 omega =
      aux_lem_local_normalizations_RLsmall RL0 H e 0 z omega := by
  have h := aux_lem_local_normalizations_RL_small RL0 H e z 0
    (zpow_pos (by norm_num : (0 : ℝ) < 3) _) omega
  have h3 : (3 : ℝ) ^ (-((0 : ℕ) : ℤ)) = 1 := by simp
  simp only [h3] at h
  exact h

/-- **Clause 7b**, the limiting scaling identity, simultaneously for all data. -/
theorem aux_lem_local_normalizations_limit_scaling
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (e : ℕ → ℝ) (he : ∀ k, 0 < e k) (he0 : e 0 = 1) (k : ℕ) (z : SpatialCoordinates d)
    (hrk : 0 < (3 : ℝ) ^ (-(k : ℤ))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ g : SpatialCoordinates d → ℝ,
      (aux_lem_local_normalizations_RL RL0 H e z ((3 : ℝ) ^ (-(k : ℤ))) hrk omega g) ^ 2 =
        (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
          Real.exp (aux_lem_local_normalizations_Gc H k omega z) *
          (aux_lem_local_normalizations_RL RL0 H e 0 1 zero_lt_one
            (aux_lem_local_normalizations_Theta k z omega)
            (g ∘ aux_lem_local_normalizations_T k z)) ^ 2 := by
  filter_upwards [aux_lem_local_normalizations_H_Theta M H HI k z] with omega hH g
  rw [aux_lem_local_normalizations_RL_small, aux_lem_local_normalizations_RL_one,
    aux_lem_local_normalizations_RLsmall_sq RL0 H e k (he k),
    aux_lem_local_normalizations_RLsmall_sq RL0 H e 0 (he 0),
    aux_lem_local_normalizations_Theta_zero_zero, aux_lem_local_normalizations_T_zero_zero]
  have hG0 : aux_lem_local_normalizations_Gc H 0
      (aux_lem_local_normalizations_Theta k z omega) 0 = 0 := by
    have h := congrArg (fun F : C(SpatialCoordinates d, ℝ) => F 0) hH
    simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
      aux_lem_local_normalizations_T_zero, sub_self] at h
    simp [aux_lem_local_normalizations_Gc, h]
  rw [hG0, he0]
  simp

/-- The deterministic lower bound `κ_{N-k}/κ_N ≥ e^{-kτ²}` (cutoff monotonicity of `ahom`). -/
theorem aux_lem_local_normalizations_kap_ratio_lb (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (k N : ℕ) (hkN : k ≤ N) :
    Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ≤
      aux_lem_local_normalizations_kap M (N - k) / aux_lem_local_normalizations_kap M N := by
  unfold aux_lem_local_normalizations_kap
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hB := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
  have hmono := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ahom_le_ahom_of_le M (Nat.sub_le N k)
  rw [le_div_iff₀ (by positivity), Nat.cast_sub hkN]
  have e1 : Real.exp (-((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
      (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) =
      Real.exp (((N : ℝ) - k + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le

-- ===== from LNMain.lean =====

variable {d : ℕ}

/-- **Clause 1**: the deterministic scalar ratios converge to positive limits. -/
theorem aux_lem_local_normalizations_e_exists
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (beta : ℝ) (hbeta1 : beta ≤ 1)
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (hpos : ∀ p : Fin d → ℝ, p ≠ 0 → ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (aux_lem_local_normalizations_aff p)) ^ 2)
    (p1 : Fin d → ℝ) (hp1 : p1 ≠ 0)
    (hX : ∀ k : ℕ, ∃ Xl : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 ((3 : ℝ) ^ (-(k : ℤ)))
          (zpow_pos (by norm_num) _) N om (aux_lem_local_normalizations_aff p1)) atTop Xl) :
    ∃ e : ℕ → ℝ, (∀ k, 0 < e k ∧ Tendsto (fun N => aux_lem_local_normalizations_kap M (N - k) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 (e k))) ∧ e 0 = 1 := by
  set μ := (chaosSampleLaw M).toMeasure
  have hek : ∀ k : ℕ, ∃ e : ℝ, 0 < e ∧ Tendsto (fun N => aux_lem_local_normalizations_kap M
      (N - k) / aux_lem_local_normalizations_kap M N) atTop (𝓝 e) := by
    intro k
    obtain ⟨Xl, hXl⟩ := hX k
    have hr : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
    set T := aux_lem_local_normalizations_T (d := d) k 0
    set Θ := aux_lem_local_normalizations_Theta (d := d) k 0
    have hMP : MeasurePreserving Θ μ μ :=
      aux_lem_local_normalizations_Theta_measurePreserving M k 0
    set g := aux_lem_local_normalizations_aff (d := d) p1
    have hgT : IsCellBoundaryClass beta 0 1 (g ∘ T) :=
      aux_lem_local_normalizations_smooth_class beta hbeta1 0 1 _
        ((aux_lem_local_normalizations_aff_smooth p1).comp
          (show ContDiff ℝ ∞ (T : SpatialCoordinates d → SpatialCoordinates d) by
            apply contDiff_pi.2; intro i
            exact contDiff_const.add (contDiff_const.mul
              ((contDiff_apply ℝ ℝ i).sub contDiff_const))))
    have hY0 : TendstoInMeasure μ
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos (N - k) (Θ om) (g ∘ T))
        atTop (fun om => (RL0 (Θ om) (g ∘ T)) ^ 2) :=
      (aux_lem_local_normalizations_tim_comp_mp μ Θ hMP _ _ (hRL0conv _ hgT)).comp
        (tendsto_sub_atTop_nat k)
    have hYm : ∀ N, AEStronglyMeasurable
        (fun om => aux_lem_local_normalizations_Lam M H 0 1 one_pos (N - k) (Θ om) (g ∘ T)) μ :=
      fun N => (aux_lem_local_normalizations_Lam_aesm M H HI.1 μ (N - k) 0 1 one_pos
        (g ∘ T)).comp_measurePreserving hMP
    set F : BilateralField d → ℝ := fun om => (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
      Real.exp (aux_lem_local_normalizations_Gc H k om 0)
    have hF : AEStronglyMeasurable F μ :=
      (measurable_const.mul (Real.measurable_exp.comp
        (aux_lem_local_normalizations_Gc_meas H HI.1 k 0))).aestronglyMeasurable
    have hY := aux_lem_local_normalizations_tim_scale μ _ _ hY0 hYm (fun _ => (1 : ℝ)) 1
      tendsto_const_nhds F hF
    -- positivity of the limit
    have hq : ((3 : ℝ) ^ (-(k : ℤ))) • p1 ≠ 0 := smul_ne_zero hr.ne' hp1
    have hsh := aux_lem_local_normalizations_unit_pos_shift M H beta RL0 hbeta1 hRL0conv hpos _
      hq (∑ i : Fin d, p1 i * (0 : SpatialCoordinates d) i)
    have hYpos : ∀ᵐ om ∂μ, 0 < 1 * F om * (RL0 (Θ om) (g ∘ T)) ^ 2 := by
      filter_upwards [hMP.quasiMeasurePreserving.ae hsh] with om hom
      have hcomp : g ∘ T = fun y => aux_lem_local_normalizations_aff
          (((3 : ℝ) ^ (-(k : ℤ))) • p1) y + ∑ i : Fin d, p1 i * (0 : SpatialCoordinates d) i :=
        aux_lem_local_normalizations_aff_comp p1 0 _
      rw [hcomp]
      have : 0 < F om := by positivity
      positivity
    have hid : ∀ N, k ≤ N → ∀ᵐ om ∂μ,
        aux_lem_local_normalizations_Lam M H 0 ((3 : ℝ) ^ (-(k : ℤ))) hr N om g =
          (aux_lem_local_normalizations_kap M (N - k) / aux_lem_local_normalizations_kap M N) *
            ((fun _ => (1 : ℝ)) N * F om *
              aux_lem_local_normalizations_Lam M H 0 1 one_pos (N - k) (Θ om) (g ∘ T)) := by
      intro N hN
      filter_upwards [aux_lem_local_normalizations_finite_scaling M H HI k 0 hr] with om hom
      unfold aux_lem_local_normalizations_Lam
      rw [hom N hN g]
      ring
    have hlb := aux_lem_local_normalizations_kap_ratio_lb M k
    obtain ⟨e, he, hce, -⟩ := aux_lem_local_normalizations_ratio_limit_lb μ
      (fun N => aux_lem_local_normalizations_kap M (N - k) / aux_lem_local_normalizations_kap M N)
      _ (Real.exp_pos _) k hlb _ _ Xl _ hXl hY hid hYpos
    exact ⟨e, he, hce⟩
  choose e he using hek
  refine ⟨e, he, ?_⟩
  have h1 : Tendsto (fun N => aux_lem_local_normalizations_kap M (N - 0) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
    simp only [Nat.sub_zero]
    exact (div_self (aux_lem_local_normalizations_kap_pos M N).ne').symm
  exact tendsto_nhds_unique (he 0).2 h1

/-- **The rooted conclusion**: every clause of the frozen theorem, with clauses 2--4 on
triadic cubes, for the transported seminorm. -/
theorem aux_lem_local_normalizations_rooted
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (beta : ℝ) (hbeta1 : beta ≤ 1)
    (RL0 : BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hRL0conv : ∀ g, IsCellBoundaryClass beta 0 1 g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 1 one_pos N om g) atTop
        (fun om => (RL0 om g) ^ 2))
    (hRL0bd : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ g, IsCellBoundaryClass beta 0 1 g →
        (RL0 om g) ^ 2 ≤ K * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2)
    (hpos : ∀ p : Fin d → ℝ, p ≠ 0 → ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (aux_lem_local_normalizations_aff p)) ^ 2)
    (e : ℕ → ℝ)
    (he : ∀ k, 0 < e k ∧ Tendsto (fun N => aux_lem_local_normalizations_kap M (N - k) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 (e k)))
    (he0 : e 0 = 1) :
    (∀ k : ℕ, 0 < e k ∧ Tendsto (fun N => aux_lem_local_normalizations_kap M (N - k) /
      aux_lem_local_normalizations_kap M N) atTop (𝓝 (e k))) ∧
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (g : SpatialCoordinates d → ℝ),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) → IsCellBoundaryClass beta z r g →
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H z r hr N om g) atTop
        (fun om => (aux_lem_local_normalizations_RL RL0 H e z r hr om g) ^ 2)) ∧
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
        ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta z r g →
          (aux_lem_local_normalizations_RL RL0 H e z r hr om g) ^ 2 ≤
            K * (cellBoundaryQuotientNorm beta z r g) ^ 2) ∧
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : Fin d → ℝ),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) → p ≠ 0 →
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        0 < (aux_lem_local_normalizations_RL RL0 H e z r hr om
          (fun x : SpatialCoordinates d => ∑ i : Fin d, p i * x i)) ^ 2) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d),
      MeasurePreserving (aux_lem_local_normalizations_Theta k z)
        (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        H (aux_lem_local_normalizations_Theta k z om) =
          (aux_lem_local_normalizations_Gc H k om).comp (aux_lem_local_normalizations_T k z) -
            ContinuousMap.const _ (aux_lem_local_normalizations_Gc H k om z)) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        (∀ (N : ℕ), k ≤ N → ∀ (g : SpatialCoordinates d → ℝ),
          IsCellBoundaryClass beta z ((3 : ℝ) ^ (-(k : ℤ))) g →
          aux_lem_local_normalizations_Lam M H z ((3 : ℝ) ^ (-(k : ℤ)))
              (zpow_pos zero_lt_three (-(k : ℤ))) N om g =
            (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
              (aux_lem_local_normalizations_kap M (N - k) /
                aux_lem_local_normalizations_kap M N) *
              Real.exp (aux_lem_local_normalizations_Gc H k om z) *
              aux_lem_local_normalizations_Lam M H 0 1 zero_lt_one (N - k)
                (aux_lem_local_normalizations_Theta k z om)
                (g ∘ aux_lem_local_normalizations_T k z)) ∧
        (∀ (g : SpatialCoordinates d → ℝ),
          IsCellBoundaryClass beta z ((3 : ℝ) ^ (-(k : ℤ))) g →
          (aux_lem_local_normalizations_RL RL0 H e z ((3 : ℝ) ^ (-(k : ℤ)))
              (zpow_pos zero_lt_three (-(k : ℤ))) om g) ^ 2 =
            (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
              Real.exp (aux_lem_local_normalizations_Gc H k om z) *
              (aux_lem_local_normalizations_RL RL0 H e 0 1 zero_lt_one
                (aux_lem_local_normalizations_Theta k z om)
                (g ∘ aux_lem_local_normalizations_T k z)) ^ 2)) := by
  have hepos : ∀ k, 0 < e k := fun k => (he k).1
  refine ⟨he, ?_, ?_, ?_, fun k z => aux_lem_local_normalizations_Theta_measurePreserving M k z,
    fun k z => aux_lem_local_normalizations_H_Theta M H HI k z, ?_⟩
  · intro z r hr g htri hg
    rcases aux_lem_local_normalizations_triadic_cases r htri with ⟨k, rfl⟩ | ⟨m, hm, rfl⟩
    · refine (aux_lem_local_normalizations_conv_small M H HI beta RL0 hRL0conv e he k z hr g
        hg).congr_right (ae_of_all _ fun om => ?_)
      dsimp only
      rw [aux_lem_local_normalizations_RL_small]
    · refine (aux_lem_local_normalizations_conv_big M H HI beta RL0 hRL0conv e he m z hr g
        hg).congr_right (ae_of_all _ fun om => ?_)
      dsimp only
      rw [aux_lem_local_normalizations_RL_big RL0 H e z m hm]
  · intro z r hr htri
    rcases aux_lem_local_normalizations_triadic_cases r htri with ⟨k, rfl⟩ | ⟨m, hm, rfl⟩
    · filter_upwards [aux_lem_local_normalizations_bound_small M H beta RL0 hRL0bd e hepos k z]
        with om hom
      simp only [aux_lem_local_normalizations_RL_small]
      exact hom
    · filter_upwards [aux_lem_local_normalizations_bound_big M H beta RL0 hRL0bd e hepos m z]
        with om hom
      simp only [aux_lem_local_normalizations_RL_big RL0 H e z m hm]
      exact hom
  · intro z r hr p htri hp
    rcases aux_lem_local_normalizations_triadic_cases r htri with ⟨k, rfl⟩ | ⟨m, hm, rfl⟩
    · filter_upwards [aux_lem_local_normalizations_pos_small M H beta RL0 hbeta1 hRL0conv hpos
        e hepos k z p hp] with om hom
      rw [aux_lem_local_normalizations_RL_small]
      exact hom
    · filter_upwards [aux_lem_local_normalizations_pos_big M H beta RL0 hbeta1 hRL0conv hpos
        e hepos m z p hp] with om hom
      rw [aux_lem_local_normalizations_RL_big RL0 H e z m hm]
      exact hom
  · intro k z
    have hrk : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos zero_lt_three (-(k : ℤ))
    filter_upwards [aux_lem_local_normalizations_finite_scaling M H HI k z hrk,
      aux_lem_local_normalizations_limit_scaling M H HI RL0 e hepos he0 k z hrk] with om h1 h2
    exact ⟨fun N hN g _ => h1 N hN g, fun g _ => h2 g⟩

-- ===== from LNFinal.lean =====

theorem aux_lem_local_normalizations_triadic_of_determining
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        -- (D1) determining responses on the unit cube: the `hsubseq` premise of
        -- `lem_local_normalizations_full_cutoff` for every smooth datum (`mfd:lem-local-normalizations`)
        (∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
          ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos
                  (ψ (ψ' n)) omega g) atTop (𝓝 (Rlim omega))) →
        -- (D2) the same premise for one nonconstant affine datum on each cube `3^{-k} Q₀`
        (∀ k : ℕ, ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                  ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (ψ (ψ' n)) omega
                  (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                  atTop (𝓝 (Rlim omega))) →
        let kap : ℕ → ℝ :=
          fun N => Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
        let rscale : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ))
        let hrscale : ∀ k : ℕ, 0 < rscale k :=
          fun k => zpow_pos zero_lt_three (-(k : ℤ))
        let T (k : ℕ) (z : SpatialCoordinates d) :
            C(SpatialCoordinates d, SpatialCoordinates d) :=
          ⟨cubeDilation z 0 (rscale k),
            continuous_cubeDilation z 0 (rscale k)⟩
        let Theta (k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) :
            BilateralField d :=
          fun j : ℤ => (omega (j - (k : ℤ))).comp (T k z)
        let Gc (k : ℕ) (omega : BilateralField d) :
            C(SpatialCoordinates d, ℝ) :=
          H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
        let Lam (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
            (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) : ℝ :=
          sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
              (U : SpatialCoordinates d → ℝ),
            ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
            ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
              U x = g x) ∧
            e = sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N z hr) u.val u.val}
        ∃ e : ℕ → ℝ,
          ∃ RL : (z : SpatialCoordinates d) → (r : ℝ) → (hr : 0 < r) →
              BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ),
            (∀ k : ℕ, 0 < e k ∧
              Tendsto (fun N => kap (N - k) / kap N) atTop (nhds (e k))) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
                (g : SpatialCoordinates d → ℝ),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              IsCellBoundaryClass beta z r g →
              TendstoInMeasure (chaosSampleLaw M).toMeasure
                (fun N omega => Lam z r hr N omega g) atTop
                (fun omega => (RL z r hr omega g) ^ 2)) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∃ K : ℝ, 0 < K ∧
                  ∀ (g : SpatialCoordinates d → ℝ),
                    IsCellBoundaryClass beta z r g →
                    (RL z r hr omega g) ^ 2 ≤
                      K * (cellBoundaryQuotientNorm beta z r g) ^ 2) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
                (p : Fin d → ℝ),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              p ≠ 0 →
                ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  0 <
                    (RL z r hr omega
                      (fun x : SpatialCoordinates d =>
                        ∑ i : Fin d, p i * x i)) ^ 2) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              MeasurePreserving (Theta k z)
                (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                H (Theta k z omega) =
                  (Gc k omega).comp (T k z) -
                    ContinuousMap.const _ (Gc k omega z)) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                (∀ (N : ℕ), k ≤ N →
                  ∀ (g : SpatialCoordinates d → ℝ),
                    IsCellBoundaryClass beta z (rscale k) g →
                    Lam z (rscale k) (hrscale k) N omega g =
                      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
                        (kap (N - k) / kap N) * Real.exp (Gc k omega z) *
                        Lam 0 1 zero_lt_one (N - k) (Theta k z omega)
                          (g ∘ T k z)) ∧
                (∀ (g : SpatialCoordinates d → ℝ),
                  IsCellBoundaryClass beta z (rscale k) g →
                    (RL z (rscale k) (hrscale k) omega g) ^ 2 =
                      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
                        Real.exp (Gc k omega z) *
                        (RL 0 1 zero_lt_one (Theta k z omega)
                          (g ∘ T k z)) ^ 2)) := by
  obtain ⟨δ1, hδ1, hRL⟩ := aux_lem_local_normalizations_unit_RL hd Jc Xc Sf beta
    hbeta_lower hbeta_upper
  obtain ⟨δ2, hδ2, hPos⟩ := aux_lem_local_normalizations_unit_pos hd Jc Xc Sf
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm H HI hMδ hD1 hD2
  have hMδ1 : M.delta ≤ δ1 := hMδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMδ2 : M.delta ≤ δ2 := hMδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hconvU : ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
      ∃ L : BilateralField d → ℝ, TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
          (cutoffPositiveCoefficient M H om N 0 one_pos) g)) atTop L := by
    intro g hg
    have h := lem_local_normalizations_full_cutoff d hd Jc Pc Xc Sf beta hbeta_lower
      hbeta_upper (min δ1 δ2) (lt_min hδ1 hδ2) M Rm H HI hMδ 0 1 one_pos g
      (aux_lem_local_normalizations_smooth_class beta hbeta_upper.le 0 1 g hg) hg
    obtain ⟨Rlim, hR, -⟩ := h (hD1 g hg)
    exact ⟨Rlim, hR⟩
  obtain ⟨RL0, hRL0conv, hRL0bd⟩ := hRL M Rm H HI hMδ1 hconvU
  have hpos : ∀ p : Fin d → ℝ, p ≠ 0 → ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      0 < (RL0 om (aux_lem_local_normalizations_aff p)) ^ 2 := fun p hp =>
    hPos M Rm H HI hMδ2 p hp _ (hRL0conv _ (aux_lem_local_normalizations_smooth_class beta
      hbeta_upper.le 0 1 _ (aux_lem_local_normalizations_aff_smooth p)))
  set p1 : Fin d → ℝ := fun _ => 1 with hp1def
  have hp1 : p1 ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [p1] at this
  have hX : ∀ k : ℕ, ∃ Xl : BilateralField d → ℝ,
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun N om => aux_lem_local_normalizations_Lam M H 0 ((3 : ℝ) ^ (-(k : ℤ)))
          (zpow_pos (by norm_num) _) N om (aux_lem_local_normalizations_aff p1)) atTop Xl := by
    intro k
    have h := lem_local_normalizations_full_cutoff d hd Jc Pc Xc Sf beta hbeta_lower
      hbeta_upper (min δ1 δ2) (lt_min hδ1 hδ2) M Rm H HI hMδ 0 ((3 : ℝ) ^ (-(k : ℤ)))
      (zpow_pos (by norm_num) _) (aux_lem_local_normalizations_aff p1)
      (aux_lem_local_normalizations_smooth_class beta hbeta_upper.le 0 _ _
        (aux_lem_local_normalizations_aff_smooth p1))
      (aux_lem_local_normalizations_aff_smooth p1)
    obtain ⟨Rlim, hR, -⟩ := h (hD2 k)
    exact ⟨Rlim, hR⟩
  obtain ⟨e, he, he0⟩ := aux_lem_local_normalizations_e_exists M H HI beta hbeta_upper.le RL0
    hRL0conv hpos p1 hp1 hX
  have hroot := aux_lem_local_normalizations_rooted M H HI beta hbeta_upper.le RL0 hRL0conv
    hRL0bd hpos e he he0
  exact ⟨e, aux_lem_local_normalizations_RL RL0 H e, hroot⟩


/-- **The repaired principal from the determining supplier.**  The statement is the frozen
`lem_local_normalizations` with the triadic guard in clauses 2--4, and the single hypothesis
`hdet` is the determining-response supplier (the `hsubseq` premise of
`lem_local_normalizations_full_cutoff`, `mfd:lem-local-normalizations`). -/
theorem aux_lem_local_normalizations_repaired_of_determining
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1)
    
    (hdet : ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        (∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
          ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos
                  (ψ (ψ' n)) omega g) atTop (𝓝 (Rlim omega))) ∧
        (∀ k : ℕ, ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                  ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (ψ (ψ' n)) omega
                  (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                  atTop (𝓝 (Rlim omega)))) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        let kap : ℕ → ℝ :=
          fun N => Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
        let rscale : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ))
        let hrscale : ∀ k : ℕ, 0 < rscale k :=
          fun k => zpow_pos zero_lt_three (-(k : ℤ))
        let T (k : ℕ) (z : SpatialCoordinates d) :
            C(SpatialCoordinates d, SpatialCoordinates d) :=
          ⟨cubeDilation z 0 (rscale k),
            continuous_cubeDilation z 0 (rscale k)⟩
        let Theta (k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) :
            BilateralField d :=
          fun j : ℤ => (omega (j - (k : ℤ))).comp (T k z)
        let Gc (k : ℕ) (omega : BilateralField d) :
            C(SpatialCoordinates d, ℝ) :=
          H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
        let Lam (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
            (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) : ℝ :=
          sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
              (U : SpatialCoordinates d → ℝ),
            ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
            ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
              U x = g x) ∧
            e = sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N z hr) u.val u.val}
        ∃ e : ℕ → ℝ,
          ∃ RL : (z : SpatialCoordinates d) → (r : ℝ) → (hr : 0 < r) →
              BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ),
            (∀ k : ℕ, 0 < e k ∧
              Tendsto (fun N => kap (N - k) / kap N) atTop (nhds (e k))) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
                (g : SpatialCoordinates d → ℝ),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              IsCellBoundaryClass beta z r g →
              TendstoInMeasure (chaosSampleLaw M).toMeasure
                (fun N omega => Lam z r hr N omega g) atTop
                (fun omega => (RL z r hr omega g) ^ 2)) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∃ K : ℝ, 0 < K ∧
                  ∀ (g : SpatialCoordinates d → ℝ),
                    IsCellBoundaryClass beta z r g →
                    (RL z r hr omega g) ^ 2 ≤
                      K * (cellBoundaryQuotientNorm beta z r g) ^ 2) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
                (p : Fin d → ℝ),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              p ≠ 0 →
                ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  0 <
                    (RL z r hr omega
                      (fun x : SpatialCoordinates d =>
                        ∑ i : Fin d, p i * x i)) ^ 2) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              MeasurePreserving (Theta k z)
                (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                H (Theta k z omega) =
                  (Gc k omega).comp (T k z) -
                    ContinuousMap.const _ (Gc k omega z)) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                (∀ (N : ℕ), k ≤ N →
                  ∀ (g : SpatialCoordinates d → ℝ),
                    IsCellBoundaryClass beta z (rscale k) g →
                    Lam z (rscale k) (hrscale k) N omega g =
                      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
                        (kap (N - k) / kap N) * Real.exp (Gc k omega z) *
                        Lam 0 1 zero_lt_one (N - k) (Theta k z omega)
                          (g ∘ T k z)) ∧
                (∀ (g : SpatialCoordinates d → ℝ),
                  IsCellBoundaryClass beta z (rscale k) g →
                    (RL z (rscale k) (hrscale k) omega g) ^ 2 =
                      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
                        Real.exp (Gc k omega z) *
                        (RL 0 1 zero_lt_one (Theta k z omega)
                          (g ∘ T k z)) ^ 2)) := by
  obtain ⟨δ1, hδ1, hdet⟩ := hdet
  obtain ⟨δ0, hδ0, hred⟩ := aux_lem_local_normalizations_triadic_of_determining d hd Jc Pc Xc Sf
    beta hbeta_lower hbeta_upper
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, ?_⟩
  intro M Rm Sreg It H HI hM
  have hM0 : M.delta ≤ min 1 δ0 := hM.trans (min_le_min le_rfl (min_le_left _ _))
  have hM1 : M.delta ≤ min 1 δ1 := hM.trans (min_le_min le_rfl (min_le_right _ _))
  have hD := hdet M Rm Sreg It H HI hM1
  exact hred M Rm H HI hM0 hD.1 hD.2

end LNHelpers

open scoped ContDiff

/-! The determining-response supplier is reduced to the two substantive
compactness and uniqueness inputs for the smooth and affine determining data.
The assembly below is fully proved; the four inputs retain the exact
compactness/uniqueness interfaces needed by the compactness argument. -/

theorem aux_lem_local_normalizations_ae_eq_of_tim {Om : Type*} {mOm : MeasurableSpace Om}
    (mu : Measure Om) [IsFiniteMeasure mu] (X : ℕ → Om → ℝ) (Lm : Om → ℝ)
    (hLm : TendstoInMeasure mu X atTop Lm)
    (Xm : ∀ n, AEStronglyMeasurable (X n) mu)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (L : Om → ℝ)
    (hL : ∀ᵐ om ∂mu, Tendsto (fun n => X (phi n) om) atTop (𝓝 (L om))) :
    L =ᵐ[mu] Lm := by
  have h1 : TendstoInMeasure mu (fun n => X (phi n)) atTop Lm :=
    hLm.comp hphi.tendsto_atTop
  have h2 : TendstoInMeasure mu (fun n => X (phi n)) atTop L :=
    tendstoInMeasure_of_tendsto_ae (fun n => Xm (phi n)) hL
  exact tendstoInMeasure_ae_unique h2 h1





theorem aux_lem_local_normalizations_lnorm_compact_affine_RD
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ k : ℕ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ L : BilateralField d → ℝ,
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            Tendsto (fun n => aux_lem_local_normalizations_lnorm_proxy_RD (0 : SpatialCoordinates d)
              ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ)))
              (aux_lem_local_normalizations_lnorm_hP_general d hd 0 ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))))
              (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
                (zpow_pos zero_lt_three (-(k : ℤ)))) (fun _ => (1 : ℝ)) 0)
              M H (ψ (ψ' n)) omega) atTop (𝓝 (L omega)) := by
  have haD : 0 < aux_lem_local_normalizations_prop16_aD d := by
    unfold aux_lem_local_normalizations_prop16_aD
    have hA : (0 : ℝ) < (d : ℝ) - 1 / 2 := by
      have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hB : (d : ℝ) - 1 / 2 - (d : ℝ) + 1 = 1 / 2 := by ring
    have hC : (0 : ℝ) < (d : ℝ) - 1 / 2 + 1 := by linarith
    rw [hB]
    apply div_pos
    apply div_pos
    · exact mul_pos hA (by norm_num)
    · exact hC
    · exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨q1, delta0mom, hq1, hdelta0mom, hmom_all⟩ :=
    aux_lem_local_normalizations_test_rembank_rd_moments d hd Jc Pc Xc W Sf D
  obtain ⟨delta0band, hdelta0band, hband_all⟩ :=
    aux_lem_local_normalizations_test_prop16_rd_band d hd Jc Pc Xc W Sf D
  refine ⟨min delta0mom delta0band, lt_min hdelta0mom hdelta0band, ?_⟩
  intro M Rm Sreg It H HI hM k ψ hψ
  have hMmom : M.delta ≤ min 1 delta0mom :=
    hM.trans (min_le_min_left 1 (min_le_left delta0mom delta0band))
  have hMband : M.delta ≤ min 1 delta0band :=
    hM.trans (min_le_min_left 1 (min_le_right delta0mom delta0band))
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos zero_lt_three (-(k : ℤ))
  have hrle : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (Int.natCast_nonneg k))
  have hP := aux_lem_local_normalizations_lnorm_hP_general d hd (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr
  set b := affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) hr)
    (fun _ : Fin d => (1 : ℝ)) 0 with hbdef
  have hphi : ContDiff ℝ ∞ (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) := by
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (contDiff_apply ℝ ℝ i)
  have hbeq : ((b : SobolevData (centeredCube (0 : SpatialCoordinates d)
      ((3 : ℝ) ^ (-(k : ℤ))) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ (-(k : ℤ))) hr : Set (SpatialCoordinates d))]
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) := by
    filter_upwards [affineL2_coeFn (centeredCube_isBounded (0 : SpatialCoordinates d) hr)
      (fun _ : Fin d => (1 : ℝ)) 0] with x hx
    show (affineL2 (centeredCube_isBounded (0 : SpatialCoordinates d) hr)
      (fun _ : Fin d => (1 : ℝ)) 0 : SpatialCoordinates d → ℝ) x = _
    rw [hx, affineSlope_apply, add_zero]
  obtain ⟨x0, hx0, y0, hy0, hxy⟩ :=
    aux_lem_local_normalizations_lnorm_affine_nonconst d hd (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr
  obtain ⟨Cmom6, hCmom6, hmomN⟩ :=
    hmom_all (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr hrle hP
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) hphi b hbeq
      M Rm Sreg It H HI hMmom
  obtain ⟨Cband, hCband, hbandN⟩ :=
    hband_all (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr hrle hP
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) hphi
      ⟨x0, hx0, y0, hy0, hxy⟩ b hbeq M Rm Sreg It H HI hMband
  have hRDmem6 : ∀ N, MemLp (aux_lem_local_normalizations_lnorm_proxy_RD (0 : SpatialCoordinates d)
      ((3 : ℝ) ^ (-(k : ℤ))) hr hP b M H N) (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure :=
    fun N => (hmomN N).1
  have hRDbound6 : ∀ N, eLpNorm (aux_lem_local_normalizations_lnorm_proxy_RD (0 : SpatialCoordinates d)
      ((3 : ℝ) ^ (-(k : ℤ))) hr hP b M H N) (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cmom6 := fun N => (hmomN N).2.2.1
  exact aux_lem_local_normalizations_lnorm_general_compact (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr hP b M H
    HI Cmom6 Cband (aux_lem_local_normalizations_prop16_aD d) hCmom6 hCband haD hRDmem6 hRDbound6 hbandN ψ hψ




/-- A smooth datum itself, including its interior values, has a weak Sobolev representative. -/
theorem aux_lem_local_normalizations_smooth_representative
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) :
    ∃ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g := by
  let v := Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (aux_lem_local_normalizations_lnorm_isOpenBoundedConvexDomain z r hr) (hg.of_le (by norm_num))
  obtain ⟨b, hb, -⟩ := exists_weakSobolevGraph_of_nativeH1 v
  exact ⟨b, hb⟩

/-- The actual variational minimum vanishes when the prescribed boundary trace is constant. -/
theorem aux_lem_local_normalizations_Lam_eq_zero_of_constant_trace
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) (c : ℝ)
    (hg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = c) :
    aux_lem_local_normalizations_Lam M H z r hr N omega g = 0 := by
  let a := cutoffPositiveCoefficient M H omega N z hr
  have hz : 0 ∈ aux_lem_local_normalizations_Lset z r hr a g := by
    refine ⟨affineSobolev (centeredCube_isBounded z hr) 0 c, fun _ => c,
      continuousOn_const, ?_, fun x hx => (hg x hx).symm, ?_⟩
    · filter_upwards [affineL2_coeFn (centeredCube_isBounded z hr) (0 : Fin d → ℝ) c]
        with x hx
      change (affineL2 (centeredCube_isBounded z hr) (0 : Fin d → ℝ) c) x = c
      simpa only [affineSlope_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        zero_add] using hx
    · exact (aux_lem_local_normalizations_form_const z r hr a
        (affineSobolevData (centeredCube_isBounded z hr) 0 c) c).symm
  exact le_antisymm
    (csInf_le ⟨0, aux_lem_local_normalizations_Lset_nonneg z r hr a g⟩ hz)
    (aux_lem_local_normalizations_sInf_nonneg z r hr a g)

/-- The exponent in the response band approximation is positive in dimensions at least two. -/
theorem aux_lem_local_normalizations_band_exponent_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < aux_lem_local_normalizations_prop16_aD d := by
  unfold aux_lem_local_normalizations_prop16_aD
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith
  have hB : (d : ℝ) - 1 / 2 - (d : ℝ) + 1 = 1 / 2 := by ring
  have hC : (0 : ℝ) < (d : ℝ) - 1 / 2 + 1 := by linarith
  rw [hB]
  exact div_pos (div_pos (mul_pos hA (by norm_num)) hC)
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

theorem aux_lem_local_normalizations_hdet_compact_smooth (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
          ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ L : BilateralField d → ℝ,
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos
                  (ψ (ψ' n)) omega g) atTop (𝓝 (L omega)) := by
  classical
  obtain ⟨q, δmom, hq, hδmom, hmom⟩ := aux_lem_local_normalizations_test_rembank_rd_moments d hd Jc Pc Xc W Sf D
  obtain ⟨δband, hδband, hband⟩ := aux_lem_local_normalizations_test_prop16_rd_band d hd Jc Pc Xc W Sf D
  refine ⟨min δmom δband, lt_min hδmom hδband, ?_⟩
  intro M Rm Sreg It H HI hM g hg ψ hψ
  have hMmom : M.delta ≤ min 1 δmom :=
    hM.trans (min_le_min_left 1 (min_le_left _ _))
  have hMband : M.delta ≤ min 1 δband :=
    hM.trans (min_le_min_left 1 (min_le_right _ _))
  by_cases hn : ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ∃ y ∈ frontier
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)), g x ≠ g y
  · obtain ⟨b, hb⟩ := aux_lem_local_normalizations_smooth_representative 0 1 one_pos g hg
    let hP := aux_lem_local_normalizations_lnorm_hP_general d hd 0 1 one_pos
    obtain ⟨Cmom, hCmom, hmomN⟩ :=
      hmom 0 1 one_pos le_rfl hP g hg b hb M Rm Sreg It H HI hMmom
    obtain ⟨Cband, hCband, hbandN⟩ :=
      hband 0 1 one_pos le_rfl hP g hg hn b hb M Rm Sreg It H HI hMband
    obtain ⟨ψ', hψ', L, hL⟩ := aux_lem_local_normalizations_lnorm_general_compact 0 1 one_pos hP b M H HI
      Cmom Cband (aux_lem_local_normalizations_prop16_aD d) hCmom hCband
      (aux_lem_local_normalizations_band_exponent_pos d hd)
      (fun N => (hmomN N).1) (fun N => (hmomN N).2.2.1) hbandN ψ hψ
    refine ⟨ψ', hψ', L, ?_⟩
    filter_upwards [hL] with omega homega
    have heq : ∀ n, aux_lem_local_normalizations_Lam M H 0 1 one_pos
        (ψ (ψ' n)) omega g = aux_lem_local_normalizations_lnorm_proxy_RD 0 1 one_pos hP b M H (ψ (ψ' n)) omega :=
      fun n => aux_lem_local_normalizations_Lam_eq_response hd M H omega (ψ (ψ' n))
        0 one_pos hP (cutoffPositiveCoefficient M H omega (ψ (ψ' n)) 0 one_pos)
        b g g hg.continuous.continuousOn hb (fun _ _ => rfl) rfl
    exact homega.congr' (Eventually.of_forall fun n => (heq n).symm)
  · push Not at hn
    obtain ⟨x, hx, y, hy, hxy⟩ := aux_lem_local_normalizations_lnorm_affine_nonconst d hd 0 1 one_pos
    refine ⟨id, strictMono_id, fun _ => 0, Eventually.of_forall fun omega => ?_⟩
    have heq : ∀ n, aux_lem_local_normalizations_Lam M H 0 1 one_pos
        (ψ (id n)) omega g = 0 := fun n =>
      aux_lem_local_normalizations_Lam_eq_zero_of_constant_trace M H 0 1 one_pos
        (ψ (id n)) omega g (g x) (fun w hw => hn w hw x hx)
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => (heq n).symm)

theorem aux_lem_local_normalizations_hdet_unique_smooth (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
          ∀ (φ1 φ2 : ℕ → ℕ), StrictMono φ1 → StrictMono φ2 →
          ∀ (L1 L2 : BilateralField d → ℝ),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos (φ1 n) omega g)
                atTop (𝓝 (L1 omega))) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos (φ2 n) omega g)
                atTop (𝓝 (L2 omega))) →
            L1 =ᵐ[(chaosSampleLaw M).toMeasure] L2 := by
  obtain ⟨δc, hδc, hc⟩ :=
    lem_local_normalizations_common_smooth d hd Jc Pc Xc Sf W Cp D hES Step Interp EM
  refine ⟨min 1 δc, lt_min one_pos hδc, ?_⟩
  intro M Rm Sreg It H HI hM g hg φ1 φ2 hφ1 hφ2 L1 L2 hL1 hL2
  have hMc : M.delta ≤ min 1 δc := hM.trans (min_le_right _ _)
  have hM1 : M.delta ≤ min (1 : ℝ) 1 := by
    have h := hM.trans (min_le_left (1 : ℝ) (min 1 δc)); simpa using h
  have hcommon := hc M Rm Sreg It H HI hMc g hg
  obtain ⟨Rlim, hfull, -⟩ := lem_local_normalizations_full_cutoff d hd Jc Pc Xc Sf
    (3 / 4 : ℝ) (by norm_num) (by norm_num) 1 one_pos M Rm H HI hM1
    0 1 one_pos g
    (aux_lem_local_normalizations_smooth_class (3 / 4 : ℝ) (by norm_num)
      0 1 g hg) hg hcommon
  have hL1m : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega => aux_lem_local_normalizations_Lam M H 0 1 one_pos (φ1 n) omega g)
      atTop L1 :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => aux_lem_local_normalizations_Lam_aesm M H HI.1
        (chaosSampleLaw M).toMeasure (φ1 n) 0 1 one_pos g) hL1
  have hL2m : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega => aux_lem_local_normalizations_Lam M H 0 1 one_pos (φ2 n) omega g)
      atTop L2 :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => aux_lem_local_normalizations_Lam_aesm M H HI.1
        (chaosSampleLaw M).toMeasure (φ2 n) 0 1 one_pos g) hL2
  have hfull1 := hfull.comp hφ1.tendsto_atTop
  have hfull2 := hfull.comp hφ2.tendsto_atTop
  have heq1 := tendstoInMeasure_ae_unique hL1m hfull1
  have heq2 := tendstoInMeasure_ae_unique hL2m hfull2
  filter_upwards [heq1, heq2] with omega h1 h2
  exact h1.trans h2.symm


theorem aux_lem_local_normalizations_hdet_compact_affine (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ k : ℕ,
          ∀ ψ : ℕ → ℕ, StrictMono ψ →
        ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ L : BilateralField d → ℝ,
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                  ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (ψ (ψ' n)) omega
                  (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                  atTop (𝓝 (L omega)) := by
  obtain ⟨delta1, hdelta1, hbody⟩ := aux_lem_local_normalizations_lnorm_compact_affine_RD d hd Jc Pc Xc Sf W D
  refine ⟨delta1, hdelta1, ?_⟩
  intro M Rm Sreg It H HI hM k ψ hψ
  obtain ⟨ψ', hψ', L, hL⟩ := hbody M Rm Sreg It H HI hM k ψ hψ
  refine ⟨ψ', hψ', L, ?_⟩
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos zero_lt_three (-(k : ℤ))
  set hP := aux_lem_local_normalizations_lnorm_hP_general d hd (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr
    with hPdef
  set hb := affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) hr)
    (fun _ : Fin d => (1 : ℝ)) 0 with hbdef
  have hbeq : ((hb : SobolevData (centeredCube (0 : SpatialCoordinates d)
      ((3 : ℝ) ^ (-(k : ℤ))) hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube (0 : SpatialCoordinates d)
        ((3 : ℝ) ^ (-(k : ℤ))) hr : Set (SpatialCoordinates d))]
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) := by
    filter_upwards [affineL2_coeFn (centeredCube_isBounded (0 : SpatialCoordinates d) hr)
      (fun _ : Fin d => (1 : ℝ)) 0] with x hx
    show (affineL2 (centeredCube_isBounded (0 : SpatialCoordinates d) hr)
      (fun _ : Fin d => (1 : ℝ)) 0 : SpatialCoordinates d → ℝ) x = _
    rw [hx, affineSlope_apply, add_zero]
  have hgcont : ContinuousOn (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)
      (closedCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr :
        Set (SpatialCoordinates d)) :=
    (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).continuousOn
  have heq : ∀ (n : ℕ) (omega : BilateralField d),
      aux_lem_local_normalizations_Lam M H 0 ((3 : ℝ) ^ (-(k : ℤ))) hr
        (ψ (ψ' n)) omega (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i) =
      aux_lem_local_normalizations_lnorm_proxy_RD (0 : SpatialCoordinates d) ((3 : ℝ) ^ (-(k : ℤ))) hr hP hb M H
        (ψ (ψ' n)) omega :=
    fun n omega => aux_lem_local_normalizations_Lam_eq_response hd M H omega (ψ (ψ' n))
      (0 : SpatialCoordinates d) hr hP
      (cutoffPositiveCoefficient M H omega (ψ (ψ' n)) 0 hr) hb
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)
      (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)
      hgcont hbeq (fun x _ => rfl) rfl
  filter_upwards [hL] with omega hom
  simpa only [heq] using hom


theorem aux_lem_local_normalizations_hdet_unique_affine (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        ∀ k : ℕ,
          ∀ (φ1 φ2 : ℕ → ℕ), StrictMono φ1 → StrictMono φ2 →
          ∀ (L1 L2 : BilateralField d → ℝ),
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (φ1 n) omega
                (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                atTop (𝓝 (L1 omega))) →
            (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (φ2 n) omega
                (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                atTop (𝓝 (L2 omega))) →
            L1 =ᵐ[(chaosSampleLaw M).toMeasure] L2 := by
  obtain ⟨δc, hδc, hc⟩ :=
    lem_local_normalizations_common_affine d hd Jc Pc Xc Sf W Cp D hES Step Interp EM
  refine ⟨min 1 δc, lt_min one_pos hδc, ?_⟩
  intro M Rm Sreg It H HI hM k φ1 φ2 hφ1 hφ2 L1 L2 hL1 hL2
  have hMc : M.delta ≤ min 1 δc := hM.trans (min_le_right _ _)
  have hM1 : M.delta ≤ min (1 : ℝ) 1 := by
    have h := hM.trans (min_le_left (1 : ℝ) (min 1 δc)); simpa using h
  have hcommon := hc M Rm Sreg It H HI hMc k
  have hphi : ContDiff ℝ ∞ (fun x : SpatialCoordinates d =>
      ∑ i : Fin d, (1 : ℝ) * x i) := by
    apply ContDiff.sum
    intro i hi
    exact contDiff_const.mul (contDiff_apply ℝ ℝ i)
  obtain ⟨Rlim, hfull, -⟩ := lem_local_normalizations_full_cutoff d hd Jc Pc Xc Sf
    (3 / 4 : ℝ) (by norm_num) (by norm_num) 1 one_pos M Rm H HI hM1
    0 ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ)))
    (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)
    (aux_lem_local_normalizations_smooth_class (3 / 4 : ℝ) (by norm_num)
      0 ((3 : ℝ) ^ (-(k : ℤ))) _ hphi) hphi hcommon
  have hL1m : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega => aux_lem_local_normalizations_Lam M H 0
        ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (φ1 n) omega
        (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)) atTop L1 :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => aux_lem_local_normalizations_Lam_aesm M H HI.1
        (chaosSampleLaw M).toMeasure (φ1 n) 0 ((3 : ℝ) ^ (-(k : ℤ)))
        (zpow_pos zero_lt_three (-(k : ℤ)))
        (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)) hL1
  have hL2m : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n omega => aux_lem_local_normalizations_Lam M H 0
        ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (φ2 n) omega
        (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)) atTop L2 :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => aux_lem_local_normalizations_Lam_aesm M H HI.1
        (chaosSampleLaw M).toMeasure (φ2 n) 0 ((3 : ℝ) ^ (-(k : ℤ)))
        (zpow_pos zero_lt_three (-(k : ℤ)))
        (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i)) hL2
  have hfull1 := hfull.comp hφ1.tendsto_atTop
  have hfull2 := hfull.comp hφ2.tendsto_atTop
  have heq1 := tendstoInMeasure_ae_unique hL1m hfull1
  have heq2 := tendstoInMeasure_ae_unique hL2m hfull2
  filter_upwards [heq1, heq2] with omega h1 h2
  exact h1.trans h2.symm

theorem aux_lem_local_normalizations_hdet_assembly (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta1 →
        (∀ g : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ g →
          ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos
                  (ψ (ψ' n)) omega g) atTop (𝓝 (Rlim omega))) ∧
        (∀ k : ℕ, ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                  ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (ψ (ψ' n)) omega
                  (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                  atTop (𝓝 (Rlim omega))) := by
  obtain ⟨δ1, hδ1, hC1⟩ :=
    aux_lem_local_normalizations_hdet_compact_smooth d hd Jc Pc Xc Sf W Cp D hES
  obtain ⟨δ2, hδ2, hU1⟩ :=
    aux_lem_local_normalizations_hdet_unique_smooth d hd Jc Pc Xc Sf W Cp D hES Step Interp EM
  obtain ⟨δ3, hδ3, hC2⟩ :=
    aux_lem_local_normalizations_hdet_compact_affine d hd Jc Pc Xc Sf W Cp D hES
  obtain ⟨δ4, hδ4, hU2⟩ :=
    aux_lem_local_normalizations_hdet_unique_affine d hd Jc Pc Xc Sf W Cp D hES Step Interp EM
  refine ⟨min (min δ1 δ2) (min δ3 δ4), lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4), ?_⟩
  intro M Rm Sreg It H HI hM
  have hM1 : M.delta ≤ min 1 δ1 :=
    hM.trans (min_le_min le_rfl ((min_le_left _ _).trans (min_le_left _ _)))
  have hM2 : M.delta ≤ min 1 δ2 :=
    hM.trans (min_le_min le_rfl ((min_le_left _ _).trans (min_le_right _ _)))
  have hM3 : M.delta ≤ min 1 δ3 :=
    hM.trans (min_le_min le_rfl ((min_le_right _ _).trans (min_le_left _ _)))
  have hM4 : M.delta ≤ min 1 δ4 :=
    hM.trans (min_le_min le_rfl ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨ψ0', hψ0', L0, hL0⟩ := hC1 M Rm Sreg It H HI hM1 g hg id strictMono_id
    refine ⟨L0, ?_⟩
    intro ψ hψ
    obtain ⟨ψ', hψ', L, hL⟩ := hC1 M Rm Sreg It H HI hM1 g hg ψ hψ
    refine ⟨ψ', hψ', ?_⟩
    have hEq := hU1 M Rm Sreg It H HI hM2 g hg ψ0' (ψ ∘ ψ') hψ0' (hψ.comp hψ') L0 L hL0 hL
    filter_upwards [hL, hEq] with omega htend heq
    rw [heq]
    exact htend
  · intro k
    obtain ⟨ψ0', hψ0', L0, hL0⟩ := hC2 M Rm Sreg It H HI hM3 k id strictMono_id
    refine ⟨L0, ?_⟩
    intro ψ hψ
    obtain ⟨ψ', hψ', L, hL⟩ := hC2 M Rm Sreg It H HI hM3 k ψ hψ
    refine ⟨ψ', hψ', ?_⟩
    have hEq := hU2 M Rm Sreg It H HI hM4 k ψ0' (ψ ∘ ψ') hψ0' (hψ.comp hψ') L0 L hL0 hL
    filter_upwards [hL, hEq] with omega htend heq
    rw [heq]
    exact htend

theorem aux_lem_local_normalizations_hdet_supplier (d : ℕ) (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
      M.delta ≤ min 1 delta1 →
        (∀ g : SpatialCoordinates d → ℝ,
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
          ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0 1 one_pos
                  (ψ (ψ' n)) omega g) atTop (𝓝 (Rlim omega))) ∧
        (∀ k : ℕ, ∃ Rlim : BilateralField d → ℝ, ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto (fun n => aux_lem_local_normalizations_Lam M H 0
                  ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three (-(k : ℤ))) (ψ (ψ' n)) omega
                  (fun x : SpatialCoordinates d => ∑ i : Fin d, (1 : ℝ) * x i))
                  atTop (𝓝 (Rlim omega))) := by
    exact aux_lem_local_normalizations_hdet_assembly d hd Jc Pc Xc Sf W Cp D hES Step Interp EM



/--
- Actual M,kappa,H law and reindexed full fields; in_normalization,in_common_scale_coupling,lem_infrared.
- Actual variational coefficient/domain/trace pin; in_dirichlet_response,in_killed_energy,lem_extension. No empty-class real-sInf use on the admitted trace class.
- Complete layer-law preservation and retained-oscillation identity are conclusions, sourced from `mfd:lem-local-normalizations`, not abstract assumptions.
- Positive scalar limit and finite/limiting scaling identities are conclusions; scalar convergence uses fixed nonconstant affine data and actual response convergence, not unrelated Z/W binders or assumed scaling.
- thm_c1's concluding `mfd:lem-local-normalizations` paragraph supplies full-cutoff convergence through relative compactness/unique candidates/boundary minima, with a separate export requested from G5.
- Source tick: `mfd:lem-local-normalizations` invokes the nonconstant affine boundary response positivity supplied by the already constructed boundary minimum and coarse Poincare (prop_boundary, lem_coercivity/in_poincare).
- Extension to all admissible beta>1/2 traces uses lem_extension, countable determining traces and continuity of squared seminorms. Constants may depend on fixed cube, beta, omega, never on g or kappa cutoff.
- The parent proof consumes the two common-limit nodes; their closure is required separately.
-/
theorem lem_local_normalizations
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        let kap : ℕ → ℝ :=
          fun N => Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
        let rscale : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ))
        let hrscale : ∀ k : ℕ, 0 < rscale k :=
          fun k => zpow_pos zero_lt_three (-(k : ℤ))
        let T (k : ℕ) (z : SpatialCoordinates d) :
            C(SpatialCoordinates d, SpatialCoordinates d) :=
          ⟨cubeDilation z 0 (rscale k),
            continuous_cubeDilation z 0 (rscale k)⟩
        let Theta (k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) :
            BilateralField d :=
          fun j : ℤ => (omega (j - (k : ℤ))).comp (T k z)
        let Gc (k : ℕ) (omega : BilateralField d) :
            C(SpatialCoordinates d, ℝ) :=
          H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
        let Lam (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
            (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) : ℝ :=
          sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
              (U : SpatialCoordinates d → ℝ),
            ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
            ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
              U x = g x) ∧
            e = sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N z hr) u.val u.val}
        ∃ e : ℕ → ℝ,
          ∃ RL : (z : SpatialCoordinates d) → (r : ℝ) → (hr : 0 < r) →
              BilateralField d → Seminorm ℝ (SpatialCoordinates d → ℝ),
            (∀ k : ℕ, 0 < e k ∧
              Tendsto (fun N => kap (N - k) / kap N) atTop (nhds (e k))) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
                (g : SpatialCoordinates d → ℝ),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              IsCellBoundaryClass beta z r g →
              TendstoInMeasure (chaosSampleLaw M).toMeasure
                (fun N omega => Lam z r hr N omega g) atTop
                (fun omega => (RL z r hr omega g) ^ 2)) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∃ K : ℝ, 0 < K ∧
                  ∀ (g : SpatialCoordinates d → ℝ),
                    IsCellBoundaryClass beta z r g →
                    (RL z r hr omega g) ^ 2 ≤
                      K * (cellBoundaryQuotientNorm beta z r g) ^ 2) ∧
            (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
                (p : Fin d → ℝ),
              (∃ j : ℤ, r = (3 : ℝ) ^ j) →
              p ≠ 0 →
                ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  0 <
                    (RL z r hr omega
                      (fun x : SpatialCoordinates d =>
                        ∑ i : Fin d, p i * x i)) ^ 2) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              MeasurePreserving (Theta k z)
                (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                H (Theta k z omega) =
                  (Gc k omega).comp (T k z) -
                    ContinuousMap.const _ (Gc k omega z)) ∧
            (∀ (k : ℕ) (z : SpatialCoordinates d),
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                (∀ (N : ℕ), k ≤ N →
                  ∀ (g : SpatialCoordinates d → ℝ),
                    IsCellBoundaryClass beta z (rscale k) g →
                    Lam z (rscale k) (hrscale k) N omega g =
                      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
                        (kap (N - k) / kap N) * Real.exp (Gc k omega z) *
                        Lam 0 1 zero_lt_one (N - k) (Theta k z omega)
                          (g ∘ T k z)) ∧
                (∀ (g : SpatialCoordinates d → ℝ),
                  IsCellBoundaryClass beta z (rscale k) g →
                    (RL z (rscale k) (hrscale k) omega g) ^ 2 =
                      (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) * e k *
                        Real.exp (Gc k omega z) *
                        (RL 0 1 zero_lt_one (Theta k z omega)
                          (g ∘ T k z)) ^ 2)) := by
  -- The determining-response input is supplied by
  -- aux_lem_local_normalizations_hdet_supplier in the application below.
  obtain ⟨delta0, hdelta0, hmain⟩ :=
    aux_lem_local_normalizations_repaired_of_determining d hd Jc Pc Xc Sf beta
      hbeta_lower hbeta_upper
      (aux_lem_local_normalizations_hdet_supplier d hd Jc Pc Xc Sf W Cp D hES Step Interp EM)
  exact ⟨delta0, hdelta0, hmain⟩

end SubdiffusiveProcess.Paper

