module

public import SubdiffusiveProcess.Paper.in_moments_response_moment
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prefix_score_cauchy
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lem_prefix_limit_actual_coordinate_cauchy
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_compact
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_moving_chart_moment
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Lane4.Carriers
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.branch_candidate_setup
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldEvenFinite
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SubdiffusiveProcess.Paper.finite_cutoff_log_abs_majorant
public import SubdiffusiveProcess.Paper.coefficient_physical_identity
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Sobolev.GMCAnchoredOrlicz
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.OrliczLpNorm
public import SubdiffusiveProcess.Probability.GeometricSeriesLp
public import SubdiffusiveProcess.Probability.OrliczNormSeries
public import SubdiffusiveProcess.Probability.OrliczFiniteSum
public import SubdiffusiveProcess.Probability.OrliczExponentialMoment

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section LemPrefixLimitGenericHelpers
open Filter MeasureTheory Set Real
open scoped ENNReal NNReal BigOperators Topology

namespace Paper

theorem aux_lem_prefix_limit_lp_limit_of_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 1 ≤ p) (f : ℕ → Ω → ℝ)
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ)
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n n' : ℕ, n₀ ≤ n → n₀ ≤ n' →
      eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) :
    ∃ g : Ω → ℝ, MemLp g (ENNReal.ofReal p) μ ∧
      Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  let F : ℕ → ↥(Lp ℝ (ENNReal.ofReal p) μ) := fun n => (hf n).toLp (f n)
  have hcauF : CauchySeq F := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    obtain ⟨n₀, hn₀⟩ := hcau r (ENNReal.ofReal_pos.mp hr0)
    refine ⟨n₀, fun m hm n hn => ?_⟩
    rw [Lp.edist_def]
    rw [eLpNorm_congr_ae ((hf m).coeFn_toLp.sub (hf n).coeFn_toLp)]
    exact lt_of_le_of_lt (hn₀ m n hm hn) hrε
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauF
  refine ⟨↑↑G, Lp.memLp G, ?_⟩
  have hconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F G).mp hG
  exact Tendsto.congr (fun n => eLpNorm_congr_ae ((hf n).coeFn_toLp.sub (ae_eq_refl (μ := μ) (↑↑G)))) hconv

theorem aux_lem_prefix_limit_tendsto_eLpNorm_of_exponent_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p q : ℝ) (hpq : p ≤ q)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal q) μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun n => bot_le) (fun n => ?_)
  rw [← Pi.sub_def]
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)

theorem aux_lem_prefix_limit_eLpNorm_limit_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 1 ≤ p) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (K : ℝ) (hK : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    MemLp g (ENNReal.ofReal p) μ ∧ eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hle : ∀ n, eLpNorm g (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal K + eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ := by
    intro n
    have hmeas_sub : AEStronglyMeasurable (fun ω => f n ω - g ω) μ := (hf n).sub hg
    have h_eq : g = (f n) - (fun ω => f n ω - g ω) := by
      ext ω
      show g ω = f n ω - (f n ω - g ω)
      ring
    have hsub := eLpNorm_sub_le (μ := μ) (f := f n) (g := fun ω => f n ω - g ω) h1
    rw [← h_eq] at hsub
    calc eLpNorm g (ENNReal.ofReal p) μ
        ≤ eLpNorm (f n) (ENNReal.ofReal p) μ + eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ := hsub
      _ ≤ ENNReal.ofReal K + eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ :=
          add_le_add (hK n) le_rfl
  have htend : Tendsto (fun n => ENNReal.ofReal K + eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ)
      atTop (𝓝 (ENNReal.ofReal K)) := by
    have ht := hconv.const_add (ENNReal.ofReal K)
    simpa using ht
  have hbound : eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K :=
    ge_of_tendsto htend (Eventually.of_forall hle)
  exact ⟨lt_of_le_of_lt hbound ENNReal.ofReal_lt_top, hbound⟩

theorem aux_lem_prefix_limit_prefix_sum_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 1 ≤ p) (start : ℤ) (D cbuf : ℕ) (V : ℤ → Ω → ℝ)
    (hV : ∀ j, AEStronglyMeasurable (V j) μ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ j, eLpNorm (V j) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) :
    eLpNorm (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K * ((D : ℝ) + (cbuf : ℝ) + 1)) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hfun : (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ)), V j ω)
      = ∑ j ∈ Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ)), V j := by
    funext ω; rw [Finset.sum_apply]
  have hcard : (Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ))).card = D + cbuf + 1 := by
    rw [Int.card_Icc]
    have hz : start + (D:ℤ) + 1 - (start - (cbuf:ℤ)) = ((D + cbuf + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hz, Int.toNat_natCast]
  calc
    eLpNorm (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ)), V j ω) (ENNReal.ofReal p) μ
        = eLpNorm (∑ j ∈ Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ)), V j) (ENNReal.ofReal p) μ := by rw [hfun]
    _ ≤ ∑ j ∈ Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ)), eLpNorm (V j) (ENNReal.ofReal p) μ :=
        eLpNorm_sum_le h1
    _ ≤ ∑ j ∈ Finset.Icc (start - (cbuf:ℤ)) (start + (D:ℤ)), ENNReal.ofReal K :=
        Finset.sum_le_sum (fun j _ => hK j)
    _ = ENNReal.ofReal (K * ((D:ℝ) + (cbuf:ℝ) + 1)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast (D + cbuf + 1)]
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((D + cbuf + 1 : ℕ) : ℝ))]
        congr 1
        push_cast
        ring

theorem aux_lem_prefix_limit_prefix_sum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 1 ≤ p) (s : Finset ℤ) (f : ℕ → ℤ → Ω → ℝ) (g : ℤ → Ω → ℝ)
    (hf : ∀ n j, AEStronglyMeasurable (f n j) μ) (hg : ∀ j, AEStronglyMeasurable (g j) μ)
    (hconv : ∀ j ∈ s, Tendsto (fun n => eLpNorm (fun ω => f n j ω - g j ω)
      (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => ∑ j ∈ s, f n j ω - ∑ j ∈ s, g j ω)
      (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hbound : ∀ n, eLpNorm (fun ω => ∑ j ∈ s, f n j ω - ∑ j ∈ s, g j ω) (ENNReal.ofReal p) μ
      ≤ ∑ j ∈ s, eLpNorm (fun ω => f n j ω - g j ω) (ENNReal.ofReal p) μ := by
    intro n
    have hfun : (fun ω => ∑ j ∈ s, f n j ω - ∑ j ∈ s, g j ω)
        = (∑ j ∈ s, fun ω => f n j ω - g j ω) := by
      funext ω
      rw [Finset.sum_apply, Finset.sum_sub_distrib]
    rw [hfun]
    exact eLpNorm_sum_le h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by
      have := tendsto_finset_sum s hconv
      simpa using this)
    (fun n => bot_le) hbound

theorem aux_lem_prefix_limit_exceedance_passage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : ℕ → Ω → ℝ) (psi : ℕ → ℕ) (g : Ω → ℝ)
    (hconv : TendstoInMeasure μ (fun n => u (psi n)) atTop g)
    (a a' : ℝ) (haa : a < a') (c : ℝ≥0∞)
    (hbound : ∀ n, μ {ω | a < u n ω} ≤ c) :
    μ {ω | a' < g ω} ≤ c := by
  have hε : 0 < a' - a := sub_pos.mpr haa
  have hincl : ∀ n, {ω : Ω | a' < g ω} ⊆
      {ω | a < u (psi n) ω} ∪ {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_cases h : a < u (psi n) ω
    · exact Or.inl h
    · right
      simp only [Set.mem_setOf_eq]
      push_neg at h
      have hgu : a' - a ≤ g ω - u (psi n) ω := by linarith
      have hpos : 0 ≤ g ω - u (psi n) ω := by linarith
      rw [edist_dist, Real.dist_eq, abs_sub_comm]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonneg hpos]
      exact hgu
  have hmain : ∀ n, μ {ω : Ω | a' < g ω} ≤
      c + μ {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)} := by
    intro n
    calc μ {ω : Ω | a' < g ω}
        ≤ μ ({ω | a < u (psi n) ω} ∪
            {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)}) :=
          measure_mono (hincl n)
      _ ≤ μ {ω | a < u (psi n) ω} +
            μ {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)} :=
          measure_union_le _ _
      _ ≤ c + μ {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)} :=
          add_le_add (hbound (psi n)) le_rfl
  have hε' : 0 < ENNReal.ofReal (a' - a) := ENNReal.ofReal_pos.mpr hε
  have hf : Tendsto (fun n => μ {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)})
      atTop (𝓝 0) :=
    hconv (ENNReal.ofReal (a' - a)) hε'
  have hlim : Tendsto (fun n => c + μ {ω | ENNReal.ofReal (a' - a) ≤ edist (u (psi n) ω) (g ω)})
      atTop (𝓝 c) := by
    simpa using hf.const_add c
  exact ge_of_tendsto hlim (Eventually.of_forall hmain)

theorem aux_lem_prefix_limit_prefix_clause {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (moments : Finset ℝ)
    (hmom : ∀ p ∈ moments, 1 ≤ p) (K : ℝ → ℝ) (hK : ∀ p ∈ insert 1 moments, 0 < K p)
    (u : ℕ → ℤ → Ω → ℝ) (V : ℤ → Ω → ℝ) (phi psi : ℕ → ℕ)
    (hu : ∀ N j, AEStronglyMeasurable (u N j) μ)
    (hV : ∀ j, AEStronglyMeasurable (V j) μ)
    (hVb : ∀ p ∈ insert 1 moments, ∀ j,
      eLpNorm (V j) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K p))
    (hconv : ∀ p ∈ insert 1 moments, ∀ j, Tendsto (fun n => eLpNorm (fun ω =>
      u (phi (psi n)) j ω - V j ω) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    (start : ℤ) (D cbuf : ℕ) :
    let prefixN : ℕ → Ω → ℝ := fun N ω =>
      ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u N j ω
    let prefixLim : Ω → ℝ := fun ω =>
      ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω
    AEStronglyMeasurable prefixLim μ ∧
    (∀ p ∈ insert 1 moments,
      eLpNorm prefixLim (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (K p * ((D : ℝ) + (cbuf : ℝ) + 1)) ∧
      Tendsto (fun n => eLpNorm (fun ω => prefixN (phi (psi n)) ω - prefixLim ω)
        (ENNReal.ofReal p) μ) atTop (𝓝 0)) ∧
    (∀ A a a' : ℝ, 0 < A → a < a' →
      (∀ n, μ {ω | a < prefixN (phi n) ω} ≤ ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) →
      μ {ω | a' < prefixLim ω} ≤ ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) := by
  intro prefixN prefixLim
  have hdefN : ∀ N ω, prefixN N ω
      = ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u N j ω := fun N ω => rfl
  have hdefL : ∀ ω, prefixLim ω
      = ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω := fun ω => rfl
  have hAsmL : AEStronglyMeasurable prefixLim μ := by
    show AEStronglyMeasurable
      (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω) μ
    have hfun : (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω)
        = (∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j) := by
      funext ω; rw [Finset.sum_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ (fun j _ => hV j)
  have hN_meas : ∀ N, AEStronglyMeasurable (prefixN N) μ := by
    intro N
    have hfun : (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u N j ω)
        = (∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u N j) := by
      funext ω; rw [Finset.sum_apply]
    show AEStronglyMeasurable
      (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u N j ω) μ
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ (fun j _ => hu N j)
  refine ⟨hAsmL, ?_, ?_⟩
  · intro p hp
    have hp1 : 1 ≤ p := by
      rcases Finset.mem_insert.mp hp with h | h
      · exact le_of_eq h.symm
      · exact hmom p h
    refine ⟨?_, ?_⟩
    · show eLpNorm (fun ω => ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K p * ((D : ℝ) + (cbuf : ℝ) + 1))
      exact aux_lem_prefix_limit_prefix_sum_eLpNorm_le μ p hp1 start D cbuf V hV (K p) (hK p hp).le
        (fun j => hVb p hp j)
    · have hc := aux_lem_prefix_limit_prefix_sum_tendsto μ p hp1
        (Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)))
        (fun n j => u (phi (psi n)) j) V (fun n j => hu _ j) hV (fun j _ => hconv p hp j)
      have hfun_eq : (fun n => eLpNorm (fun ω => prefixN (phi (psi n)) ω - prefixLim ω)
            (ENNReal.ofReal p) μ)
          = (fun n => eLpNorm (fun ω =>
              ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u (phi (psi n)) j ω
              - ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω)
            (ENNReal.ofReal p) μ) := by
        funext n
        apply congrArg (fun F : Ω → ℝ => eLpNorm F (ENNReal.ofReal p) μ)
        ext ω
        rw [hdefN, hdefL]
      rw [hfun_eq]
      exact hc
  · intro A a a' hA haa hb
    have hmem1 : (1 : ℝ) ∈ insert 1 moments := Finset.mem_insert_self 1 moments
    have hsum := aux_lem_prefix_limit_prefix_sum_tendsto μ 1 le_rfl
      (Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)))
      (fun n j => u (phi (psi n)) j) V (fun n j => hu _ j) hV (fun j _ => hconv 1 hmem1 j)
    have hconvprefix : Tendsto (fun n => eLpNorm (fun ω => prefixN (phi (psi n)) ω - prefixLim ω)
        (ENNReal.ofReal 1) μ) atTop (𝓝 0) := by
      have hfun_eq : (fun n => eLpNorm (fun ω => prefixN (phi (psi n)) ω - prefixLim ω)
            (ENNReal.ofReal 1) μ)
          = (fun n => eLpNorm (fun ω =>
              ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), u (phi (psi n)) j ω
              - ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)), V j ω)
            (ENNReal.ofReal 1) μ) := by
        funext n
        apply congrArg (fun F : Ω → ℝ => eLpNorm F (ENNReal.ofReal 1) μ)
        ext ω
        rw [hdefN, hdefL]
      rw [hfun_eq]
      exact hsum
    have hTIM : TendstoInMeasure μ (fun n => prefixN (phi (psi n))) atTop prefixLim := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := ENNReal.ofReal 1)
      · simp
      · exact hconvprefix
    exact aux_lem_prefix_limit_exceedance_passage μ (fun n => prefixN (phi n)) psi prefixLim hTIM
      a a' haa (ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) hb

theorem aux_lem_prefix_limit_coordinate_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (moments : Finset ℝ)
    (hmom : ∀ p ∈ moments, 1 ≤ p) (K : ℝ → ℝ) (v : ℕ → Ω → ℝ)
    (hv : ∀ p ∈ insert 1 moments, ∀ N, MemLp (v N) (ENNReal.ofReal p) μ ∧
      eLpNorm (v N) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K p))
    (hcau : ∀ p ∈ insert 1 moments, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n n' : ℕ, n₀ ≤ n → n₀ ≤ n' →
      eLpNorm (fun ω => v n ω - v n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε) :
    ∃ V : Ω → ℝ, AEStronglyMeasurable V μ ∧
      (∀ p ∈ insert 1 moments, MemLp V (ENNReal.ofReal p) μ ∧
        eLpNorm V (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K p)) ∧
      (∀ p ∈ insert 1 moments, Tendsto (fun n => eLpNorm (fun ω => v n ω - V ω)
        (ENNReal.ofReal p) μ) atTop (𝓝 0)) := by
  classical
  have hSne : (insert 1 moments).Nonempty := ⟨1, Finset.mem_insert_self 1 moments⟩
  set pmax : ℝ := (insert 1 moments).max' hSne with hpmax
  have h1 : ∀ p ∈ insert 1 moments, 1 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact le_of_eq hp.symm
    · exact hmom p hp
  have hpm : pmax ∈ insert 1 moments := by
    rw [hpmax]
    exact Finset.max'_mem _ hSne
  have hmax : ∀ p ∈ insert 1 moments, p ≤ pmax := by
    intro p hp
    rw [hpmax]
    exact (Finset.isGreatest_max' _ hSne).2 hp
  obtain ⟨g, hg, hconv⟩ :=
    aux_lem_prefix_limit_lp_limit_of_cauchy μ pmax (h1 pmax hpm) v
      (fun N => (hv pmax hpm N).1) (hcau pmax hpm)
  refine ⟨g, hg.aestronglyMeasurable, ?_, ?_⟩
  · intro p hp
    have hp_conv := aux_lem_prefix_limit_tendsto_eLpNorm_of_exponent_le μ p pmax (hmax p hp) v g
      (fun N => (hv p hp N).1.aestronglyMeasurable) hg.aestronglyMeasurable hconv
    exact aux_lem_prefix_limit_eLpNorm_limit_le μ p (h1 p hp) v g
      (fun N => (hv p hp N).1.aestronglyMeasurable) hg.aestronglyMeasurable (K p)
      (fun N => (hv p hp N).2) hp_conv
  · intro p hp
    exact aux_lem_prefix_limit_tendsto_eLpNorm_of_exponent_le μ p pmax (hmax p hp) v g
      (fun N => (hv p hp N).1.aestronglyMeasurable) hg.aestronglyMeasurable hconv

theorem aux_lem_prefix_limit_q_exists (d : ℕ) (s sigma : ℝ) (moments : Finset ℝ) :
    ∃ q : ℝ, 1 ≤ q ∧ (∀ p ∈ moments, 2 * p ≤ q) ∧ 32 * (d : ℝ) / min s sigma ≤ q := by
  refine ⟨1 + |32 * (d : ℝ) / min s sigma| + ∑ p ∈ moments, |2 * p|, ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ |32 * (d : ℝ) / min s sigma| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ ∑ p ∈ moments, |2 * p| :=
      Finset.sum_nonneg (fun p _ => abs_nonneg _)
    linarith
  · intro p hp
    have h1 : (0 : ℝ) ≤ |32 * (d : ℝ) / min s sigma| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ ∑ r ∈ moments, |2 * r| :=
      Finset.sum_nonneg (fun r _ => abs_nonneg _)
    have h3 : |2 * p| ≤ ∑ r ∈ moments, |2 * r| :=
      Finset.single_le_sum (s := moments) (f := fun r => |2 * r|) (fun r _ => abs_nonneg _) hp
    have h4 : 2 * p ≤ |2 * p| := le_abs_self _
    linarith
  · have h1 : (0 : ℝ) ≤ |32 * (d : ℝ) / min s sigma| := abs_nonneg _
    have h4 : 32 * (d : ℝ) / min s sigma ≤ |32 * (d : ℝ) / min s sigma| := le_abs_self _
    have h2 : (0 : ℝ) ≤ ∑ p ∈ moments, |2 * p| :=
      Finset.sum_nonneg (fun p _ => abs_nonneg _)
    linarith

theorem aux_lem_prefix_limit_threshold (q Cresp δ : ℝ) (hq : 0 < q) (hC : 0 < Cresp)
    (hδ : 0 < δ) (hδe : δ ≤ Real.exp (-1)) (hδq : δ ≤ 1 / (12 * q * Cresp)) :
    12 * q ≤ Cresp⁻¹ * (δ ^ 2)⁻¹ * |Real.log δ|⁻¹ := by
    have hle : Real.log δ ≤ -1 := by
      have h := Real.log_le_log hδ hδe
      rwa [Real.log_exp] at h
    have hlog_neg : Real.log δ < 0 := by linarith
    have habs : |Real.log δ| = -Real.log δ := abs_of_neg hlog_neg
    have hδinv : -Real.log δ ≤ δ⁻¹ := by
      have h := Real.neg_inv_le_log hδ.le
      linarith
    have h1 : δ ^ 2 * |Real.log δ| ≤ δ := by
      calc δ ^ 2 * |Real.log δ| = δ ^ 2 * (-Real.log δ) := by rw [habs]
        _ ≤ δ ^ 2 * δ⁻¹ := mul_le_mul_of_nonneg_left hδinv (sq_nonneg δ)
        _ = δ := by rw [sq, mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ), mul_one]
    have h2 : 0 < |Real.log δ| := abs_pos.mpr (ne_of_lt hlog_neg)
    have hc : 0 < 12 * q * Cresp := by positivity
    have hmul : (12 * q * Cresp) * δ ≤ 1 := by
      have h := (le_div_iff₀ hc).mp hδq
      nlinarith [h]
    have hstep : (12 * q * Cresp) * (δ ^ 2 * |Real.log δ|) ≤ (12 * q * Cresp) * δ :=
      mul_le_mul_of_nonneg_left h1 hc.le
    have hprod : (12 * q * Cresp) * (δ ^ 2 * |Real.log δ|) ≤ 1 := le_trans hstep hmul
    have hRpos : 0 < Cresp * δ ^ 2 * |Real.log δ| :=
      mul_pos (mul_pos hC (sq_pos_of_pos hδ)) h2
    have key : 12 * q * (Cresp * δ ^ 2 * |Real.log δ|) ≤ 1 := by
      have hr : (12 * q * Cresp) * (δ ^ 2 * |Real.log δ|) = 12 * q * (Cresp * δ ^ 2 * |Real.log δ|) := by ring
      linarith [hprod, hr]
    have hmain : 12 * q ≤ (Cresp * δ ^ 2 * |Real.log δ|)⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hRpos).mpr key
    calc
      12 * q ≤ (Cresp * δ ^ 2 * |Real.log δ|)⁻¹ := hmain
      _ = Cresp⁻¹ * (δ ^ 2)⁻¹ * |Real.log δ|⁻¹ := by rw [mul_inv, mul_inv]

end Paper

end LemPrefixLimitGenericHelpers

noncomputable section LemPrefixLimitRawHelpers
open Filter MeasureTheory Set
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

namespace Paper

-- from flash order fg_g8_F_uniform (harvest)
theorem aux_lem_prefix_limit_F_eLpNorm_uniform {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (delta0 : ℝ) (hM : M.delta ≤ delta0)
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
    (N m : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d => (F N m z omega).toReal)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((1 + (d : ℝ)) * delta0 * ∑' j : ℕ,
        (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
          (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
  have hFmeas := (aux_lem_prefix_limit_actual_Fsc_raw_aemeas M s eps
    (chaosSampleLaw M).toMeasure eta (fun N => prefix_eta_aemeasurable M eta hEta N)
    F Praw Rraw Draw Z rawGood hPrimitive N m z).aestronglyMeasurable
  have hraw := prefix_eta_raw_Fsc_eLpNorm_even M s eps hs eta hEta F Praw Rraw Draw Z rawGood hPrimitive N m z q hq
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hFmeas] at hraw
  refine hraw.trans ?_
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdelta0 : 0 ≤ delta0 := le_trans M.shellPrefix.delta_pos.le hM
  have hc0 : 0 ≤ (1 + (d : ℝ)) * delta0 :=
    mul_nonneg (by linarith) hdelta0
  have hσne : aux_psf_sigma M ≠ 0 := ne_of_gt (aux_psf_sigma_pos M)
  have hb0 : ∀ j : ℕ, 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
      (2 * ((q : ℝ) + 1 + prefix_log_card d j)) := by
    intro j
    have hL := prefix_log_card_nonneg d j
    positivity
  have heq : ∀ j : ℕ, prefix_even_series_bound M s q j = aux_psf_sigma M *
      ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
        (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
    intro j
    rw [prefix_even_series_bound]
    ring
  have hsum : Summable (fun j : ℕ => (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
      (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
    refine ((prefix_even_series_bound_summable M s hs q).mul_left (aux_psf_sigma M)⁻¹).congr ?_
    intro j
    rw [heq j, ← mul_assoc, inv_mul_cancel₀ hσne, one_mul]
  have hterm : ∀ j : ℕ, prefix_even_series_bound M s q j ≤ ((1 + (d : ℝ)) * delta0) *
      ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
        (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
    intro j
    have hσle : aux_psf_sigma M ≤ (1 + (d : ℝ)) * delta0 := by
      unfold aux_psf_sigma
      exact mul_le_mul_of_nonneg_left hM (by linarith)
    rw [heq j]
    exact mul_le_mul_of_nonneg_right hσle (hb0 j)
  have hsumc : Summable (fun j : ℕ => ((1 + (d : ℝ)) * delta0) *
      ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
        (2 * ((q : ℝ) + 1 + prefix_log_card d j)))) :=
    hsum.mul_left ((1 + (d : ℝ)) * delta0)
  calc ∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j)
      ≤ ∑' j : ℕ, ENNReal.ofReal (((1 + (d : ℝ)) * delta0) *
          ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
            (2 * ((q : ℝ) + 1 + prefix_log_card d j)))) :=
        ENNReal.tsum_le_tsum (fun j => ENNReal.ofReal_le_ofReal (hterm j))
    _ = ENNReal.ofReal (∑' j : ℕ, ((1 + (d : ℝ)) * delta0) *
          ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
            (2 * ((q : ℝ) + 1 + prefix_log_card d j)))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hc0 (hb0 j)) hsumc).symm
    _ = ENNReal.ofReal (((1 + (d : ℝ)) * delta0) * ∑' j : ℕ,
          (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
            (2 * ((q : ℝ) + 1 + prefix_log_card d j))) := by
        rw [tsum_mul_left]

-- from flash order fg_g8_Praw_uniform
theorem aux_praw_uniform_CB_mono (d : ℕ) (R σ σ0 : ℝ) (hR : 1 ≤ R) (hσ : 0 ≤ σ) (hσσ : σ ≤ σ0) :
    ((7 : ℝ) ^ d * (Real.exp ((6 * R + 1) ^ 2 * σ ^ 2 / 4) * 2)) ^ (9 * R / (6 * R + 1)) ≤
      ((7 : ℝ) ^ d * (Real.exp ((6 * R + 1) ^ 2 * σ0 ^ 2 / 4) * 2)) ^ (9 * R / (6 * R + 1)) := by
  refine Real.rpow_le_rpow (by positivity) ?_ ?_
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
    refine Real.exp_le_exp.2 ?_
    have hsq : σ ^ 2 ≤ σ0 ^ 2 := pow_le_pow_left₀ hσ hσσ 2
    have h1 : (6 * R + 1) ^ 2 * σ ^ 2 ≤ (6 * R + 1) ^ 2 * σ0 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg (6 * R + 1))
    linarith
  · exact div_nonneg (by linarith) (by linarith)

theorem aux_praw_uniform_term_mono_sigma (d : ℕ) (s R σ σ0 CB : ℝ) (hσ : 0 ≤ σ)
    (hσσ : σ ≤ σ0) (j : ℕ) :
    aux_prefix_praw_term d s R σ CB j ≤ aux_prefix_praw_term d s R σ0 CB j := by
  unfold aux_prefix_praw_term
  have hsq : σ ^ 2 ≤ σ0 ^ 2 := pow_le_pow_left₀ hσ hσσ 2
  have hexp : Real.exp (R ^ 2 * σ ^ 2 / 4) ≤ Real.exp (R ^ 2 * σ0 ^ 2 / 4) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : R ^ 2 * σ ^ 2 ≤ R ^ 2 * σ0 ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    linarith
  have hD : (Real.exp (R ^ 2 * σ ^ 2 / 4) * 2) ^ (2 * j + 1) ≤
      (Real.exp (R ^ 2 * σ0 ^ 2 / 4) * 2) ^ (2 * j + 1) :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hexp (by norm_num)) (2 * j + 1)
  have hC : (0 : ℝ) ≤ (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R := by positivity
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (R - 1) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hA
  refine mul_le_mul_of_nonneg_left ?_ hB
  exact add_le_add_left (mul_le_mul_of_nonneg_left hD hC) CB

theorem aux_praw_uniform_term_mono (d : ℕ) (s R σ σ0 CB CB0 : ℝ) (hσ : 0 ≤ σ) (hσσ : σ ≤ σ0)
    (hCB : CB ≤ CB0) (j : ℕ) :
    aux_prefix_praw_term d s R σ CB j ≤ aux_prefix_praw_term d s R σ0 CB0 j := by
  refine (aux_praw_uniform_term_mono_sigma d s R σ σ0 CB hσ hσσ j).trans ?_
  unfold aux_prefix_praw_term
  have hA : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) ^ R := by positivity
  have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (R - 1) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hA
  refine mul_le_mul_of_nonneg_left ?_ hB
  exact add_le_add le_rfl hCB

theorem aux_lem_prefix_limit_Praw_eLpNorm_uniform {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps R : ℝ) (hR : 1 ≤ R) (delta0 : ℝ) (hM : M.delta ≤ delta0)
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
    (N m : ℕ) (w : Vec d) (p : ℝ) (hpR : p ≤ R) :
    eLpNorm (fun omega => (Praw N m w omega).toReal) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
      (∑' j : ℕ, ENNReal.ofReal (aux_prefix_praw_term d s R ((1 + (d : ℝ)) * delta0)
        (((7 : ℝ) ^ d * (Real.exp ((6 * R + 1) ^ 2 * ((1 + (d : ℝ)) * delta0) ^ 2 / 4) * 2)) ^
          (9 * R / (6 * R + 1))) j)) ^ (1 / R) := by
  refine (aux_prefix_praw_actual_eLpNorm_le M s eps R hR eta hEta F Praw Rraw Draw Z rawGood
    hPrimitive N m w p hpR).trans ?_
  refine ENNReal.rpow_le_rpow ?_ ?_
  · apply ENNReal.tsum_le_tsum
    intro j
    apply ENNReal.ofReal_le_ofReal
    refine aux_praw_uniform_term_mono d s R (aux_psf_sigma M) ((1 + (d : ℝ)) * delta0)
      (aux_prefix_praw_CB M R) _ (aux_psf_sigma_pos M).le ?_ ?_ j
    · unfold aux_psf_sigma
      exact mul_le_mul_of_nonneg_left hM (by positivity)
    · unfold aux_prefix_praw_CB
      refine aux_praw_uniform_CB_mono d R (aux_psf_sigma M) ((1 + (d : ℝ)) * delta0) hR
        (aux_psf_sigma_pos M).le ?_
      unfold aux_psf_sigma
      exact mul_le_mul_of_nonneg_left hM (by positivity)
  · have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
    exact div_nonneg zero_le_one hRpos.le

-- from flash order fg_g8_Z_bound
theorem aux_lem_prefix_limit_Z_value_eLpNorm_le {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ)
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
    (N : ℕ) (n : ℤ) (z : Vec d) (p : ℝ) :
    eLpNorm (fun omega : BilateralField d =>
        if n ≤ (N : ℤ) then Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega else 0)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal 3 := by
  have hZmeas : AEStronglyMeasurable (fun omega : BilateralField d =>
      if n ≤ (N : ℤ) then Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega else 0)
      (chaosSampleLaw M).toMeasure := by
    by_cases h : n ≤ (N : ℤ)
    · simpa only [if_pos h] using (actual_Z_aemeas M s eps (chaosSampleLaw M).toMeasure
        eta (fun N => prefix_eta_aemeasurable M eta hEta N)
        F Praw Rraw Draw Z rawGood hPrimitive N _ _).aestronglyMeasurable
    · simpa only [if_neg h] using (aestronglyMeasurable_const (μ := (chaosSampleLaw M).toMeasure)
        (b := (0 : ℝ)))
  refine (eLpNorm_le_of_ae_bound (C := 3) hZmeas ?_).trans ?_
  · filter_upwards [hPrimitive] with omega hps
    obtain ⟨_, _, _, _, _, _, _, _, _, hZ, _⟩ := hps N
    by_cases h : n ≤ (N : ℤ)
    · rw [if_pos h, Real.norm_eq_abs]
      obtain ⟨_, hZ0, hZ3⟩ := hZ ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
      rw [abs_of_nonneg hZ0]; exact hZ3
    · rw [if_neg h, norm_zero]; norm_num
  · rw [measure_univ, ENNReal.one_rpow, one_mul]

-- from flash order fg_g8_t4_pointwise
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_le_bank_tsum {d : ℕ} (k : ℕ) (w : Vec d)
    (om : PotentialSample d) :
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w om ≤ ∑' j : ℕ, (if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k * ((3 : ℝ) ^ j)⁻¹ *
        aux_prefix_bank_maxObs j j w om) else 0) := by
  unfold aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  by_cases hkj : k ≤ j
  · rw [if_pos hkj, if_pos hkj]
    rw [mul_assoc, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ k)]
    refine mul_le_mul_right ?_ (ENNReal.ofReal ((3 : ℝ) ^ k))
    refine sSup_le ?_
    rintro v ⟨x, hx, rfl⟩
    have hx' : x ∈ translatedCube d (j : ℤ) w := by
      rw [aux_psf_mem_translatedCube_iff] at hx ⊢
      intro i
      have hmono : (3 : ℝ) ^ (k : ℤ) ≤ (3 : ℝ) ^ (j : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by exact_mod_cast hkj)
      linarith [hx i]
    have hbank := aux_prefix_bank_le_maxObs j j le_rfl w x om hx'
    have hterm : (3 : ℝ) ^ j * euclideanNorm (shellGradient (om j) x) ≤
        aux_prefix_bank_maxObs j j w om := by
      linarith [abs_nonneg ((om j) x)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_of_nonneg (euclideanNorm_nonneg (shellGradient (om j) x)), inv_mul_eq_div,
      le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ j), mul_comm]
    exact hterm
  · exact le_of_eq (by simp only [if_neg hkj])

-- from flash order fg_g8_t4_moment
theorem aux_lem_prefix_limit_actual_coordinate_cauchy_geom_hasSum :
    HasSum (fun i : ℕ => ((3 : ℝ)⁻¹) ^ i) (3 / 2) := by
  have hnorm : ‖((3 : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)]
    norm_num
  have h := hasSum_geometric_of_norm_lt_one (ξ := ((3 : ℝ)⁻¹)) hnorm
  have hval : (1 - (3 : ℝ)⁻¹)⁻¹ = 3 / 2 := by norm_num
  rwa [hval] at h

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_geom_tsum :
    (∑' i : ℕ, ((3 : ℝ)⁻¹) ^ i) = 3 / 2 :=
  aux_lem_prefix_limit_actual_coordinate_cauchy_geom_hasSum.tsum_eq

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_geom_tsum_ennreal :
    (∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i)) = ENNReal.ofReal (3 / 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i : ℕ => by positivity)
    aux_lem_prefix_limit_actual_coordinate_cauchy_geom_hasSum.summable,
    aux_lem_prefix_limit_actual_coordinate_cauchy_geom_tsum]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_weight_shift (k i : ℕ) :
    (3 : ℝ) ^ k * ((3 : ℝ) ^ (i + k))⁻¹ = ((3 : ℝ)⁻¹) ^ i := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [pow_add, inv_pow, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero k h3), one_mul]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_guard_tsum_shift
    (F : ℕ → ENNReal) (k : ℕ) :
    (∑' j : ℕ, (if k ≤ j then F j else 0)) = ∑' i : ℕ, F (i + k) := by
  have hinj : Function.Injective (fun i : ℕ => i + k) := fun x y h => Nat.add_right_cancel h
  have hsupp : Function.support (fun j : ℕ => if k ≤ j then F j else 0) ⊆
      Set.range (fun i : ℕ => i + k) := by
    intro j hj
    by_cases h : k ≤ j
    · exact ⟨j - k, Nat.sub_add_cancel h⟩
    · have hz : (if k ≤ j then F j else 0) = 0 := if_neg h
      exact absurd hz hj
  have hmain := Function.Injective.tsum_eq (g := fun i : ℕ => i + k) hinj
    (f := fun j : ℕ => if k ≤ j then F j else 0) hsupp
  rw [← hmain]
  apply tsum_congr
  intro i
  have hle : k ≤ i + k := by omega
  change (if k ≤ i + k then F (i + k) else 0) = F (i + k)
  rw [if_pos hle]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_bank_eLpNorm {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N j : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs j j w (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
  have hmom : ∀ (N i n : ℕ) (z : Vec d) (q : ℕ), 1 ≤ q →
      (∫⁻ omega : BilateralField d, ENNReal.ofReal
        (((aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
        ∂(chaosSampleLaw M).toMeasure) ≤
      2 * ENNReal.ofReal (((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ))) ^ q) :=
    fun N i n z q hq =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_even_moment_log M eta hEta N i n z q hq
  have h := aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_eLpNorm_linear
    M eta hEta hmom N j j w q hq
  simp only [Nat.sub_self] at h
  refine h.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (le_of_lt (aux_psf_sigma_pos M))]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_bank_lintegral_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N j : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    (∫⁻ omega : BilateralField d, ENNReal.ofReal (aux_prefix_bank_maxObs j j w (eta N omega))
      ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
  have hp1 : (1 : ENNReal) ≤ ((2 * q : ℕ) : ENNReal) := by
    rw [← Nat.cast_one, Nat.cast_le]
    omega
  have hmeas : AEStronglyMeasurable
      (fun omega : BilateralField d => aux_prefix_bank_maxObs j j w (eta N omega))
      (chaosSampleLaw M).toMeasure :=
    ((prefix_bank_maxObs_measurable j j w).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  have h1 : eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs j j w (eta N omega))
        1 (chaosSampleLaw M).toMeasure ≤
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs j j w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure :=
    eLpNorm_le_eLpNorm_of_exponent_le hp1
  have h2 : (∫⁻ omega : BilateralField d, ENNReal.ofReal (aux_prefix_bank_maxObs j j w (eta N omega))
        ∂(chaosSampleLaw M).toMeasure) =
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs j j w (eta N omega))
        1 (chaosSampleLaw M).toMeasure := by
    rw [eLpNorm_one_eq_lintegral_enorm hmeas]
    apply lintegral_congr
    intro omega
    rw [Real.enorm_eq_ofReal (prefix_bank_maxObs_nonneg j j w (eta N omega))]
  rw [h2]
  exact h1.trans
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_bank_eLpNorm M eta hEta N j w q hq)

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_summable_of_tsum_ofReal_lt_top
    (a : ℕ → ℝ) (ha : ∀ j : ℕ, 0 ≤ a j)
    (h : (∑' j : ℕ, ENNReal.ofReal (a j)) < ⊤) : Summable a := by
  refine summable_of_sum_range_le (f := a) (c := (∑' j : ℕ, ENNReal.ofReal (a j)).toReal)
    ha (fun n => ?_)
  have h1 : (∑ j ∈ Finset.range n, ENNReal.ofReal (a j)) ≤
      ∑' j : ℕ, ENNReal.ofReal (a j) := ENNReal.sum_le_tsum (Finset.range n)
  have h2 : (∑ j ∈ Finset.range n, ENNReal.ofReal (a j)).toReal ≤
      (∑' j : ℕ, ENNReal.ofReal (a j)).toReal := ENNReal.toReal_mono (ne_of_lt h) h1
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)] at h2
  calc ∑ j ∈ Finset.range n, a j
      = ∑ j ∈ Finset.range n, (ENNReal.ofReal (a j)).toReal := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ENNReal.toReal_ofReal (ha j)]
    _ ≤ (∑' j : ℕ, ENNReal.ofReal (a j)).toReal := h2

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_summable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N k : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Summable (fun i : ℕ => ((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)) := by
  have hterm_meas : ∀ i : ℕ, AEMeasurable (fun omega : BilateralField d =>
      ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)))
      (chaosSampleLaw M).toMeasure :=
    fun i => (((prefix_bank_maxObs_measurable (i + k) (i + k) w).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).const_mul (((3 : ℝ)⁻¹) ^ i)).ennreal_ofReal
  have hstep : ∀ i : ℕ,
      (∫⁻ omega : BilateralField d, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
        ∂(chaosSampleLaw M).toMeasure)
      ≤ ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) *
        ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
          Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
    intro i
    have hw0 : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ i := by positivity
    calc (∫⁻ omega : BilateralField d, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
          aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
          ∂(chaosSampleLaw M).toMeasure)
        = ∫⁻ omega : BilateralField d, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) *
            ENNReal.ofReal (aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
            ∂(chaosSampleLaw M).toMeasure := by
          apply lintegral_congr
          intro omega
          rw [ENNReal.ofReal_mul hw0]
      _ = ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) *
            (∫⁻ omega : BilateralField d,
              ENNReal.ofReal (aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
              ∂(chaosSampleLaw M).toMeasure) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) *
            ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
              Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) :=
          mul_le_mul_right
            (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_bank_lintegral_le
              M eta hEta N (i + k) w q hq) _
  have hbound : (∑' i : ℕ, ∫⁻ omega : BilateralField d, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
        ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (3 / 2 * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) := by
    calc
      (∑' i : ℕ, ∫⁻ omega : BilateralField d, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
          aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
          ∂(chaosSampleLaw M).toMeasure)
          ≤ ∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) *
              ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
                Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) :=
            ENNReal.tsum_le_tsum hstep
      _ = (∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i)) *
              ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
                Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) :=
            ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (3 / 2) * ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
              Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
            rw [aux_lem_prefix_limit_actual_coordinate_cauchy_geom_tsum_ennreal]
      _ = ENNReal.ofReal (3 / 2 * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
              Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hGfun : Measurable (fun p : PotentialSample d => ∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
      aux_prefix_bank_maxObs (i + k) (i + k) w p)) :=
    Measurable.ennreal_tsum (fun i =>
      ((prefix_bank_maxObs_measurable (i + k) (i + k) w).const_mul
        (((3 : ℝ)⁻¹) ^ i)).ennreal_ofReal)
  have hfinbound : ENNReal.ofReal (3 / 2 * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
      Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hG : (∫⁻ omega : BilateralField d, (∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)))
      ∂(chaosSampleLaw M).toMeasure) ≠ ⊤ := by
    rw [lintegral_tsum hterm_meas]
    exact ne_top_of_le_ne_top hfinbound hbound
  have hint : (∫⁻ p : PotentialSample d, (∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
      aux_prefix_bank_maxObs (i + k) (i + k) w p)) ∂M.P.toMeasure) ≠ ⊤ := by
    rw [← prefix_eta_law M eta hEta N,
      lintegral_map' hGfun.aemeasurable (prefix_eta_aemeasurable M eta hEta N)]
    exact hG
  have hae : ∀ᵐ p ∂M.P.toMeasure, (∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
      aux_prefix_bank_maxObs (i + k) (i + k) w p)) < ⊤ := ae_lt_top hGfun hint
  rw [← prefix_eta_law M eta hEta N] at hae
  filter_upwards [MeasureTheory.ae_of_ae_map (prefix_eta_aemeasurable M eta hEta N) hae]
    with omega hω
  exact aux_lem_prefix_limit_actual_coordinate_cauchy_summable_of_tsum_ofReal_lt_top
    (fun i : ℕ => ((3 : ℝ)⁻¹) ^ i * aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
    (fun i => mul_nonneg (by positivity)
      (prefix_bank_maxObs_nonneg (i + k) (i + k) w (eta N omega))) hω

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_partial_eLpNorm_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N k : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    eLpNorm (fun omega : BilateralField d => ∑ i ∈ Finset.range n,
        ((3 : ℝ)⁻¹) ^ i * aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3 / 2 * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) := by
  have hp1 : (1 : ENNReal) ≤ ((2 * q : ℕ) : ENNReal) := by
    rw [← Nat.cast_one, Nat.cast_le]
    omega
  have hstep : ∀ i ∈ Finset.range n,
      eLpNorm (fun omega : BilateralField d => ((3 : ℝ)⁻¹) ^ i *
          aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) * ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
    intro i _
    have hsm : (fun omega : BilateralField d => ((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)) =
        ((3 : ℝ)⁻¹) ^ i • (fun omega : BilateralField d =>
          aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)) := by
      funext omega
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsm, eLpNorm_const_smul (((3 : ℝ)⁻¹) ^ i)
        (fun omega : BilateralField d => aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure,
      Real.enorm_eq_ofReal (by positivity : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ i)]
    exact mul_le_mul_right
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_bank_eLpNorm M eta hEta N (i + k) w q hq) _
  have hsum_meas : ∀ i ∈ Finset.range n, AEStronglyMeasurable
      (fun omega : BilateralField d => ((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
      (chaosSampleLaw M).toMeasure :=
    fun i _ => (((prefix_bank_maxObs_measurable (i + k) (i + k) w).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).const_mul (((3 : ℝ)⁻¹) ^ i)).aestronglyMeasurable
  calc
    eLpNorm (fun omega : BilateralField d => ∑ i ∈ Finset.range n,
        ((3 : ℝ)⁻¹) ^ i * aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure
        = eLpNorm (∑ i ∈ Finset.range n, (fun omega : BilateralField d => ((3 : ℝ)⁻¹) ^ i *
            aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)))
          ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure := by
          congr 1
          funext omega
          rw [Finset.sum_apply]
    _ ≤ ∑ i ∈ Finset.range n, eLpNorm (fun omega : BilateralField d => ((3 : ℝ)⁻¹) ^ i *
          aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure :=
        eLpNorm_sum_le hp1
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i) *
          ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
            Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) :=
        Finset.sum_le_sum hstep
    _ = (∑ i ∈ Finset.range n, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i)) *
          ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
            Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) :=
        (Finset.sum_mul (Finset.range n) _ _).symm
    _ ≤ ENNReal.ofReal (3 / 2) * ENNReal.ofReal (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
            Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
        refine mul_le_mul_left ?_ _
        exact (ENNReal.sum_le_tsum (Finset.range n)).trans (le_of_eq
          aux_lem_prefix_limit_actual_coordinate_cauchy_geom_tsum_ennreal)
    _ = ENNReal.ofReal (3 / 2 * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
            Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]

theorem aux_lem_prefix_limit_actual_coordinate_cauchy_t4_eLpNorm_uniform {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (hpt : ∀ (k : ℕ) (w : Vec d) (om : PotentialSample d),
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w om ≤ ∑' j : ℕ, (if k ≤ j then ENNReal.ofReal
        ((3 : ℝ) ^ k * ((3 : ℝ) ^ j)⁻¹ * aux_prefix_bank_maxObs j j w om) else 0))
    (N k : ℕ) (w : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w (eta N omega)).toReal)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((3 / 2 : ℝ) * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) := by
  have hmeas : ∀ i : ℕ, AEStronglyMeasurable (fun omega : BilateralField d =>
      ((3 : ℝ)⁻¹) ^ i * aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
      (chaosSampleLaw M).toMeasure :=
    fun i => (((prefix_bank_maxObs_measurable (i + k) (i + k) w).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).const_mul (((3 : ℝ)⁻¹) ^ i)).aestronglyMeasurable
  have hsumm := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_summable M eta hEta N k w q hq
  have htsum := prefix_eLpNorm_tsum_le (chaosSampleLaw M).toMeasure
    (fun i omega => ((3 : ℝ)⁻¹) ^ i * aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega))
    ((2 * q : ℕ) : ENNReal)
    (ENNReal.ofReal (3 / 2 * (aux_psf_sigma M * (2 * ((q : ℝ) + 1 +
      Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))))
    hmeas hsumm
    (fun n => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_partial_eLpNorm_le
      M eta hEta N k w q hq n)
  have hmono : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ‖(aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w (eta N omega)).toReal‖ ≤
      ‖∑' i : ℕ, ((3 : ℝ)⁻¹) ^ i *
        aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)‖ := by
    filter_upwards [hsumm] with omega hω
    have hX0 : ∀ j : ℕ, 0 ≤ aux_prefix_bank_maxObs j j w (eta N omega) :=
      fun j => prefix_bank_maxObs_nonneg j j w (eta N omega)
    have hEq2 : (∑' j : ℕ, (if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k * ((3 : ℝ) ^ j)⁻¹ *
          aux_prefix_bank_maxObs j j w (eta N omega)) else 0))
        = ∑' i : ℕ, ENNReal.ofReal (((3 : ℝ)⁻¹) ^ i *
            aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega)) := by
      rw [aux_lem_prefix_limit_actual_coordinate_cauchy_guard_tsum_shift
        (fun j : ℕ => ENNReal.ofReal ((3 : ℝ) ^ k * ((3 : ℝ) ^ j)⁻¹ *
          aux_prefix_bank_maxObs j j w (eta N omega))) k]
      exact tsum_congr
        (fun i => by rw [aux_lem_prefix_limit_actual_coordinate_cauchy_weight_shift k i])
    have hfin : (∑' j : ℕ, (if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k * ((3 : ℝ) ^ j)⁻¹ *
          aux_prefix_bank_maxObs j j w (eta N omega)) else 0)) ≠ ⊤ := by
      rw [hEq2, ← ENNReal.ofReal_tsum_of_nonneg
        (fun i : ℕ => mul_nonneg (by positivity) (hX0 (i + k))) hω]
      exact ENNReal.ofReal_ne_top
    have hraw : (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w (eta N omega)).toReal ≤
        ∑' i : ℕ, ((3 : ℝ)⁻¹) ^ i *
          aux_prefix_bank_maxObs (i + k) (i + k) w (eta N omega) := by
      have h1 := ENNReal.toReal_mono hfin (hpt k w (eta N omega))
      refine h1.trans (le_of_eq ?_)
      rw [hEq2, ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
      exact tsum_congr (fun i => ENNReal.toReal_ofReal
        (mul_nonneg (by positivity) (hX0 (i + k))))
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_of_nonneg (tsum_nonneg (fun i => mul_nonneg (by positivity) (hX0 (i + k))))]
    exact hraw
  have hDt4meas : AEStronglyMeasurable
      (fun omega : BilateralField d =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w (eta N omega)).toReal)
      (chaosSampleLaw M).toMeasure := by
    simpa only [aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4, dscNormOn] using!
      ((ENNReal.measurable_toReal.comp (dsc_fourth_summand_meas k w)).comp_aemeasurable
        (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  exact (eLpNorm_mono_ae hDt4meas hmono).trans htsum

-- ===== G8 raw half: assembly (paper 2746--2763: the raw moment estimates are uniform in the cutoff,
-- the deterministic position and the model below the threshold) =====

/-- Exponent monotonicity on a probability space, with `MemLp`. -/
theorem aux_lem_prefix_limit_raw_memLp_of_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ)
    (p : ℝ) (r : ℝ≥0∞) (hpr : ENNReal.ofReal p ≤ r) (B : ℝ≥0∞) (hB0 : B ≠ ⊤)
    (hB : eLpNorm f r μ ≤ B) :
    MemLp f (ENNReal.ofReal p) μ ∧ eLpNorm f (ENNReal.ofReal p) μ ≤ B := by
  have h := (eLpNorm_le_eLpNorm_of_exponent_le hpr).trans hB
  exact ⟨lt_of_le_of_lt h (lt_top_iff_ne_top.mpr hB0), h⟩

/-- A guarded coordinate inherits measurability and bounds of its active branch. -/
theorem aux_lem_prefix_limit_raw_guard {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Prop) [Decidable P] (f : Ω → ℝ) (r : ℝ≥0∞) (B : ℝ≥0∞)
    (hf : P → AEStronglyMeasurable f μ) (hB : P → eLpNorm f r μ ≤ B) :
    AEStronglyMeasurable (fun ω => if P then f ω else 0) μ ∧
      eLpNorm (fun ω => if P then f ω else 0) r μ ≤ B := by
  by_cases h : P
  · simp only [if_pos h]
    exact ⟨hf h, hB h⟩
  · simp only [if_neg h]
    exact ⟨aestronglyMeasurable_const, by simp⟩

/-- Four-term triangle inequality with explicit bounds. -/
theorem aux_lem_prefix_limit_raw_eLpNorm_add4_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : ℝ≥0∞) (hr : 1 ≤ r) (f1 f2 f3 f4 : Ω → ℝ)
    (h1 : AEStronglyMeasurable f1 μ) (h2 : AEStronglyMeasurable f2 μ)
    (h3 : AEStronglyMeasurable f3 μ) (h4 : AEStronglyMeasurable f4 μ)
    (B1 B2 B3 B4 : ℝ≥0∞) (hb1 : eLpNorm f1 r μ ≤ B1) (hb2 : eLpNorm f2 r μ ≤ B2)
    (hb3 : eLpNorm f3 r μ ≤ B3) (hb4 : eLpNorm f4 r μ ≤ B4) :
    eLpNorm (fun ω => f1 ω + f2 ω + f3 ω + f4 ω) r μ ≤ B1 + B2 + B3 + B4 := by
  have e : (fun ω => f1 ω + f2 ω + f3 ω + f4 ω) = f1 + f2 + f3 + f4 := rfl
  rw [e]
  calc eLpNorm (f1 + f2 + f3 + f4) r μ
      ≤ eLpNorm (f1 + f2 + f3) r μ + eLpNorm f4 r μ :=
        eLpNorm_add_le hr
    _ ≤ (eLpNorm (f1 + f2) r μ + eLpNorm f3 r μ) + eLpNorm f4 r μ := by
        gcongr
        exact eLpNorm_add_le hr
    _ ≤ ((eLpNorm f1 r μ + eLpNorm f2 r μ) + eLpNorm f3 r μ) + eLpNorm f4 r μ := by
        gcongr
        exact eLpNorm_add_le hr
    _ ≤ B1 + B2 + B3 + B4 := by gcongr

/-- `3^{-ak}(A + Bk) ≤ A + B/a` with `a = s/8` (the discount beats the linear entropy). -/
theorem aux_lem_prefix_limit_raw_t3_term_le (s : ℝ) (hs : 0 < s) (A B : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (k : ℕ) :
    (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (A + B * (k : ℝ)) ≤ A + B * (8 / s) := by
  have hx : 0 ≤ (s / 8) * (k : ℝ) := by positivity
  have hle1 : (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlog : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp : 0 < (3 : ℝ) ^ ((s / 8) * (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (s / 8) * (k : ℝ) ≤ (3 : ℝ) ^ ((s / 8) * (k : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    have he := Real.add_one_le_exp (Real.log 3 * ((s / 8) * (k : ℝ)))
    nlinarith [hx, hlog]
  have hkey : (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (k : ℝ) ≤ 8 / s := by
    rw [neg_mul, Real.rpow_neg (by norm_num), inv_mul_le_iff₀ hp]
    have hk : (k : ℝ) = (8 / s) * ((s / 8) * (k : ℝ)) := by field_simp
    calc (k : ℝ) = (8 / s) * ((s / 8) * (k : ℝ)) := hk
      _ ≤ (8 / s) * (3 : ℝ) ^ ((s / 8) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (3 : ℝ) ^ ((s / 8) * (k : ℝ)) * (8 / s) := by ring
  calc (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (A + B * (k : ℝ))
      = (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * A +
          B * ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (k : ℝ)) := by ring
    _ ≤ 1 * A + B * (8 / s) :=
        add_le_add (mul_le_mul_of_nonneg_right hle1 hA) (mul_le_mul_of_nonneg_left hkey hB)
    _ = A + B * (8 / s) := by ring

/-- A common even moment order above every prescribed moment. -/
theorem aux_lem_prefix_limit_raw_order (moments : Finset ℝ) :
    ∃ q0 : ℕ, 1 ≤ q0 ∧ ∀ p ∈ insert 1 moments, p ≤ ((2 * q0 : ℕ) : ℝ) := by
  refine ⟨⌈∑ p ∈ moments, |p|⌉₊ + 1, by omega, ?_⟩
  intro p hp
  have h0 : 0 ≤ ∑ p ∈ moments, |p| := Finset.sum_nonneg (fun p _ => abs_nonneg p)
  have hsum : p ≤ ∑ p ∈ moments, |p| + 1 := by
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h]; linarith
    · have h3 : |p| ≤ ∑ p ∈ moments, |p| :=
        Finset.single_le_sum (f := fun p => |p|) (fun p _ => abs_nonneg p) h
      linarith [le_abs_self p]
  have hc : ∑ p ∈ moments, |p| ≤ (⌈∑ p ∈ moments, |p|⌉₊ : ℝ) := Nat.le_ceil _
  have hc0 : (0 : ℝ) ≤ (⌈∑ p ∈ moments, |p|⌉₊ : ℝ) := Nat.cast_nonneg _
  push_cast
  linarith

theorem aux_lem_prefix_limit_raw_log_cells_nonneg (d : ℕ) :
    0 ≤ Real.log (2 * ((aux_psf_cells d 0).card : ℝ)) := by
  have h : (2 * ((aux_psf_cells d 0).card : ℝ)) = ((2 * (aux_psf_cells d 0).card : ℕ) : ℝ) := by
    push_cast; ring
  rw [h]
  exact Real.log_natCast_nonneg _

/-- The model-uniform `L^{2q0}` bound of the Draw coordinate (sum of the four clause-(5) bounds with
`σ ≤ 1 + d`). -/
def aux_lem_prefix_limit_raw_BD (d : ℕ) (s : ℝ) (q0 : ℕ) : ℝ :=
  1 + (∑' L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * ((1 + (d : ℝ)) *
      (2 * ((q0 : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))) +
    ((1 + (d : ℝ)) * (2 * ((q0 : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3)) +
      (1 + (d : ℝ)) * (2 * ((d : ℝ) * Real.log 3)) * (8 / s)) +
    3 / 2 * ((1 + (d : ℝ)) * (2 * ((q0 : ℝ) + 1 + Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))

theorem aux_lem_prefix_limit_raw_t2_summable (d : ℕ) (s : ℝ) (hs : 0 < s) (σ : ℝ) (q0 : ℕ) :
    Summable (fun L : ℕ => (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) *
        ((L : ℝ) * (σ * (2 * ((q0 : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))) := by
  refine (aux_lem_prefix_limit_actual_coordinate_cauchy_rpow_neg_linear_sq_summable s
    (σ * (2 * ((q0 : ℝ) + 1 + Real.log 3)))
    (σ * (2 * ((d : ℝ) * Real.log 3))) hs).congr (fun L => ?_)
  push_cast
  ring

theorem aux_lem_prefix_limit_raw_Draw_bound {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (hM1 : M.delta ≤ 1)
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
    (N : ℕ) (n : ℤ) (z : Vec d) (q0 : ℕ) (hq0 : 1 ≤ q0) :
    AEStronglyMeasurable (fun omega => if n ≤ (N : ℤ) then
        (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0)
      (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun omega => if n ≤ (N : ℤ) then
        (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0)
      ((2 * q0 : ℕ) : ℝ≥0∞) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_lem_prefix_limit_raw_BD d s q0) := by
  have hσ0 : 0 < aux_psf_sigma M := aux_psf_sigma_pos M
  have hd0 : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
  have hσ1 : aux_psf_sigma M ≤ 1 + (d : ℝ) := by
    unfold aux_psf_sigma
    simpa using mul_le_mul_of_nonneg_left hM1 hd0
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hq0r : (0 : ℝ) ≤ (q0 : ℝ) := Nat.cast_nonneg q0
  have hr : (1 : ℝ≥0∞) ≤ ((2 * q0 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_one, Nat.cast_le]; omega
  have hmeas := dsc_raw_aemeas M s eps (chaosSampleLaw M).toMeasure eta
    (fun N => prefix_eta_aemeasurable M eta hEta N) F Praw Rraw Draw Z rawGood hPrimitive
    N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
  refine aux_lem_prefix_limit_raw_guard _ (n ≤ (N : ℤ)) _ _ _
    (fun _ => hmeas.aestronglyMeasurable) (fun hn => ?_)
  -- the a.s. four-term split of clause (5)
  have hsplit := aux_lem_prefix_limit_actual_coordinate_cauchy_Draw_value_split M s eps eta
    F Praw Rraw Draw Z rawGood hPrimitive
    (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_ne_top M s hs k w om)
    (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top s k w om)
    (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_ne_top s k w om)
    n z
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_ne_top M eta hEta
      (fun N => ((N : ℤ) - n).toNat) (fun N => (3 : ℝ) ^ N • z))
  have hae : (fun omega => (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal)
      =ᵐ[(chaosSampleLaw M).toMeasure] fun omega =>
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)).toReal +
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)).toReal +
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)).toReal +
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)).toReal := by
    filter_upwards [hsplit] with omega hω
    have h := hω N
    simp only [if_pos hn] at h
    exact h
  rw [eLpNorm_congr_ae hae]
  have hm234 := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable M s eta
    hEta N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)
  -- the four bounds
  have hbank : ∀ (N i n : ℕ) (w : Vec d) (q : ℕ), 1 ≤ q →
      eLpNorm (fun omega : BilateralField d => aux_prefix_bank_maxObs i n w (eta N omega))
        ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_psf_sigma M) * ENNReal.ofReal (2 * ((q : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) :=
    fun N i n w q hq =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_eLpNorm_linear M eta hEta
        (aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_even_moment_log M eta hEta)
        N i n w q hq
  have hb1 : eLpNorm (fun omega : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega)).toReal) ((2 * q0 : ℕ) : ℝ≥0∞)
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal 1 := by
    have hDt1meas : AEStronglyMeasurable
        (fun omega : BilateralField d =>
          (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat
            ((3 : ℝ) ^ N • z) (eta N omega)).toReal) (chaosSampleLaw M).toMeasure := by
      simpa only [aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1] using!
        ((ENNReal.measurable_toReal.comp (aux_lem_prefix_limit_actual_Dsc_first_meas M s _ _)).comp_aemeasurable
          (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
    refine (eLpNorm_le_of_ae_bound (C := 1) hDt1meas ?_).trans ?_
    · refine Eventually.of_forall (fun omega => ?_)
      have hle : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega) ≤ 1 := by
        simpa only [aux_psf_Jval] using! aux_psf_Dterm1_le_one M s hs ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (hle.trans ENNReal.ofReal_one.symm.le)
    · rw [measure_univ, ENNReal.one_rpow, one_mul]
  have hb2 : eLpNorm (fun omega : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega)).toReal) ((2 * q0 : ℕ) : ℝ≥0∞)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (∑' L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * ((1 + (d : ℝ)) *
        (2 * ((q0 : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3))))) := by
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hm234.1]
    refine (aux_lem_prefix_limit_actual_coordinate_cauchy_t2_eLpNorm_uniform M s eta
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
      q0 hq0
      (fun N k j w => aux_lem_prefix_limit_actual_coordinate_cauchy_t2_inner_eLpNorm_le
        M eta hEta hbank N k j w q0 hq0)
      (aux_lem_prefix_limit_raw_t2_summable d s hs (aux_psf_sigma M) q0) hσ0 N _ _).trans ?_
    refine ENNReal.ofReal_le_ofReal (Summable.tsum_le_tsum (fun L => ?_)
      (aux_lem_prefix_limit_raw_t2_summable d s hs (aux_psf_sigma M) q0)
      (aux_lem_prefix_limit_raw_t2_summable d s hs (1 + (d : ℝ)) q0))
    have hc : 0 ≤ 2 * ((q0 : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3) := by positivity
    have h3 : 0 ≤ (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) := by positivity
    have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hσ1 hc) hL) h3
  have hb3 : eLpNorm (fun omega : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega)).toReal) ((2 * q0 : ℕ) : ℝ≥0∞)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((1 + (d : ℝ)) * (2 * ((q0 : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3)) +
        (1 + (d : ℝ)) * (2 * ((d : ℝ) * Real.log 3)) * (8 / s)) := by
    refine (aux_lem_prefix_limit_actual_coordinate_cauchy_t3_eLpNorm_le M s eta hEta hbank
      N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) q0 hq0).trans (ENNReal.ofReal_le_ofReal ?_)
    set k : ℕ := ((N : ℤ) - n).toNat
    have heq : aux_psf_sigma M * (2 * ((q0 : ℝ) + 1 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)) =
        aux_psf_sigma M * (2 * ((q0 : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3)) +
          aux_psf_sigma M * (2 * ((d : ℝ) * Real.log 3)) * (k : ℝ) := by
      push_cast; ring
    rw [heq]
    refine (aux_lem_prefix_limit_raw_t3_term_le s hs _ _ (by positivity) (by positivity) k).trans ?_
    have hA : 0 ≤ 2 * ((q0 : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3) := by positivity
    have hB : 0 ≤ 2 * ((d : ℝ) * Real.log 3) * (8 / s) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hσ1 hA, mul_le_mul_of_nonneg_right hσ1 hB]
  have hb4 : eLpNorm (fun omega : BilateralField d =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega)).toReal) ((2 * q0 : ℕ) : ℝ≥0∞)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3 / 2 * ((1 + (d : ℝ)) * (2 * ((q0 : ℝ) + 1 +
        Real.log (2 * ((aux_psf_cells d 0).card : ℝ)))))) := by
    refine (aux_lem_prefix_limit_actual_coordinate_cauchy_t4_eLpNorm_uniform M eta hEta
      (fun k w om => aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_le_bank_tsum k w om)
      N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) q0 hq0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hX : 0 ≤ 2 * ((q0 : ℝ) + 1 + Real.log (2 * ((aux_psf_cells d 0).card : ℝ))) := by
      have := aux_lem_prefix_limit_raw_log_cells_nonneg d
      positivity
    have := mul_le_mul_of_nonneg_right hσ1 hX
    linarith
  refine (aux_lem_prefix_limit_raw_eLpNorm_add4_le _ _ hr _ _ _ _
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_aestronglyMeasurable M s eta hEta N _ _)
    hm234.1 hm234.2.1 hm234.2.2 _ _ _ _ hb1 hb2 hb3 hb4).trans (le_of_eq ?_)
  have hT2 : 0 ≤ ∑' L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * ((1 + (d : ℝ)) *
      (2 * ((q0 : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3)))) :=
    tsum_nonneg (fun L => by positivity)
  have hT3 : 0 ≤ (1 + (d : ℝ)) * (2 * ((q0 : ℝ) + 1 + ((d : ℝ) + 1) * Real.log 3)) +
      (1 + (d : ℝ)) * (2 * ((d : ℝ) * Real.log 3)) * (8 / s) := by positivity
  have hT4 : 0 ≤ 3 / 2 * ((1 + (d : ℝ)) * (2 * ((q0 : ℝ) + 1 +
      Real.log (2 * ((aux_psf_cells d 0).card : ℝ))))) := by
    have := aux_lem_prefix_limit_raw_log_cells_nonneg d
    positivity
  unfold aux_lem_prefix_limit_raw_BD
  rw [ENNReal.ofReal_add (by positivity) hT4, ENNReal.ofReal_add (by positivity) hT3,
    ENNReal.ofReal_add zero_le_one hT2]

/-- The model-uniform `L^{2q0}` bound of the field coordinate (`M.delta ≤ 1`). -/
def aux_lem_prefix_limit_raw_BF (d : ℕ) (s : ℝ) (q0 : ℕ) : ℝ :=
  (1 + (d : ℝ)) * 1 * ∑' j : ℕ,
    (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
      (2 * ((q0 : ℝ) + 1 + prefix_log_card d j))

/-- The model-uniform `L^p` bound of the product coordinate, `p ∈ insert 1 moments`. -/
def aux_lem_prefix_limit_raw_BP (d : ℕ) (s : ℝ) (moments : Finset ℝ) : ℝ≥0∞ :=
  (∑' j : ℕ, ENNReal.ofReal (aux_prefix_praw_term d s (aux_prefix_praw_R d s moments)
    ((1 + (d : ℝ)) * aux_prefix_praw_delta0 d s moments)
    (((7 : ℝ) ^ d * (Real.exp ((6 * aux_prefix_praw_R d s moments + 1) ^ 2 *
      ((1 + (d : ℝ)) * aux_prefix_praw_delta0 d s moments) ^ 2 / 4) * 2)) ^
        (9 * aux_prefix_praw_R d s moments / (6 * aux_prefix_praw_R d s moments + 1))) j)) ^
    (1 / aux_prefix_praw_R d s moments)

/-- The model-uniform bound of the matched-response coordinate at its order `q` (`M.delta ≤ 1`). -/
def aux_lem_prefix_limit_raw_BR (d : ℕ) (s : ℝ) (moments : Finset ℝ) : ℝ :=
  aux_prefix_rraw_K d s (aux_prefix_rraw_q d s moments) *
    aux_prefix_rraw_rho d s (aux_prefix_rraw_q d s moments) ^ (0 + 1) *
    (aux_prefix_rraw_C d * aux_prefix_rraw_q d s moments *
      Real.log (2 + aux_prefix_rraw_q d s moments) * 1)

theorem aux_lem_prefix_limit_raw_BP_ne_top {d : ℕ} [NeZero d] (s : ℝ) (hs : 0 < s)
    (moments : Finset ℝ) : aux_lem_prefix_limit_raw_BP d s moments ≠ ⊤ := by
  have hR := aux_prefix_praw_R_one_le d s hs moments
  have hRs := aux_prefix_praw_R_budget d s hs moments
  have hR0 : 0 < aux_prefix_praw_R d s moments := by linarith
  have hd1 : (0 : ℝ) < 1 + (d : ℝ) := by positivity
  have hσ : 16 * aux_prefix_praw_R d s moments *
      ((1 + (d : ℝ)) * aux_prefix_praw_delta0 d s moments) ^ 2 ≤ s := by
    have hx : (1 + (d : ℝ)) * aux_prefix_praw_delta0 d s moments =
        Real.sqrt (s / (16 * aux_prefix_praw_R d s moments)) := by
      unfold aux_prefix_praw_delta0
      field_simp
    rw [hx, Real.sq_sqrt (by positivity)]
    have h16 : 0 < 16 * aux_prefix_praw_R d s moments := by positivity
    rw [mul_div_cancel₀ _ h16.ne']
  have hCB : (0 : ℝ) ≤ ((7 : ℝ) ^ d * (Real.exp ((6 * aux_prefix_praw_R d s moments + 1) ^ 2 *
      ((1 + (d : ℝ)) * aux_prefix_praw_delta0 d s moments) ^ 2 / 4) * 2)) ^
        (9 * aux_prefix_praw_R d s moments / (6 * aux_prefix_praw_R d s moments + 1)) := by
    positivity
  unfold aux_lem_prefix_limit_raw_BP
  refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (aux_prefix_praw_term_nonneg d s _ _ _ hCB)
    (aux_prefix_praw_term_summable d s _ _ _ hs hR hRs hσ hCB)]
  exact ENNReal.ofReal_ne_top

theorem aux_lem_prefix_limit_raw_BR_nonneg (d : ℕ) (s : ℝ) (hs : 0 < s) (moments : Finset ℝ) :
    0 ≤ aux_lem_prefix_limit_raw_BR d s moments := by
  have hq2 := aux_prefix_rraw_two_le_q d s moments
  have hq0 : 0 < aux_prefix_rraw_q d s moments := by linarith
  have hsq := aux_prefix_rraw_margin d s hs moments
  have hρ0 := aux_prefix_rraw_rho_pos d s (aux_prefix_rraw_q d s moments)
  have hρ1 := aux_prefix_rraw_rho_lt_one d s (aux_prefix_rraw_q d s moments) hq0 hsq
  have hK : 0 ≤ aux_prefix_rraw_K d s (aux_prefix_rraw_q d s moments) := by
    unfold aux_prefix_rraw_K
    exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  have hC := (aux_prefix_rraw_C_spec d).1
  have hlog : 0 ≤ Real.log (2 + aux_prefix_rraw_q d s moments) := Real.log_nonneg (by linarith)
  unfold aux_lem_prefix_limit_raw_BR
  have := hρ0.le
  positivity

theorem aux_lem_prefix_limit_raw_BF_nonneg (d : ℕ) (s : ℝ) (q0 : ℕ) :
    0 ≤ aux_lem_prefix_limit_raw_BF d s q0 := by
  unfold aux_lem_prefix_limit_raw_BF
  refine mul_nonneg (by positivity) (tsum_nonneg (fun j => ?_))
  have := prefix_log_card_nonneg d j
  positivity

theorem aux_lem_prefix_limit_raw_BD_nonneg (d : ℕ) (s : ℝ) (hs : 0 < s) (q0 : ℕ) :
    0 ≤ aux_lem_prefix_limit_raw_BD d s q0 := by
  have hT2 : 0 ≤ ∑' L : ℕ, (3 : ℝ) ^ (-(s / 8) * (L : ℝ)) * ((L : ℝ) * ((1 + (d : ℝ)) *
      (2 * ((q0 : ℝ) + 1 + ((d * L + 1 : ℕ) : ℝ) * Real.log 3)))) :=
    tsum_nonneg (fun L => by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity)
  have hlog3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  have hlc := aux_lem_prefix_limit_raw_log_cells_nonneg d
  unfold aux_lem_prefix_limit_raw_BD
  positivity

theorem aux_lem_prefix_limit_raw_Rraw_bound {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (moments : Finset ℝ)
    (hMr : M.delta ≤ aux_prefix_rraw_delta0 d s moments) (hM1 : M.delta ≤ 1)
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
    (N : ℕ) (n : ℤ) (z : Vec d) :
    AEStronglyMeasurable (fun omega => if n ≤ (N : ℤ) then
        (Rraw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0)
      (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun omega => if n ≤ (N : ℤ) then
        (Rraw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal else 0)
      (ENNReal.ofReal (aux_prefix_rraw_q d s moments)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_lem_prefix_limit_raw_BR d s moments) := by
  refine aux_lem_prefix_limit_raw_guard _ (n ≤ (N : ℤ)) _ _ _
    (fun _ => (aux_lem_prefix_limit_actual_Rraw_aemeas M s eps (chaosSampleLaw M).toMeasure eta
      (fun N => prefix_eta_aemeasurable M eta hEta N) F Praw Rraw Draw Z rawGood hPrimitive
      N _ _).aestronglyMeasurable) (fun _ => ?_)
  have hq2 := aux_prefix_rraw_two_le_q d s moments
  have hq1 : 1 ≤ aux_prefix_rraw_q d s moments := by linarith
  have hq0 : 0 < aux_prefix_rraw_q d s moments := by linarith
  have hsq := aux_prefix_rraw_margin d s hs moments
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hbank := (aux_prefix_rraw_delta0_spec d s moments).2 M hdelta hMr
  have hC := (aux_prefix_rraw_C_spec d).1
  have hlog : 0 ≤ Real.log (2 + aux_prefix_rraw_q d s moments) := Real.log_nonneg (by linarith)
  have hb : 0 ≤ aux_prefix_rraw_C d * aux_prefix_rraw_q d s moments *
      Real.log (2 + aux_prefix_rraw_q d s moments) * M.delta ^ 2 := by positivity
  have hgood : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Rraw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega =
        aux_prefix_rraw_Rset M s (eta N omega) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) := by
    filter_upwards [hPrimitive] with omega hω
    obtain ⟨_, _, _, _, _, _, hR, _⟩ := hω N
    exact hR _ _
  have htail := (aux_prefix_rraw_tail_eLpNorm_le M s eta hEta _ _ hq1 hbank N
    ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) 0).trans
    (aux_prefix_rraw_tail_numeric d s _ hq0 hsq _ hb 0 ((N : ℤ) - n).toNat)
  refine (eLpNorm_mono_ae_real
    (aux_lem_prefix_limit_actual_Rraw_aemeas M s eps (chaosSampleLaw M).toMeasure eta
      (fun N => prefix_eta_aemeasurable M eta hEta N) F Praw Rraw Draw Z rawGood hPrimitive
      N _ _).aestronglyMeasurable ?_).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hgood] with omega hω
    rw [hω, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact aux_prefix_rraw_Rset_toReal_le_tail_zero M s _ _ _
  · have hρ0 := aux_prefix_rraw_rho_pos d s (aux_prefix_rraw_q d s moments)
    have hρ1 := aux_prefix_rraw_rho_lt_one d s (aux_prefix_rraw_q d s moments) hq0 hsq
    have hK : 0 ≤ aux_prefix_rraw_K d s (aux_prefix_rraw_q d s moments) := by
      unfold aux_prefix_rraw_K
      exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have hδ2 : M.delta ^ 2 ≤ 1 := by nlinarith
    unfold aux_lem_prefix_limit_raw_BR
    have hKρ : 0 ≤ aux_prefix_rraw_K d s (aux_prefix_rraw_q d s moments) *
        aux_prefix_rraw_rho d s (aux_prefix_rraw_q d s moments) ^ (0 + 1) := by
      have := hρ0.le; positivity
    refine mul_le_mul_of_nonneg_left ?_ hKρ
    exact mul_le_mul_of_nonneg_left hδ2 (by positivity)

/-- G8 raw half, per coordinate: every raw coordinate has, for every prescribed moment, a moment
bound by one constant chosen after the finite moment list (paper 2746--2763). -/
def aux_lem_prefix_limit_raw_K (d : ℕ) (s : ℝ) (moments : Finset ℝ) (q0 : ℕ) : ℝ :=
  aux_lem_prefix_limit_raw_BF d s q0 + (aux_lem_prefix_limit_raw_BP d s moments).toReal +
    aux_lem_prefix_limit_raw_BR d s moments + aux_lem_prefix_limit_raw_BD d s q0 + 3 + 1

theorem aux_lem_prefix_limit_raw_all {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (moments : Finset ℝ) (q0 : ℕ) (hq0 : 1 ≤ q0)
    (hq0P : ∀ p ∈ insert 1 moments, p ≤ ((2 * q0 : ℕ) : ℝ))
    (hMP : M.delta ≤ aux_prefix_praw_delta0 d s moments)
    (hMr : M.delta ≤ aux_prefix_rraw_delta0 d s moments) (hM1 : M.delta ≤ 1)
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
    (p : ℝ) (hp : p ∈ insert 1 moments) (N : ℕ) (n : ℤ) (z : Vec d) (j : Fin 5) :
    MemLp (fun omega => if n ≤ (N : ℤ) then
            let m := ((N : ℤ) - n).toNat
            let w := (3 : ℝ) ^ N • z
            if j = 0 then (F N m w omega).toReal
            else if j = 1 then (Praw N m w omega).toReal
            else if j = 2 then (Rraw N m w omega).toReal
            else if j = 3 then (Draw N m w omega).toReal
            else Z N m w omega
          else 0) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun omega => if n ≤ (N : ℤ) then
            let m := ((N : ℤ) - n).toNat
            let w := (3 : ℝ) ^ N • z
            if j = 0 then (F N m w omega).toReal
            else if j = 1 then (Praw N m w omega).toReal
            else if j = 2 then (Rraw N m w omega).toReal
            else if j = 3 then (Draw N m w omega).toReal
            else Z N m w omega
          else 0) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aux_lem_prefix_limit_raw_K d s moments q0) := by
  have hBF := aux_lem_prefix_limit_raw_BF_nonneg d s q0
  have hBP := ENNReal.toReal_nonneg (a := aux_lem_prefix_limit_raw_BP d s moments)
  have hBR := aux_lem_prefix_limit_raw_BR_nonneg d s hs moments
  have hBD := aux_lem_prefix_limit_raw_BD_nonneg d s hs q0
  have hpq : ENNReal.ofReal p ≤ ((2 * q0 : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hq0P p hp)
  by_cases hj0 : j = 0
  · subst hj0
    obtain ⟨hm, hb⟩ := aux_lem_prefix_limit_raw_guard (chaosSampleLaw M).toMeasure (n ≤ (N : ℤ))
      (fun omega => (F N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal)
      ((2 * q0 : ℕ) : ℝ≥0∞) (ENNReal.ofReal (aux_lem_prefix_limit_raw_BF d s q0))
      (fun _ => (aux_lem_prefix_limit_actual_Fsc_raw_aemeas M s eps (chaosSampleLaw M).toMeasure
        eta (fun N => prefix_eta_aemeasurable M eta hEta N) F Praw Rraw Draw Z rawGood hPrimitive
        N _ _).aestronglyMeasurable)
      (fun _ => aux_lem_prefix_limit_F_eLpNorm_uniform M s eps hs 1 hM1 eta hEta
        F Praw Rraw Draw Z rawGood hPrimitive N _ _ q0 hq0)
    obtain ⟨h1, h2⟩ := aux_lem_prefix_limit_raw_memLp_of_le _ _ hm p _ hpq _ ENNReal.ofReal_ne_top hb
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    unfold aux_lem_prefix_limit_raw_K
    linarith
  by_cases hj1 : j = 1
  · subst hj1
    have hR := aux_prefix_praw_R_one_le d s hs moments
    obtain ⟨hm, hb⟩ := aux_lem_prefix_limit_raw_guard (chaosSampleLaw M).toMeasure (n ≤ (N : ℤ))
      (fun omega => (Praw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal)
      (ENNReal.ofReal p) (aux_lem_prefix_limit_raw_BP d s moments)
      (fun _ => (aux_lem_prefix_limit_actual_Praw_raw_aemeas M s eps (chaosSampleLaw M).toMeasure
        eta (fun N => prefix_eta_aemeasurable M eta hEta N) F Praw Rraw Draw Z rawGood hPrimitive
        N _ _).aestronglyMeasurable)
      (fun _ => aux_lem_prefix_limit_Praw_eLpNorm_uniform M s eps _ hR _ hMP eta hEta
        F Praw Rraw Draw Z rawGood hPrimitive N _ _ p (aux_prefix_praw_le_R d s hs moments p hp))
    have hne := aux_lem_prefix_limit_raw_BP_ne_top (d := d) s hs moments
    refine ⟨lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hne), hb.trans ?_⟩
    rw [← ENNReal.ofReal_toReal hne]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold aux_lem_prefix_limit_raw_K
    linarith
  by_cases hj2 : j = 2
  · subst hj2
    obtain ⟨hm, hb⟩ := aux_lem_prefix_limit_raw_Rraw_bound M s eps hs moments hMr hM1 eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N n z
    have hpr : ENNReal.ofReal p ≤ ENNReal.ofReal (aux_prefix_rraw_q d s moments) :=
      ENNReal.ofReal_le_ofReal (aux_prefix_rraw_lt_q d s moments p hp).le
    obtain ⟨h1, h2⟩ := aux_lem_prefix_limit_raw_memLp_of_le _ _ hm p _ hpr _ ENNReal.ofReal_ne_top hb
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    unfold aux_lem_prefix_limit_raw_K
    linarith
  by_cases hj3 : j = 3
  · subst hj3
    obtain ⟨hm, hb⟩ := aux_lem_prefix_limit_raw_Draw_bound M s eps hs hM1 eta hEta
      F Praw Rraw Draw Z rawGood hPrimitive N n z q0 hq0
    obtain ⟨h1, h2⟩ := aux_lem_prefix_limit_raw_memLp_of_le _ _ hm p _ hpq _ ENNReal.ofReal_ne_top hb
    refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    unfold aux_lem_prefix_limit_raw_K
    linarith
  have hj4 : j = 4 := by
    have key : ∀ x : Fin 5, ¬x = 0 → ¬x = 1 → ¬x = 2 → ¬x = 3 → x = 4 := by decide
    exact key j hj0 hj1 hj2 hj3
  subst hj4
  have hm := (aux_lem_prefix_limit_raw_guard (chaosSampleLaw M).toMeasure (n ≤ (N : ℤ))
      (fun omega => Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega) (ENNReal.ofReal p) ⊤
      (fun _ => (actual_Z_aemeas M s eps (chaosSampleLaw M).toMeasure
        eta (fun N => prefix_eta_aemeasurable M eta hEta N) F Praw Rraw Draw Z rawGood hPrimitive
        N _ _).aestronglyMeasurable) (fun _ => le_top)).1
  have hb := aux_lem_prefix_limit_Z_value_eLpNorm_le M s eps eta hEta
    F Praw Rraw Draw Z rawGood hPrimitive N n z p
  refine ⟨lt_of_le_of_lt hb ENNReal.ofReal_lt_top, hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  unfold aux_lem_prefix_limit_raw_K
  linarith

end Paper

end LemPrefixLimitRawHelpers

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper


theorem aux_lem_prefix_limit_kappa_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (J : ℕ) :
    0 < Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M J := by
  exact mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M J)

theorem aux_lem_prefix_limit_positivity {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)) :
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun n z omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) z
        else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) z
    let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun N n z omega => kappa ((N : ℤ) - n).toNat / kappa N *
        Real.exp (H omega z + retained n z omega)
    ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (omega : BilateralField d),
      n ≤ (N : ℤ) → 0 < reference N n z omega ∧
      0 < I.lam z ((3 : ℝ) ^ (-n)) (sidePos n)
        (Lane4.cutoffPositiveCoefficient M H omega N z (sidePos n))
        z ((3 : ℝ) ^ (-n)) sigma 2 := by
  dsimp only
  intro N n z omega hn
  refine ⟨?_, ?_⟩
  · exact mul_pos (div_pos (aux_lem_prefix_limit_kappa_pos M _) (aux_lem_prefix_limit_kappa_pos M N))
      (Real.exp_pos _)
  · exact I.lam_pos z _ (sidePos n) _ z _ sigma 2



/-- The enlarged finite moment list: it contains `insert 1 moments` and every doubled prescribed moment, so that
the uniform bank is available at an order strictly above each prescribed one. -/
theorem aux_lem_prefix_limit_moments2 (moments : Finset ℝ) (hmom : ∀ p ∈ moments, 1 ≤ p) :
    ∃ m2 : Finset ℝ, (∀ p ∈ m2, 1 ≤ p) ∧ (∀ p ∈ insert 1 moments, p ∈ insert 1 m2) ∧
      (∀ p ∈ insert 1 moments, 2 * p ∈ insert 1 m2) := by
  have hone : ∀ p ∈ insert 1 moments, 1 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · exact le_of_eq h.symm
    · exact hmom p h
  refine ⟨moments ∪ (insert 1 moments).image (fun p => 2 * p), ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hmom p h
    · obtain ⟨r, hr, hrp⟩ := Finset.mem_image.mp h
      have := hone r hr
      linarith
  · intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
  · intro p hp
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))

/-- Convergence in probability plus a uniform bound at the doubled order gives an `L^p` limit
(paper 2749--2752: the response coordinates converge strongly by uniform higher moments). -/
theorem aux_lem_prefix_limit_lp_limit_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ) (hp1 : 1 ≤ p)
    (f : ℕ → Ω → ℝ) (lim : Ω → ℝ) (hlim : TendstoInMeasure μ f atTop lim) (K2 : ℝ)
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) μ)
    (hf2 : ∀ n, eLpNorm (f n) (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal K2) :
    ∃ g : Ω → ℝ, AEStronglyMeasurable g μ ∧
      Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hcim := aux_prefix_rraw_cim_of_tendstoInMeasure μ f lim hlim
  have hcau : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n n' : ℕ, n₀ ≤ n → n₀ ≤ n' →
      eLpNorm (fun ω => f n ω - f n' ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε :=
    fun ε hε => aux_prefix_rraw_Lp_cauchy_of_cim μ p (2 * p) hp1 (by linarith) f
      (fun n => (hf n).aestronglyMeasurable) (ENNReal.ofReal K2) ENNReal.ofReal_ne_top hf2 hcim ε hε
  obtain ⟨g, hg, hgt⟩ := aux_lem_prefix_limit_lp_limit_of_cauchy μ p hp1 f hf hcau
  exact ⟨g, hg.aestronglyMeasurable, hgt⟩

/-- G8, raw half (typed goal): cutoff-, position- and model-uniform moments of the five raw score coordinates
(`Sum.inl`), the constants chosen after the finite moment list and before the model (paper 2746--2763). -/
theorem aux_lem_prefix_limit_raw_moments
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
    ∃ deltaR : ℝ, 0 < deltaR ∧ ∃ KR : ℝ → ℝ, (∀ p ∈ insert 1 moments, 0 < KR p) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaR →
        ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)),
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
        ∀ p ∈ insert 1 moments, ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (j : Fin 5),
          MemLp (value N n z (Sum.inl j)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (value N n z (Sum.inl j)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (KR p) := by
  obtain ⟨q0, hq0, hq0P⟩ := aux_lem_prefix_limit_raw_order moments
  have hK : 0 < aux_lem_prefix_limit_raw_K d s moments q0 := by
    have hBF := aux_lem_prefix_limit_raw_BF_nonneg d s q0
    have hBP := ENNReal.toReal_nonneg (a := aux_lem_prefix_limit_raw_BP d s moments)
    have hBR := aux_lem_prefix_limit_raw_BR_nonneg d s hs.1 moments
    have hBD := aux_lem_prefix_limit_raw_BD_nonneg d s hs.1 q0
    unfold aux_lem_prefix_limit_raw_K
    linarith
  refine ⟨min (min (aux_prefix_praw_delta0 d s moments) (aux_prefix_rraw_delta0 d s moments)) 1,
    lt_min (lt_min (aux_prefix_praw_delta0_pos d s hs.1 moments)
      (aux_prefix_rraw_delta0_pos d s moments)) one_pos,
    fun _ => aux_lem_prefix_limit_raw_K d s moments q0, fun _ _ => hK, ?_⟩
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
    kappa retained reference Test value p hp N n z j
  exact aux_lem_prefix_limit_raw_all M s eps hs.1 moments q0 hq0 hq0P
    (hM.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (hM.trans ((min_le_left _ _).trans (min_le_right _ _)))
    (hM.trans (min_le_right _ _)) eta hEta F Praw Rraw Draw Z rawGood hPrim p hp N n z j

/- G8 response half: `aux_lem_prefix_limit_response_moments` is stated and proved below, after the
   G9 helper lemmas it depends on (see the "G8 response moments (relocated proof)" block before
   `lem_prefix_limit`).  Header unchanged. -/






theorem aux_lem_prefix_limit_g9_tauSq_nonneg {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M) :
    0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
  obtain ⟨h1, h2⟩ := Rm.ahom_ordering 0 1 (by norm_num)
  have hpos := ahom_pos M 0
  have h2' : ahom M 0 ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((1 : ℝ) - 0)) * ahom M 0 := by
    calc ahom M 0
        ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((1 : ℝ) - 0)) * ahom M 1 := by
          simpa using h2
      _ ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((1 : ℝ) - 0)) * ahom M 0 :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have h3 : (1 : ℝ) ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((1 : ℝ) - 0)) := by
    by_contra hcon
    push_neg at hcon
    have hlt : Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((1 : ℝ) - 0)) * ahom M 0 <
        1 * ahom M 0 := mul_lt_mul_of_pos_right hcon hpos
    rw [one_mul] at hlt
    linarith [h2']
  have h4 : Real.exp 0 ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((1 : ℝ) - 0)) := by
    rw [Real.exp_zero]; exact h3
  have h5 := Real.exp_le_exp.mp h4
  linarith [h5]



theorem aux_lem_prefix_limit_g9_ahom_ratio_bound {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (A B : ℕ) (hAB : A ≤ B) :
    Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A))) ≤ ahom M B / ahom M A ∧
      ahom M B / ahom M A ≤ 1 := by
  have hApos := ahom_pos M A
  rcases eq_or_lt_of_le hAB with heq | hlt
  · subst heq
    simp [div_self (ne_of_gt hApos)]
  · obtain ⟨h1, h2⟩ := Rm.ahom_ordering A B hlt
    refine ⟨?_, (div_le_one hApos).mpr h1⟩
    rw [le_div_iff₀ hApos, mul_comm]
    have hE : Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A)) *
        Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A))) = 1 := by
      rw [← Real.exp_add]; simp
    calc ahom M A * Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A)))
        ≤ (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A)) * ahom M B) *
            Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A))) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = ahom M B * (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A)) *
            Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A)))) := by ring
      _ = ahom M B := by rw [hE, mul_one]

/-- Generic helper (PROVEN): the reciprocal of a ratio `x ∈ [exp(-c), 1]` (`c ≥ 0`) lies in
`[1, exp(c)]`. -/
theorem aux_lem_prefix_limit_g9_ratio_inv_env {x c : ℝ} (hx0 : 0 < x)
    (hlo : Real.exp (-c) ≤ x) (hhi : x ≤ 1) :
    (1 : ℝ) ≤ x⁻¹ ∧ x⁻¹ ≤ Real.exp c := by
  constructor
  · rw [show x⁻¹ = 1 / x from (one_div x).symm, le_div_iff₀ hx0]
    linarith
  · rw [show x⁻¹ = 1 / x from (one_div x).symm, div_le_iff₀ hx0]
    calc (1 : ℝ) = Real.exp c * Real.exp (-c) := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp c * x := mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le

/-- G9-1' (PROVEN): the symmetric (any `A, B`, absolute-gap) form of G9-1. -/
theorem aux_lem_prefix_limit_g9_ahom_ratio_bound_any {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M) (A B : ℕ) :
    Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(A : ℝ) - B|)) ≤ ahom M A / ahom M B ∧
      ahom M A / ahom M B ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(A : ℝ) - B|) := by
  rcases le_total A B with hAB | hAB
  · obtain ⟨hlo, hhi⟩ := aux_lem_prefix_limit_g9_ahom_ratio_bound M Rm A B hAB
    have hApos := ahom_pos M A
    have hcast : (A : ℝ) ≤ B := by exact_mod_cast hAB
    have habs : |(A : ℝ) - B| = (B : ℝ) - A := by rw [abs_of_nonpos (by linarith)]; ring
    have hratio_pos : (0 : ℝ) < ahom M B / ahom M A := div_pos (ahom_pos M B) hApos
    obtain ⟨hi1, hi2⟩ := aux_lem_prefix_limit_g9_ratio_inv_env
      (x := ahom M B / ahom M A)
      (c := 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A)) hratio_pos hlo hhi
    rw [inv_div] at hi1 hi2
    rw [habs]
    have htau := aux_lem_prefix_limit_g9_tauSq_nonneg M Rm
    have hone : Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((B : ℝ) - A))) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [htau, hcast])
    exact ⟨le_trans hone hi1, hi2⟩
  · obtain ⟨hlo, hhi⟩ := aux_lem_prefix_limit_g9_ahom_ratio_bound M Rm B A hAB
    have hcast : (B : ℝ) ≤ A := by exact_mod_cast hAB
    have habs : |(A : ℝ) - B| = (A : ℝ) - B := abs_of_nonneg (by linarith)
    rw [habs]
    have htau := aux_lem_prefix_limit_g9_tauSq_nonneg M Rm
    have hone : (1 : ℝ) ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [htau, hcast])
    exact ⟨hlo, hhi.trans hone⟩

/-- Generic helper (PROVEN): the product of two positive quantities, each within a
symmetric exponential envelope, lies within the summed envelope. -/
theorem aux_lem_prefix_limit_g9_exp_env_mul {u v c1 c2 : ℝ}
    (hu1 : Real.exp (-c1) ≤ u) (hu2 : u ≤ Real.exp c1)
    (hv1 : Real.exp (-c2) ≤ v) (hv2 : v ≤ Real.exp c2) :
    Real.exp (-(c1 + c2)) ≤ u * v ∧ u * v ≤ Real.exp (c1 + c2) := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu1
  have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv1
  constructor
  · calc Real.exp (-(c1 + c2)) = Real.exp (-c1) * Real.exp (-c2) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ u * v := mul_le_mul hu1 hv1 (Real.exp_pos _).le hu0.le
  · calc u * v ≤ Real.exp c1 * Real.exp c2 := mul_le_mul hu2 hv2 hv0.le (Real.exp_pos _).le
      _ = Real.exp (c1 + c2) := by rw [← Real.exp_add]

/-- G9-2a (PROVEN): `Int.toNat` is `1`-Lipschitz, so the two clamped scale indices feeding
`kappa` in the "reference ratio" coordinate differ by at most `|mm - nn|`. -/
theorem aux_lem_prefix_limit_g9_toNat_diff_le (N : ℕ) (nn mm : ℤ) :
    |(((N : ℤ) - nn).toNat : ℝ) - (((N : ℤ) - mm).toNat : ℝ)| ≤ |(mm : ℝ) - nn| := by
  rcases le_total nn mm with h | h
  · have h1 : ((N : ℤ) - mm).toNat ≤ ((N : ℤ) - nn).toNat := by omega
    have h2 : (((N : ℤ) - nn).toNat : ℤ) - (((N : ℤ) - mm).toNat : ℤ) ≤ mm - nn := by omega
    have h1' : (((N : ℤ) - mm).toNat : ℝ) ≤ (((N : ℤ) - nn).toNat : ℝ) := by exact_mod_cast h1
    have h2' : (((N : ℤ) - nn).toNat : ℝ) - (((N : ℤ) - mm).toNat : ℝ) ≤ (mm : ℝ) - nn := by
      exact_mod_cast h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr h)]
    linarith
  · have h1 : ((N : ℤ) - nn).toNat ≤ ((N : ℤ) - mm).toNat := by omega
    have h2 : (((N : ℤ) - mm).toNat : ℤ) - (((N : ℤ) - nn).toNat : ℤ) ≤ nn - mm := by omega
    have h1' : (((N : ℤ) - nn).toNat : ℝ) ≤ (((N : ℤ) - mm).toNat : ℝ) := by exact_mod_cast h1
    have h2' : (((N : ℤ) - mm).toNat : ℝ) - (((N : ℤ) - nn).toNat : ℝ) ≤ (nn : ℝ) - mm := by
      exact_mod_cast h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr h)]
    linarith

/-- G9-2 (PROVEN): the deterministic `kappa`-ratio driving the "reference ratio" response
coordinate is bounded by an `N`-independent constant, uniformly in `N`, once the position,
offset and level are fixed (so `nn, mm` are fixed integers).  Matches `value`'s own
`if nn ≤ N ∧ mm ≤ N` guard, so the bound also covers the guard-false `0` branch. -/
theorem aux_lem_prefix_limit_g9_kappa_ratio_bounded {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M) (nn mm : ℤ) :
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
          kappa ((N : ℤ) - nn).toNat / kappa ((N : ℤ) - mm).toNat
        else 0) ∈ Set.Icc (0 : ℝ) C := by
  intro kappa
  have htau := aux_lem_prefix_limit_g9_tauSq_nonneg M Rm
  set k : ℝ := |(mm : ℝ) - nn| with hkdef
  have hk0 : 0 ≤ k := abs_nonneg _
  refine ⟨Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k), Real.exp_pos _, ?_⟩
  intro N
  by_cases hguard : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
  · rw [if_pos hguard]
    set A : ℕ := ((N : ℤ) - nn).toNat with hAdef
    set B : ℕ := ((N : ℤ) - mm).toNat with hBdef
    have hApos := ahom_pos M A
    have hBpos := ahom_pos M B
    have hkAB_pos : 0 < kappa A / kappa B :=
      div_pos (mul_pos (Real.exp_pos _) hApos) (mul_pos (Real.exp_pos _) hBpos)
    refine ⟨hkAB_pos.le, ?_⟩
    have hdiff : |(A : ℝ) - B| ≤ k := aux_lem_prefix_limit_g9_toNat_diff_le N nn mm
    obtain ⟨hle1, hle2⟩ := abs_le.mp hdiff
    have hexp_arg : ((A : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
        (((B : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B) := by ring
    have hkeq : kappa A / kappa B =
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) * (ahom M A / ahom M B) := by
      show (Real.exp (((A : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M A) /
          (Real.exp (((B : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M B) = _
      rw [← div_mul_div_comm, ← Real.exp_sub, hexp_arg]
    rw [hkeq]
    have hexp_env : Real.exp (-(SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)) ≤
          Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) ∧
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) ≤
          Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := by
      constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [hle1, hle2, htau]
    have hahom_env := aux_lem_prefix_limit_g9_ahom_ratio_bound_any M Rm A B
    have hwiden : Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)) ≤
          Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(A : ℝ) - B|)) ∧
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(A : ℝ) - B|) ≤
          Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := by
      constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [hdiff, htau]
    obtain ⟨e1, e2⟩ := aux_lem_prefix_limit_g9_exp_env_mul
        (c1 := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)
        (c2 := 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)
        hexp_env.1 hexp_env.2 (hwiden.1.trans hahom_env.1) (hahom_env.2.trans hwiden.2)
    calc Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) * (ahom M A / ahom M B)
        ≤ Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k +
            2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := e2
      _ ≤ Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := by
          apply Real.exp_le_exp.mpr; nlinarith
  · rw [if_neg hguard]
    exact ⟨le_refl 0, (Real.exp_pos _).le⟩

/-- G9-3 (PROVEN): algebraic identity for the "reference ratio" test coordinate -- its
entire `N`-dependence factors through the deterministic `kappa`-ratio, since the random
exponential factor `exp(H omega z + retained n z omega)` does not depend on `N`. Matches
`value`'s own guard exactly. -/
theorem aux_lem_prefix_limit_g9_value_ref_ratio_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (nn mm : ℤ)
    (z w : SpatialCoordinates d) :
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun n zz omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) zz
        else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) zz
    let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun N n zz omega => kappa ((N : ℤ) - n).toNat / kappa N *
        Real.exp (H omega zz + retained n zz omega)
    ∀ (N : ℕ) (omega : BilateralField d),
      (if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then reference N nn z omega / reference N mm w omega
        else 0) =
        (if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
            kappa ((N : ℤ) - nn).toNat / kappa ((N : ℤ) - mm).toNat else 0) *
          Real.exp (H omega z + retained nn z omega - (H omega w + retained mm w omega)) := by
  intro kappa retained reference N omega
  by_cases hguard : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
  · rw [if_pos hguard, if_pos hguard]
    have hkN : kappa N ≠ 0 := ne_of_gt (mul_pos (Real.exp_pos _) (ahom_pos M N))
    have hkmm : kappa ((N : ℤ) - mm).toNat ≠ 0 :=
      ne_of_gt (mul_pos (Real.exp_pos _) (ahom_pos M _))
    show (kappa ((N : ℤ) - nn).toNat / kappa N * Real.exp (H omega z + retained nn z omega)) /
        (kappa ((N : ℤ) - mm).toNat / kappa N * Real.exp (H omega w + retained mm w omega)) = _
    rw [Real.exp_sub]
    field_simp
  · rw [if_neg hguard, if_neg hguard, zero_mul]




theorem aux_lem_prefix_limit_g8b_layer_point_map_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℤ) (y : SpatialCoordinates d) :
    Measure.map (fun omega : BilateralField d => omega i y) (chaosSampleLaw M).toMeasure =
      Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g ((3 : ℝ) ^ (-i) • y))
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
  classical
  set forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
    with hmu0
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hpzapp : ∀ (w : NativeBilateralPotentialSample d),
      (pz w) i y = (w i) ((3 : ℝ) ^ (-i) • y) := by
    intro w
    show (layerScaling d i (forget (w i))) y = _
    simp [layerScaling, ContinuousMap.compRightContinuousMap, hforget]
    rfl
  have hevalmeas : Measurable (fun omega : BilateralField d => omega i y) :=
    (continuous_eval_const y).measurable.comp (measurable_pi_apply i)
  have hevalmeas0 : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      g ((3 : ℝ) ^ (-i) • y)) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _
  have hevalimeas : Measurable (fun w : NativeBilateralPotentialSample d => w i) :=
    measurable_pi_apply i
  have hmarg : Measure.map (fun w : NativeBilateralPotentialSample d => w i) mu0 =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    simpa [mu0] using Measure.infinitePi_map_eval
      (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) i
  calc Measure.map (fun omega : BilateralField d => omega i y) (chaosSampleLaw M).toMeasure
      = Measure.map (fun omega : BilateralField d => omega i y) (Measure.map pz mu0) := by
        rw [hpzmap]
    _ = Measure.map ((fun omega : BilateralField d => omega i y) ∘ pz) mu0 :=
        Measure.map_map hevalmeas hpzmeas
    _ = Measure.map (fun w : NativeBilateralPotentialSample d => (w i) ((3 : ℝ) ^ (-i) • y))
          mu0 := by
        congr 1
    _ = Measure.map ((fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          g ((3 : ℝ) ^ (-i) • y)) ∘ (fun w : NativeBilateralPotentialSample d => w i)) mu0 := rfl
    _ = Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          g ((3 : ℝ) ^ (-i) • y))
          (Measure.map (fun w : NativeBilateralPotentialSample d => w i) mu0) :=
        (Measure.map_map hevalmeas0 hevalimeas).symm
    _ = Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          g ((3 : ℝ) ^ (-i) • y)) (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
        rw [hmarg]

theorem aux_lem_prefix_limit_g8b_layer_point_ogamma {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℤ) (y : SpatialCoordinates d) :
    (∫⁻ omega : BilateralField d, ENNReal.ofReal
        (Real.exp ((|omega i y| / M.delta) ^ 2)) ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  classical
  have hmapeq := aux_lem_prefix_limit_g8b_layer_point_map_eq M i y
  have hevalmeas : Measurable (fun omega : BilateralField d => omega i y) :=
    (continuous_eval_const y).measurable.comp (measurable_pi_apply i)
  have hevalmeas0 : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      g ((3 : ℝ) ^ (-i) • y)) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _
  have hFmeas : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp ((|r| / M.delta) ^ 2))) := by
    fun_prop
  calc (∫⁻ omega : BilateralField d, ENNReal.ofReal
        (Real.exp ((|omega i y| / M.delta) ^ 2)) ∂(chaosSampleLaw M).toMeasure)
      = ∫⁻ r : ℝ, ENNReal.ofReal (Real.exp ((|r| / M.delta) ^ 2))
          ∂(Measure.map (fun omega : BilateralField d => omega i y)
            (chaosSampleLaw M).toMeasure) :=
        (lintegral_map hFmeas hevalmeas).symm
    _ = ∫⁻ r : ℝ, ENNReal.ofReal (Real.exp ((|r| / M.delta) ^ 2))
          ∂(Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
            g ((3 : ℝ) ^ (-i) • y)) (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by
        rw [hmapeq]
    _ = ∫⁻ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, ENNReal.ofReal
          (Real.exp ((|g ((3 : ℝ) ^ (-i) • y)| / M.delta) ^ 2))
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
        lintegral_map hFmeas hevalmeas0
    _ ≤ 2 := by
        obtain ⟨hint, hle⟩ := aux_finite_cutoff_log_abs_majorant_ogamma_eval M
          ((3 : ℝ) ^ (-i) • y)
        have heq : (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
            Real.exp ((M.delta⁻¹ * max (|g ((3 : ℝ) ^ (-i) • y)|) 0) ^ (2 : ℝ))) =
            fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
              Real.exp ((|g ((3 : ℝ) ^ (-i) • y)| / M.delta) ^ 2) := by
          funext g
          rw [max_eq_left (abs_nonneg _), show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num,
            Real.rpow_natCast]
          congr 1
          field_simp
        rw [heq] at hle
        have hpos : ∀ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, 0 ≤
            Real.exp ((|g ((3 : ℝ) ^ (-i) • y)| / M.delta) ^ 2) :=
          fun g => (Real.exp_pos _).le
        have hrw := ofReal_integral_eq_lintegral_ofReal
          (by simpa only [heq] using hint) (Filter.Eventually.of_forall hpos)
        rw [← hrw, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        exact ENNReal.ofReal_le_ofReal hle

theorem aux_lem_prefix_limit_g8b_exists_e0 {d : ℕ} (sh : SpatialCoordinates d) :
    ∃ E0 : ℕ, (2 / 3 : ℝ) * (‖sh‖ + 1) ≤ (3 : ℝ) ^ E0 := by
  obtain ⟨E0, hE0⟩ := pow_unbounded_of_one_lt ((2 / 3 : ℝ) * (‖sh‖ + 1)) (by norm_num : (1:ℝ) < 3)
  exact ⟨E0, hE0.le⟩

theorem aux_lem_prefix_limit_g8b_hassum_shift (Diff : ℤ → ℝ) (S : ℝ)
    (hF : HasSum (fun n : ℕ => Diff (n + 1)) S) (edge : ℤ) :
    HasSum (fun k : ℕ => Diff (edge + 1 + k))
      ((∑ i ∈ Finset.range (-edge).toNat, Diff (edge + 1 + i)) + S -
        ∑ i ∈ Finset.range edge.toNat, Diff (i + 1)) := by
  rcases le_or_gt 0 edge with hedge | hedge
  · have hneg : (-edge).toNat = 0 := by omega
    have hshift := (hasSum_nat_add_iff' (f := fun n : ℕ => Diff (n + 1)) edge.toNat).2 hF
    have hshift' : HasSum (fun j : ℕ => Diff (edge + 1 + j))
        (S - ∑ i ∈ Finset.range edge.toNat, Diff (i + 1)) := by
      refine hshift.congr_fun ?_
      intro j
      congr 1
      omega
    simpa [hneg] using hshift'
  · have hpos : edge.toNat = 0 := by omega
    set e' : ℕ := (-edge).toNat with he'
    have hbase : HasSum (fun n : ℕ => Diff (edge + 1 + (n + e'))) S := by
      refine hF.congr_fun ?_
      intro n
      congr 1
      omega
    have hshift := (hasSum_nat_add_iff (f := fun k : ℕ => Diff (edge + 1 + k)) e').1
      (by simpa using hbase)
    have hcomm : S + ∑ k ∈ Finset.range e', Diff (edge + 1 + (k : ℤ)) =
        (∑ i ∈ Finset.range e', Diff (edge + 1 + (i : ℤ))) + S - ∑ i ∈ Finset.range edge.toNat,
          Diff (i + 1) := by
      rw [hpos]
      simp
      ring
    rwa [hcomm] at hshift

theorem aux_lem_prefix_limit_g8b_sum_range_shift (G : ℤ → ℝ) (a : ℤ) (t : ℕ) :
    ∑ k ∈ Finset.range t, G (a + k) = ∑ j ∈ Finset.Ico a (a + t), G j := by
  refine Finset.sum_nbij' (fun k : ℕ => a + (k : ℤ)) (fun j : ℤ => (j - a).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico]; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_range]; omega
  · intro k _; simp
  · intro j hj; simp only [Finset.mem_Ico] at hj; omega
  · intro k _; rfl

/-- Pure Finset algebra (no measure theory, holds for EVERY `omega`): the retained-block
difference between evaluating at `y` and at the anchor `0`, at ANY level `k : ℤ`, equals the
same two finite corrections `aux_lem_prefix_limit_g8b_hassum_shift`'s `TailDiff(edge)` formula produces at
`edge := -k`. -/
theorem aux_lem_prefix_limit_g8b_retained_diff_eq {d : ℕ} (omega : BilateralField d) (y : SpatialCoordinates d)
    (k : ℤ)
    (retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (hretained : ∀ (kk : ℤ) (yy : SpatialCoordinates d),
      retained kk yy omega = if 0 ≤ kk then ∑ j ∈ Finset.Ico (0 : ℤ) kk, omega (-j) yy
        else -∑ j ∈ Finset.Ico kk (0 : ℤ), omega (-j) yy) :
    retained k y omega - retained k 0 omega =
      (∑ i ∈ Finset.range k.toNat, ((omega (-k + 1 + i) y - omega (-k + 1 + i) 0))) -
        ∑ i ∈ Finset.range (-k).toNat, ((omega (i + 1) y - omega (i + 1) 0)) := by
  rw [hretained k y, hretained k 0]
  rcases le_or_gt 0 k with hk | hk
  · rw [if_pos hk, if_pos hk]
    have hk' : (-k).toNat = 0 := by omega
    rw [hk']
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    rw [← Finset.sum_sub_distrib]
    have hshift : ∑ i ∈ Finset.range k.toNat, (omega (-k + 1 + (i : ℤ)) y -
        omega (-k + 1 + (i : ℤ)) 0) =
        ∑ j ∈ Finset.Ico (-k + 1) (-k + 1 + k.toNat), (omega j y - omega j 0) :=
      aux_lem_prefix_limit_g8b_sum_range_shift (fun j => omega j y - omega j 0) (-k + 1) k.toNat
    rw [hshift]
    have heq : (-k + 1 + (k.toNat : ℤ)) = 1 := by omega
    rw [heq]
    have hrefl : ∑ j ∈ Finset.Ico (0 : ℤ) k, (omega (-j) y - omega (-j) 0) =
        ∑ i ∈ Finset.Ico (-k + 1) 1, (omega i y - omega i 0) := by
      refine Finset.sum_nbij' (fun j => -j) (fun i => -i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      · intro j _; simp
      · intro i _; simp
      · intro j _; rfl
    rw [← hrefl, Finset.sum_sub_distrib]
  · rw [if_neg (not_le.mpr hk), if_neg (not_le.mpr hk)]
    have hk' : k.toNat = 0 := by omega
    rw [hk']
    simp only [Finset.range_zero, Finset.sum_empty]
    have hshift0 : ∑ i ∈ Finset.range (-k).toNat, (omega (1 + (i : ℤ)) y -
        omega (1 + (i : ℤ)) 0) =
        ∑ j ∈ Finset.Ico (1 : ℤ) (1 + (-k).toNat), (omega j y - omega j 0) :=
      aux_lem_prefix_limit_g8b_sum_range_shift (fun j => omega j y - omega j 0) 1 (-k).toNat
    have hshift : ∑ i ∈ Finset.range (-k).toNat, (omega ((i : ℤ) + 1) y -
        omega ((i : ℤ) + 1) 0) =
        ∑ j ∈ Finset.Ico (1 : ℤ) (1 + (-k).toNat), (omega j y - omega j 0) := by
      rw [← hshift0]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hii : (1 : ℤ) + (i : ℤ) = (i : ℤ) + 1 := by ring
      rw [hii]
    have heq : (1 + ((-k).toNat : ℤ)) = 1 - k := by omega
    rw [heq] at hshift
    have hrefl : ∑ j ∈ Finset.Ico k (0 : ℤ), (omega (-j) y - omega (-j) 0) =
        ∑ i ∈ Finset.Ico 1 (1 - k), (omega i y - omega i 0) := by
      refine Finset.sum_nbij' (fun j => -j) (fun i => -i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      · intro j _; simp
      · intro i _; simp
      · intro j _; rfl
    have hAB : (∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) y) -
        ∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) 0 =
        ∑ i ∈ Finset.range (-k).toNat, (omega ((i : ℤ) + 1) y - omega ((i : ℤ) + 1) 0) := by
      rw [hshift, ← hrefl, Finset.sum_sub_distrib]
    linarith [hAB]










/-- Root-field two-point sub-Gaussian exp-square moment bound: for `f ~ chaosRootFieldLaw M`,
`|f (u+δ) - f u|` is controlled at scale `c·(3/2)·m·δ` whenever `‖δ‖ ≤ (3/2)·c`, `0<c≤1`. -/
theorem aux_lem_prefix_limit_g8c_tail_root_exp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (u δ : SpatialCoordinates d) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
        (hδ : ‖δ‖ ≤ (3 / 2 : ℝ) * c),
        (∫⁻ f, ENNReal.ofReal (Real.exp
            ((|f (u + δ) - f u| /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
          ∂(chaosRootFieldLaw M).toMeasure) ≤ 2 := by
  obtain ⟨m, hm, hexp⟩ :=
    exists_gmc_anchored_contraction_exp_square (d := d) (3 / 2 : ℝ) (by norm_num)
  refine ⟨m, hm, ?_⟩
  intro M u δ c hc0 hc1 hδ
  let K0 : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) (3 / 2 : ℝ),
      isCompact_closedBall _ _⟩
  letI : Nonempty K0 := ⟨⟨0, by
    change dist (0 : SpatialCoordinates d) 0 ≤ (3 / 2 : ℝ)
    norm_num⟩⟩
  letI : Nontrivial C(K0, ℝ) := inferInstance
  have hK0 : ∀ x ∈ (K0 : Set (SpatialCoordinates d)), ‖x‖ ≤ (3 / 2 : ℝ) := by
    intro x hx
    simpa [K0, Metric.mem_closedBall, dist_eq_norm] using hx
  have hbase := hexp M K0 hK0 c hc0 hc1
  dsimp only at hbase
  let dilation : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => c • x, (by fun_prop)⟩
  let Φ : C(SpatialCoordinates d, ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp
      ((‖(f.comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
          ContinuousMap.const K0 (f 0)‖ /
        (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
  have hΦmeas : Measurable Φ := by
    have hcomp : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f.comp dilation) :=
      ContinuousMap.continuous_precomp dilation
    have hrestrict : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        (f.comp dilation).restrict (K0 : Set (SpatialCoordinates d))) :=
      (ContinuousMap.continuous_restrict (K0 : Set (SpatialCoordinates d))).comp hcomp
    have hanchor : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const K0 (f 0)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const 0)
    have hnorm : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ‖(f.comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
          ContinuousMap.const K0 (f 0)‖) := continuous_norm.comp (hrestrict.sub hanchor)
    have hcont : Continuous Φ := by
      apply ENNReal.continuous_ofReal.comp
      apply Real.continuous_exp.comp
      exact (hnorm.div_const _).pow 2
    exact hcont.measurable
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw M
  let translate : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ
      (⟨fun x : SpatialCoordinates d => x + u,
        continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))
  have hstat : MeasurePreserving translate (ν : Measure C(SpatialCoordinates d, ℝ))
      (ν : Measure C(SpatialCoordinates d, ℝ)) := by
    simpa [translate, ν, chaosRootFieldLaw] using! gmc_zero_field_law_stationary M u
  have htranslated :
      (∫⁻ f, Φ (translate f) ∂(ν : Measure C(SpatialCoordinates d, ℝ))) ≤ 2 := by
    calc (∫⁻ f, Φ (translate f) ∂(ν : Measure C(SpatialCoordinates d, ℝ)))
        = ∫⁻ f, Φ f ∂Measure.map translate (ν : Measure C(SpatialCoordinates d, ℝ)) :=
          (lintegral_map hΦmeas hstat.measurable).symm
      _ = ∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by rw [hstat.map_eq]
      _ ≤ 2 := by
          simpa [ν, chaosRootFieldLaw] using hbase
  have hx0 : (1 / c) • δ ∈ (K0 : Set (SpatialCoordinates d)) := by
    change dist ((1 / c) • δ) (0 : SpatialCoordinates d) ≤ (3 / 2 : ℝ)
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < 1 / c by positivity)]
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hc0]
    linarith [hδ]
  have hcancel : c • ((1 / c) • δ) = δ := by
    rw [smul_smul]
    rw [show c * (1 / c) = 1 by field_simp]
    exact one_smul ℝ δ
  have hpoint : ∀ f : C(SpatialCoordinates d, ℝ),
      |f (u + δ) - f u| ≤
        ‖((translate f).comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
          ContinuousMap.const K0 ((translate f) 0)‖ := by
    intro f
    have hnc := ContinuousMap.norm_coe_le_norm
      (((translate f).comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
        ContinuousMap.const K0 ((translate f) 0)) ⟨(1 / c) • δ, hx0⟩
    have heq : (((translate f).comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
        ContinuousMap.const K0 ((translate f) 0)) ⟨(1 / c) • δ, hx0⟩ =
        f (u + δ) - f u := by
      show (translate f) (dilation ((1 / c) • δ)) - (translate f) 0 = f (u + δ) - f u
      show (translate f) (c • ((1 / c) • δ)) - (translate f) 0 = f (u + δ) - f u
      rw [hcancel]
      show f (δ + u) - f (0 + u) = f (u + δ) - f u
      rw [zero_add, add_comm δ u]
    rw [heq] at hnc
    simpa using hnc
  have hmono : ∀ f : C(SpatialCoordinates d, ℝ),
      ENNReal.ofReal (Real.exp
          ((|f (u + δ) - f u| /
            (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2)) ≤
        Φ (translate f) := by
    intro f
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    have hA : 0 < c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta) :=
      mul_pos (mul_pos hc0 (by norm_num)) (mul_pos (by exact_mod_cast hm) (M.shellPrefix.delta_pos))
    have hle : |f (u + δ) - f u| ≤
        ‖((translate f).comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
          ContinuousMap.const K0 ((translate f) 0)‖ := hpoint f
    have h1 : 0 ≤ |f (u + δ) - f u| / (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) :=
      div_nonneg (abs_nonneg _) hA.le
    have h2 : 0 ≤ ‖((translate f).comp dilation).restrict (K0 : Set (SpatialCoordinates d)) -
          ContinuousMap.const K0 ((translate f) 0)‖ /
        (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := div_nonneg (norm_nonneg _) hA.le
    apply (sq_le_sq₀ h1 h2).2
    gcongr
  calc (∫⁻ f, ENNReal.ofReal (Real.exp
          ((|f (u + δ) - f u| /
            (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂(chaosRootFieldLaw M).toMeasure)
      ≤ ∫⁻ f, Φ (translate f) ∂(chaosRootFieldLaw M).toMeasure :=
        lintegral_mono hmono
    _ ≤ 2 := htranslated

/-- Layer transfer: for `omega ~ chaosSampleLaw M`, the positive-index layer `omega i`
(`i : ℤ`) has the same two-point sub-Gaussian exp-square bound at `z, z+off`. -/
theorem aux_lem_prefix_limit_g8c_tail_layer_exp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℤ)
        (z off : SpatialCoordinates d) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
        (hδ : ‖((3 : ℝ) ^ (-i)) • off‖ ≤ (3 / 2 : ℝ) * c),
        (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
            ((|omega i z - omega i (z + off)| /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
          ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  obtain ⟨m, hm, hroot⟩ := aux_lem_prefix_limit_g8c_tail_root_exp (d := d)
  refine ⟨m, hm, ?_⟩
  intro M i z off c hc0 hc1 hδ
  set u : SpatialCoordinates d := (3 : ℝ) ^ (-i) • z with hudef
  set δ : SpatialCoordinates d := (3 : ℝ) ^ (-i) • off with hδdef
  set A : ℝ := c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta) with hAdef
  set G : C(SpatialCoordinates d, ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp ((|f z - f (z + off)| / A) ^ 2)) with hGdef
  have hGmeas : Measurable G := by
    have hc : Continuous (fun f : C(SpatialCoordinates d, ℝ) => |f z - f (z + off)|) :=
      ((continuous_eval_const z).sub (continuous_eval_const (z + off))).abs
    have : Continuous G := by
      apply ENNReal.continuous_ofReal.comp
      apply Real.continuous_exp.comp
      exact (hc.div_const _).pow 2
    exact this.measurable
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ))
  have hP : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := by rfl
  have heval := measurePreserving_eval_infinitePi laws i
  have hstep1 : (∫⁻ omega : BilateralField d, G (omega i) ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ f, G f ∂(laws i) := by
    rw [hP]
    exact heval.lintegral_comp hGmeas
  have hstep2 : (∫⁻ f, G f ∂(laws i)) =
      ∫⁻ g, G (layerScaling d i g) ∂(chaosRootFieldLaw M).toMeasure := by
    show (∫⁻ f, G f ∂(scaledLayerLaw d (chaosRootFieldLaw M) i : Measure _)) = _
    simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
    exact lintegral_map hGmeas (layerScaling d i).continuous.measurable
  have hval : ∀ g : C(SpatialCoordinates d, ℝ),
      G (layerScaling d i g) = ENNReal.ofReal (Real.exp ((|g u - g (u + δ)| / A) ^ 2)) := by
    intro g
    have h1 : (layerScaling d i g) z = g u := by
      show g ((3 : ℝ) ^ (-i) • z) = g u
      rw [hudef]
    have h2 : (layerScaling d i g) (z + off) = g (u + δ) := by
      show g ((3 : ℝ) ^ (-i) • (z + off)) = g (u + δ)
      rw [hudef, hδdef, smul_add]
    rw [hGdef]
    dsimp only
    rw [h1, h2]
  calc (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
          ((|omega i z - omega i (z + off)| / A) ^ 2))
        ∂(chaosSampleLaw M).toMeasure)
      = ∫⁻ omega : BilateralField d, G (omega i) ∂(chaosSampleLaw M).toMeasure := by
        apply lintegral_congr
        intro omega
        rw [hGdef]
    _ = ∫⁻ f, G f ∂(laws i) := hstep1
    _ = ∫⁻ g, G (layerScaling d i g) ∂(chaosRootFieldLaw M).toMeasure := hstep2
    _ = ∫⁻ g, ENNReal.ofReal (Real.exp ((|g u - g (u + δ)| / A) ^ 2))
          ∂(chaosRootFieldLaw M).toMeasure := by
        apply lintegral_congr
        exact hval
    _ = ∫⁻ g, ENNReal.ofReal (Real.exp ((|g (u + δ) - g u| / A) ^ 2))
          ∂(chaosRootFieldLaw M).toMeasure := by
        apply lintegral_congr
        intro g
        rw [abs_sub_comm]
    _ ≤ 2 := hroot M u δ c hc0 hc1 hδ

/-- Lp version, all `p ≥ 1`: the two-point positive-layer increment `omega i z - omega i (z+off)`
has `eLpNorm` at most `C·A·√p`, `A := c·(3/2)·m·δ`. -/
theorem aux_lem_prefix_limit_g8c_tail_layer_lp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℤ)
        (z off : SpatialCoordinates d) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
        (hδ : ‖((3 : ℝ) ^ (-i)) • off‖ ≤ (3 / 2 : ℝ) * c)
        (p : ℝ) (hp : 1 ≤ p),
        eLpNorm (fun omega : BilateralField d => omega i z - omega i (z + off))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) * Real.sqrt p) := by
  obtain ⟨m, hm, hexp⟩ := aux_lem_prefix_limit_g8c_tail_layer_exp (d := d)
  obtain ⟨C0, hC0, hOrlicz⟩ := exists_universal_orlicz_eLpNorm_constant
  refine ⟨m, hm, C0 * Real.sqrt 2, by positivity, ?_⟩
  intro M i z off c hc0 hc1 hδ p hp
  set μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hμdef
  set A : ℝ := c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta) with hAdef
  have hApos : 0 < A := by
    have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
    rw [hAdef]; positivity
  set X : BilateralField d → ℝ := fun omega => |omega i z - omega i (z + off)| with hXdef
  have hXmeas : Measurable X := by
    have hz : Continuous (fun omega : BilateralField d => omega i z) :=
      (continuous_eval_const z).comp (continuous_apply i)
    have hzoff : Continuous (fun omega : BilateralField d => omega i (z + off)) :=
      (continuous_eval_const (z + off)).comp (continuous_apply i)
    have : Continuous (fun omega : BilateralField d => omega i z - omega i (z + off)) :=
      hz.sub hzoff
    exact this.abs.measurable
  have hXnonneg : ∀ omega, 0 ≤ X omega := fun omega => abs_nonneg _
  have hXexp : (∫⁻ omega, ENNReal.ofReal (Real.exp ((X omega / A) ^ 2)) ∂μ) ≤ 2 := by
    rw [hμdef]
    exact hexp M i z off c hc0 hc1 hδ
  have hp2case : ∀ q : ℝ≥0∞, q ≠ ∞ → 2 ≤ q →
      eLpNorm X q μ ≤ ENNReal.ofReal (C0 * A * Real.sqrt q.toReal) :=
    hOrlicz μ X A hXmeas hXnonneg hApos hXexp
  have hXeq2 : X = fun omega : BilateralField d => ‖omega i z - omega i (z + off)‖ := by
    funext omega
    rw [hXdef]
    exact (Real.norm_eq_abs _).symm
  have hXeq : eLpNorm (fun omega : BilateralField d => omega i z - omega i (z + off))
      (ENNReal.ofReal p) μ = eLpNorm X (ENNReal.ofReal p) μ := by
    rw [hXeq2]
    exact (eLpNorm_norm _
      (((continuous_eval_const z).measurable.comp (measurable_pi_apply i)).aestronglyMeasurable.sub
        ((continuous_eval_const (z + off)).measurable.comp (measurable_pi_apply i)).aestronglyMeasurable)).symm
  rw [hXeq]
  by_cases hp2 : 2 ≤ p
  · have hqle : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal hp2
    have hbound := hp2case (ENNReal.ofReal p) ENNReal.ofReal_ne_top hqle
    have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
    rw [hpr] at hbound
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1le2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hstep : C0 ≤ C0 * Real.sqrt 2 := le_mul_of_one_le_right hC0.le h1le2
    calc C0 * A * Real.sqrt p = C0 * (A * Real.sqrt p) := by ring
      _ ≤ (C0 * Real.sqrt 2) * (A * Real.sqrt p) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = C0 * Real.sqrt 2 * A * Real.sqrt p := by ring
  · push_neg at hp2
    have hmono : eLpNorm X (ENNReal.ofReal p) μ ≤ eLpNorm X 2 μ := by
      apply eLpNorm_le_eLpNorm_of_exponent_le
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal hp2.le
    have hbound2 := hp2case 2 (by norm_num) le_rfl
    have hpr2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [hpr2] at hbound2
    refine hmono.trans (hbound2.trans (ENNReal.ofReal_le_ofReal ?_))
    have hsqrtp1 : (1 : ℝ) ≤ Real.sqrt p := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    calc C0 * A * Real.sqrt 2 = (C0 * Real.sqrt 2 * A) * 1 := by ring
      _ ≤ (C0 * Real.sqrt 2 * A) * Real.sqrt p :=
          mul_le_mul_of_nonneg_left hsqrtp1 (by positivity)
      _ = C0 * Real.sqrt 2 * A * Real.sqrt p := by ring

/-- The positive-layer tail sum `Σ'_{k:ℕ} (omega (κ+1+k) z - omega (κ+1+k) (z+off))` is
well-defined in `Lp` and geometrically small in `κ`, uniformly in `z` and `M.delta`. -/
theorem aux_lem_prefix_limit_g8c_tail_pos_tail_lp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z off : SpatialCoordinates d) (κ : ℕ)
        (hκ : (2 / 3 : ℝ) * (‖off‖ + 1) ≤ (3 : ℝ) ^ (κ + 1 : ℕ))
        (p : ℝ) (hp : 1 ≤ p),
        MemLp (fun omega : BilateralField d =>
            ∑' k : ℕ, (omega (((κ : ℤ) + 1 + k)) z - omega ((κ : ℤ) + 1 + k) (z + off)))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega : BilateralField d =>
            ∑' k : ℕ, (omega ((κ : ℤ) + 1 + k) z - omega ((κ : ℤ) + 1 + k) (z + off)))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * (‖off‖ + 1) * (m : ℝ) * M.delta * Real.sqrt p *
            (3 : ℝ) ^ (-(κ : ℤ))) := by
  obtain ⟨m, hm, C0, hC0, hlp⟩ := aux_lem_prefix_limit_g8c_tail_layer_lp (d := d)
  refine ⟨m, hm, C0 / 2, by positivity, ?_⟩
  intro M z off κ hκ p hp
  set μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hμdef
  set F : ℕ → BilateralField d → ℝ := fun k omega =>
    omega ((κ : ℤ) + 1 + k) z - omega ((κ : ℤ) + 1 + k) (z + off) with hFdef
  set c : ℕ → ℝ := fun k => (2 / 3 : ℝ) * (‖off‖ + 1) * (3 : ℝ) ^ (-((κ : ℤ) + 1 + k)) with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => by
    rw [hcdef]; positivity
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    rw [hcdef]
    have hmono : (3 : ℝ) ^ (-((κ : ℤ) + 1 + k)) ≤ (3 : ℝ) ^ (-((κ : ℤ) + 1)) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 3)
      omega
    have hbase : (2 / 3 : ℝ) * (‖off‖ + 1) * (3 : ℝ) ^ (-((κ : ℤ) + 1)) ≤ 1 := by
      have hzpoweq : (3 : ℝ) ^ (-((κ : ℤ) + 1)) = 1 / (3 : ℝ) ^ (κ + 1 : ℕ) := by
        rw [show (-(((κ : ℤ) + 1))) = -((κ + 1 : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg,
          zpow_natCast, one_div]
      rw [hzpoweq, mul_one_div, div_le_one (by positivity : (0:ℝ) < (3:ℝ) ^ (κ + 1 : ℕ))]
      exact hκ
    calc (2 / 3 : ℝ) * (‖off‖ + 1) * (3 : ℝ) ^ (-((κ : ℤ) + 1 + k))
        ≤ (2 / 3 : ℝ) * (‖off‖ + 1) * (3 : ℝ) ^ (-((κ : ℤ) + 1)) := by
          apply mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ 1 := hbase
  have hδ : ∀ k, ‖((3 : ℝ) ^ (-((κ : ℤ) + 1 + (k : ℕ)))) • off‖ ≤ (3 / 2 : ℝ) * c k := by
    intro k
    rw [hcdef, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (3:ℝ) ^ (-((κ:ℤ)+1+(k:ℕ))))]
    nlinarith [norm_nonneg off, (by positivity : (0:ℝ) < (3:ℝ) ^ (-((κ:ℤ)+1+(k:ℕ))))]
  set B : ℝ := C0 * ((‖off‖ + 1) * (m : ℝ) * M.delta) * Real.sqrt p *
      (3 : ℝ) ^ (-((κ : ℤ) + 1)) with hBdef
  have hBnonneg : 0 ≤ B := by
    have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
    rw [hBdef]; positivity
  have hzpow : ∀ k : ℕ, (3 : ℝ) ^ (-((κ : ℤ) + 1 + (k : ℕ))) =
      (3 : ℝ) ^ (-((κ : ℤ) + 1)) * (1 / 3 : ℝ) ^ k := by
    intro k
    have h1 : (1 / 3 : ℝ) ^ k = (3 : ℝ) ^ (-(k : ℤ)) := by
      rw [_root_.zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [h1, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    push_cast; ring
  have hbound : ∀ k, eLpNorm (F k) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * (1 / 3 : ℝ) ^ k) := by
    intro k
    have hb := hlp M ((κ : ℤ) + 1 + (k : ℕ)) z off (c k) (hcpos k) (hc1 k) (hδ k) p hp
    have heq : C0 * (c k * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) * Real.sqrt p =
        B * (1 / 3 : ℝ) ^ k := by
      rw [hcdef]
      dsimp only
      rw [hzpow k, hBdef]
      ring
    rwa [heq] at hb
  have hFmeas : ∀ k, Measurable (F k) := by
    intro k
    have hz : Continuous (fun omega : BilateralField d => omega ((κ : ℤ) + 1 + (k:ℕ)) z) :=
      (continuous_eval_const z).comp (continuous_apply ((κ : ℤ) + 1 + (k:ℕ)))
    have hzoff : Continuous
        (fun omega : BilateralField d => omega ((κ : ℤ) + 1 + (k:ℕ)) (z + off)) :=
      (continuous_eval_const (z + off)).comp (continuous_apply ((κ : ℤ) + 1 + (k:ℕ)))
    exact (hz.sub hzoff).measurable
  have hFmem : ∀ k, MemLp (F k) (ENNReal.ofReal p) μ :=
    fun k => (hbound k).trans_lt ENNReal.ofReal_lt_top
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1:ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  obtain ⟨-, htail⟩ := memLp_geometric_tsum_tails μ hp1 ENNReal.ofReal_ne_top
    F hFmem hBnonneg (by norm_num : (0:ℝ) ≤ (1/3:ℝ)) (by norm_num : (1/3:ℝ) < 1) hbound
  obtain ⟨hmem0, hnorm0⟩ := htail 0
  refine ⟨?_, ?_⟩
  · simpa only [add_zero] using hmem0
  · have hrhs : B * (1 / 3 : ℝ) ^ (0:ℕ) / (1 - 1 / 3 : ℝ) = (C0 / 2 : ℝ) * (‖off‖ + 1) *
        (m : ℝ) * M.delta * Real.sqrt p * (3 : ℝ) ^ (-(κ : ℤ)) := by
      rw [hBdef]
      have hsplit : (3 : ℝ) ^ (-((κ : ℤ) + 1)) = (3 : ℝ) ^ (-(κ : ℤ)) * (1 / 3 : ℝ) := by
        rw [show (1 / 3 : ℝ) = (3 : ℝ) ^ (-1 : ℤ) by rw [_root_.zpow_neg_one]; norm_num,
          ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1; ring
      rw [hsplit]; ring
    simpa only [add_zero, hrhs] using hnorm0

/-- Uniform (any sign of `n`, any sign of the layer index) tail bound: for the FIXED shift
`sh` and ANY depth `n`, the tail sum `Σ'_{k} (omega(edge+1+k) z - omega(edge+1+k)(z+3^{-n}•sh))`
has a sub-Gaussian bound at scale `~ (‖sh‖+1)·m·δ·3^{-(edge+n)}`, decaying in `edge+n` alone
(never `edge`/`n` separately), which is the quantity `H2''`'s route keeps fixed via `E0`. -/
theorem aux_lem_prefix_limit_g8c_tail_uniform_exp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z sh : SpatialCoordinates d)
        (n edge : ℤ)
        (hedge : (2 / 3 : ℝ) * (‖sh‖ + 1) ≤ (3 : ℝ) ^ (edge + n + 1)),
        (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
            ((‖∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z -
                omega (edge + 1 + (k : ℤ)) (z + ((3 : ℝ) ^ (-n)) • sh))‖ /
              ((1 / 2 : ℝ) * (m : ℝ) * M.delta * (‖sh‖ + 1) * (3 : ℝ) ^ (-(edge + n)))) ^ 2))
          ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  obtain ⟨m, hm, hlp⟩ := aux_lem_prefix_limit_g8c_tail_layer_exp (d := d)
  refine ⟨m, hm, ?_⟩
  intro M z sh n edge hedge
  set μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hμdef
  set off : SpatialCoordinates d := (3 : ℝ) ^ (-n) • sh with hoffdef
  set F : ℕ → BilateralField d → ℝ := fun k omega =>
    omega (edge + 1 + (k : ℤ)) z - omega (edge + 1 + (k : ℤ)) (z + off) with hFdef
  set c : ℕ → ℝ := fun k =>
    (2 / 3 : ℝ) * (‖sh‖ + 1) * (3 : ℝ) ^ (-(edge + 1 + (k : ℤ) + n)) with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => by rw [hcdef]; positivity
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    rw [hcdef]
    have hmono : (3 : ℝ) ^ (-(edge + 1 + (k : ℤ) + n)) ≤ (3 : ℝ) ^ (-(edge + n + 1)) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      omega
    have hbase : (2 / 3 : ℝ) * (‖sh‖ + 1) * (3 : ℝ) ^ (-(edge + n + 1)) ≤ 1 := by
      have hzpoweq : (3 : ℝ) ^ (-(edge + n + 1)) = 1 / (3 : ℝ) ^ (edge + n + 1) := by
        rw [_root_.zpow_neg, one_div]
      rw [hzpoweq, mul_one_div, div_le_one (by positivity : (0:ℝ) < (3:ℝ) ^ (edge + n + 1))]
      exact hedge
    calc (2 / 3 : ℝ) * (‖sh‖ + 1) * (3 : ℝ) ^ (-(edge + 1 + (k : ℤ) + n))
        ≤ (2 / 3 : ℝ) * (‖sh‖ + 1) * (3 : ℝ) ^ (-(edge + n + 1)) := by
          apply mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ 1 := hbase
  have hδ : ∀ k : ℕ, ‖((3 : ℝ) ^ (-(edge + 1 + (k : ℤ)))) • off‖ ≤ (3 / 2 : ℝ) * c k := by
    intro k
    have hrw : ((3 : ℝ) ^ (-(edge + 1 + (k : ℤ)))) • off =
        ((3 : ℝ) ^ (-(edge + 1 + (k : ℤ) + n))) • sh := by
      rw [hoffdef, smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      ring
    rw [hrw, hcdef, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (3:ℝ) ^ (-(edge + 1 + (k : ℤ) + n)))]
    nlinarith [norm_nonneg sh,
      (by positivity : (0:ℝ) < (3:ℝ) ^ (-(edge + 1 + (k : ℤ) + n)))]
  set a : ℕ → ℝ := fun k => (m : ℝ) * M.delta * (‖sh‖ + 1) *
      (3 : ℝ) ^ (-(edge + 1 + (k : ℤ) + n)) with hadef
  have hbound : ∀ k, (∫⁻ omega, ENNReal.ofReal (Real.exp ((‖F k omega‖ / a k) ^ 2)) ∂μ) ≤ 2 := by
    intro k
    have hb := hlp M (edge + 1 + (k : ℤ)) z off (c k) (hcpos k) (hc1 k) (hδ k)
    have heq : c k * (3 / 2 : ℝ) * ((m : ℝ) * M.delta) = a k := by
      rw [hcdef, hadef]; ring
    have hFeq : ∀ omega, ‖F k omega‖ = |omega (edge + 1 + (k:ℤ)) z - omega (edge + 1 + (k:ℤ)) (z + off)| := by
      intro omega
      rw [hFdef]
      exact Real.norm_eq_abs _
    simp_rw [hFeq]
    rwa [heq] at hb
  have hapos : ∀ k, 0 < a k := fun k => by
    have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
    rw [hadef]; positivity
  have hzpow : ∀ k : ℕ, (3 : ℝ) ^ (-(edge + 1 + (k : ℤ) + n)) =
      (3 : ℝ) ^ (-(edge + n + 1)) * (1 / 3 : ℝ) ^ k := by
    intro k
    have h1 : (1 / 3 : ℝ) ^ k = (3 : ℝ) ^ (-(k : ℤ)) := by
      rw [_root_.zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [h1, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1; ring
  have hsuma : Summable a := by
    have heq2 : a = fun k => ((m:ℝ)*M.delta*(‖sh‖+1)*(3:ℝ)^(-(edge+n+1))) * (1/3:ℝ)^k := by
      funext k; rw [hadef]; dsimp only; rw [hzpow k]; ring
    rw [heq2]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    have hz : Continuous (fun omega : BilateralField d => omega (edge+1+(k:ℤ)) z) :=
      (continuous_eval_const z).comp (continuous_apply (edge+1+(k:ℤ)))
    have hzoff : Continuous (fun omega : BilateralField d => omega (edge+1+(k:ℤ)) (z+off)) :=
      (continuous_eval_const (z+off)).comp (continuous_apply (edge+1+(k:ℤ)))
    exact (hz.sub hzoff).aestronglyMeasurable
  have hck0 : ∀ k : ℕ, c k = c 0 * (1 / 3 : ℝ) ^ k := by
    intro k
    rw [hcdef]
    dsimp only
    rw [show (-(edge + 1 + (k : ℤ) + n)) = (-(edge + 1 + (0 : ℤ) + n)) + (-(k : ℤ)) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      show (3 : ℝ) ^ (-(k : ℤ)) = (1 / 3 : ℝ) ^ k by
        rw [_root_.zpow_neg, zpow_natCast, one_div, inv_pow]]
    ring
  have hsumF : ∀ᵐ omega ∂μ, Summable (fun k => ‖F k omega‖) := by
    obtain ⟨m', hm', C0', hC0', hlp'⟩ := aux_lem_prefix_limit_g8c_tail_layer_lp (d := d)
    set B2 : ℝ := C0' * (c 0 * (3 / 2 : ℝ) * ((m' : ℝ) * M.delta)) * Real.sqrt 2 with hB2def
    have hB2 : 0 ≤ B2 := by
      have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
      rw [hB2def]; positivity
    have h2eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    have hF2mem : ∀ k, MemLp (F k) (2 : ℝ≥0∞) μ := by
      intro k
      rw [h2eq]
      simp only [hFdef]
      have hbb := hlp' M (edge + 1 + (k : ℤ)) z off (c k) (hcpos k) (hc1 k) (hδ k) 2 (by norm_num)
      exact lt_of_le_of_lt hbb ENNReal.ofReal_lt_top
    have hF2bound : ∀ k, eLpNorm (F k) (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal (B2 * (1 / 3 : ℝ) ^ k) := by
      intro k
      rw [h2eq]
      simp only [hFdef]
      have hbb := hlp' M (edge + 1 + (k : ℤ)) z off (c k) (hcpos k) (hc1 k) (hδ k) 2 (by norm_num)
      refine hbb.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hB2def, hck0 k]
      exact le_of_eq (by ring)
    obtain ⟨hae, -⟩ := memLp_geometric_tsum_tails μ (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) F hF2mem hB2
      (by norm_num : (0:ℝ) ≤ (1/3:ℝ)) (by norm_num : (1/3:ℝ) < 1) hF2bound
    exact hae
  have hmain := lintegral_exp_sq_norm_tsum_le μ F hFmeas a hapos hsuma hsumF hbound
  have hσ : (∑' k : ℕ, a k) = (1/2:ℝ)*(m:ℝ)*M.delta*(‖sh‖+1)*(3:ℝ)^(-(edge+n)) := by
    have heq2 : a = fun k => ((m:ℝ)*M.delta*(‖sh‖+1)*(3:ℝ)^(-(edge+n+1))) * (1/3:ℝ)^k := by
      funext k; rw [hadef]; dsimp only; rw [hzpow k]; ring
    rw [heq2, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    have hsplit : (3 : ℝ) ^ (-(edge + n + 1)) = (3 : ℝ) ^ (-(edge+n)) * (1/3:ℝ) := by
      rw [show (1/3:ℝ) = (3:ℝ)^(-1:ℤ) by rw [_root_.zpow_neg_one]; norm_num,
        ← zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
      congr 1; ring
    rw [hsplit]; ring
  rw [hσ] at hmain
  exact hmain






/-! ## Part 2: the algebraic engine (Step 2 of PROGRESS-G8b.md) -/

/-- `retained`, exactly `lem_band`/`lem_prefix_limit`'s own `let` (`node_candidate.lean`'s
`aux_g9chart_transport_ret`, copied so this file is self-contained/independently testable). -/
def aux_lem_prefix_limit_g8c_ret (k : ℤ) (f : ℤ → ℝ) : ℝ :=
  if 0 ≤ k then ∑ j ∈ Finset.Ico (0 : ℤ) k, f (-j) else -∑ j ∈ Finset.Ico k (0 : ℤ), f (-j)

/-- `retained k y omega`, exactly `node_candidate.lean`'s `aux_g9chart_transport_retained`. -/
def aux_lem_prefix_limit_g8c_retained {d : ℕ} (k : ℤ) (y : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  aux_lem_prefix_limit_g8c_ret k (fun j => om j y)

/-- The anchor-0 `HasSum` fact (`N = 0` instance of `coefficient_physical_identity`), for
EVERY point `y` at once, a.e. `omega`. -/
theorem aux_lem_prefix_limit_g8c_hassum_diff0 {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ y : SpatialCoordinates d,
      HasSum (fun n : ℕ => omega ((n : ℤ) + 1) y - omega ((n : ℤ) + 1) 0) (H omega y) := by
  have hbase := (coefficient_physical_identity M H hH
    (fun N omega i y => omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (fun N omega i y => rfl)
    (fun N omega y => Real.exp (∑ i ∈ Finset.range (N + 1),
      (omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y) -
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))) (fun N omega y => rfl)).2
  filter_upwards [hbase] with omega homega y
  have hF0raw := homega 0 y
  simp only [Nat.cast_zero, neg_zero, zpow_zero, one_smul, pow_zero] at hF0raw
  refine hF0raw.congr_fun ?_
  intro n
  have hidx : (n : ℤ) + 1 = ((0 + 1 + n : ℕ) : ℤ) - 0 := by push_cast; ring
  rw [hidx]

/-- The keystone corollary: `H omega y + retained k y omega - retained k 0 omega` equals the
tail sum split at level `-k`, for ANY `k : ℤ` and ANY `y`, a.e. `omega`. -/
theorem aux_lem_prefix_limit_g8c_t_sub_retained0_tailsum {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (k : ℤ) (y : SpatialCoordinates d),
      H omega y + aux_lem_prefix_limit_g8c_retained k y omega - aux_lem_prefix_limit_g8c_retained k 0 omega =
        ∑' j : ℕ, (omega (-k + 1 + j) y - omega (-k + 1 + j) 0) := by
  filter_upwards [aux_lem_prefix_limit_g8c_hassum_diff0 M H hH] with omega hF0all k y
  have hF0 := hF0all y
  have hshift := aux_lem_prefix_limit_g8b_hassum_shift (fun j => omega j y - omega j 0) (H omega y) hF0 (-k)
  have heqNat : (-(-k)).toNat = k.toNat := by omega
  rw [heqNat] at hshift
  have hrd := aux_lem_prefix_limit_g8b_retained_diff_eq omega y k aux_lem_prefix_limit_g8c_retained (fun _ _ => rfl)
  have hTD := hshift.tsum_eq
  rw [hTD]
  linarith [hrd]

/-- Reanchoring a `HasSum` tail sum: for `a ≤ b`, `TailSum(a) - TailSum(b)` equals the finite
block `Σ_{i∈Ico(a+1,b+1)} Diff i`. Pure `HasSum`/`Finset` algebra given one `HasSum` witness. -/
theorem aux_lem_prefix_limit_g8c_tailsum_diff_le (Diff : ℤ → ℝ) (S : ℝ)
    (hF : HasSum (fun n : ℕ => Diff (n + 1)) S) (a b : ℤ) (hab : a ≤ b) :
    (∑' j : ℕ, Diff (a + 1 + j)) - (∑' j : ℕ, Diff (b + 1 + j)) =
      ∑ i ∈ Finset.Ico (a + 1) (b + 1), Diff i := by
  have hA := aux_lem_prefix_limit_g8b_hassum_shift Diff S hF a
  set t : ℕ := (b - a).toNat with ht
  have hshift2 := (hasSum_nat_add_iff' (f := fun j : ℕ => Diff (a + 1 + j)) t).2 hA
  have hshift2' : HasSum (fun j : ℕ => Diff (b + 1 + j))
      (((∑ i ∈ Finset.range (-a).toNat, Diff (a + 1 + i)) + S -
        ∑ i ∈ Finset.range a.toNat, Diff (i + 1)) - ∑ i ∈ Finset.range t, Diff (a + 1 + i)) := by
    refine hshift2.congr_fun ?_
    intro j
    congr 1
    omega
  have hSA : (∑' j : ℕ, Diff (a + 1 + j)) =
      (∑ i ∈ Finset.range (-a).toNat, Diff (a + 1 + i)) + S -
        ∑ i ∈ Finset.range a.toNat, Diff (i + 1) := hA.tsum_eq
  have hSB : (∑' j : ℕ, Diff (b + 1 + j)) =
      ((∑ i ∈ Finset.range (-a).toNat, Diff (a + 1 + i)) + S -
        ∑ i ∈ Finset.range a.toNat, Diff (i + 1)) - ∑ i ∈ Finset.range t, Diff (a + 1 + i) :=
    hshift2'.tsum_eq
  rw [hSA, hSB]
  have hreindex : ∑ i ∈ Finset.range t, Diff (a + 1 + i) =
      ∑ i ∈ Finset.Ico (a + 1) (b + 1), Diff i := by
    have hrs := aux_lem_prefix_limit_g8b_sum_range_shift Diff (a + 1) t
    rwa [show a + 1 + (t : ℤ) = b + 1 by omega] at hrs
  rw [hreindex]
  ring

/-- `ret`-difference at ANY two indices `a ≤ b` (same underlying `f`): a pure `Finset` identity,
no measure theory. -/
theorem aux_lem_prefix_limit_g8c_ret_diff_le (f : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b) :
    aux_lem_prefix_limit_g8c_ret b f - aux_lem_prefix_limit_g8c_ret a f = ∑ i ∈ Finset.Ico (1 - b) (1 - a), f i := by
  have hmid : aux_lem_prefix_limit_g8c_ret b f - aux_lem_prefix_limit_g8c_ret a f = ∑ j ∈ Finset.Ico a b, f (-j) := by
    unfold aux_lem_prefix_limit_g8c_ret
    by_cases ha0 : 0 ≤ a
    · have hb0 : 0 ≤ b := le_trans ha0 hab
      rw [if_pos hb0, if_pos ha0]
      have hU : Finset.Ico (0 : ℤ) b = Finset.Ico (0 : ℤ) a ∪ Finset.Ico a b := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hD : Disjoint (Finset.Ico (0 : ℤ) a) (Finset.Ico a b) :=
        Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
      rw [hU, Finset.sum_union hD]; ring
    · by_cases hb0 : 0 ≤ b
      · rw [if_pos hb0, if_neg ha0]
        have hU : Finset.Ico a (0 : ℤ) ∪ Finset.Ico (0 : ℤ) b = Finset.Ico a b := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
        have hD : Disjoint (Finset.Ico a (0 : ℤ)) (Finset.Ico (0 : ℤ) b) :=
          Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
        have hsum : ∑ j ∈ Finset.Ico a b, f (-j) =
            ∑ j ∈ Finset.Ico a (0 : ℤ), f (-j) + ∑ j ∈ Finset.Ico (0 : ℤ) b, f (-j) := by
          rw [← hU, Finset.sum_union hD]
        rw [hsum]; ring
      · rw [if_neg hb0, if_neg ha0]
        push_neg at ha0 hb0
        have hU : Finset.Ico a (0 : ℤ) = Finset.Ico a b ∪ Finset.Ico b (0 : ℤ) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
        have hD : Disjoint (Finset.Ico a b) (Finset.Ico b (0 : ℤ)) :=
          Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
        have hsum : ∑ j ∈ Finset.Ico a (0 : ℤ), f (-j) =
            ∑ j ∈ Finset.Ico a b, f (-j) + ∑ j ∈ Finset.Ico b (0 : ℤ), f (-j) := by
          rw [hU, Finset.sum_union hD]
        rw [hsum]; ring
  rw [hmid]
  refine Finset.sum_nbij' (fun j => -j) (fun i => -i) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
  · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
  · intro j _; simp
  · intro i _; simp
  · intro j _; rfl

/-- A finite sum `Σ_{i∈S} omega i (y i)` of RAW single-point layer evaluations (any points
`y i`, no separation hypothesis) has a Γ₂ (Orlicz-exp-square) bound at scale `S.card * M.delta`
-- combines `aux_lem_prefix_limit_g8b_layer_point_ogamma` (each term individually) via
`lintegral_exp_sq_finset_sum_le`, then the triangle inequality `|Σ| ≤ Σ|·|`. -/
theorem aux_lem_prefix_limit_g8c_finset_point_ogamma {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (S : Finset ℤ) (y : ℤ → SpatialCoordinates d) :
    ∃ A : ℝ, 0 < A ∧
      (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
          ((|∑ i ∈ S, omega i (y i)| / A) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, ?_⟩
    subst hS
    have hval : ∀ omega : BilateralField d, ENNReal.ofReal (Real.exp
        ((|∑ i ∈ (∅ : Finset ℤ), omega i (y i)| / (1:ℝ)) ^ 2)) = 1 := by
      intro omega
      simp
    simp only [hval, lintegral_const, measure_univ, mul_one]
    norm_num
  · refine ⟨(S.card : ℝ) * M.delta, by positivity, ?_⟩
    have hcombine := lintegral_exp_sq_finset_sum_le (chaosSampleLaw M).toMeasure S
      (fun i omega => |omega i (y i)|) (fun _ => M.delta) hS
      (fun i _ => by
        have : Continuous (fun omega : BilateralField d => omega i (y i)) :=
          (continuous_eval_const (y i)).comp (continuous_apply i)
        exact this.abs.measurable.aestronglyMeasurable)
      (fun i _ => Filter.Eventually.of_forall fun omega => abs_nonneg _)
      (fun i _ => hδpos)
      (fun i _ => aux_lem_prefix_limit_g8b_layer_point_ogamma M i (y i))
    have hsumA : (∑ _i ∈ S, M.delta) = (S.card : ℝ) * M.delta := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsumA] at hcombine
    refine (lintegral_mono ?_).trans hcombine
    intro omega
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    have htri : |∑ i ∈ S, omega i (y i)| ≤ ∑ i ∈ S, |omega i (y i)| :=
      Finset.abs_sum_le_sum_abs _ _
    have hApos : (0:ℝ) < (S.card : ℝ) * M.delta := by positivity
    have h1 : 0 ≤ |∑ i ∈ S, omega i (y i)| / ((S.card : ℝ) * M.delta) :=
      div_nonneg (abs_nonneg _) hApos.le
    have h2 : 0 ≤ (∑ i ∈ S, |omega i (y i)|) / ((S.card : ℝ) * M.delta) :=
      div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) hApos.le
    apply (sq_le_sq₀ h1 h2).2
    gcongr








/-! ## Part 3a: combining Orlicz pieces (sum, monotone transfer, difference-of-finite-sums) -/

/-- Two nonnegative Γ₂(2,·)-bounded pieces combine additively: `X+Y` is Γ₂(2,a+b). Special
case of `lintegral_exp_sq_finset_sum_le` at a two-element `Finset ℕ`. -/
theorem aux_lem_prefix_limit_g8c_orlicz_add {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (X Y : BilateralField d → ℝ) (a b : ℝ)
    (hXm : AEStronglyMeasurable X (chaosSampleLaw M).toMeasure)
    (hYm : AEStronglyMeasurable Y (chaosSampleLaw M).toMeasure)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (ha : 0 < a) (hb : 0 < b)
    (hXb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((X omega / a) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2)
    (hYb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((Y omega / b) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp (((X omega + Y omega) / (a + b)) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  set Z : ℕ → BilateralField d → ℝ := fun i => if i = 0 then X else Y with hZdef
  set c : ℕ → ℝ := fun i => if i = 0 then a else b with hcdef
  have hcomb := lintegral_exp_sq_finset_sum_le (chaosSampleLaw M).toMeasure ({0, 1} : Finset ℕ)
    Z c ⟨0, by simp⟩
    (by intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa [hZdef] using hXm
        · simpa [hZdef] using hYm)
    (by intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa [hZdef] using Filter.Eventually.of_forall hX0
        · simpa [hZdef] using Filter.Eventually.of_forall hY0)
    (by intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa [hcdef] using ha
        · simpa [hcdef] using hb)
    (by intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa [hZdef, hcdef] using hXb
        · simpa [hZdef, hcdef] using hYb)
  have hZsum : ∀ omega, (∑ i ∈ ({0, 1} : Finset ℕ), Z i omega) = X omega + Y omega := by
    intro omega
    rw [Finset.sum_pair h01]
    simp [hZdef]
  have hcsum : (∑ i ∈ ({0, 1} : Finset ℕ), c i) = a + b := by
    rw [Finset.sum_pair h01]
    simp [hcdef]
  simp only [hZsum, hcsum] at hcomb
  exact hcomb

/-- Nonnegative dominated transfer: if `0 ≤ X ≤ Y` pointwise and `Y` is Γ₂(2,a)-bounded, then
so is `X`. -/
theorem aux_lem_prefix_limit_g8c_orlicz_mono {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (X Y : BilateralField d → ℝ) (a : ℝ)
    (hXY : ∀ omega, 0 ≤ X omega ∧ X omega ≤ Y omega) (ha : 0 < a)
    (hYb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((Y omega / a) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp ((X omega / a) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  refine (lintegral_mono ?_).trans hYb
  intro omega
  apply ENNReal.ofReal_mono
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ X omega / a := div_nonneg (hXY omega).1 ha.le
  have h2 : 0 ≤ Y omega / a := div_nonneg ((hXY omega).1.trans (hXY omega).2) ha.le
  refine (sq_le_sq₀ h1 h2).2 ?_
  gcongr
  exact (hXY omega).2

/-- A finite sum of DIFFERENCES `Σ_{i∈S} (omega i (y1 i) - omega i (y2 i))` has a Γ₂ bound at
scale `2 * S.card * M.delta` (or `2*M.delta` if `S` empty) -- via `aux_lem_prefix_limit_g8c_finset_point_ogamma`
applied to `y1` and `y2` separately, combined by `aux_lem_prefix_limit_g8c_orlicz_add`, then the triangle
inequality `|Σ D_i| ≤ |Σ y1| + |Σ y2|` via `aux_lem_prefix_limit_g8c_orlicz_mono`. -/
theorem aux_lem_prefix_limit_g8c_finset_diff_ogamma {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (S : Finset ℤ)
    (y1 y2 : ℤ → SpatialCoordinates d) :
    ∃ A : ℝ, 0 < A ∧
      (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
          ((|∑ i ∈ S, (omega i (y1 i) - omega i (y2 i))| / A) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  obtain ⟨A1, hA1pos, hA1⟩ := aux_lem_prefix_limit_g8c_finset_point_ogamma M S y1
  obtain ⟨A2, hA2pos, hA2⟩ := aux_lem_prefix_limit_g8c_finset_point_ogamma M S y2
  have hX1m : AEStronglyMeasurable (fun omega : BilateralField d => |∑ i ∈ S, omega i (y1 i)|)
      (chaosSampleLaw M).toMeasure := by
    have : Continuous (fun omega : BilateralField d => ∑ i ∈ S, omega i (y1 i)) :=
      continuous_finset_sum S (fun i _ => (continuous_eval_const (y1 i)).comp (continuous_apply i))
    exact this.abs.measurable.aestronglyMeasurable
  have hX2m : AEStronglyMeasurable (fun omega : BilateralField d => |∑ i ∈ S, omega i (y2 i)|)
      (chaosSampleLaw M).toMeasure := by
    have : Continuous (fun omega : BilateralField d => ∑ i ∈ S, omega i (y2 i)) :=
      continuous_finset_sum S (fun i _ => (continuous_eval_const (y2 i)).comp (continuous_apply i))
    exact this.abs.measurable.aestronglyMeasurable
  have hadd := aux_lem_prefix_limit_g8c_orlicz_add M
    (fun omega => |∑ i ∈ S, omega i (y1 i)|) (fun omega => |∑ i ∈ S, omega i (y2 i)|) A1 A2
    hX1m hX2m (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hA1pos hA2pos hA1 hA2
  refine ⟨A1 + A2, by positivity, ?_⟩
  refine aux_lem_prefix_limit_g8c_orlicz_mono M
    (fun omega => |∑ i ∈ S, (omega i (y1 i) - omega i (y2 i))|)
    (fun omega => |∑ i ∈ S, omega i (y1 i)| + |∑ i ∈ S, omega i (y2 i)|) (A1 + A2)
    (fun omega => ⟨abs_nonneg _, ?_⟩) (by positivity) hadd
  show |∑ i ∈ S, (omega i (y1 i) - omega i (y2 i))| ≤
      |∑ i ∈ S, omega i (y1 i)| + |∑ i ∈ S, omega i (y2 i)|
  have hsplit : ∑ i ∈ S, (omega i (y1 i) - omega i (y2 i)) =
      (∑ i ∈ S, omega i (y1 i)) - ∑ i ∈ S, omega i (y2 i) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  calc |(∑ i ∈ S, omega i (y1 i)) - ∑ i ∈ S, omega i (y2 i)|
      = |(∑ i ∈ S, omega i (y1 i)) + (-(∑ i ∈ S, omega i (y2 i)))| := by ring_nf
    _ ≤ |∑ i ∈ S, omega i (y1 i)| + |-(∑ i ∈ S, omega i (y2 i))| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (∑ i ∈ S, omega i (y1 i)) (-(∑ i ∈ S, omega i (y2 i)))
    _ = |∑ i ∈ S, omega i (y1 i)| + |∑ i ∈ S, omega i (y2 i)| := by rw [abs_neg]




/-! ## Part 3b: explicit-scale variants + a.e. monotone transfer + continuity of `retained` -/

theorem aux_lem_prefix_limit_g8c_retained_continuous {d : ℕ} (k : ℤ) (y : SpatialCoordinates d) :
    Continuous (fun omega : BilateralField d => aux_lem_prefix_limit_g8c_retained k y omega) := by
  unfold aux_lem_prefix_limit_g8c_retained aux_lem_prefix_limit_g8c_ret
  split_ifs with h
  · exact continuous_finset_sum _
      (fun j _ => (continuous_eval_const y).comp (continuous_apply (-j)))
  · exact (continuous_finset_sum _
      (fun j _ => (continuous_eval_const y).comp (continuous_apply (-j)))).neg

theorem aux_lem_prefix_limit_g8c_orlicz_mono_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (X Y : BilateralField d → ℝ) (a : ℝ)
    (hXY : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ X omega ∧ X omega ≤ Y omega) (ha : 0 < a)
    (hYb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((Y omega / a) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp ((X omega / a) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  refine (lintegral_mono_ae ?_).trans hYb
  filter_upwards [hXY] with omega hxy
  apply ENNReal.ofReal_mono
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ X omega / a := div_nonneg hxy.1 ha.le
  have h2 : 0 ≤ Y omega / a := div_nonneg (hxy.1.trans hxy.2) ha.le
  refine (sq_le_sq₀ h1 h2).2 ?_
  gcongr
  exact hxy.2

theorem aux_lem_prefix_limit_g8c_finset_point_ogamma' {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (S : Finset ℤ) (y : ℤ → SpatialCoordinates d) :
    (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
        ((|∑ i ∈ S, omega i (y i)| / ((max S.card 1 : ℕ) * M.delta)) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    have hval : ∀ omega : BilateralField d, ENNReal.ofReal (Real.exp
        ((|∑ i ∈ (∅ : Finset ℤ), omega i (y i)| / ((max (0:ℕ) 1 : ℕ) * M.delta)) ^ 2)) = 1 := by
      intro omega
      simp
    simp only [Finset.card_empty]
    simp only [hval, lintegral_const, measure_univ, mul_one]
    norm_num
  · have hcardeq : ((max S.card 1 : ℕ) : ℝ) = (S.card : ℝ) := by
      have h1 : 1 ≤ S.card := Finset.Nonempty.card_pos hS
      have h2 : max S.card 1 = S.card := by omega
      exact_mod_cast h2
    rw [hcardeq]
    have hcombine := lintegral_exp_sq_finset_sum_le (chaosSampleLaw M).toMeasure S
      (fun i omega => |omega i (y i)|) (fun _ => M.delta) hS
      (fun i _ => by
        have : Continuous (fun omega : BilateralField d => omega i (y i)) :=
          (continuous_eval_const (y i)).comp (continuous_apply i)
        exact this.abs.measurable.aestronglyMeasurable)
      (fun i _ => Filter.Eventually.of_forall fun omega => abs_nonneg _)
      (fun i _ => hδpos)
      (fun i _ => aux_lem_prefix_limit_g8b_layer_point_ogamma M i (y i))
    have hsumA : (∑ _i ∈ S, M.delta) = (S.card : ℝ) * M.delta := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsumA] at hcombine
    refine (lintegral_mono ?_).trans hcombine
    intro omega
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    have htri : |∑ i ∈ S, omega i (y i)| ≤ ∑ i ∈ S, |omega i (y i)| :=
      Finset.abs_sum_le_sum_abs _ _
    have hApos : (0:ℝ) < (S.card : ℝ) * M.delta := by positivity
    have h1 : 0 ≤ |∑ i ∈ S, omega i (y i)| / ((S.card : ℝ) * M.delta) :=
      div_nonneg (abs_nonneg _) hApos.le
    have h2 : 0 ≤ (∑ i ∈ S, |omega i (y i)|) / ((S.card : ℝ) * M.delta) :=
      div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) hApos.le
    apply (sq_le_sq₀ h1 h2).2
    gcongr

theorem aux_lem_prefix_limit_g8c_finset_diff_ogamma' {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (S : Finset ℤ) (y1 y2 : ℤ → SpatialCoordinates d) :
    (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
        ((|∑ i ∈ S, (omega i (y1 i) - omega i (y2 i))| /
          (2 * (max S.card 1 : ℕ) * M.delta)) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  have hX1m : AEStronglyMeasurable (fun omega : BilateralField d => |∑ i ∈ S, omega i (y1 i)|)
      (chaosSampleLaw M).toMeasure := by
    have : Continuous (fun omega : BilateralField d => ∑ i ∈ S, omega i (y1 i)) :=
      continuous_finset_sum S (fun i _ => (continuous_eval_const (y1 i)).comp (continuous_apply i))
    exact this.abs.measurable.aestronglyMeasurable
  have hX2m : AEStronglyMeasurable (fun omega : BilateralField d => |∑ i ∈ S, omega i (y2 i)|)
      (chaosSampleLaw M).toMeasure := by
    have : Continuous (fun omega : BilateralField d => ∑ i ∈ S, omega i (y2 i)) :=
      continuous_finset_sum S (fun i _ => (continuous_eval_const (y2 i)).comp (continuous_apply i))
    exact this.abs.measurable.aestronglyMeasurable
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hadd := aux_lem_prefix_limit_g8c_orlicz_add M
    (fun omega => |∑ i ∈ S, omega i (y1 i)|) (fun omega => |∑ i ∈ S, omega i (y2 i)|)
    ((max S.card 1 : ℕ) * M.delta) ((max S.card 1 : ℕ) * M.delta)
    hX1m hX2m (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (by positivity) (by positivity)
    (aux_lem_prefix_limit_g8c_finset_point_ogamma' M S y1) (aux_lem_prefix_limit_g8c_finset_point_ogamma' M S y2)
  have heq : ((max S.card 1 : ℕ):ℝ) * M.delta + ((max S.card 1 : ℕ):ℝ) * M.delta =
      2 * (max S.card 1 : ℕ) * M.delta := by ring
  rw [heq] at hadd
  refine aux_lem_prefix_limit_g8c_orlicz_mono M
    (fun omega => |∑ i ∈ S, (omega i (y1 i) - omega i (y2 i))|)
    (fun omega => |∑ i ∈ S, omega i (y1 i)| + |∑ i ∈ S, omega i (y2 i)|)
    (2 * (max S.card 1 : ℕ) * M.delta)
    (fun omega => ⟨abs_nonneg _, ?_⟩) (by positivity) hadd
  show |∑ i ∈ S, (omega i (y1 i) - omega i (y2 i))| ≤
      |∑ i ∈ S, omega i (y1 i)| + |∑ i ∈ S, omega i (y2 i)|
  have hsplit : ∑ i ∈ S, (omega i (y1 i) - omega i (y2 i)) =
      (∑ i ∈ S, omega i (y1 i)) - ∑ i ∈ S, omega i (y2 i) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  calc |(∑ i ∈ S, omega i (y1 i)) - ∑ i ∈ S, omega i (y2 i)|
      = |(∑ i ∈ S, omega i (y1 i)) + (-(∑ i ∈ S, omega i (y2 i)))| := by ring_nf
    _ ≤ |∑ i ∈ S, omega i (y1 i)| + |-(∑ i ∈ S, omega i (y2 i))| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (∑ i ∈ S, omega i (y1 i)) (-(∑ i ∈ S, omega i (y2 i)))
    _ = |∑ i ∈ S, omega i (y1 i)| + |∑ i ∈ S, omega i (y2 i)| := by rw [abs_neg]





/-! ## Part 4: final assembly (H2'') -/

/-- The common tail and three finite corrections for the reference exponent. -/
theorem aux_lem_prefix_limit_ratio_tail_decomposition {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (n off edge : ℤ) (z w : SpatialCoordinates d)
    (hedgen : -n ≤ edge) (hedgem : -(n + off) ≤ edge) :
    let m := n + off
    let Rz := Finset.Ico (-n + 1) (edge + 1)
    let Rw := Finset.Ico (-m + 1) (edge + 1)
    let Rret := if 0 ≤ off then Finset.Ico (1 - m) (1 - n)
      else Finset.Ico (1 - n) (1 - m)
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
          (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)) =
        (∑' j : ℕ, (omega (edge + 1 + (j:ℤ)) z - omega (edge + 1 + (j:ℤ)) w)) +
          (if 0 ≤ off then (-1:ℝ) else 1) * (∑ i ∈ Rret, omega i 0) +
          ((∑ i ∈ Rz, (omega i z - omega i 0)) - ∑ i ∈ Rw, (omega i w - omega i 0)) := by
  classical
  intro m Rz Rw Rret
  have hmdef : m = n + off := rfl
  have hRzdef : Rz = Finset.Ico (-n + 1) (edge + 1) := rfl
  have hRwdef : Rw = Finset.Ico (-m + 1) (edge + 1) := rfl
  have hRretdef : Rret = if 0 ≤ off then Finset.Ico (1 - m) (1 - n)
      else Finset.Ico (1 - n) (1 - m) := rfl
  have hF0all := aux_lem_prefix_limit_g8c_hassum_diff0 M H hH
  have hTS := aux_lem_prefix_limit_g8c_t_sub_retained0_tailsum M H hH
  filter_upwards [hF0all, hTS] with omega hF0allo hTSo
  have hF0z := hF0allo z
  have hF0w := hF0allo w
  have hTz := hTSo n z
  have hTw := hTSo m w
  have hRzs := aux_lem_prefix_limit_g8b_hassum_shift (fun l => omega l z - omega l 0) (H omega z) hF0z edge
  have hRws := aux_lem_prefix_limit_g8b_hassum_shift (fun l => omega l w - omega l 0) (H omega w) hF0w edge
  have hRzws := hRzs.sub hRws
  have hRzweq : (fun j : ℕ => (omega (edge + 1 + (j:ℤ)) z - omega (edge + 1 + (j:ℤ)) 0) -
      (omega (edge + 1 + (j:ℤ)) w - omega (edge + 1 + (j:ℤ)) 0)) =
      (fun j : ℕ => omega (edge + 1 + (j:ℤ)) z - omega (edge + 1 + (j:ℤ)) w) := by
    funext j; ring
  rw [hRzweq] at hRzws
  have hTailval := hRzws.tsum_eq
  have hTSzedge := hRzs.tsum_eq
  have hTSwedge := hRws.tsum_eq
  have hCorrz := aux_lem_prefix_limit_g8c_tailsum_diff_le (fun l => omega l z - omega l 0) (H omega z) hF0z
    (-n) edge (by omega)
  have hCorrw := aux_lem_prefix_limit_g8c_tailsum_diff_le (fun l => omega l w - omega l 0) (H omega w) hF0w
    (-m) edge (by omega)
  have hCorrzeq : (∑ i ∈ Finset.Ico (-n + 1) (edge + 1), (omega i z - omega i 0)) =
      (∑ i ∈ Rz, (omega i z - omega i 0)) := by rw [hRzdef]
  have hCorrweq : (∑ i ∈ Finset.Ico (-m + 1) (edge + 1), (omega i w - omega i 0)) =
      (∑ i ∈ Rw, (omega i w - omega i 0)) := by rw [hRwdef]
  rw [hCorrzeq] at hCorrz
  rw [hCorrweq] at hCorrw
  have hretd : aux_lem_prefix_limit_g8c_retained n 0 omega - aux_lem_prefix_limit_g8c_retained m 0 omega =
      (if 0 ≤ off then (-1:ℝ) else 1) * (∑ i ∈ Rret, omega i 0) := by
    by_cases hoff : 0 ≤ off
    · rw [if_pos hoff]
      have hnm : n ≤ m := by rw [hmdef]; omega
      have hd := aux_lem_prefix_limit_g8c_ret_diff_le (fun j => omega j (0:SpatialCoordinates d)) n m hnm
      have hRreteq : Rret = Finset.Ico (1 - m) (1 - n) := by rw [hRretdef, if_pos hoff]
      rw [hRreteq]
      simp only [aux_lem_prefix_limit_g8c_retained]
      linarith [hd]
    · rw [if_neg hoff]
      have hmn : m ≤ n := by rw [hmdef]; omega
      have hd := aux_lem_prefix_limit_g8c_ret_diff_le (fun j => omega j (0:SpatialCoordinates d)) m n hmn
      have hRreteq : Rret = Finset.Ico (1 - n) (1 - m) := by rw [hRretdef, if_neg hoff]
      rw [hRreteq]
      simp only [aux_lem_prefix_limit_g8c_retained]
      linarith [hd]
  linarith [hTz, hTw, hCorrz, hCorrw, hretd, hTailval, hTSzedge, hTSwedge]

theorem aux_lem_prefix_limit_ratio_abs_four (t z w r e : ℝ) (he : |e| = 1) :
    |t + e * r + (z - w)| ≤ ((|t| + |z|) + |w|) + |r| := by
  have h1 : |t + e * r + (z - w)| ≤ |t + e * r| + |z - w| := by
    simpa only [Real.norm_eq_abs] using norm_add_le (t + e * r) (z - w)
  have h2 : |t + e * r| ≤ |t| + |e * r| := by
    simpa only [Real.norm_eq_abs] using norm_add_le t (e * r)
  have h3 : |z - w| ≤ |z| + |w| := by
    simpa only [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using norm_add_le z (-w)
  have h4 : |e * r| = |r| := by rw [abs_mul, he, one_mul]
  linarith

/-- Four-term Orlicz addition, with no concrete field expressions in its proof. -/
theorem aux_lem_prefix_limit_ratio_orlicz_four {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (X Y Z R : BilateralField d → ℝ) (a b c e : ℝ)
    (hX : AEStronglyMeasurable X (chaosSampleLaw M).toMeasure)
    (hY : AEStronglyMeasurable Y (chaosSampleLaw M).toMeasure)
    (hZ : AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure)
    (hR : AEStronglyMeasurable R (chaosSampleLaw M).toMeasure)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hZ0 : ∀ omega, 0 ≤ Z omega) (hR0 : ∀ omega, 0 ≤ R omega)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hXb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((X omega / a) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2)
    (hYb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((Y omega / b) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2)
    (hZb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((Z omega / c) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2)
    (hRb : (∫⁻ omega, ENNReal.ofReal (Real.exp ((R omega / e) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2) :
    (∫⁻ omega, ENNReal.ofReal
      (Real.exp ((((X omega + Y omega) + Z omega + R omega) / (a + b + c + e)) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  have h1 := aux_lem_prefix_limit_g8c_orlicz_add M X Y a b hX hY hX0 hY0 ha hb hXb hYb
  have h2 := aux_lem_prefix_limit_g8c_orlicz_add M (fun omega => X omega + Y omega) Z
    (a + b) c (hX.add hY) hZ (fun omega => add_nonneg (hX0 omega) (hY0 omega))
    hZ0 (add_pos ha hb) hc h1 hZb
  exact aux_lem_prefix_limit_g8c_orlicz_add M (fun omega => X omega + Y omega + Z omega) R
    (a + b + c) e ((hX.add hY).add hZ) hR
    (fun omega => add_nonneg (add_nonneg (hX0 omega) (hY0 omega)) (hZ0 omega))
    hR0 (add_pos (add_pos ha hb) hc) he h2 hRb

/-- Combine measurable finite corrections with the tail Orlicz estimate. -/
theorem aux_lem_prefix_limit_ratio_orlicz_of_decomposition {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (n m off edge : ℤ) (z w : SpatialCoordinates d)
    (Rz Rw Rret : Finset ℤ) (Tscale : ℝ) (hTscalepos : 0 < Tscale)
    (hAscale' : (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
      ((|∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z - omega (edge + 1 + (k : ℤ)) w)| /
        Tscale) ^ 2)) ∂(chaosSampleLaw M).toMeasure) ≤ 2)
    (hcombine_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
        (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)) =
      (∑' j : ℕ, (omega (edge + 1 + (j:ℤ)) z - omega (edge + 1 + (j:ℤ)) w)) +
        (if 0 ≤ off then (-1:ℝ) else 1) * (∑ i ∈ Rret, omega i 0) +
        ((∑ i ∈ Rz, (omega i z - omega i 0)) - ∑ i ∈ Rw, (omega i w - omega i 0))) :
    Measurable (fun omega => H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
        (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)) ∧
      (∫⁻ omega, ENNReal.ofReal (Real.exp ((|H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
        (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)| / (Tscale + 2 * ((max Rz.card 1 : ℕ) : ℝ) * M.delta +
          2 * ((max Rw.card 1 : ℕ) : ℝ) * M.delta + ((max Rret.card 1 : ℕ) : ℝ) * M.delta)) ^ 2))
        ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  -- Measurability
  have hAqmeas : Measurable (fun omega : BilateralField d => H omega z +
      aux_lem_prefix_limit_g8c_retained n z omega - (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)) := by
    have h1 : Measurable (fun omega : BilateralField d => H omega z) :=
      (continuous_eval_const z).measurable.comp hH.1
    have h2 : Measurable (fun omega : BilateralField d => H omega w) :=
      (continuous_eval_const w).measurable.comp hH.1
    have h3 := (aux_lem_prefix_limit_g8c_retained_continuous n z).measurable
    have h4 := (aux_lem_prefix_limit_g8c_retained_continuous m w).measurable
    exact (h1.add h3).sub (h2.add h4)
  have hRScont : Continuous
      (fun omega : BilateralField d => ∑ i ∈ Rret, omega i (0 : SpatialCoordinates d)) :=
    continuous_finset_sum Rret (fun i _ => (continuous_eval_const 0).comp (continuous_apply i))
  have hCZcont : Continuous (fun omega : BilateralField d =>
      ∑ i ∈ Rz, (omega i z - omega i (0 : SpatialCoordinates d))) :=
    continuous_finset_sum Rz (fun i _ =>
      ((continuous_eval_const z).comp (continuous_apply i)).sub
        ((continuous_eval_const 0).comp (continuous_apply i)))
  have hCWcont : Continuous (fun omega : BilateralField d =>
      ∑ i ∈ Rw, (omega i w - omega i (0 : SpatialCoordinates d))) :=
    continuous_finset_sum Rw (fun i _ =>
      ((continuous_eval_const w).comp (continuous_apply i)).sub
        ((continuous_eval_const 0).comp (continuous_apply i)))
  have hTSmeas : AEStronglyMeasurable
      (fun omega : BilateralField d => ∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z -
        omega (edge + 1 + (k : ℤ)) w)) (chaosSampleLaw M).toMeasure := by
    have hGmeas : AEStronglyMeasurable
        (fun omega : BilateralField d => (H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
            (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)) -
          (if 0 ≤ off then (-1 : ℝ) else 1) * (∑ i ∈ Rret, omega i 0) -
          ((∑ i ∈ Rz, (omega i z - omega i 0)) - ∑ i ∈ Rw, (omega i w - omega i 0)))
        (chaosSampleLaw M).toMeasure :=
      (((hAqmeas.sub (measurable_const.mul hRScont.measurable)).sub
        (hCZcont.measurable.sub hCWcont.measurable))).aestronglyMeasurable
    refine hGmeas.congr ?_
    filter_upwards [hcombine_ae] with omega heqo
    linarith [heqo]
  -- Convert the tail bound to `|·|` form (matches the other three pieces)
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hTSabsmeas : AEStronglyMeasurable
      (fun omega : BilateralField d => |∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z -
        omega (edge + 1 + (k : ℤ)) w)|) (chaosSampleLaw M).toMeasure :=
    hTSmeas.norm.congr (Filter.Eventually.of_forall (fun omega => Real.norm_eq_abs _))
  have hCZabsmeas : AEStronglyMeasurable
      (fun omega : BilateralField d => |∑ i ∈ Rz, (omega i z - omega i (0:SpatialCoordinates d))|)
      (chaosSampleLaw M).toMeasure := hCZcont.abs.measurable.aestronglyMeasurable
  have hCWabsmeas : AEStronglyMeasurable
      (fun omega : BilateralField d => |∑ i ∈ Rw, (omega i w - omega i (0:SpatialCoordinates d))|)
      (chaosSampleLaw M).toMeasure := hCWcont.abs.measurable.aestronglyMeasurable
  have hRSabsmeas : AEStronglyMeasurable
      (fun omega : BilateralField d => |∑ i ∈ Rret, omega i (0:SpatialCoordinates d)|)
      (chaosSampleLaw M).toMeasure := hRScont.abs.measurable.aestronglyMeasurable
  have hRzdiffscale := aux_lem_prefix_limit_g8c_finset_diff_ogamma' M Rz (fun _ => z)
    (fun _ => (0 : SpatialCoordinates d))
  have hRwdiffscale := aux_lem_prefix_limit_g8c_finset_diff_ogamma' M Rw (fun _ => w)
    (fun _ => (0 : SpatialCoordinates d))
  have hRretptscale := aux_lem_prefix_limit_g8c_finset_point_ogamma' M Rret (fun _ => (0 : SpatialCoordinates d))
  set Zscale : ℝ := 2 * ((max Rz.card 1 : ℕ) : ℝ) * M.delta with hZscaledef
  set Wscale : ℝ := 2 * ((max Rw.card 1 : ℕ) : ℝ) * M.delta with hWscaledef
  set Rscale : ℝ := ((max Rret.card 1 : ℕ) : ℝ) * M.delta with hRscaledef
  have hZscalepos : 0 < Zscale := by rw [hZscaledef]; positivity
  have hWscalepos : 0 < Wscale := by rw [hWscaledef]; positivity
  have hRscalepos : 0 < Rscale := by rw [hRscaledef]; positivity
  have hadd3 := aux_lem_prefix_limit_ratio_orlicz_four M
    (fun omega => |∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z - omega (edge + 1 + (k : ℤ)) w)|)
    (fun omega => |∑ i ∈ Rz, (omega i z - omega i (0 : SpatialCoordinates d))|)
    (fun omega => |∑ i ∈ Rw, (omega i w - omega i (0 : SpatialCoordinates d))|)
    (fun omega => |∑ i ∈ Rret, omega i (0 : SpatialCoordinates d)|)
    Tscale Zscale Wscale Rscale hTSabsmeas hCZabsmeas hCWabsmeas hRSabsmeas
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
    hTscalepos hZscalepos hWscalepos hRscalepos hAscale' hRzdiffscale hRwdiffscale hRretptscale
  -- A.e. domination: |Aq| ≤ the combined nonneg sum
  have hAqdom : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      0 ≤ |H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
          (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)| ∧
      |H omega z + aux_lem_prefix_limit_g8c_retained n z omega - (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)| ≤
        ((|∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z - omega (edge + 1 + (k : ℤ)) w)| +
          |∑ i ∈ Rz, (omega i z - omega i (0:SpatialCoordinates d))|) +
          |∑ i ∈ Rw, (omega i w - omega i (0:SpatialCoordinates d))|) +
        |∑ i ∈ Rret, omega i (0:SpatialCoordinates d)| := by
    filter_upwards [hcombine_ae] with omega heqo
    refine ⟨abs_nonneg _, ?_⟩
    rw [heqo]
    exact aux_lem_prefix_limit_ratio_abs_four _ _ _ _ _ (by split_ifs <;> norm_num)
  have hOrlicz := aux_lem_prefix_limit_g8c_orlicz_mono_ae M
    (fun omega => |H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
      (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)|)
    (fun omega => ((|∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z - omega (edge + 1 + (k : ℤ)) w)| +
      |∑ i ∈ Rz, (omega i z - omega i (0:SpatialCoordinates d))|) +
      |∑ i ∈ Rw, (omega i w - omega i (0:SpatialCoordinates d))|) +
      |∑ i ∈ Rret, omega i (0:SpatialCoordinates d)|)
    (Tscale + Zscale + Wscale + Rscale) hAqdom (by positivity) hadd3
  exact ⟨hAqmeas, hOrlicz⟩

/-- Uniform sub-Gaussian control of the logarithmic reference ratio. -/
theorem aux_lem_prefix_limit_ratio_uniform_orlicz {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (off : ℤ) (sh : SpatialCoordinates d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (n : ℤ) (z : SpatialCoordinates d),
        Measurable (fun omega => H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
        (H omega (z + ((3 : ℝ) ^ (-n)) • sh) +
          aux_lem_prefix_limit_g8c_retained (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega)) ∧
        (∫⁻ omega, ENNReal.ofReal (Real.exp ((|H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
        (H omega (z + ((3 : ℝ) ^ (-n)) • sh) +
          aux_lem_prefix_limit_g8c_retained (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega)| / (C * M.delta)) ^ 2))
          ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
  classical
  obtain ⟨E0raw, hE0raw⟩ := aux_lem_prefix_limit_g8b_exists_e0 sh
  set E0 : ℕ := max E0raw (max 1 (1 - off).toNat) with hE0def
  have hE0ge1 : 1 ≤ E0 := le_trans (le_max_left 1 (1 - off).toNat) (le_max_right E0raw _)
  have hE0geoff : (1 : ℤ) - off ≤ (E0 : ℤ) := by
    have h1 : (1 - off).toNat ≤ E0 := le_trans (le_max_right 1 (1 - off).toNat)
      (le_max_right E0raw _)
    omega
  have hE0bound : (2 / 3 : ℝ) * (‖sh‖ + 1) ≤ (3 : ℝ) ^ E0 := by
    have hmono : (3 : ℝ) ^ E0raw ≤ (3 : ℝ) ^ E0 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (le_max_left E0raw _)
    linarith
  obtain ⟨mtail, hmtailpos, htail⟩ := aux_lem_prefix_limit_g8c_tail_uniform_exp (d := d)
  set K_A : ℝ := (1 / 2 : ℝ) * (mtail : ℝ) * (‖sh‖ + 1) * (3 : ℝ) ^ (-((E0 : ℤ) - 1)) +
      2 * ((max (((E0 : ℤ) - 1).toNat) 1 : ℕ) : ℝ) +
      2 * ((max (((E0 : ℤ) - 1 + off).toNat) 1 : ℕ) : ℝ) +
      ((max (off.natAbs) 1 : ℕ) : ℝ) with hK_Adef
  have hK_Apos : 0 < K_A := by
    have h1 : (0 : ℝ) < (1 / 2 : ℝ) * (mtail : ℝ) * (‖sh‖ + 1) * (3 : ℝ) ^ (-((E0 : ℤ) - 1)) := by
      positivity
    have h2 : (0 : ℝ) ≤ 2 * ((max (((E0 : ℤ) - 1).toNat) 1 : ℕ) : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 2 * ((max (((E0 : ℤ) - 1 + off).toNat) 1 : ℕ) : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ ((max (off.natAbs) 1 : ℕ) : ℝ) := by positivity
    rw [hK_Adef]; linarith
  clear_value E0 K_A
  refine ⟨K_A, hK_Apos, ?_⟩
  intro M H hH n z
  set m : ℤ := n + off with hmdef
  set w : SpatialCoordinates d := z + ((3 : ℝ) ^ (-n)) • sh with hwdef
  set edge : ℤ := (E0 : ℤ) - n - 1 with hedgedef
  have hedgen' : edge + n = (E0 : ℤ) - 1 := by rw [hedgedef]; ring
  have hedgem' : edge + m = (E0 : ℤ) - 1 + off := by rw [hedgedef, hmdef]; ring
  have hedgeineq : (2 / 3 : ℝ) * (‖sh‖ + 1) ≤ (3 : ℝ) ^ (edge + n + 1) := by
    have heq1 : edge + n + 1 = (E0 : ℤ) := by rw [hedgen']; ring
    rw [heq1, show ((E0:ℤ)) = ((E0:ℕ):ℤ) from rfl, zpow_natCast]
    exact hE0bound
  have hAscale := htail M z sh n edge hedgeineq
  set Rz : Finset ℤ := Finset.Ico (-n + 1) (edge + 1) with hRzdef
  set Rw : Finset ℤ := Finset.Ico (-m + 1) (edge + 1) with hRwdef
  set Rret : Finset ℤ := if 0 ≤ off then Finset.Ico (1 - m) (1 - n)
    else Finset.Ico (1 - n) (1 - m) with hRretdef
  have hRzcard : Rz.card = ((E0:ℤ) - 1).toNat := by
    rw [hRzdef, Int.card_Ico]
    congr 1
    omega
  have hRwcard : Rw.card = ((E0:ℤ) - 1 + off).toNat := by
    rw [hRwdef, Int.card_Ico]
    congr 1
    omega
  have hRretcard : Rret.card = off.natAbs := by
    rw [hRretdef]
    by_cases hoff : 0 ≤ off
    · rw [if_pos hoff, Int.card_Ico]
      omega
    · rw [if_neg hoff, Int.card_Ico]
      omega
  clear_value edge Rz Rw Rret
  have hcombine_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
        (H omega w + aux_lem_prefix_limit_g8c_retained m w omega)) =
      (∑' j : ℕ, (omega (edge + 1 + (j:ℤ)) z - omega (edge + 1 + (j:ℤ)) w)) +
        (if 0 ≤ off then (-1:ℝ) else 1) * (∑ i ∈ Rret, omega i 0) +
        ((∑ i ∈ Rz, (omega i z - omega i 0)) - ∑ i ∈ Rw, (omega i w - omega i 0)) := by
    simpa only [hmdef, hRzdef, hRwdef, hRretdef] using
      aux_lem_prefix_limit_ratio_tail_decomposition M H hH n off edge z w
        (by omega) (by omega)
  let Tscale : ℝ := (1 / 2 : ℝ) * (mtail : ℝ) * M.delta * (‖sh‖ + 1) *
    (3 : ℝ) ^ (-(edge + n))
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hTscalepos : 0 < Tscale := by dsimp only [Tscale]; positivity
  have hAscale' : (∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp
      ((|∑' k : ℕ, (omega (edge + 1 + (k : ℤ)) z - omega (edge + 1 + (k : ℤ)) w)| /
        Tscale) ^ 2)) ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
    simpa only [Real.norm_eq_abs] using hAscale
  obtain ⟨hmeas, hbound⟩ := aux_lem_prefix_limit_ratio_orlicz_of_decomposition
    M H hH n m off edge z w Rz Rw Rret Tscale hTscalepos hAscale' hcombine_ae
  have hscaleeq : Tscale + 2 * ((max Rz.card 1 : ℕ) : ℝ) * M.delta +
          2 * ((max Rw.card 1 : ℕ) : ℝ) * M.delta + ((max Rret.card 1 : ℕ) : ℝ) * M.delta = K_A * M.delta := by
    dsimp only [Tscale]
    rw [hK_Adef, hRzcard, hRwcard, hRretcard, hedgen']
    ring
  rw [hscaleeq] at hbound
  exact ⟨hmeas, hbound⟩

/-- Convert uniform logarithmic Orlicz control into exponential Lp moments. -/
theorem aux_lem_prefix_limit_ratio_exp_memLp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hM : M.delta ≤ 1)
    (A : BilateralField d → ℝ) (hA : Measurable A)
    (C : ℝ) (hC : 0 < C) (p : ℝ) (hp : 0 < p)
    (hOrlicz : (∫⁻ omega, ENNReal.ofReal (Real.exp ((|A omega| / (C * M.delta)) ^ 2))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2) :
    MemLp (fun omega => Real.exp (A omega)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun omega => Real.exp (A omega)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (((C * 1) ^ 2 * p ^ 2 / 4 + Real.log 2) / p)) := by
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨hintP, hbdP⟩ := orlicz_exp_linear_integrable_integral_le
    (chaosSampleLaw M).toMeasure (fun omega => |A omega|) (C * M.delta) p
    hA.abs (fun _ => abs_nonneg _) (by positivity) hp.le hOrlicz
  have hdom : ∀ omega, Real.exp (p * A omega) ≤ Real.exp (p * |A omega|) := by
    intro omega
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) hp.le)
  have hintSigned : Integrable (fun omega => Real.exp (p * A omega))
      (chaosSampleLaw M).toMeasure := by
    refine hintP.mono' ((measurable_const.mul hA).exp).aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hdom omega
  have hbdSigned : (∫ omega, Real.exp (p * A omega) ∂(chaosSampleLaw M).toMeasure) ≤
      2 * Real.exp ((C * M.delta) ^ 2 * p ^ 2 / 4) :=
    (integral_mono hintSigned hintP hdom).trans hbdP
  have hcval : Real.exp (p * (((C * M.delta) ^ 2 * p ^ 2 / 4 + Real.log 2) / p)) =
      2 * Real.exp ((C * M.delta) ^ 2 * p ^ 2 / 4) := by
    rw [mul_div_cancel₀ _ hp.ne', Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    ring
  have hbdFinal : (∫ omega, Real.exp (p * A omega) ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp (p * (((C * M.delta) ^ 2 * p ^ 2 / 4 + Real.log 2) / p)) := by
    rw [hcval]
    exact hbdSigned
  obtain ⟨hmem, hnorm⟩ := aux_finite_cutoff_log_abs_majorant_eLpNorm_exp
    (chaosSampleLaw M).toMeasure A hA p hp hintSigned
    (((C * M.delta) ^ 2 * p ^ 2 / 4 + Real.log 2) / p) hbdFinal
  refine ⟨hmem, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  apply Real.exp_le_exp.mpr
  have hscalele : C * M.delta ≤ C * 1 := mul_le_mul_of_nonneg_left hM hC.le
  have hsqle : (C * M.delta) ^ 2 ≤ (C * 1) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hscalele
  gcongr

theorem aux_lem_prefix_limit_g8c_rr_cw_moment_core {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (moments : Finset ℝ) (hmom : ∀ p ∈ moments, 1 ≤ p)
    (off : ℤ) (sh : SpatialCoordinates d) :
    ∃ deltaC : ℝ, 0 < deltaC ∧ ∃ KC : ℝ → ℝ, (∀ p ∈ insert 1 moments, 0 < KC p) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaC →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (n : ℤ) (z : SpatialCoordinates d),
      ∀ p ∈ insert 1 moments,
        MemLp (fun omega => Real.exp (H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
            (H omega (z + ((3 : ℝ) ^ (-n)) • sh) +
              aux_lem_prefix_limit_g8c_retained (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega)))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => Real.exp (H omega z + aux_lem_prefix_limit_g8c_retained n z omega -
            (H omega (z + ((3 : ℝ) ^ (-n)) • sh) +
              aux_lem_prefix_limit_g8c_retained (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega)))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (KC p) := by
  obtain ⟨C, hC, hbound⟩ := aux_lem_prefix_limit_ratio_uniform_orlicz off sh
  refine ⟨1, one_pos, fun p => Real.exp (((C * 1) ^ 2 * p ^ 2 / 4 + Real.log 2) / p), ?_, ?_⟩
  · intro p _
    positivity
  · intro M hM H hH n z p hp
    have hp1 : 1 ≤ p := by
      rcases Finset.mem_insert.mp hp with h | h
      · exact h.ge
      · exact hmom p h
    obtain ⟨hmeas, horlicz⟩ := hbound M H hH n z
    exact aux_lem_prefix_limit_ratio_exp_memLp M hM _ hmeas C hC p (by linarith) horlicz

theorem aux_lem_prefix_limit_rr_cw_moment
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (moments : Finset ℝ) (hmom : ∀ p ∈ moments, 1 ≤ p)
    (off : ℤ) (sh : SpatialCoordinates d) :
    ∃ deltaC : ℝ, 0 < deltaC ∧ ∃ KC : ℝ → ℝ, (∀ p ∈ insert 1 moments, 0 < KC p) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaC →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (n : ℤ) (z : SpatialCoordinates d),
      let m : ℤ := n + off
      let w : SpatialCoordinates d := z + ((3 : ℝ) ^ (-n)) • sh
      let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
        fun k y omega => if 0 ≤ k then ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) y
          else -∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) y
      ∀ p ∈ insert 1 moments,
        MemLp (fun omega => Real.exp (H omega z + retained n z omega -
            (H omega w + retained m w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => Real.exp (H omega z + retained n z omega -
            (H omega w + retained m w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (KC p) := by
  simpa only [aux_lem_prefix_limit_g8c_retained, aux_lem_prefix_limit_g8c_ret] using
    (aux_lem_prefix_limit_g8c_rr_cw_moment_core hd moments hmom off sh)

/-- G9-4 (OPEN): the fixed (non-`N`-dependent) random factor of the "reference ratio"
coordinate has a finite first moment.  Plausible from subgaussian/finite-moment control of
individual `BilateralField` layers (`SubdiffusiveProcess.CoarseGrainingVocab.OGammaTail.HasSubgaussianMGF`,
`ogammaLE_sum_range_of_iIndepFun`) plus `InfraredCharacterization`'s a.s. limit
representation of `H`, but not verified against a specific citation within this session's
budget -- flagged, not fabricated. This is the ONLY missing ingredient for a fully closed
`L¹`-compactness (hence `TendstoInMeasure`) proof of the reference-ratio coordinate. -/
theorem aux_lem_prefix_limit_g9_reference_factor_memLp {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
    (nn mm : ℤ) (z w : SpatialCoordinates d) :
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun n zz omega => if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, omega (-j) zz
        else -∑ j ∈ Finset.Ico n (0 : ℤ), omega (-j) zz
    MemLp (fun omega => Real.exp (H omega z + retained nn z omega -
        (H omega w + retained mm w omega))) 1 (chaosSampleLaw M).toMeasure := by
  intro retained
  show MemLp (fun omega => Real.exp (H omega z + aux_lem_prefix_limit_g8c_retained nn z omega -
      (H omega w + aux_lem_prefix_limit_g8c_retained mm w omega))) 1 (chaosSampleLaw M).toMeasure
  set off : ℤ := mm - nn with hoffdef
  set sh : SpatialCoordinates d := (3 : ℝ) ^ nn • (w - z) with hshdef
  have hwsub : z + (3 : ℝ) ^ (-nn) • sh = w := by
    rw [hshdef, smul_smul, ← zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num), neg_add_cancel, zpow_zero,
      one_smul]
    abel
  have hmoff : nn + off = mm := by omega
  have hMdelta1 : M.delta ≤ 1 := le_trans M.shellPrefix.delta_le_half (by norm_num)
  obtain ⟨C, hCpos, hbound⟩ := aux_lem_prefix_limit_ratio_uniform_orlicz off sh
  obtain ⟨hAmeas, hOrlicz⟩ := hbound M H _hH nn z
  rw [hmoff, hwsub] at hAmeas hOrlicz
  have hMemLp := (aux_lem_prefix_limit_ratio_exp_memLp M hMdelta1
    (fun omega => H omega z + aux_lem_prefix_limit_g8c_retained nn z omega -
      (H omega w + aux_lem_prefix_limit_g8c_retained mm w omega))
    hAmeas C hCpos 1 one_pos hOrlicz).1
  simpa only [ENNReal.ofReal_one] using hMemLp

/-- G9-5 (PROVEN): if a fixed function `Cw` is `MemLp 1 μ` and `kR : ℕ → ℝ` is bounded
within `[0, C]`, the family `N ↦ kR N • Cw` is `L¹`-relatively compact -- feeding directly
into `aux_lem_prefix_limit_atom_extraction_subseq`'s `hcomp` hypothesis. -/
theorem aux_lem_prefix_limit_g9_scaled_compact {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Cw : Ω → ℝ) (hCw : MemLp Cw 1 μ) (kR : ℕ → ℝ) (C : ℝ)
    (hkR : ∀ N, kR N ∈ Set.Icc (0 : ℝ) C) :
    ∃ hmem : ∀ N, MemLp (kR N • Cw) 1 μ,
      IsCompact (closure (Set.range (fun N => (hmem N).toLp (kR N • Cw)))) := by
  refine ⟨fun N => hCw.const_smul (kR N), ?_⟩
  set g : Lp ℝ 1 μ := hCw.toLp Cw with hg
  have hΦcont : Continuous (fun c : ℝ => c • g) := continuous_id.smul continuous_const
  have hKcompact : IsCompact ((fun c : ℝ => c • g) '' Set.Icc (0 : ℝ) C) :=
    isCompact_Icc.image hΦcont
  have hsub : Set.range (fun N => (hCw.const_smul (kR N)).toLp (kR N • Cw)) ⊆
      (fun c : ℝ => c • g) '' Set.Icc (0 : ℝ) C := by
    rintro _ ⟨N, rfl⟩
    exact ⟨kR N, hkR N, (MemLp.toLp_const_smul (kR N) hCw).symm⟩
  exact hKcompact.of_isClosed_subset isClosed_closure (closure_minimal hsub hKcompact.isClosed)

/-- G9 (typed goal): joint extraction, inside any prescribed `phi`, along which every full coarse response coordinate
(`Sum.inr`) at every countable position, offset and test converges in probability (paper 2749--2752 via
mfd:sec-local-form, mfd:prop-response-compact, conv_represented_sequence). -/
theorem aux_lem_prefix_limit_response_in_measure
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
    ∃ deltaE : ℝ, 0 < deltaE ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaE →
        ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)),
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
        ∀ (Pos : Type) [Countable Pos] (level : Pos → ℤ) (centre : Pos → SpatialCoordinates d)
          (phi : ℕ → ℕ), StrictMono phi →
          ∃ psi : ℕ → ℕ, StrictMono psi ∧
            ∀ (pos : Pos) (j : ℤ) (i : Fin T) (rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)),
              ∃ lim : BilateralField d → ℝ, TendstoInMeasure (chaosSampleLaw M).toMeasure
                (fun n omega => value (phi (psi n)) (level pos + j) (centre pos) (Sum.inr (i, rt)) omega)
                atTop lim := by
  obtain ⟨delta0, hdelta0pos, hChart⟩ :=
    lem_prefix_limit_g9_chart_compact hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp sigma s hs hsigma
  refine ⟨min 1 delta0, lt_min one_pos hdelta0pos, ?_⟩
  intro M hM Rm hRmC Sreg _It H hH eta hEta F Praw Rraw Draw Z rawGood hPrimitive sidePos
  intro kappa retained reference Test value
  intro Pos _ level centre phi hphi
  have hMdelta0 : M.delta ≤ delta0 := le_trans hM (min_le_right 1 delta0)
  have hval_ref : ∀ (pos : Pos) (jz : ℤ) (i : Fin T) (N : ℕ) (omega : BilateralField d),
      value N (level pos + jz) (centre pos)
          (Sum.inr (i, Sum.inr (Sum.inr (1 : Fin 2)))) omega =
        (if (level pos + jz) ≤ (N : ℤ) ∧ (level pos + jz + offset i) ≤ (N : ℤ) then
            reference N (level pos + jz) (centre pos) omega /
              reference N (level pos + jz + offset i)
                (centre pos + (3 : ℝ) ^ (-(level pos + jz)) • shift i) omega
          else 0) := by
    intro pos jz i N omega
    rfl
  have hcomp : ∀ kk : Pos × ℤ × Fin T × (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)),
      ∃ hmem : ∀ N, MemLp (fun omega => value N (level kk.1 + kk.2.1) (centre kk.1)
          (Sum.inr (kk.2.2.1, kk.2.2.2)) omega) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp (fun omega =>
          value N (level kk.1 + kk.2.1) (centre kk.1)
            (Sum.inr (kk.2.2.1, kk.2.2.2)) omega)))) := by
    rintro ⟨pos, jz, i, rt⟩
    dsimp only
    by_cases hrt : rt = Sum.inr (Sum.inr (1 : Fin 2))
    · subst hrt
      set nn : ℤ := level pos + jz with hnn
      set mm : ℤ := level pos + jz + offset i with hmm
      set z : SpatialCoordinates d := centre pos with hz
      set w : SpatialCoordinates d :=
        centre pos + (3 : ℝ) ^ (-(level pos + jz)) • shift i with hw
      obtain ⟨C, hCpos, hCbd⟩ := aux_lem_prefix_limit_g9_kappa_ratio_bounded M Rm nn mm
      have hCw := aux_lem_prefix_limit_g9_reference_factor_memLp M H hH nn mm z w
      set Cw : BilateralField d → ℝ := fun omega => Real.exp (H omega z + retained nn z omega -
          (H omega w + retained mm w omega)) with hCwdef
      set kR : ℕ → ℝ := fun N => if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
          kappa ((N : ℤ) - nn).toNat / kappa ((N : ℤ) - mm).toNat else 0 with hkRdef
      have hfeq : (fun N => fun omega => value N (level pos + jz) (centre pos)
          (Sum.inr (i, Sum.inr (Sum.inr (1 : Fin 2)))) omega) = (fun N => kR N • Cw) := by
        funext N omega
        show value N (level pos + jz) (centre pos)
            (Sum.inr (i, Sum.inr (Sum.inr (1 : Fin 2)))) omega = (kR N • Cw) omega
        rw [hval_ref pos jz i N omega]
        show (if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then reference N nn z omega / reference N mm w omega
            else 0) = kR N * Cw omega
        rw [aux_lem_prefix_limit_g9_value_ref_ratio_eq]
      show ∃ hmem : ∀ N, MemLp ((fun N => fun omega => value N (level pos + jz) (centre pos)
          (Sum.inr (i, Sum.inr (Sum.inr (1 : Fin 2)))) omega) N) 1 (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp
          ((fun N => fun omega => value N (level pos + jz) (centre pos)
            (Sum.inr (i, Sum.inr (Sum.inr (1 : Fin 2)))) omega) N))))
      rw [hfeq]
      exact aux_lem_prefix_limit_g9_scaled_compact (μ := (chaosSampleLaw M).toMeasure) Cw hCw kR C
        hCbd
    · -- The six coefficient-field-dependent shapes (ellipticity ratios, chart matrix
      -- ratios, homogenization error): wired to G9-6 `lem_prefix_limit_g9_chart_compact`
      -- (needs the coefficient-field compactness + continuity-transfer machinery flagged
      -- there as missing from the imported libraries; the only sorry this branch inherits).
      set nn : ℤ := level pos + jz with hnn
      set mm : ℤ := level pos + jz + offset i with hmm
      set z : SpatialCoordinates d := centre pos with hz
      set w : SpatialCoordinates d :=
        centre pos + (3 : ℝ) ^ (-(level pos + jz)) • shift i with hw
      have hfeq : (fun N => fun omega => value N nn z (Sum.inr (i, rt)) omega) =
          (fun N => fun omega =>
            let aN := Lane4.cutoffPositiveCoefficient M H omega N w (sidePos mm)
            let r := (3 : ℝ) ^ (-mm)
            let ref := reference N mm w omega
            if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
              Sum.elim
                (fun j => if j = 0 then I.lam w r (sidePos mm) aN w r sigma 2 / ref
                  else if j = 1 then I.Lam w r (sidePos mm) aN w r sigma 2 / ref
                  else ref / I.lam w r (sidePos mm) aN w r sigma 2)
                (Sum.elim
                  (fun ab => if ab.1 then
                    (Homogenization.Book.Ch02.sigmaCoarse
                      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                      ((I.chart w r (sidePos mm) aN w r).coeffOn
                        (Homogenization.originCube d 0))) ab.2.1 ab.2.2 / ref
                    else ref * (Homogenization.Book.Ch02.sigmaStarInvCoarse
                      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                      ((I.chart w r (sidePos mm) aN w r).coeffOn
                        (Homogenization.originCube d 0))) ab.2.1 ab.2.2)
                  (fun j => if j = 0 then I.err w r (sidePos mm) aN w r ref s 2
                    else reference N nn z omega / ref)) rt
            else 0) := by
        funext N omega
        rfl
      show ∃ hmem : ∀ N, MemLp ((fun N => fun omega => value N nn z (Sum.inr (i, rt)) omega) N) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range (fun N => (hmem N).toLp
          ((fun N => fun omega => value N nn z (Sum.inr (i, rt)) omega) N))))
      rw [hfeq]
      exact hChart M hMdelta0 Rm hRmC Sreg _It H hH sidePos nn mm z w rt hrt
  obtain ⟨psi, hpsi, hlim⟩ := aux_lem_prefix_limit_atom_extraction_subseq
    (μ := (chaosSampleLaw M).toMeasure)
    (κ := Pos × ℤ × Fin T × (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)))
    (fun kk N => fun omega => value N (level kk.1 + kk.2.1) (centre kk.1)
      (Sum.inr (kk.2.2.1, kk.2.2.2)) omega)
    hcomp phi
  exact ⟨psi, hpsi, fun pos jz i rt => hlim (pos, jz, i, rt)⟩


/- ===================================================================================
   G8 response moments (relocated proof).  The typed goal `aux_lem_prefix_limit_response_moments`
   (header unchanged) is stated and proved here, after the G9 helper lemmas
   (`aux_lem_prefix_limit_g9_*`, `aux_lem_prefix_limit_rr_cw_moment`) it consumes; its only use
   is `lem_prefix_limit` below.  Suppliers: `lem_prefix_limit_g9_moving_chart_moment` (five
   coefficient shapes, model-uniform), `lem_prefix_limit_g9_chart_compact` (measurability of the
   coefficient-dependent coordinates), `aux_lem_prefix_limit_rr_cw_moment` (reference-ratio
   factor) and `in_J.bound_ellipticities_by_error` (homogenization error).
   =================================================================================== -/

/-- A common positive lower bound for finitely many positive numbers. -/
theorem aux_lem_prefix_limit_g8r_exists_common_delta {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a S ha ih =>
    obtain ⟨δ, hδ, hδS⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (f a), lt_min hδ (hf a (Finset.mem_insert_self a S)), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδS i hi)

theorem aux_lem_prefix_limit_g8r_kappa_ratio_explicit {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M) (nn mm : ℤ) :
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
    ∀ N : ℕ,
      (if nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ) then
          kappa ((N : ℤ) - nn).toNat / kappa ((N : ℤ) - mm).toNat
        else 0) ∈ Set.Icc (0 : ℝ)
          (Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(mm : ℝ) - nn|)) := by
  intro kappa
  have htau := aux_lem_prefix_limit_g9_tauSq_nonneg M Rm
  set k : ℝ := |(mm : ℝ) - nn| with hkdef
  have hk0 : 0 ≤ k := abs_nonneg _
  intro N
  by_cases hguard : nn ≤ (N : ℤ) ∧ mm ≤ (N : ℤ)
  · rw [if_pos hguard]
    set A : ℕ := ((N : ℤ) - nn).toNat with hAdef
    set B : ℕ := ((N : ℤ) - mm).toNat with hBdef
    have hApos := ahom_pos M A
    have hBpos := ahom_pos M B
    have hkAB_pos : 0 < kappa A / kappa B :=
      div_pos (mul_pos (Real.exp_pos _) hApos) (mul_pos (Real.exp_pos _) hBpos)
    refine ⟨hkAB_pos.le, ?_⟩
    have hdiff : |(A : ℝ) - B| ≤ k := aux_lem_prefix_limit_g9_toNat_diff_le N nn mm
    obtain ⟨hle1, hle2⟩ := abs_le.mp hdiff
    have hexp_arg : ((A : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
        (((B : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B) := by ring
    have hkeq : kappa A / kappa B =
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) * (ahom M A / ahom M B) := by
      show (Real.exp (((A : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M A) /
          (Real.exp (((B : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M B) = _
      rw [← div_mul_div_comm, ← Real.exp_sub, hexp_arg]
    rw [hkeq]
    have hexp_env : Real.exp (-(SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)) ≤
          Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) ∧
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) ≤
          Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := by
      constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [hle1, hle2, htau]
    have hahom_env := aux_lem_prefix_limit_g9_ahom_ratio_bound_any M Rm A B
    have hwiden : Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)) ≤
          Real.exp (-(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(A : ℝ) - B|)) ∧
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |(A : ℝ) - B|) ≤
          Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := by
      constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [hdiff, htau]
    obtain ⟨e1, e2⟩ := aux_lem_prefix_limit_g9_exp_env_mul
        (c1 := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)
        (c2 := 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k)
        hexp_env.1 hexp_env.2 (hwiden.1.trans hahom_env.1) (hahom_env.2.trans hwiden.2)
    calc Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((A : ℝ) - B)) * (ahom M A / ahom M B)
        ≤ Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k +
            2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := e2
      _ ≤ Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * k) := by
          apply Real.exp_le_exp.mpr; nlinarith
  · rw [if_neg hguard]
    exact ⟨le_refl 0, (Real.exp_pos _).le⟩



/-- The homogenization-error coordinate is dominated by `1 + Λ/ref + ref/λ`, so it inherits the `L^p`
bound of the two ellipticity ratios; measurability is supplied separately. -/
theorem aux_lem_prefix_limit_g8r_err_of_ellipticity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 ≤ p)
    (err Lam lam ref : Ω → ℝ) (hmeas : AEStronglyMeasurable err μ)
    (hLam : ∀ ω, 0 < Lam ω) (hlam : ∀ ω, 0 < lam ω) (href : ∀ ω, 0 < ref ω)
    (hbound : ∀ ω, (1 / 2 : ℝ) * err ω ^ 2 ≤ max ((ref ω)⁻¹ * Lam ω) (ref ω * (lam ω)⁻¹))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hA : MemLp (fun ω => Lam ω / ref ω) (ENNReal.ofReal p) μ)
    (hAn : eLpNorm (fun ω => Lam ω / ref ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K)
    (hB : MemLp (fun ω => ref ω / lam ω) (ENNReal.ofReal p) μ)
    (hBn : eLpNorm (fun ω => ref ω / lam ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) :
    MemLp err (ENNReal.ofReal p) μ ∧
      eLpNorm err (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (1 + 2 * K) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have h1n : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal p) μ ≤ 1 := by
    rw [eLpNorm_const _ hpne (NeZero.ne μ)]
    simp
  have h1mem : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal p) μ := memLp_const 1
  have hdom : ∀ ω, ‖err ω‖ ≤ ‖1 + Lam ω / ref ω + ref ω / lam ω‖ := by
    intro ω
    have ha : 0 ≤ Lam ω / ref ω := (div_pos (hLam ω) (href ω)).le
    have hb : 0 ≤ ref ω / lam ω := (div_pos (href ω) (hlam ω)).le
    have hmax : max ((ref ω)⁻¹ * Lam ω) (ref ω * (lam ω)⁻¹) ≤ Lam ω / ref ω + ref ω / lam ω := by
      apply max_le
      · rw [inv_mul_eq_div]; linarith
      · rw [← div_eq_mul_inv]; linarith
    have hsq : err ω ^ 2 ≤ (1 + (Lam ω / ref ω + ref ω / lam ω)) ^ 2 := by
      nlinarith [hbound ω, sq_nonneg (Lam ω / ref ω + ref ω / lam ω)]
    have h1 : |err ω| ≤ 1 + (Lam ω / ref ω + ref ω / lam ω) :=
      abs_le_of_sq_le_sq' hsq (by positivity) |> fun h => abs_le.mpr h
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hnn : 0 ≤ 1 + Lam ω / ref ω + ref ω / lam ω := by positivity
    rw [abs_of_nonneg hnn]
    linarith
  have hgmem : MemLp (fun ω => 1 + Lam ω / ref ω + ref ω / lam ω) (ENNReal.ofReal p) μ :=
    (h1mem.add hA).add hB
  refine ⟨hgmem.of_le hmeas (Filter.Eventually.of_forall hdom), ?_⟩
  have hs1 : eLpNorm (fun ω => 1 + Lam ω / ref ω + ref ω / lam ω) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => 1 + Lam ω / ref ω) (ENNReal.ofReal p) μ +
        eLpNorm (fun ω => ref ω / lam ω) (ENNReal.ofReal p) μ :=
    eLpNorm_add_le hp1
  have hs2 : eLpNorm (fun ω => 1 + Lam ω / ref ω) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal p) μ +
        eLpNorm (fun ω => Lam ω / ref ω) (ENNReal.ofReal p) μ :=
    eLpNorm_add_le hp1
  calc eLpNorm err (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun ω => 1 + Lam ω / ref ω + ref ω / lam ω) (ENNReal.ofReal p) μ :=
        eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall hdom)
    _ ≤ (1 + ENNReal.ofReal K) + ENNReal.ofReal K :=
        hs1.trans (add_le_add (hs2.trans (add_le_add h1n hAn)) hBn)
    _ = ENNReal.ofReal (1 + 2 * K) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hK0,
          ← ENNReal.ofReal_add (by positivity) hK0]
        congr 1; ring


/-- The model-uniform bound `τ² ≤ 1` (from `τ² ≤ (log 2 / 2) δ²` and `δ ≤ 1/2`). -/
theorem aux_lem_prefix_limit_g8r_tauSq_le_one {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 1 := by
  have h := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
  have hp := M.shellPrefix.delta_pos
  have hh := M.shellPrefix.delta_le_half
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsq : M.delta ^ 2 ≤ 1 / 4 := by nlinarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hlog0 (sq_nonneg M.delta)]

/-- The reference-ratio coordinate is the product of the deterministic `κ`-ratio (bounded by
`exp (3 τ² |off|) ≤ exp (3 |off|)`, uniformly in `N`, `n`) and the random factor whose moments are
`aux_lem_prefix_limit_rr_cw_moment`. -/
theorem aux_lem_prefix_limit_g8r_refratio_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (off : ℤ) (sh : SpatialCoordinates d) (p : ℝ) (KC : ℝ)
    (hCw : ∀ (n : ℤ) (z : SpatialCoordinates d),
      let m : ℤ := n + off
      let w : SpatialCoordinates d := z + ((3 : ℝ) ^ (-n)) • sh
      let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
        fun k y omega => if 0 ≤ k then ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) y
          else -∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) y
      MemLp (fun omega => Real.exp (H omega z + retained n z omega -
            (H omega w + retained m w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => Real.exp (H omega z + retained n z omega -
            (H omega w + retained m w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal KC)
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) :
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun k y omega => if 0 ≤ k then ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) y
        else -∑ j ∈ Finset.Ico k (0 : ℤ), omega (-j) y
    let reference : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun N k zz omega => kappa ((N : ℤ) - k).toNat / kappa N *
        Real.exp (H omega zz + retained k zz omega)
    MemLp (fun omega => if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
        reference N n z omega / reference N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega else 0)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun omega => if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
        reference N n z omega / reference N (n + off) (z + ((3 : ℝ) ^ (-n)) • sh) omega else 0)
      (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (3 * |(off : ℝ)|) * KC) := by
  intro kappa retained reference
  obtain ⟨hmem, hnorm⟩ := hCw n z
  set w : SpatialCoordinates d := z + ((3 : ℝ) ^ (-n)) • sh with hw
  have heq : (fun omega => if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
        reference N n z omega / reference N (n + off) w omega else 0) =
      fun omega => (if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
            kappa ((N : ℤ) - n).toNat / kappa ((N : ℤ) - (n + off)).toNat else 0) *
          Real.exp (H omega z + retained n z omega - (H omega w + retained (n + off) w omega)) := by
    funext omega
    exact aux_lem_prefix_limit_g9_value_ref_ratio_eq M H n (n + off) z w N omega
  rw [heq]
  set c : ℝ := (if n ≤ (N : ℤ) ∧ n + off ≤ (N : ℤ) then
            kappa ((N : ℤ) - n).toNat / kappa ((N : ℤ) - (n + off)).toNat else 0) with hc
  have hcb := aux_lem_prefix_limit_g8r_kappa_ratio_explicit M Rm n (n + off) N
  have hcoff : |((n + off : ℤ) : ℝ) - n| = |(off : ℝ)| := by
    push_cast; ring_nf
  have htau0 := aux_lem_prefix_limit_g9_tauSq_nonneg M Rm
  have htau1 := aux_lem_prefix_limit_g8r_tauSq_le_one M
  have hcle : c ≤ Real.exp (3 * |(off : ℝ)|) := by
    have h1 : c ≤ Real.exp (3 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * |((n + off : ℤ) : ℝ) - n|) :=
      hcb.2
    rw [hcoff] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ |(off : ℝ)| := abs_nonneg _
    nlinarith
  have hc0 : 0 ≤ c := hcb.1
  refine ⟨hmem.const_mul c, ?_⟩
  have hnorm' : eLpNorm (fun omega => c * Real.exp (H omega z + retained n z omega -
      (H omega w + retained (n + off) w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure =
      ‖c‖ₑ * eLpNorm (fun omega => Real.exp (H omega z + retained n z omega -
        (H omega w + retained (n + off) w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
    have := eLpNorm_const_smul (μ := (chaosSampleLaw M).toMeasure) (p := ENNReal.ofReal p) c
      (fun omega => Real.exp (H omega z + retained n z omega -
        (H omega w + retained (n + off) w omega)))
    simpa [smul_eq_mul, Pi.smul_def] using this
  rw [hnorm']
  calc ‖c‖ₑ * eLpNorm (fun omega => Real.exp (H omega z + retained n z omega -
        (H omega w + retained (n + off) w omega))) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (Real.exp (3 * |(off : ℝ)|)) * ENNReal.ofReal KC := by
        apply mul_le_mul'
        · rw [Real.enorm_eq_ofReal hc0]
          exact ENNReal.ofReal_le_ofReal hcle
        · exact hnorm
    _ = ENNReal.ofReal (Real.exp (3 * |(off : ℝ)|) * KC) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]


theorem aux_lem_prefix_limit_g8r_moment_transfer {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    {q : ℝ≥0∞} {K : ℝ≥0∞} (h : f = g) (hm : MemLp g q μ) (hn : eLpNorm g q μ ≤ K) :
    MemLp f q μ ∧ eLpNorm f q μ ≤ K := h ▸ ⟨hm, hn⟩

/-- G8, response half (typed goal): cutoff-, position- and model-uniform moments of the full coarse response
coordinates (`Sum.inr`), the constants chosen after the finite moment list and before the model (paper 2746--2763;
p.coarse.grained.bound and e.annealed.ordering.ratio). -/
theorem aux_lem_prefix_limit_response_moments
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
    ∃ deltaS : ℝ, 0 < deltaS ∧ ∃ KS : ℝ → ℝ, (∀ p ∈ insert 1 moments, 0 < KS p) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaS →
        ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)),
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
        ∀ p ∈ insert 1 moments, ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (ij : Fin T × (Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2))),
          MemLp (value N n z (Sum.inr ij)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (value N n z (Sum.inr ij)) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (KS p) := by
  classical
  have hS1 : ∀ p ∈ insert (1 : ℝ) moments, 1 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · exact h.ge
    · exact hmom p h
  obtain ⟨δch, hδch, hChart⟩ := lem_prefix_limit_g9_chart_compact hd I _Poincare _Extension
    _Perturbation _Sobolev D Cresp hCresp sigma s hs hsigma
  have hMv := fun (p : ℝ) (hp : p ∈ insert (1 : ℝ) moments) =>
    lem_prefix_limit_g9_moving_chart_moment hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp sigma p hsigma (hS1 p hp)
  choose! δ1 K1 hδ1 hK1 hbd1 using hMv
  have hMs := fun (p : ℝ) (hp : p ∈ insert (1 : ℝ) moments) =>
    lem_prefix_limit_g9_moving_chart_moment hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp s p hs (hS1 p hp)
  choose! δ2 K2 hδ2 hK2 hbd2 using hMs
  have hRR := fun i : Fin T => aux_lem_prefix_limit_rr_cw_moment d hd moments hmom (offset i) (shift i)
  choose δ3 hδ3 KC hKC hbd3 using hRR
  obtain ⟨δ1c, hδ1c, hδ1c'⟩ := aux_lem_prefix_limit_g8r_exists_common_delta (insert (1 : ℝ) moments) δ1 hδ1
  obtain ⟨δ2c, hδ2c, hδ2c'⟩ := aux_lem_prefix_limit_g8r_exists_common_delta (insert (1 : ℝ) moments) δ2 hδ2
  obtain ⟨δ3c, hδ3c, hδ3c'⟩ := aux_lem_prefix_limit_g8r_exists_common_delta (Finset.univ : Finset (Fin T)) δ3
    (fun i _ => hδ3 i)
  refine ⟨min δch (min δ1c (min δ2c δ3c)), lt_min hδch (lt_min hδ1c (lt_min hδ2c hδ3c)),
    fun p => 1 + K1 p + 2 * K2 p + ∑ i : Fin T, Real.exp (3 * |(offset i : ℝ)|) * KC i p, ?_, ?_⟩
  · intro p hp
    have h1 := hK1 p hp
    have h2 := hK2 p hp
    have h3 : 0 ≤ ∑ i : Fin T, Real.exp (3 * |(offset i : ℝ)|) * KC i p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le (hKC i p hp).le
    linarith
  · intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
      kappa retained reference Test value p hp N n z ij
    obtain ⟨i, rt⟩ := ij
    have hMch : M.delta ≤ δch := hM.trans (min_le_left _ _)
    have hM1 : M.delta ≤ δ1 p :=
      hM.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (hδ1c' p hp))
    have hM2 : M.delta ≤ δ2 p :=
      hM.trans (((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans
        (hδ2c' p hp))
    have hM3 : M.delta ≤ δ3 i :=
      hM.trans (((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))).trans
        (hδ3c' i (Finset.mem_univ i)))
    have hp1 : 1 ≤ p := hS1 p hp
    have hK1p := hK1 p hp
    have hK2p := hK2 p hp
    have hsnn : ∀ j : Fin T, 0 ≤ Real.exp (3 * |(offset j : ℝ)|) * KC j p :=
      fun j => mul_nonneg (Real.exp_pos _).le (hKC j p hp).le
    have hsle : Real.exp (3 * |(offset i : ℝ)|) * KC i p ≤
        ∑ j : Fin T, Real.exp (3 * |(offset j : ℝ)|) * KC j p :=
      Finset.single_le_sum (fun j _ => hsnn j) (Finset.mem_univ i)
    have hs0 : 0 ≤ ∑ j : Fin T, Real.exp (3 * |(offset j : ℝ)|) * KC j p :=
      Finset.sum_nonneg fun j _ => hsnn j
    by_cases hrt : rt = Sum.inr (Sum.inr 1)
    · subst hrt
      have hval : value N n z (Sum.inr (i, Sum.inr (Sum.inr 1))) = fun omega =>
          if n ≤ (N : ℤ) ∧ n + offset i ≤ (N : ℤ) then
            reference N n z omega / reference N (n + offset i)
              (z + ((3 : ℝ) ^ (-n)) • shift i) omega else 0 := rfl
      rw [hval]
      obtain ⟨hm, hn⟩ := aux_lem_prefix_limit_g8r_refratio_moment M Rm H (offset i) (shift i) p (KC i p)
        (fun n z => hbd3 i M hM3 H hH n z p hp) N n z
      exact ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩
    · by_cases hg : n ≤ (N : ℤ) ∧ n + offset i ≤ (N : ℤ)
      · have hmN : n + offset i ≤ (N : ℤ) := hg.2
        have hK1le : K1 p ≤ 1 + K1 p + 2 * K2 p + ∑ j : Fin T,
            Real.exp (3 * |(offset j : ℝ)|) * KC j p := by linarith
        have hK2le : 1 + 2 * K2 p ≤ 1 + K1 p + 2 * K2 p + ∑ j : Fin T,
            Real.exp (3 * |(offset j : ℝ)|) * KC j p := by linarith
        obtain ⟨hlam, hLamb, hinv, hsig, hsigst⟩ := hbd1 p hp M hM1 Rm hRm Sreg It H hH N (n + offset i)
          hmN (z + ((3 : ℝ) ^ (-n)) • shift i) (sidePos (n + offset i))
        rcases rt with j | rt2
        · fin_cases j
          · refine aux_lem_prefix_limit_g8r_moment_transfer ?_ hlam.1 (hlam.2.trans (ENNReal.ofReal_le_ofReal hK1le))
            funext omega
            exact if_pos hg
          · refine aux_lem_prefix_limit_g8r_moment_transfer ?_ hLamb.1 (hLamb.2.trans (ENNReal.ofReal_le_ofReal hK1le))
            funext omega
            exact if_pos hg
          · refine aux_lem_prefix_limit_g8r_moment_transfer ?_ hinv.1 (hinv.2.trans (ENNReal.ofReal_le_ofReal hK1le))
            funext omega
            exact if_pos hg
        · rcases rt2 with ab | j2
          · obtain ⟨b, a1, a2⟩ := ab
            cases b
            · refine aux_lem_prefix_limit_g8r_moment_transfer ?_ (hsigst a1 a2).1
                ((hsigst a1 a2).2.trans (ENNReal.ofReal_le_ofReal hK1le))
              funext omega
              exact if_pos hg
            · refine aux_lem_prefix_limit_g8r_moment_transfer ?_ (hsig a1 a2).1
                ((hsig a1 a2).2.trans (ENNReal.ofReal_le_ofReal hK1le))
              funext omega
              exact if_pos hg
          · fin_cases j2
            · -- the homogenization error, at the reference scalar `ref`
              have hmeasE : AEStronglyMeasurable
                  (value N n z (Sum.inr (i, Sum.inr (Sum.inr 0)))) (chaosSampleLaw M).toMeasure := by
                obtain ⟨hmem1, -⟩ := hChart M hMch Rm hRm Sreg It H hH sidePos n (n + offset i) z
                  (z + ((3 : ℝ) ^ (-n)) • shift i) (Sum.inr (Sum.inr 0)) (by simp)
                exact (hmem1 N).aestronglyMeasurable
              obtain ⟨-, ⟨hA, hAn⟩, ⟨hB, hBn⟩, -, -⟩ := hbd2 p hp M hM2 Rm hRm Sreg It H hH N
                (n + offset i) hmN (z + ((3 : ℝ) ^ (-n)) • shift i) (sidePos (n + offset i))
              have hrefpos : ∀ omega, 0 < aux_g9chart_transport_reference M H N (n + offset i)
                  (z + ((3 : ℝ) ^ (-n)) • shift i) omega :=
                fun omega => aux_g9chart_transport_reference_pos M H N _ _ omega
              have hE := aux_lem_prefix_limit_g8r_err_of_ellipticity (chaosSampleLaw M).toMeasure p hp1
                (value N n z (Sum.inr (i, Sum.inr (Sum.inr 0))))
                (fun omega => I.Lam (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i)))
                  (sidePos (n + offset i))
                  (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • shift i)
                    (sidePos (n + offset i)))
                  (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) s 2)
                (fun omega => I.lam (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i)))
                  (sidePos (n + offset i))
                  (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • shift i)
                    (sidePos (n + offset i)))
                  (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) s 2)
                (fun omega => aux_g9chart_transport_reference M H N (n + offset i)
                  (z + ((3 : ℝ) ^ (-n)) • shift i) omega)
                hmeasE (fun omega => I.Lam_pos _ _ _ _ _ _ _ _) (fun omega => I.lam_pos _ _ _ _ _ _ _ _)
                hrefpos ?_ (K2 p) hK2p.le hA hAn hB hBn
              · exact ⟨hE.1, hE.2.trans (ENNReal.ofReal_le_ofReal hK2le)⟩
              · intro omega
                have hb := (I.bound_ellipticities_by_error (z + ((3 : ℝ) ^ (-n)) • shift i)
                  ((3 : ℝ) ^ (-(n + offset i))) (sidePos (n + offset i))
                  (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • shift i)
                    (sidePos (n + offset i)))
                  (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i)))
                  (aux_g9chart_transport_reference M H N (n + offset i)
                    (z + ((3 : ℝ) ^ (-n)) • shift i) omega) (hrefpos omega) s hs 2 (Or.inr rfl)).1
                have e : value N n z (Sum.inr (i, Sum.inr (Sum.inr 0))) omega =
                    I.err (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i)))
                      (sidePos (n + offset i))
                      (Lane4.cutoffPositiveCoefficient M H omega N (z + ((3 : ℝ) ^ (-n)) • shift i)
                        (sidePos (n + offset i)))
                      (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i)))
                      (aux_g9chart_transport_reference M H N (n + offset i)
                        (z + ((3 : ℝ) ^ (-n)) • shift i) omega) s 2 := if_pos hg
                rw [e]
                exact hb
            · exact absurd rfl hrt
      · have h0 : value N n z (Sum.inr (i, rt)) = fun _ => 0 := by
          funext omega
          exact if_neg hg
        rw [h0]
        refine ⟨memLp_const 0, ?_⟩
        simp




theorem lem_prefix_limit
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
    ∃ q delta0 : ℝ, ∃ K : ℝ → ℝ,
      1 ≤ q ∧ (∀ p ∈ moments, 2 * p ≤ q) ∧
      32 * (d : ℝ) / min s sigma ≤ q ∧ 0 < delta0 ∧
      (∀ p ∈ insert 1 moments, 0 < K p) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H →
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
          (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega) (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)),
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
        (∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (omega : BilateralField d),
          n ≤ (N : ℤ) → 0 < reference N n z omega ∧
          0 < I.lam z ((3 : ℝ) ^ (-n)) (sidePos n)
            (Lane4.cutoffPositiveCoefficient M H omega N z (sidePos n))
            z ((3 : ℝ) ^ (-n)) sigma 2) ∧
        12 * q ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ ∧
        ∀ (Pos : Type) [Countable Pos]
          (level : Pos → ℤ) (centre : Pos → SpatialCoordinates d)
          (phi : ℕ → ℕ), StrictMono phi →
          ∃ psi : ℕ → ℕ, StrictMono psi ∧
          ∃ Vlim : Pos → ℤ → Test → BilateralField d → ℝ,
            (∀ pos j test, AEStronglyMeasurable (Vlim pos j test)
              (chaosSampleLaw M).toMeasure) ∧
            (∀ p ∈ insert 1 moments, ∀ pos j test,
              MemLp (Vlim pos j test) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
              eLpNorm (Vlim pos j test) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                ENNReal.ofReal (K p)) ∧
            (∀ p ∈ insert 1 moments, ∀ N pos j test,
              MemLp (value N (level pos + j) (centre pos) test)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
              eLpNorm (value N (level pos + j) (centre pos) test)
                (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (K p)) ∧
            (∀ p ∈ insert 1 moments, ∀ pos j test,
              Tendsto (fun n => eLpNorm (fun omega =>
                value (phi (psi n)) (level pos + j) (centre pos) test omega -
                  Vlim pos j test omega) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
                atTop (𝓝 0)) ∧
            (∀ (pos : Pos) (start : ℤ) (D cbuf : ℕ) (test : Test),
              let prefixN : ℕ → BilateralField d → ℝ := fun N omega =>
                ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)),
                  value N (level pos + j) (centre pos) test omega
              let prefixLim : BilateralField d → ℝ := fun omega =>
                ∑ j ∈ Finset.Icc (start - (cbuf : ℤ)) (start + (D : ℤ)),
                  Vlim pos j test omega
              AEStronglyMeasurable prefixLim (chaosSampleLaw M).toMeasure ∧
              (∀ p ∈ insert 1 moments,
                eLpNorm prefixLim (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
                  ENNReal.ofReal (K p * ((D : ℝ) + (cbuf : ℝ) + 1)) ∧
                Tendsto (fun n => eLpNorm (fun omega =>
                  prefixN (phi (psi n)) omega - prefixLim omega)
                    (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) ∧
              (∀ A a a' : ℝ, 0 < A → a < a' →
                (∀ n, (chaosSampleLaw M).toMeasure
                  {omega | a < prefixN (phi n) omega} ≤
                    ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))) →
                (chaosSampleLaw M).toMeasure {omega | a' < prefixLim omega} ≤
                  ENNReal.ofReal (Real.exp (-(A * (D : ℝ))))))
    := by
  -- Constants before the model: the finite moment bank (enlarged by the doubled orders), the order `q`,
  -- the child's Cauchy threshold, the moment thresholds and the response-extraction threshold.
  obtain ⟨m2, hm2, hm2sub, hm2dbl⟩ := aux_lem_prefix_limit_moments2 moments hmom
  obtain ⟨q, hq1, hq2, hq3⟩ := aux_lem_prefix_limit_q_exists d s sigma moments
  obtain ⟨deltaC, hdC, hChild⟩ := lem_prefix_limit_actual_coordinate_cauchy d hd I _Poincare
    _Extension _Perturbation _Sobolev D Cresp hCresp s sigma eps hs hsigma heps T offset shift
    moments hmom
  obtain ⟨deltaR, hdR, KR, hKR, hRaw⟩ := aux_lem_prefix_limit_raw_moments d hd I _Poincare
    _Extension _Perturbation _Sobolev D Cresp hCresp s sigma eps hs hsigma heps T offset shift
    m2 hm2
  obtain ⟨deltaS, hdS, KS, hKS, hRespM⟩ := aux_lem_prefix_limit_response_moments d hd I _Poincare
    _Extension _Perturbation _Sobolev D Cresp hCresp s sigma eps hs hsigma heps T offset shift
    m2 hm2
  obtain ⟨deltaE, hdE, hExt⟩ := aux_lem_prefix_limit_response_in_measure d hd I _Poincare
    _Extension _Perturbation _Sobolev D Cresp hCresp s sigma eps hs hsigma heps T offset shift
    moments hmom
  have hqpos : 0 < q := by linarith
  have hone : ∀ p ∈ insert 1 moments, 1 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · exact le_of_eq h.symm
    · exact hmom p h
  refine ⟨q, min (min deltaC deltaR) (min (min deltaS deltaE)
      (min (Real.exp (-1)) (1 / (12 * q * Cresp)))), fun p => max (KR p) (KS p),
    hq1, hq2, hq3, ?_, fun p hp => lt_max_of_lt_left (hKR p (hm2sub p hp)), ?_⟩
  · have h12 : 0 < 1 / (12 * q * Cresp) := by positivity
    exact lt_min (lt_min hdC hdR) (lt_min (lt_min hdS hdE) (lt_min (Real.exp_pos _) h12))
  intro M hM Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
  have hMC : M.delta ≤ deltaC := hM.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hMR : M.delta ≤ deltaR := hM.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hMS : M.delta ≤ deltaS :=
    hM.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hME : M.delta ≤ deltaE :=
    hM.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hMe : M.delta ≤ Real.exp (-1) :=
    hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMq : M.delta ≤ 1 / (12 * q * Cresp) :=
    hM.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hA := hRaw M hMR Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
  have hB := hRespM M hMS Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
  have hE := hExt M hME Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
  have hCh := hChild M hMC Rm hRm Sreg It H hH eta hEta F Praw Rraw Draw Z rawGood hPrim sidePos
  intro kappa retained reference Test value
  -- The uniform moment bank of every actual coordinate (raw and response halves).
  have hK : ∀ p ∈ insert 1 m2, ∀ (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (test : Test),
      MemLp (value N n z test) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (value N n z test) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max (KR p) (KS p)) := by
    intro p hp N n z test
    rcases test with j | ij
    · obtain ⟨h1, h2⟩ := hA p hp N n z j
      exact ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    · obtain ⟨h1, h2⟩ := hB p hp N n z ij
      exact ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  refine ⟨aux_lem_prefix_limit_positivity I M H sigma sidePos,
    aux_lem_prefix_limit_threshold q Cresp M.delta hqpos hCresp M.shellPrefix.delta_pos hMe hMq, ?_⟩
  intro Pos _ level centre phi hphi
  -- G9: joint extraction `psi1` of the response coordinates, upgraded to `L^p` by the doubled-order bank.
  obtain ⟨psi1, hpsi1, hconv1⟩ := hE Pos level centre phi hphi
  have hResp2 : ∀ p ∈ insert 1 moments, ∀ (pos : Pos) (j : ℤ) (i : Fin T)
      (rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)),
      ∃ lim : BilateralField d → ℝ,
        AEStronglyMeasurable lim (chaosSampleLaw M).toMeasure ∧
        Tendsto (fun n => eLpNorm (fun omega =>
            value (phi (psi1 n)) (level pos + j) (centre pos) (Sum.inr (i, rt)) omega - lim omega)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0) := by
    intro p hp pos j i rt
    obtain ⟨lim, hlim⟩ := hconv1 pos j i rt
    exact aux_lem_prefix_limit_lp_limit_of_tendstoInMeasure (chaosSampleLaw M).toMeasure p
      (hone p hp)
      (fun n omega => value (phi (psi1 n)) (level pos + j) (centre pos) (Sum.inr (i, rt)) omega)
      lim hlim (max (KR (2 * p)) (KS (2 * p)))
      (fun n => (hK p (hm2sub p hp) (phi (psi1 n)) (level pos + j) (centre pos)
        (Sum.inr (i, rt))).1)
      (fun n => (hK (2 * p) (hm2dbl p hp) (phi (psi1 n)) (level pos + j) (centre pos)
        (Sum.inr (i, rt))).2)
  have hResp1 : ∀ p ∈ insert 1 moments, ∃ q' : ℝ, p < q' ∧
      ∃ B : ℝ≥0∞, ∀ (pos : Pos) (j : ℤ) (i : Fin T)
        (rt : Fin 3 ⊕ ((Bool × (Fin d × Fin d)) ⊕ Fin 2)) (N : ℕ),
        MemLp (fun omega => value N (level pos + j) (centre pos) (Sum.inr (i, rt)) omega)
            (ENNReal.ofReal q') (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun omega => value N (level pos + j) (centre pos) (Sum.inr (i, rt)) omega)
            (ENNReal.ofReal q') (chaosSampleLaw M).toMeasure ≤ B := by
    intro p hp
    have hp1 := hone p hp
    exact ⟨2 * p, by linarith, ENNReal.ofReal (max (KR (2 * p)) (KS (2 * p))),
      fun pos j i rt N => hK (2 * p) (hm2dbl p hp) N (level pos + j) (centre pos) (Sum.inr (i, rt))⟩
  
  obtain ⟨psi2, hpsi2, hcau⟩ := hCh Pos level centre (phi ∘ psi1) (hphi.comp hpsi1)
    ⟨hResp1, hResp2⟩
  -- Limits of the individual coordinates.
  have hlim : ∀ (pos : Pos) (j : ℤ) (test : Test), ∃ V : BilateralField d → ℝ,
      AEStronglyMeasurable V (chaosSampleLaw M).toMeasure ∧
      (∀ p ∈ insert 1 moments, MemLp V (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm V (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (max (KR p) (KS p))) ∧
      (∀ p ∈ insert 1 moments, Tendsto (fun n => eLpNorm (fun omega =>
          value (phi ((psi1 ∘ psi2) n)) (level pos + j) (centre pos) test omega - V omega)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) atTop (𝓝 0)) := by
    intro pos j test
    exact aux_lem_prefix_limit_coordinate_limit (chaosSampleLaw M).toMeasure moments hmom
      (fun p => max (KR p) (KS p))
      (fun n => value (phi ((psi1 ∘ psi2) n)) (level pos + j) (centre pos) test)
      (fun p hp N => hK p (hm2sub p hp) (phi ((psi1 ∘ psi2) N)) (level pos + j) (centre pos) test)
      (fun p hp ε hε => hcau p hp pos j test ε hε)
  choose Vlim hVm hVmom hVconv using hlim
  refine ⟨psi1 ∘ psi2, hpsi1.comp hpsi2, Vlim, hVm, fun p hp pos j test => hVmom pos j test p hp,
    fun p hp N pos j test => hK p (hm2sub p hp) N (level pos + j) (centre pos) test,
    fun p hp pos j test => hVconv pos j test p hp, ?_⟩
  intro pos start Dn cbuf test
  exact aux_lem_prefix_limit_prefix_clause (chaosSampleLaw M).toMeasure moments hmom
    (fun p => max (KR p) (KS p)) (fun p hp => lt_max_of_lt_left (hKR p (hm2sub p hp)))
    (fun N j => value N (level pos + j) (centre pos) test) (fun j => Vlim pos j test)
    phi (psi1 ∘ psi2)
    (fun N j => (hK 1 (hm2sub 1 (Finset.mem_insert_self _ _)) N (level pos + j) (centre pos)
      test).1.aestronglyMeasurable)
    (fun j => hVm pos j test) (fun p hp j => (hVmom pos j test p hp).2)
    (fun p hp j => hVconv pos j test p hp) start Dn cbuf

end Paper
