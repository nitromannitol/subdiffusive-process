module

public import SubdiffusiveProcess.Analysis.RawLp

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

/-! Quantitative countable subsequence selection by weighted summation and Fatou.
This classical statement concerns arbitrary random variables and contains
no form, field, energy, or concentration assertion. Proof: with injective `e : ι → ℕ` and weights
`w_j = 2^{-(e j+1)}/(1+C_j)` the sums `S_n = ∑_j w_j |F_j n|` have `∫ S_n ≤ 1`; Fatou for
`T_n = S_n + |Q_n|^p` gives `∫ liminf T_n ≤ 1 + B^p`, and the majorant is `K = (liminf T + 1)^{1/p}`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Summable positive weights for the countable moment-bank construction. -/
def aux_cms_w {ι : Type*} (e : ι → ℕ) (C : ι → ℝ≥0) (j : ι) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ (e j + 1) * (1 + (C j : ℝ≥0∞))⁻¹

theorem aux_cms_geom_inj {ι : Type*} (e : ι → ℕ) (he : Function.Injective e) :
    ∑' j, (2⁻¹ : ℝ≥0∞) ^ (e j + 1) ≤ 1 := by
  have h := ENNReal.tsum_comp_le_tsum_of_injective he (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ (n + 1))
  have hge : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1)) = 1 := by
    have hstep : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1))
        = (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) * 2⁻¹ := by
      simp only [pow_succ]
      rw [ENNReal.tsum_mul_right]
    rw [hstep, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [hge] at h
  exact h

theorem aux_cms_w_sum_le {ι : Type*} (e : ι → ℕ) (he : Function.Injective e) (C : ι → ℝ≥0) :
    ∑' j, aux_cms_w e C j * (C j : ℝ≥0∞) ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum (fun j => ?_)) (aux_cms_geom_inj e he)
  simp only [aux_cms_w]
  rw [mul_assoc]
  apply mul_le_of_le_one_right zero_le
  rw [ENNReal.inv_mul_le_iff (by simp) (by simp)]
  simp

theorem aux_cms_w_ne {ι : Type*} (e : ι → ℕ) (C : ι → ℝ≥0) (j : ι) :
    aux_cms_w e C j ≠ 0 ∧ aux_cms_w e C j ≠ ⊤ := by
  unfold aux_cms_w
  constructor
  · apply mul_ne_zero
    · apply pow_ne_zero
      exact ENNReal.inv_ne_zero.2 (by norm_num)
    · apply ENNReal.inv_ne_zero.2
      simp
  · apply ENNReal.mul_ne_top
    · apply ENNReal.pow_ne_top
      exact ENNReal.inv_ne_top.2 (by norm_num)
    · apply ENNReal.inv_ne_top.2
      simp

theorem aux_cms_lintegral_S {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} [Countable ι] (e : ι → ℕ) (he : Function.Injective e)
    (F : ι → ℕ → Ω → ℝ) (C : ι → ℝ≥0)
    (hmem : ∀ j n, MemLp (F j n) 1 P) (hbound : ∀ j n, eLpNorm (F j n) 1 P ≤ C j) (n : ℕ) :
    ∫⁻ ω, ∑' j, aux_cms_w e C j * ‖F j n ω‖ₑ ∂P ≤ 1 := by
  have h_meas : ∀ j, AEMeasurable (fun ω => aux_cms_w e C j * ‖F j n ω‖ₑ) P :=
    fun j => ((hmem j n).aestronglyMeasurable.enorm).const_mul _
  rw [lintegral_tsum h_meas]
  calc
    ∑' j, ∫⁻ ω, aux_cms_w e C j * ‖F j n ω‖ₑ ∂P
        = ∑' j, aux_cms_w e C j * ∫⁻ ω, ‖F j n ω‖ₑ ∂P :=
          tsum_congr fun j => lintegral_const_mul' _ _ (aux_cms_w_ne e C j).2
    _ ≤ ∑' j, aux_cms_w e C j * C j := by
          apply ENNReal.tsum_le_tsum
          intro j
          exact mul_le_mul_right (by simpa only [eLpNorm_one_eq_lintegral_enorm (hmem j n).aestronglyMeasurable] using hbound j n) _
    _ ≤ 1 := aux_cms_w_sum_le e he C

theorem aux_cms_lintegral_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : Ω → ℝ) (p : ℝ) (hp : 1 ≤ p) (B : ℝ≥0)
    (hQbound : SubdiffusiveProcess.RawLp.eLpNorm Q (ENNReal.ofReal p) P ≤ B) :
    ∫⁻ ω, ‖Q ω‖ₑ ^ p ∂P ≤ (B : ℝ≥0∞) ^ p := by
  have hp0 : (0:ℝ) < p := by linarith
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hp0
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have heq := SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral hpne0 hptop Q P
  rw [htoReal] at heq
  have heq' : SubdiffusiveProcess.RawLp.eLpNorm Q (ENNReal.ofReal p) P = (∫⁻ ω, ‖Q ω‖ₑ ^ p ∂P) ^ p⁻¹ := by
    rw [heq, one_div]
  have hbound' : (∫⁻ ω, ‖Q ω‖ₑ ^ p ∂P) ^ p⁻¹ ≤ (B : ℝ≥0∞) := by
    rw [← heq']; exact hQbound
  exact (ENNReal.rpow_inv_le_iff hp0).mp hbound'

theorem aux_cms_fatou {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → ℝ≥0∞) (hT : ∀ n, Measurable (T n)) (M : ℝ≥0∞) (hM : ∀ n, ∫⁻ ω, T n ω ∂P ≤ M) :
    ∫⁻ ω, liminf (fun n => T n ω) atTop ∂P ≤ M := by
  calc ∫⁻ ω, liminf (fun n => T n ω) atTop ∂P
      ≤ liminf (fun n => ∫⁻ ω, T n ω ∂P) atTop := lintegral_liminf_le hT
    _ ≤ M := Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hM)

theorem aux_cms_extract (T : ℕ → ℝ≥0∞) (h : liminf T atTop < ⊤) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ ∀ n, T (seq n) ≤ liminf T atTop + 1 := by
  have hne : liminf T atTop ≠ ⊤ := h.ne
  have hlt : liminf T atTop < liminf T atTop + 1 :=
    ENNReal.lt_add_right hne (by simp)
  have hfreq : ∃ᶠ n in atTop, T n < liminf T atTop + 1 :=
    Filter.frequently_lt_of_liminf_lt (f := atTop) (u := T) (by isBoundedDefault) hlt
  obtain ⟨φ, hφ, hle⟩ := Filter.extraction_of_frequently_atTop hfreq
  exact ⟨φ, hφ, fun n => le_of_lt (hle n)⟩

theorem aux_cms_K_pointwise (a : ℝ≥0∞) (ha : a < ⊤) (p : ℝ) (hp : 0 < p) :
    ‖((a.toReal + 1) ^ (1 / p) : ℝ)‖ₑ ^ p = a + 1 := by
  have ha' : a ≠ ⊤ := ha.ne
  have h1 : (0:ℝ) ≤ a.toReal + 1 := by positivity
  have hx : 0 ≤ (a.toReal + 1) ^ (1 / p) := Real.rpow_nonneg h1 _
  rw [Real.enorm_of_nonneg hx]
  rw [ENNReal.ofReal_rpow_of_nonneg hx (le_of_lt hp)]
  have hxp : ((a.toReal + 1) ^ (1 / p)) ^ p = a.toReal + 1 := by
    rw [← Real.rpow_mul h1, one_div_mul_cancel hp.ne', Real.rpow_one]
  rw [hxp]
  rw [ENNReal.ofReal_add (by positivity) (by norm_num : (0:ℝ) ≤ 1), ENNReal.ofReal_toReal ha',
    ENNReal.ofReal_one]

theorem aux_cms_rpow_final (p : ℝ) (hp : 1 ≤ p) (B : ℝ≥0) :
    (1 + (B : ℝ≥0∞) ^ p + 1) ^ (1 / p) ≤ ENNReal.ofReal (2 * ((B : ℝ) + 1)) := by
  have hB : (B:ℝ≥0∞) = ENNReal.ofReal (B:ℝ) := by simp
  have hle : (B:ℝ≥0∞) + 2 ≤ ENNReal.ofReal (2 * ((B:ℝ) + 1)) := by
    rw [hB, show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by simp,
        ← ENNReal.ofReal_add (p := (B:ℝ)) (q := 2) (by positivity) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [show (0:ℝ) ≤ (B:ℝ) by positivity]
  have htwo : (2:ℝ≥0∞) ≤ (2:ℝ≥0∞)^p := by
    have h := ENNReal.rpow_le_rpow_of_exponent_le (show (1:ℝ≥0∞) ≤ 2 by norm_num) hp
    simpa using h
  have hab : (B:ℝ≥0∞)^p + (2:ℝ≥0∞)^p ≤ ((B:ℝ≥0∞) + 2)^p :=
    ENNReal.add_rpow_le_rpow_add _ _ hp
  have hmain : 1 + (B:ℝ≥0∞)^p + 1 ≤ ((B:ℝ≥0∞) + 2)^p := by
    have e : 1 + (B:ℝ≥0∞)^p + 1 = (B:ℝ≥0∞)^p + 2 := by
      rw [add_comm (1:ℝ≥0∞) ((B:ℝ≥0∞)^p), add_assoc]
      norm_num
    rw [e]
    exact le_trans (add_le_add (le_refl _) htwo) hab
  have hpc : ((B:ℝ≥0∞) + 2)^p ≤ (ENNReal.ofReal (2 * ((B:ℝ) + 1)))^p :=
    ENNReal.rpow_le_rpow hle (by linarith)
  have h1 : 1 + (B:ℝ≥0∞)^p + 1 ≤ (ENNReal.ofReal (2 * ((B:ℝ) + 1)))^p := le_trans hmain hpc
  have h2 : (1 + (B:ℝ≥0∞)^p + 1)^(1/p) ≤ ((ENNReal.ofReal (2 * ((B:ℝ) + 1)))^p)^(1/p) :=
    ENNReal.rpow_le_rpow h1 (div_nonneg zero_le_one (by linarith))
  have hpp : p * (1/p) = 1 := by
    have hpne : p ≠ 0 := by linarith
    rw [mul_one_div, div_self hpne]
  calc (1 + (B:ℝ≥0∞)^p + 1)^(1/p)
      ≤ ((ENNReal.ofReal (2 * ((B:ℝ) + 1)))^p)^(1/p) := h2
    _ = (ENNReal.ofReal (2 * ((B:ℝ) + 1)))^(p*(1/p)) := (ENNReal.rpow_mul _ p (1/p)).symm
    _ = ENNReal.ofReal (2 * ((B:ℝ) + 1)) := by rw [hpp, ENNReal.rpow_one]

theorem aux_cms_K_eLpNorm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Ω → ℝ≥0∞) (hΛ : Measurable Λ) (p : ℝ) (hp : 1 ≤ p) (B : ℝ≥0)
    (hint : ∫⁻ ω, Λ ω ∂P ≤ 1 + (B : ℝ≥0∞) ^ p) :
    eLpNorm (fun ω => ((Λ ω).toReal + 1) ^ (1 / p)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (2 * ((B : ℝ) + 1)) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hptop
    ((hΛ.ennreal_toReal.add_const 1).pow_const _).aestronglyMeasurable, ENNReal.toReal_ofReal (le_of_lt hp0)]
  have hBp_top : (1 : ℝ≥0∞) + (B : ℝ≥0∞) ^ p ≠ ⊤ := by
    rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.one_ne_top, ENNReal.rpow_ne_top_of_nonneg (le_of_lt hp0) ENNReal.coe_ne_top⟩
  have hint_lt : ∫⁻ ω, Λ ω ∂P < ⊤ := lt_of_le_of_lt hint (lt_top_iff_ne_top.mpr hBp_top)
  have hΛtop : ∀ᵐ ω ∂P, Λ ω < ⊤ := ae_lt_top hΛ (ne_of_lt hint_lt)
  have hcongr : (fun ω => ‖((Λ ω).toReal + 1) ^ (1 / p)‖ₑ ^ p) =ᶠ[ae P] (fun ω => Λ ω + 1) := by
    filter_upwards [hΛtop] with ω hlt
    exact aux_cms_K_pointwise (Λ ω) hlt p hp0
  rw [lintegral_congr_ae hcongr]
  have hint_eq : ∫⁻ ω, (Λ ω + 1) ∂P = ∫⁻ ω, Λ ω ∂P + 1 := by
    rw [lintegral_add_right Λ measurable_const, lintegral_const, measure_univ, mul_one]
  rw [hint_eq]
  refine le_trans (ENNReal.rpow_le_rpow ?_ (by positivity)) (aux_cms_rpow_final p hp B)
  calc ∫⁻ ω, Λ ω ∂P + 1 ≤ (1 + (B : ℝ≥0∞) ^ p) + 1 := by gcongr
    _ = 1 + (B : ℝ≥0∞) ^ p + 1 := by ring

theorem aux_cms_abs_le (q : ℝ) (a : ℝ≥0∞) (ha : a < ⊤) (p : ℝ) (hp : 0 < p)
    (h : ‖q‖ₑ ^ p ≤ a + 1) : |q| ≤ (a.toReal + 1) ^ (1 / p) := by
  have hlt : a + 1 < ⊤ := by
    rw [ENNReal.add_lt_top]
    exact ⟨ha, ENNReal.one_lt_top⟩
  have hne : a + 1 ≠ ⊤ := hlt.ne
  have step1 : (‖q‖ₑ ^ p).toReal ≤ (a + 1).toReal := ENNReal.toReal_mono hne h
  rw [← ENNReal.toReal_rpow] at step1
  have hen : ‖q‖ₑ.toReal = |q| := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg q)]
  rw [hen] at step1
  have hadd : (a + 1).toReal = a.toReal + 1 := by
    rw [ENNReal.toReal_add ha.ne (by norm_num : (1 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_one]
  rw [hadd] at step1
  calc |q| = (|q| ^ p) ^ (1 / p) := by
        rw [one_div, Real.rpow_rpow_inv (abs_nonneg q) hp.ne']
    _ ≤ (a.toReal + 1) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg q) p) step1 (by positivity)

theorem aux_cms_F_bound (x : ℝ) (w L : ℝ≥0∞) (hw0 : w ≠ 0) (hwt : w ≠ ⊤) (hL : L < ⊤)
    (h : w * ‖x‖ₑ ≤ L) : |x| ≤ L.toReal / w.toReal := by
  have h1 : (w * ‖x‖ₑ).toReal ≤ L.toReal := ENNReal.toReal_mono hL.ne h
  rw [ENNReal.toReal_mul] at h1
  have hx : ‖x‖ₑ.toReal = |x| := by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [hx] at h1
  have hwpos : 0 < w.toReal := ENNReal.toReal_pos hw0 hwt
  rw [le_div_iff₀ hwpos]
  rw [mul_comm]
  exact h1

theorem aux_cms_main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Countable ι] (F : ι → ℕ → Ω → ℝ) (C : ι → ℝ≥0)
    (hFm : ∀ j n, Measurable (F j n))
    (hmem : ∀ i n, MemLp (F i n) 1 P) (hbound : ∀ i n, eLpNorm (F i n) 1 P ≤ C i)
    (Q : ℕ → Ω → ℝ) (hQm : ∀ n, Measurable (Q n)) (p : ℝ) (hp : 1 ≤ p) (B : ℝ≥0)
    (hQbound : ∀ n, eLpNorm (Q n) (ENNReal.ofReal p) P ≤ B) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ om, 0 ≤ K om) ∧
      eLpNorm K (ENNReal.ofReal p) P ≤ ENNReal.ofReal (2 * ((B : ℝ) + 1)) ∧
      ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧
        (∀ n, |Q (seq n) om| ≤ K om) ∧
        ∀ i, ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ n, |F i (seq n) om| ≤ Bi := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let T : ℕ → Ω → ℝ≥0∞ := fun n ω => (∑' j, aux_cms_w e C j * ‖F j n ω‖ₑ) + ‖Q n ω‖ₑ ^ p
  have hTm : ∀ n, Measurable (T n) := by
    intro n
    have h1 : Measurable fun ω => ∑' j, aux_cms_w e C j * ‖F j n ω‖ₑ :=
      Measurable.tsum fun j => (measurable_const.mul (hFm j n).enorm)
    exact h1.add ((hQm n).enorm.pow_const p)
  have hTint : ∀ n, ∫⁻ ω, T n ω ∂P ≤ 1 + (B : ℝ≥0∞) ^ p := by
    intro n
    have h1 := aux_cms_lintegral_S P e he F C hmem hbound n
    have hQraw : SubdiffusiveProcess.RawLp.eLpNorm (Q n) (ENNReal.ofReal p) P ≤ B := by
      rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hQm n).aestronglyMeasurable]
      exact hQbound n
    have h2 := aux_cms_lintegral_Q P (Q n) p hp B hQraw
    have hm1 : Measurable fun ω => ∑' j, aux_cms_w e C j * ‖F j n ω‖ₑ :=
      Measurable.tsum fun j => (measurable_const.mul (hFm j n).enorm)
    calc ∫⁻ ω, T n ω ∂P = (∫⁻ ω, ∑' j, aux_cms_w e C j * ‖F j n ω‖ₑ ∂P) + ∫⁻ ω, ‖Q n ω‖ₑ ^ p ∂P :=
          lintegral_add_left hm1 _
      _ ≤ 1 + (B : ℝ≥0∞) ^ p := add_le_add h1 h2
  let Λ : Ω → ℝ≥0∞ := fun ω => liminf (fun n => T n ω) atTop
  have hΛm : Measurable Λ := Measurable.liminf hTm
  have hΛint : ∫⁻ ω, Λ ω ∂P ≤ 1 + (B : ℝ≥0∞) ^ p := aux_cms_fatou P T hTm _ hTint
  have hfin : (1 + (B : ℝ≥0∞) ^ p) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.coe_ne_top⟩
  have hΛlt : ∀ᵐ ω ∂P, Λ ω < ⊤ := ae_lt_top hΛm (ne_top_of_le_ne_top hfin hΛint)
  refine ⟨fun ω => ((Λ ω).toReal + 1) ^ (1 / p), ?_, ?_, aux_cms_K_eLpNorm P Λ hΛm p hp B hΛint, ?_⟩
  · exact (hΛm.ennreal_toReal.add_const 1).pow_const _
  · intro ω
    exact Real.rpow_nonneg (by positivity) _
  · filter_upwards [hΛlt] with ω hω
    obtain ⟨seq, hseq, hle⟩ := aux_cms_extract (fun n => T n ω) hω
    refine ⟨seq, hseq, fun n => ?_, fun i => ?_⟩
    · refine aux_cms_abs_le (Q (seq n) ω) (Λ ω) hω p (by linarith) ?_
      exact le_trans (le_add_self) (hle n)
    · have hL : Λ ω + 1 < ⊤ := ENNReal.add_lt_top.2 ⟨hω, ENNReal.one_lt_top⟩
      obtain ⟨hw0, hwt⟩ := aux_cms_w_ne e C i
      refine ⟨(Λ ω + 1).toReal / (aux_cms_w e C i).toReal, ?_, fun n => ?_⟩
      · positivity
      · refine aux_cms_F_bound _ _ _ hw0 hwt hL ?_
        refine le_trans ?_ (hle n)
        exact le_trans (ENNReal.le_tsum (f := fun j => aux_cms_w e C j * ‖F j (seq n) ω‖ₑ) i) le_self_add


/-- A distinguished moment bank keeps a uniform moment majorant while countably many auxiliary banks become bounded. -/
theorem inputs_classical_countable_moment_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Countable ι] (F : ι → ℕ → Ω → ℝ) (C : ι → ℝ≥0)
    (_hmem : ∀ i n, MemLp (F i n) 1 P)
    (_hbound : ∀ i n, eLpNorm (F i n) 1 P ≤ C i)
    (Q : ℕ → Ω → ℝ) (p : ℝ) (_hp : 1 ≤ p) (B : ℝ≥0)
    (_hQmem : ∀ n, MemLp (Q n) (ENNReal.ofReal p) P)
    (_hQbound : ∀ n, eLpNorm (Q n) (ENNReal.ofReal p) P ≤ B) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ om, 0 ≤ K om) ∧
      eLpNorm K (ENNReal.ofReal p) P ≤ ENNReal.ofReal (2 * ((B : ℝ) + 1)) ∧
      ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧
        (∀ n, |Q (seq n) om| ≤ K om) ∧
        ∀ i, ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ n, |F i (seq n) om| ≤ Bi := by
  let F' : ι → ℕ → Ω → ℝ := fun j n => (_hmem j n).aestronglyMeasurable.mk (F j n)
  let Q' : ℕ → Ω → ℝ := fun n => (_hQmem n).aestronglyMeasurable.mk (Q n)
  have hFe : ∀ j n, F j n =ᵐ[P] F' j n := fun j n => (_hmem j n).aestronglyMeasurable.ae_eq_mk
  have hQe : ∀ n, Q n =ᵐ[P] Q' n := fun n => (_hQmem n).aestronglyMeasurable.ae_eq_mk
  obtain ⟨K, hKm, hK0, hKn, hae⟩ := aux_cms_main P F' C
    (fun j n => (_hmem j n).aestronglyMeasurable.stronglyMeasurable_mk.measurable)
    (fun j n => (_hmem j n).ae_eq (hFe j n))
    (fun j n => by rw [← eLpNorm_congr_ae (hFe j n)]; exact _hbound j n)
    Q' (fun n => (_hQmem n).aestronglyMeasurable.stronglyMeasurable_mk.measurable) p _hp B
    (fun n => by rw [← eLpNorm_congr_ae (hQe n)]; exact _hQbound n)
  refine ⟨K, hKm, hK0, hKn, ?_⟩
  have hall : ∀ᵐ om ∂P, (∀ j n, F j n om = F' j n om) ∧ ∀ n, Q n om = Q' n om := by
    refine Filter.Eventually.and ?_ ?_
    · rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro n; exact hFe j n
    · rw [ae_all_iff]; intro n; exact hQe n
  filter_upwards [hae, hall] with om ⟨subseq, hs, h1, h2⟩ ⟨hF, hQ⟩
  refine ⟨subseq, hs, fun n => ?_, fun i => ?_⟩
  · rw [hQ]; exact h1 n
  · obtain ⟨Bi, hB0, hB⟩ := h2 i
    exact ⟨Bi, hB0, fun n => by rw [hF]; exact hB n⟩

end SubdiffusiveProcess.Paper
