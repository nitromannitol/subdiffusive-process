import Mathlib

/-!
# Conditional exponential crossing estimates

The exponential discount is zero at an infinite stopping time. Restricted-measure
domination transfers the setwise conditional duration bound to the discounted
starting time; splitting into long and short durations gives a strict contraction.
The probability cap `min c0 1` also covers `c0 > 1`.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing

/-- Exponential discount, with the zero value at an infinite time. -/
def discount (F : ℝ) (s : ℝ≥0∞) : ℝ≥0∞ := if s = ∞ then 0 else ENNReal.ofReal (Real.exp (-s.toReal/F))

theorem rate_pos (c0 : ℝ) (hc0 : 0 < c0)
    (he : Real.exp (-c0) < 1) :
    0 < min c0 1 * (1 - Real.exp (-c0)) := by
  exact mul_pos (lt_min hc0 zero_lt_one) (sub_pos.mpr he)


theorem long_duration_exp (F c0 s t : ℝ) (hF : 0 < F)
    (h : c0 * F ≤ s - t) :
    Real.exp (-s / F) ≤ Real.exp (-c0) * Real.exp (-t / F) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hF).2
  have heq : (-c0 + -t / F) * F = -c0 * F - t := by
    field_simp [hF.ne']
    ring
  rw [heq]
  linarith only [h]

theorem exp_product (c t F : ℝ) (n : ℕ) :
    Real.exp (t / F) * (Real.exp (-c)) ^ n =
      Real.exp (t / F - c * n) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem probability_zero {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (A : Set α)
    (x : ℝ) (hx : 0 ≤ x) :
    mu A ≤ ENNReal.ofReal (Real.exp x) := by
  calc mu A ≤ mu Set.univ := measure_mono (Set.subset_univ A)
    _ = 1 := measure_univ
    _ ≤ ENNReal.ofReal (Real.exp x) := by
        simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_exp hx)

theorem discount_measurable (F : ℝ) : Measurable (discount F) := by
  unfold discount
  exact Measurable.ite (measurableSet_singleton ∞) measurable_const
    (((measurable_id.ennreal_toReal.neg).div_const F).exp.ennreal_ofReal)

theorem discount_le_one (F : ℝ) (hF : 0 < F) (s : ℝ≥0∞) : discount F s ≤ 1 := by
  unfold discount
  split_ifs
  · exact zero_le 1
  · have h := ENNReal.ofReal_le_ofReal
      (Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr s.toReal_nonneg) hF.le))
    simpa only [ENNReal.ofReal_one] using h

theorem discount_antitone (F : ℝ) (hF : 0 < F) : Antitone (discount F) := by
  intro s t hst
  by_cases ht : t = ∞
  · simp [ht, discount]
  · have hs : s ≠ ∞ := ne_top_of_le_ne_top ht hst
    simp only [discount, if_neg hs, if_neg ht]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (neg_le_neg (ENNReal.toReal_mono ht hst)) hF.le))

theorem discount_ofReal (F t : ℝ) (ht : 0 ≤ t) :
    discount F (ENNReal.ofReal t) = ENNReal.ofReal (Real.exp (-t/F)) := by
  simp [discount, ENNReal.toReal_ofReal ht]

theorem discount_long (F c0 : ℝ) (hF : 0 < F) (hc : 0 ≤ c0)
    (s t : ℝ≥0∞) (hst : t ≤ s) (h : ENNReal.ofReal (c0*F) ≤ s-t) :
    discount F s ≤ ENNReal.ofReal (Real.exp (-c0)) * discount F t := by
  by_cases hs : s = ∞
  · simp [discount, hs]
  · have ht : t ≠ ∞ := ne_top_of_le_ne_top hs hst
    have hsub : s - t ≠ ∞ := ne_top_of_le_ne_top hs (tsub_le_self : s - t ≤ s)
    have hr := ENNReal.toReal_mono hsub h
    rw [ENNReal.toReal_ofReal (mul_nonneg hc hF.le),
        ENNReal.toReal_sub_of_le hst hs] at hr
    simp only [discount, if_neg hs, if_neg ht]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (long_duration_exp F c0 _ _ hF hr)

theorem trim_domination {α : Type*} {m m0 : MeasurableSpace α}
    (mu : @Measure α m0) (hm : m ≤ m0) (A G : Set α)
    (hA : MeasurableSet[m] A) (q : ℝ≥0∞)
    (h : ∀ B, MeasurableSet[m] B → B ⊆ A → q*mu B ≤ mu (B∩G)) :
    q • ((mu.restrict A).trim hm) ≤ (mu.restrict G).trim hm := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply, trim_measurableSet_eq hm hB, trim_measurableSet_eq hm hB,
    Measure.restrict_apply (hm B hB), Measure.restrict_apply (hm B hB), smul_eq_mul]
  exact (h (B∩A) (hB.inter hA) (fun _ hx => hx.2)).trans
    (measure_mono (fun _ hx => ⟨hx.1.1, hx.2⟩))

theorem weighted_trim {α : Type*} {m m0 : MeasurableSpace α}
    (mu : @Measure α m0) (hm : m ≤ m0) (A G : Set α)
    (q : ℝ≥0∞) (h : q • ((mu.restrict A).trim hm) ≤ (mu.restrict G).trim hm)
    (f : α → ℝ≥0∞) (hf : Measurable[m] f) :
    q*(∫⁻ x in A, f x ∂mu) ≤ ∫⁻ x in G, f x ∂mu := by
  have hh := lintegral_mono' h (le_rfl : f ≤ f)
  rw [MeasureTheory.lintegral_smul_measure, lintegral_trim hm hf,
    lintegral_trim hm hf] at hh
  exact hh

theorem pow_bounded (a : ℕ → ℝ≥0∞) (q : ℝ≥0∞) (N : ℕ)
    (h0 : a 0 ≤ q) (hs : ∀ i, i+1<N → a (i+1) ≤ q*a i) :
    ∀ i, i<N → a i ≤ q^(i+1) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hi
    calc a (i+1) ≤ q*a i := hs i hi
      _ ≤ q*q^(i+1) := mul_le_mul_right (ih (by omega)) q
      _ = q^((i+1)+1) := by rw [pow_succ q (i+1), mul_comm]


theorem bounded_lintegral {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → ℝ≥0∞)
    (h : ∀ x, f x ≤ 1) : (∫⁻ x, f x ∂mu) ≤ 1 := by
  have hh : ∫⁻ x, f x ∂mu ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂mu := lintegral_mono h
  simpa using hh

theorem discount_rate_nonnegative (q r : ℝ) (_hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ 1-q*(1-r) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hr1)]

theorem discount_finite_restrict {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (F : ℝ) (T : α → ℝ≥0∞) (hT : Measurable T) :
    (∫⁻ x in {x | T x < ∞}, discount F (T x) ∂mu) = ∫⁻ x, discount F (T x) ∂mu := by
  have hset : MeasurableSet {x | T x < ∞} := hT measurableSet_Iio
  rw [← lintegral_indicator hset]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ {x | T x < ∞}
  · simp [Set.indicator_of_mem hx]
  · have hTop : T x = ∞ := top_unique (not_lt.mp hx)
    simp [discount, hTop]

theorem ennreal_combine (a b x : ℝ≥0∞) (hx : x ≠ ∞)
    (q r : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hqr : 0 ≤ 1-q*(1-r)) (hab : a+b=x)
    (hb : ENNReal.ofReal q*x ≤ b) :
    a + ENNReal.ofReal r*b ≤ ENNReal.ofReal (1-q*(1-r))*x := by
  have ha : a ≠ ∞ := ne_top_of_le_ne_top hx (by rw [←hab]; exact le_add_right le_rfl)
  have hbtop : b ≠ ∞ := ne_top_of_le_ne_top hx (by rw [←hab]; exact le_add_left le_rfl)
  have hrb : ENNReal.ofReal r * b ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbtop
  have hmul : ENNReal.ofReal (1-q*(1-r)) * x ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx
  have hreal := ENNReal.toReal_mono hbtop hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq] at hreal
  have habr : a.toReal + b.toReal = x.toReal := by
    rw [← ENNReal.toReal_add ha hbtop, hab]
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨ha, hrb⟩) hmul).1
  rw [ENNReal.toReal_add ha hrb, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hqr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hreal)]

theorem sum_compl_bound {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (f g : α → ℝ≥0∞) (hf : Measurable f)
    (G : Set α) (hG : MeasurableSet G) (r : ℝ≥0∞)
    (h : ∀ x, g x ≤ f x) (hgood : ∀ x ∈ G, g x ≤ r*f x) :
    (∫⁻ x, g x ∂mu) ≤ (∫⁻ x in Gᶜ, f x ∂mu) + r*(∫⁻ x in G, f x ∂mu) := by
  have h1 : (∫⁻ x in Gᶜ, g x ∂mu) ≤ ∫⁻ x in Gᶜ, f x ∂mu := lintegral_mono h
  have h2 : (∫⁻ x in G, g x ∂mu) ≤ r * ∫⁻ x in G, f x ∂mu := by
    calc (∫⁻ x in G, g x ∂mu) ≤ ∫⁻ x in G, r * f x ∂mu :=
          setLIntegral_mono (measurable_const.mul hf) hgood
      _ = r * ∫⁻ x in G, f x ∂mu := lintegral_const_mul r hf
  calc (∫⁻ x, g x ∂mu) = (∫⁻ x in G, g x ∂mu) + ∫⁻ x in Gᶜ, g x ∂mu :=
        (lintegral_add_compl g hG).symm
    _ ≤ r * (∫⁻ x in G, f x ∂mu) + ∫⁻ x in Gᶜ, f x ∂mu := add_le_add h2 h1
    _ = _ := add_comm _ _

theorem discount_inverse (F t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (t/F)) * discount F (ENNReal.ofReal t) = 1 := by
  rw [discount_ofReal F t ht, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  have h : t/F + -t/F = 0 := by ring
  rw [h, Real.exp_zero, ENNReal.ofReal_one]

theorem discount_tail {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (F t : ℝ) (hF : 0 < F)
    (T : α → ℝ≥0∞) (hT : Measurable T) (A : Set α)
    (hA : A ⊆ {x | T x ≤ ENNReal.ofReal t}) :
    discount F (ENNReal.ofReal t)*mu A ≤ ∫⁻ x, discount F (T x) ∂mu := by
  calc discount F (ENNReal.ofReal t) * mu A
      = ∫⁻ x in A, discount F (ENNReal.ofReal t) ∂mu :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in A, discount F (T x) ∂mu :=
        setLIntegral_mono ((discount_measurable F).comp hT)
          (fun x hx => discount_antitone F hF (hA hx))
    _ ≤ ∫⁻ x, discount F (T x) ∂mu := setLIntegral_le_lintegral _ _

theorem exp_ENN_product (c t F : ℝ) (n : ℕ) :
    ENNReal.ofReal (Real.exp (t/F)) * (ENNReal.ofReal (Real.exp (-c)))^n =
      ENNReal.ofReal (Real.exp (t/F-c*n)) := by
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, exp_product]

theorem finite_lintegral_of_one {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → ℝ≥0∞)
    (h : ∀ x, f x ≤ 1) : (∫⁻x,f x ∂mu) ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (bounded_lintegral mu f h)

theorem tail_assembly (a b p q : ℝ≥0∞) (hunit : a*b=1)
    (hl : b*p ≤ q) : p ≤ a*q := by
  have hh := mul_le_mul_right hl a
  calc p = a*(b*p) := by rw [←mul_assoc, hunit, one_mul]
    _ ≤ a*q := hh


theorem capped_probability (a b : ℝ≥0∞) (c0 : ℝ)
    (h : ENNReal.ofReal c0*a ≤ b) : ENNReal.ofReal (min c0 1)*a ≤ b := by
  calc ENNReal.ofReal (min c0 1)*a ≤ ENNReal.ofReal c0*a := by
        gcongr
        exact min_le_left c0 1
  _ ≤ b := h

theorem coefficient_compare (c : ℝ) :
    ENNReal.ofReal (1-c) ≤ ENNReal.ofReal (Real.exp (-c)) := by
  exact ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg c)

theorem discount_monotone_integral {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (F : ℝ) (hF : 0 < F) (S T : α → ℝ≥0∞)
    (h : ∀ x, S x ≤ T x) :
    (∫⁻ x, discount F (T x) ∂mu) ≤ ∫⁻ x, discount F (S x) ∂mu := by
  exact lintegral_mono (fun x => discount_antitone F hF (h x))

theorem rate_neg_exp_lt (c0 : ℝ) (hc0 : 0 < c0) : Real.exp (-c0) < 1 := by
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc0)



theorem contraction_factor (c0 : ℝ) (hc0 : 0 < c0) :
    0 ≤ 1 - min c0 1*(1-Real.exp (-c0)) := by
  apply discount_rate_nonnegative
  exact le_of_lt (lt_min hc0 zero_lt_one)
  exact min_le_right c0 1
  exact (Real.exp_pos _).le
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc0.le)

/-- The setwise crossing condition contracts the expected discounted endpoint time. -/
theorem discount_contraction {α : Type*} {m m0 : MeasurableSpace α}
    (mu : @Measure α m0) [IsProbabilityMeasure mu] (hm : m ≤ m0)
    (F c0 : ℝ) (hF : 0 < F) (hc0 : 0 < c0)
    (S T : α → ℝ≥0∞) (hS : Measurable[m0] S) (hT : Measurable[m] T)
    (hst : ∀ x, T x ≤ S x)
    (hcond : ∀ B, MeasurableSet[m] B → B ⊆ {x | T x < ∞} →
      ENNReal.ofReal c0*mu B ≤ mu (B∩{x | ENNReal.ofReal (c0*F) ≤ S x-T x})) :
    (∫⁻x, discount F (S x) ∂mu) ≤
      ENNReal.ofReal (Real.exp (-(min c0 1*(1-Real.exp (-c0))))) *
        (∫⁻x, discount F (T x) ∂mu) := by
  let A : Set α := {x | T x < ∞}
  let G : Set α := {x | ENNReal.ofReal (c0*F) ≤ S x-T x}
  let q : ℝ := min c0 1
  let r : ℝ := Real.exp (-c0)
  have hTm : Measurable[m0] T := hT.mono hm le_rfl
  have hf : Measurable[m] (fun x => discount F (T x)) :=
    (discount_measurable F).comp hT
  have hf0 : Measurable[m0] (fun x => discount F (T x)) := hf.mono hm le_rfl
  have hA : MeasurableSet[m] A := hT measurableSet_Iio
  have hG : MeasurableSet[m0] G := measurableSet_le measurable_const (hS.sub hTm)
  have hdom := trim_domination mu hm A G hA (ENNReal.ofReal q) (by
    intro B hB hBA
    exact capped_probability (mu B) (mu (B ∩ G)) c0 (hcond B hB hBA))
  have hw := weighted_trim mu hm A G (ENNReal.ofReal q) hdom
    (fun x => discount F (T x)) hf
  change ENNReal.ofReal q * (∫⁻ x in {x | T x < ∞}, discount F (T x) ∂mu) ≤
    ∫⁻ x in G, discount F (T x) ∂mu at hw
  rw [discount_finite_restrict mu F T hTm] at hw
  have hcmp := sum_compl_bound mu (fun x => discount F (T x))
    (fun x => discount F (S x)) hf0 G hG (ENNReal.ofReal r)
    (fun x => discount_antitone F hF (hst x))
    (fun x hx => discount_long F c0 hF hc0.le (S x) (T x) (hst x) hx)
  have hfin := finite_lintegral_of_one mu (fun x => discount F (T x))
    (fun x => discount_le_one F hF (T x))
  have hqr : 0 ≤ 1-q*(1-r) := contraction_factor c0 hc0
  have hsum : (∫⁻ x in Gᶜ, discount F (T x) ∂mu) +
      (∫⁻ x in G, discount F (T x) ∂mu) = ∫⁻ x, discount F (T x) ∂mu := by
    rw [add_comm]
    exact lintegral_add_compl _ hG
  have hbound := ennreal_combine _ _ _ hfin q r (le_of_lt (lt_min hc0 zero_lt_one))
    (Real.exp_pos _).le (rate_neg_exp_lt c0 hc0).le hqr hsum hw
  exact hcmp.trans (hbound.trans (mul_le_mul_left (coefficient_compare (q*(1-r))) _))

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
