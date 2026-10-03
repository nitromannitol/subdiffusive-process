module

public import SubdiffusiveProcess.PrefixScores.Basic
public import SubdiffusiveProcess.PrefixScores.BadBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldTwoDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseDensity

@[expose] public section

/-! Uniform exponential tails for the sum of the three primitive ramps. -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open SubdiffusiveProcess SubdiffusiveProcess.PrefixScores
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.PrefixScores
attribute [local instance] Classical.propDecidable

lemma ramp_le_goodIndicator (a b : ℝ) (X : ENNReal) (G : Prop)
    (hG : G → X ≤ ENNReal.ofReal a) :
    extendedPrimitiveRamp a b X ≤ if G then (0 : ℝ) else 1 := by
  classical
  by_cases hg : G
  · simp only [hg, if_true, extendedPrimitiveRamp, tsub_eq_zero_of_le (hG hg),
      ENNReal.zero_div, min_eq_right zero_le, ENNReal.toReal_zero, le_refl]
  · simp only [hg, if_false]
    exact (extendedPrimitiveRamp_bounds a b X).2

lemma ae_badScore_le_indicators {d : ℕ} [NeZero d] (M : GMCModel d) (s eps : ℝ)
    (heps : 0 < eps) (z : Vec d) :
    ∀ᵐ ω ∂M.P.toMeasure, ∀ m : ℕ,
      primitiveBadScore M s eps ω m z ≤
        eventIndicator ({ω | GoodFieldOne m z (eps / 2) s ω}ᶜ) ω +
        eventIndicator ({ω | GoodFieldTwo m z s ω}ᶜ) ω +
        eventIndicator ({ω | GoodResponse M none m z (eps / 2) s ω}ᶜ) ω := by
  classical
  have hp : ∀ᵐ ω ∂M.P.toMeasure, ∀ m : ℕ,
      GoodFieldTwo m z s ω → primitiveProductScore s ω m z ≤ 6 :=
    ae_all_iff.mpr (fun m => ae_goodFieldTwo_bound M s m z)
  filter_upwards [hp] with ω hP
  intro m
  have hF := ramp_le_goodIndicator (eps / 2) eps (primitiveFieldScore s ω m z)
    (GoodFieldOne m z (eps / 2) s ω) (goodFieldOne_bound s (eps / 2) ω m z (by positivity))
  have hP' := ramp_le_goodIndicator 6 12 (primitiveProductScore s ω m z)
    (GoodFieldTwo m z s ω) (by simpa only [ENNReal.ofReal_ofNat] using hP m)
  have hR := ramp_le_goodIndicator (eps ^ 2 / 4) (eps ^ 2) (primitiveResponseScore M s ω m z)
    (GoodResponse M none m z (eps / 2) s ω) (fun h => by
      have heSq : (eps / 2) ^ 2 = eps ^ 2 / 4 := by ring
      simpa only [heSq] using goodResponse_bound M s (eps / 2) ω m z h)
  unfold primitiveBadScore eventIndicator
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, ite_not]
  exact add_le_add (add_le_add hF hP') hR

lemma measure_density_translate {d : ℕ} (M : GMCModel d) (z : Vec d)
    (E F : ℕ → Set (PotentialSample d))
    (hEF : ∀ m ω, translatePotentialSample z ω ∈ E m ↔ ω ∈ F m)
    (theta : ℝ) (n K : ℕ) :
    M.P.toMeasure {ω | theta ≤ intervalEventDensity F n K ω} =
      M.P.toMeasure {ω | theta ≤ intervalEventDensity E n K ω} := by
  have hpoint : ∀ ω, intervalEventDensity F n K ω =
      intervalEventDensity E n K (translatePotentialSample z ω) := by
    intro ω
    unfold intervalEventDensity
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    unfold eventIndicator
    rw [hEF]
  have hset : {ω | theta ≤ intervalEventDensity F n K ω} =
      translatePotentialSample z ⁻¹' {ω | theta ≤ intervalEventDensity E n K ω} := by
    ext ω
    exact (congrArg (fun v : ℝ => theta ≤ v) (hpoint ω)).to_iff
  rw [hset, Section6Covariance.measure_preimage_translatePotentialSample]

lemma exists_badScore_tail (d : ℕ) [NeZero d] (s eps lam A : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ z : Vec d, ∀ n k : ℕ,
        M.P.toMeasure {ω | lam * (k : ℝ) / 4 <
          ∑ i ∈ Finset.range k, primitiveBadScore M s eps ω (n + i) z} ≤
            ENNReal.ofReal (3 * Real.exp (-(A * (k : ℝ)))) := by
  classical
  obtain ⟨C3, hC3, hresponse⟩ := exists_measure_goodResponse_badDensity_le d
  let C1 := fieldOneDensityConst d
  let C2 := 1 + fieldTwoDensityConst d ^ 2 + 2 * |fieldTwoRateDenom d|
  let r := s / 8
  let e := eps / 2
  let theta := min 1 (lam / 12)
  let B := max A 0 + 1
  have hC1 : 0 < C1 := fieldOneDensityConst_pos d
  have hC2 : 0 < C2 := by dsimp [C2]; positivity
  have hr : 0 < r := div_pos hs.1 (by norm_num)
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [hs.2]
  have he : 0 < e := div_pos heps.1 (by norm_num)
  have he1 : e ≤ 1 := by dsimp [e]; linarith [heps.2]
  have ht : 0 < theta := lt_min one_pos (div_pos hlam (by norm_num))
  have ht1 : theta ≤ 1 := min_le_left _ _
  have htlam : 3 * theta ≤ lam / 4 := by
    have h := min_le_right (1 : ℝ) (lam / 12)
    dsimp only [theta]
    linarith
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [le_max_right A 0]
  have hB : 0 < B := zero_lt_one.trans_le hB1
  have hAB : A ≤ B := by dsimp [B]; linarith [le_max_left A 0]
  obtain ⟨delta0, hdelta0, hbudgets⟩ := exists_badTest_budgets s r e theta C1 C2 C3 B
    hs.1 hr he ht hC1 hC2 hC3 hB1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hdelta z n k
  have hd := M.shellPrefix.delta_pos
  obtain ⟨hd1, hbudget1, hbudget3, hrate1, hrate3, hb2⟩ := hbudgets M.delta hd hdelta
  have hc2sq : fieldTwoDensityConst d ^ 2 ≤ C2 := by
    dsimp [C2]; nlinarith [abs_nonneg (fieldTwoRateDenom d)]
  have hsmall2 : M.delta ≤ (fieldTwoDensityConst d)⁻¹ * s * Real.sqrt theta :=
    linear_smallness_of_budget (fieldTwoDensityConst_pos M) hs.1 hd ht.le hc2sq hB1 hb2
  have hden2 : 2 * fieldTwoRateDenom d ≤ C2 := by
    dsimp [C2]
    nlinarith [le_abs_self (fieldTwoRateDenom d), sq_nonneg (fieldTwoDensityConst d)]
  have hrate2 : B ≤ s ^ 2 * theta / (2 * fieldTwoRateDenom d * M.delta ^ 2) := by
    apply rate_of_budget (mul_pos (mul_pos (by norm_num) (fieldTwoRateDenom_pos M)) (sq_pos_of_pos hd))
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden2 (sq_nonneg _)) hB.le).trans hb2
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let K := k - 1
  have hK : (K : ℝ) + 1 = (k : ℝ) := by
    dsimp [K]
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  let EF : ℕ → Set (PotentialSample d) := fun m => {ω | GoodFieldOne m z e s ω}ᶜ
  let EP : ℕ → Set (PotentialSample d) := fun m => {ω | GoodFieldTwo m z s ω}ᶜ
  let ER : ℕ → Set (PotentialSample d) := fun m => {ω | GoodResponse M none m z e s ω}ᶜ
  have htailF : M.P.toMeasure {ω | theta ≤ intervalEventDensity EF n K ω} ≤
      ENNReal.ofReal (Real.exp (-(A * (k : ℝ)))) := by
    rw [measure_density_translate M z (fun m => {ω | GoodFieldOne m 0 e s ω}ᶜ) EF (fun m ω => by
      simp only [EF, Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [Section6Covariance.goodFieldOne_translatePotentialSample, add_zero])]
    have h := measure_goodFieldOne_badDensity_le M hr hr1 ht ht1 he he1 hbudget1 n K
    have hrs : 8 * r = s := by dsimp [r]; ring
    rw [hrs, hK] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hrate := hAB.trans hrate1
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg k))
  have htailP : M.P.toMeasure {ω | theta ≤ intervalEventDensity EP n K ω} ≤
      ENNReal.ofReal (Real.exp (-(A * (k : ℝ)))) := by
    rw [measure_density_translate M z (fun m => {ω | GoodFieldTwo m 0 s ω}ᶜ) EP (fun m ω => by
      simp only [EP, Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [Section6Covariance.goodFieldTwo_translatePotentialSample, add_zero])]
    have h := measure_goodFieldTwo_badDensity_le M hs.1 hs.2 ht ht1 hsmall2 n K
    rw [hK] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (hAB.trans hrate2) (Nat.cast_nonneg k))
  have htailR : M.P.toMeasure {ω | theta ≤ intervalEventDensity ER n K ω} ≤
      ENNReal.ofReal (Real.exp (-(A * (k : ℝ)))) := by
    rw [measure_density_translate M z (fun m => {ω | GoodResponse M none m 0 e s ω}ᶜ) ER (fun m ω => by
      simp only [ER, Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [Section6Covariance.goodResponse_translatePotentialSample, add_zero])]
    have h := hresponse M r theta e ⟨hr, hr1⟩ ⟨ht, ht1⟩ ⟨he, he1⟩ (by
      simpa only [mul_assoc] using hbudget3) n K
    have hrs : 8 * r = s := by dsimp [r]; ring
    rw [hrs, hK] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (hAB.trans hrate3) (Nat.cast_nonneg k))
  have hsub : ∀ᵐ ω ∂M.P.toMeasure,
      ω ∈ {ω | lam * (k : ℝ) / 4 < ∑ i ∈ Finset.range k, primitiveBadScore M s eps ω (n + i) z} →
      ω ∈ ({ω | theta ≤ intervalEventDensity EF n K ω} ∪
        {ω | theta ≤ intervalEventDensity EP n K ω}) ∪
        {ω | theta ≤ intervalEventDensity ER n K ω} := by
    filter_upwards [ae_badScore_le_indicators M s eps heps.1 z] with ω hω
    intro hz
    by_cases hf : theta ≤ intervalEventDensity EF n K ω
    · exact Or.inl (Or.inl hf)
    by_cases hp : theta ≤ intervalEventDensity EP n K ω
    · exact Or.inl (Or.inr hp)
    by_cases hr' : theta ≤ intervalEventDensity ER n K ω
    · exact Or.inr hr'
    have hf' : (∑ m ∈ Finset.Icc n (n + K), eventIndicator (EF m) ω) < theta * (k : ℝ) := by
      exact (div_lt_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp (lt_of_not_ge hf) |>.trans_eq (by rw [hK])
    have hp' : (∑ m ∈ Finset.Icc n (n + K), eventIndicator (EP m) ω) < theta * (k : ℝ) := by
      exact (div_lt_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp (lt_of_not_ge hp) |>.trans_eq (by rw [hK])
    have hr'' : (∑ m ∈ Finset.Icc n (n + K), eventIndicator (ER m) ω) < theta * (k : ℝ) := by
      exact (div_lt_iff₀ (by positivity : 0 < (K : ℝ) + 1)).mp (lt_of_not_ge hr') |>.trans_eq (by rw [hK])
    have hsum := Finset.sum_le_sum (s := Finset.Icc n (n + K)) (fun m _ => hω m)
    simp only [Finset.sum_add_distrib] at hsum
    rw [sum_window (fun j => primitiveBadScore M s eps ω j z) n k hkpos] at hz
    have hlast := mul_le_mul_of_nonneg_right htlam (Nat.cast_nonneg k)
    change lam * (k : ℝ) / 4 < _ at hz
    dsimp only [EF, EP, ER, e, K] at hf' hp' hr'' hsum hz
    exfalso
    nlinarith
  calc
    _ ≤ M.P.toMeasure (({ω | theta ≤ intervalEventDensity EF n K ω} ∪
        {ω | theta ≤ intervalEventDensity EP n K ω}) ∪ {ω | theta ≤ intervalEventDensity ER n K ω}) :=
      measure_mono_ae hsub
    _ ≤ (M.P.toMeasure {ω | theta ≤ intervalEventDensity EF n K ω} +
        M.P.toMeasure {ω | theta ≤ intervalEventDensity EP n K ω}) +
        M.P.toMeasure {ω | theta ≤ intervalEventDensity ER n K ω} :=
      (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ (ENNReal.ofReal (Real.exp (-(A * (k : ℝ)))) + ENNReal.ofReal (Real.exp (-(A * (k : ℝ))))) +
        ENNReal.ofReal (Real.exp (-(A * (k : ℝ)))) := add_le_add (add_le_add htailF htailP) htailR
    _ = ENNReal.ofReal (3 * Real.exp (-(A * (k : ℝ)))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
      congr 1
      ring

end SubdiffusiveProcess.PrefixScores
