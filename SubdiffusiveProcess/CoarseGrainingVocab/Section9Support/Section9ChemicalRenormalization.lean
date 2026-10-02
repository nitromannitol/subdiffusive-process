import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Finset

noncomputable section

/-- The weight sequence carrying the entropy reserve of the two-seed recursion.
`theta0` is the seed weight, `a = c q` the current rate and `e k` the level-`k`
log-entropy. -/
def entropyReserveWeight (theta0 a : ℝ) (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  theta0 - (2 * a)⁻¹ * ∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i

/-- The defining property: the weight drop at level `k`, measured in the units of
the recursion, is exactly the level-`k` entropy plus the union-bound bit. -/
theorem entropyReserveWeight_step {theta0 a : ℝ} (ha : a ≠ 0) (e : ℕ → ℝ) (k : ℕ) :
    a * (2 * entropyReserveWeight theta0 a e k -
        2 * entropyReserveWeight theta0 a e (k + 1)) * 2 ^ k =
      e k + Real.log 2 := by
  have hsum : ∑ i ∈ Finset.range (k + 1), (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i =
      (∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i) +
        (e k + Real.log 2) * (2 : ℝ)⁻¹ ^ k := Finset.sum_range_succ _ k
  have hpow : ((2 : ℝ)⁻¹) ^ k * (2 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have h2a : (2 * a) * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ (by simpa using ha)
  have hnext : entropyReserveWeight theta0 a e (k + 1) =
      entropyReserveWeight theta0 a e k -
        (2 * a)⁻¹ * ((e k + Real.log 2) * (2 : ℝ)⁻¹ ^ k) := by
    simp only [entropyReserveWeight, hsum]
    ring
  rw [hnext]
  have hrw : a * (2 * entropyReserveWeight theta0 a e k -
      2 * (entropyReserveWeight theta0 a e k -
        (2 * a)⁻¹ * ((e k + Real.log 2) * (2 : ℝ)⁻¹ ^ k))) * 2 ^ k =
      ((2 * a) * (2 * a)⁻¹) * ((e k + Real.log 2) * ((2 : ℝ)⁻¹ ^ k * 2 ^ k)) := by
    ring
  rw [hrw, h2a, hpow]
  ring

/-- The reserve is never spent below `theta0 / 2` once `q` is large: the total
spend is the fixed number `S` divided by `2 a`. -/
theorem half_le_entropyReserveWeight {theta0 a S : ℝ} (ha : 0 < a) {e : ℕ → ℝ}
    (hsum : ∀ k, ∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i ≤ S)
    (hS : S ≤ a * theta0) (k : ℕ) :
    theta0 / 2 ≤ entropyReserveWeight theta0 a e k := by
  have hspend : (2 * a)⁻¹ * ∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i ≤
      theta0 / 2 := by
    have h2a : 0 < 2 * a := by linarith
    rw [inv_mul_le_iff₀ h2a]
    calc ∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i ≤ S := hsum k
      _ ≤ a * theta0 := hS
      _ = 2 * a * (theta0 / 2) := by ring
  simp only [entropyReserveWeight]
  linarith

/-- The reserve never exceeds the seed weight. -/
theorem entropyReserveWeight_le {theta0 a : ℝ} (ha : 0 < a) {e : ℕ → ℝ}
    (he : ∀ i, 0 ≤ e i) (k : ℕ) :
    entropyReserveWeight theta0 a e k ≤ theta0 := by
  have hnn : 0 ≤ ∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i := by
    refine Finset.sum_nonneg fun i _ => ?_
    have : 0 ≤ e i + Real.log 2 := by
      have := he i
      have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith [he i]
    positivity
  have h2a : 0 < (2 * a)⁻¹ := by positivity
  simp only [entropyReserveWeight]
  nlinarith



theorem le_exp_neg_of_entropyReserve_recursion
    {p e g theta : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hpnn : ∀ k, 0 ≤ p k)
    (hp0 : p 0 ≤ Real.exp (-(a * theta 0 * 2 ^ 0)))
    (hrec : ∀ k, p (k + 1) ≤ Real.exp (e k) * (p k ^ 2 + Real.exp (-(a * g k))))
    (hg : ∀ k, 2 * theta k * 2 ^ k ≤ g k)
    (hres : ∀ k, e k + Real.log 2 ≤ a * (2 * theta k - 2 * theta (k + 1)) * 2 ^ k) :
    ∀ k, p k ≤ Real.exp (-(a * theta k * 2 ^ k)) := by
  intro k
  induction k with
  | zero => exact hp0
  | succ k ih =>
    set t : ℝ := a * theta k * 2 ^ k with ht
    have hsq : p k ^ 2 ≤ Real.exp (-(2 * t)) := by
      have h1 : p k ^ 2 ≤ (Real.exp (-t)) ^ 2 :=
        pow_le_pow_left₀ (hpnn k) ih 2
      have h2 : (Real.exp (-t)) ^ 2 = Real.exp (-(2 * t)) := by
        rw [← Real.exp_nat_mul]
        ring_nf
      linarith [h2 ▸ h1]
    have htrunc : Real.exp (-(a * g k)) ≤ Real.exp (-(2 * t)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (hg k) ha.le
      have hrw : a * (2 * theta k * 2 ^ k) = 2 * t := by rw [ht]; ring
      linarith [hrw ▸ this]
    have hsum : p k ^ 2 + Real.exp (-(a * g k)) ≤ 2 * Real.exp (-(2 * t)) := by
      linarith
    have hepos : (0 : ℝ) < Real.exp (e k) := Real.exp_pos _
    have hstep : p (k + 1) ≤ Real.exp (e k) * (2 * Real.exp (-(2 * t))) :=
      (hrec k).trans (mul_le_mul_of_nonneg_left hsum hepos.le)
    have hfactor : Real.exp (e k) * (2 * Real.exp (-(2 * t))) =
        Real.exp (e k + Real.log 2 + -(2 * t)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      ring
    have hexp : e k + Real.log 2 + -(2 * t) ≤ -(a * theta (k + 1) * 2 ^ (k + 1)) := by
      have h := hres k
      have hid : a * (2 * theta k - 2 * theta (k + 1)) * 2 ^ k - 2 * t =
          -(a * theta (k + 1) * 2 ^ (k + 1)) := by
        rw [ht, pow_succ]
        ring
      linarith [hid]
    calc p (k + 1) ≤ Real.exp (e k) * (2 * Real.exp (-(2 * t))) := hstep
      _ = Real.exp (e k + Real.log 2 + -(2 * t)) := hfactor
      _ ≤ Real.exp (-(a * theta (k + 1) * 2 ^ (k + 1))) := Real.exp_le_exp.mpr hexp

/-- **The `q`-uniform form.**  With the concrete reserve `entropyReserveWeight 1 a e`,
a recursion whose accumulated entropy `S` satisfies `S ≤ a` (i.e. `q ≥ q₀(d)`
after `a = c q`) gives the rate `a / 2`, *independent of how large `a` is*. -/
theorem le_exp_neg_half_of_entropyReserve_recursion
    {p e g : ℕ → ℝ} {a S : ℝ} (ha : 0 < a) (he : ∀ i, 0 ≤ e i)
    (hpnn : ∀ k, 0 ≤ p k)
    (hsum : ∀ k, ∑ i ∈ Finset.range k, (e i + Real.log 2) * (2 : ℝ)⁻¹ ^ i ≤ S)
    (hS : S ≤ a)
    (hp0 : p 0 ≤ Real.exp (-(a * entropyReserveWeight 1 a e 0 * 2 ^ 0)))
    (hrec : ∀ k, p (k + 1) ≤ Real.exp (e k) * (p k ^ 2 + Real.exp (-(a * g k))))
    (hg : ∀ k, 2 * 2 ^ k ≤ g k) :
    ∀ k, p k ≤ Real.exp (-(a / 2 * 2 ^ k)) := by
  have hSa : S ≤ a * (1 : ℝ) := by simpa using hS
  have hhalf : ∀ k, (1 : ℝ) / 2 ≤ entropyReserveWeight 1 a e k := fun k =>
    half_le_entropyReserveWeight ha hsum hSa k
  have hle1 : ∀ k, entropyReserveWeight 1 a e k ≤ 1 := fun k =>
    entropyReserveWeight_le ha he k
  have hmain := le_exp_neg_of_entropyReserve_recursion (theta := entropyReserveWeight 1 a e)
    ha hpnn hp0 hrec
    (fun k => by
      have h1 : 2 * entropyReserveWeight 1 a e k * (2 : ℝ) ^ k ≤ 2 * 2 ^ k := by
        have hpow : (0 : ℝ) < 2 ^ k := by positivity
        nlinarith [hle1 k]
      exact h1.trans (hg k))
    (fun k => le_of_eq (entropyReserveWeight_step ha.ne' e k).symm)
  intro k
  refine (hmain k).trans (Real.exp_le_exp.mpr ?_)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : a * (1 / 2) ≤ a * entropyReserveWeight 1 a e k :=
    mul_le_mul_of_nonneg_left (hhalf k) ha.le
  have h2 := mul_le_mul_of_nonneg_right h1 hpow.le
  linarith

/-- The scale sequence `L_k = exp (√2 ^ k)`, for which `(log L_k) ^ 2 = 2 ^ k`. -/
theorem log_sq_sqrtTwo_pow (k : ℕ) : (Real.sqrt 2 ^ k) ^ 2 = 2 ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- **The scale extraction.**  A level bound `exp (-(b * 2 ^ k))` at the level
`k` determined by `L < exp (√2 ^ (k+1))` is at least as strong as the printed
`exp (-(b / 2) (log L) ^ 2)`. -/
theorem exp_neg_two_pow_le_exp_neg_log_sq {b L : ℝ} {k : ℕ} (hb : 0 ≤ b)
    (hL1 : 1 ≤ L) (hlt : L < Real.exp (Real.sqrt 2 ^ (k + 1))) :
    Real.exp (-(b * 2 ^ k)) ≤ Real.exp (-(b / 2 * Real.log L ^ 2)) := by
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlt' : Real.log L < Real.sqrt 2 ^ (k + 1) := by
    have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
    have := Real.log_lt_log hLpos hlt
    rwa [Real.log_exp] at this
  have hsq : Real.log L ^ 2 < 2 * 2 ^ k := by
    have h1 : Real.log L ^ 2 < (Real.sqrt 2 ^ (k + 1)) ^ 2 := by
      have hnn : 0 ≤ Real.sqrt 2 ^ (k + 1) := by positivity
      nlinarith
    rw [log_sq_sqrtTwo_pow] at h1
    calc Real.log L ^ 2 < 2 ^ (k + 1) := h1
      _ = 2 * 2 ^ k := by ring
  apply Real.exp_le_exp.mpr
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]

/-- Every `L ≥ e` lies between two consecutive scales `exp (√2 ^ k)`. -/
theorem exists_sqrtTwo_level (L : ℝ) (hL : Real.exp 1 ≤ L) :
    ∃ k : ℕ, Real.exp (Real.sqrt 2 ^ k) ≤ L ∧ L < Real.exp (Real.sqrt 2 ^ (k + 1)) := by
  classical
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  set P : ℕ → Prop := fun k => L < Real.exp (Real.sqrt 2 ^ k) with hP
  have hN : ∃ n, P n := by
    have htend : Filter.Tendsto (fun n : ℕ => Real.exp (Real.sqrt 2 ^ n))
        Filter.atTop Filter.atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt h1)
    exact (htend.eventually_gt_atTop L).exists
  have hk0 : P (Nat.find hN) := Nat.find_spec hN
  have hk0ne : Nat.find hN ≠ 0 := by
    intro hzero
    rw [hzero] at hk0
    simp only [hP, pow_zero] at hk0
    linarith
  refine ⟨Nat.find hN - 1, ?_, ?_⟩
  · have hk := Nat.find_min hN (Nat.sub_lt (Nat.pos_of_ne_zero hk0ne) one_pos)
    simp only [hP, not_lt] at hk
    exact hk
  · have hsucc : Nat.find hN - 1 + 1 = Nat.find hN :=
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hk0ne)
    rw [hsucc]
    exact hk0



theorem exists_level_exp_neg_log_sq {b : ℝ} (hb : 0 ≤ b) {L : ℝ} (hL : Real.exp 1 ≤ L) :
    ∃ k : ℕ, Real.exp (Real.sqrt 2 ^ k) ≤ L ∧
      Real.exp (-(b * 2 ^ k)) ≤ Real.exp (-(b / 2 * Real.log L ^ 2)) := by
  obtain ⟨k, hle, hlt⟩ := exists_sqrtTwo_level L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (by nlinarith [Real.add_one_le_exp (1 : ℝ)]) hL
  exact ⟨k, hle, exp_neg_two_pow_le_exp_neg_log_sq hb hL1 hlt⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
