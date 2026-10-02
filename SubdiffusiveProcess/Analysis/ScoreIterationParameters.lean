import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption

/-! Block contraction and exponential costs for finite score iterations.
These scalar statements do not assert any coefficient or probability estimate. -/
open Set
noncomputable section
namespace SubdiffusiveProcess

/-- A block of at least six steps makes the pure excess contraction strictly small. -/
theorem exists_score_iteration_block (A : ℝ) :
    ∃ k : ℕ, 6 ≤ k ∧
      let theta := (3:ℝ)^(-(1/4:ℝ))
      theta ∈ Ioo (0:ℝ) 1 ∧ theta^k ∈ Ioo (0:ℝ) (3/5) ∧
      A*(3:ℝ)^(-(k:ℝ)/2) ≤ theta^k/2 := by
  let q := (3:ℝ)^(1/4:ℝ)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  obtain ⟨N,hN⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (2*A)).exists
  let k := max N 6
  have hk : 6 ≤ k := Nat.le_max_right _ _
  have hp : 2*A < q^k := hN.trans_le (pow_le_pow_right₀ hq.le (Nat.le_max_left _ _))
  let theta := (3:ℝ)^(-(1/4:ℝ))
  have ht0 : 0 < theta := by dsimp only [theta]; positivity
  have ht1 : theta < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hprod : q^k*(3:ℝ)^(-(k:ℝ)/2) = theta^k := by
    dsimp only [q,theta]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤3),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤3),
      ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  have hfour : theta^4 = (1/3:ℝ) := by
    dsimp only [theta]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    norm_num only [Nat.cast_ofNat, show (-(1/4:ℝ))*4 = -1 by norm_num,
      Real.rpow_neg_one]
  have hupper := pow_le_pow_of_le_one ht0.le ht1.le (show 4≤k by omega)
  rw [hfour] at hupper
  refine ⟨k,hk,⟨ht0,ht1⟩,⟨pow_pos ht0 k,by linarith only [hupper]⟩,?_⟩
  have hh := mul_le_mul_of_nonneg_right hp.le
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (-(k:ℝ)/2))
  rw [hprod] at hh
  linarith only [hh]

/-- After the block is fixed, a positive error cap absorbs its perturbative coefficient. -/
theorem exists_score_iteration_cap (A B p q : ℝ) (hB : 0 < B) (hq : 0 < q)
    (hp : A*p ≤ q/2) :
    ∃ eta : ℝ, eta ∈ Ioc (0:ℝ) 1 ∧ A*p+B*eta ≤ q := by
  refine ⟨min 1 (q/(2*B)),⟨lt_min zero_lt_one (by positivity),min_le_left _ _⟩,?_⟩
  have he := mul_le_mul_of_nonneg_left (min_le_right 1 (q/(2*B))) hB.le
  have hcancel : B*(q/(2*B)) = q/2 := by field_simp
  rw [hcancel] at he
  linarith only [hp,he]

end SubdiffusiveProcess
