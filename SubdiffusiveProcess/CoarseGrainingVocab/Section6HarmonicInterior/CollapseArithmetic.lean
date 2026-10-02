import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletPrebalance




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open Homogenization Homogenization.Book

noncomputable section

/-- Subadditivity of the square root. -/
theorem sqrt_add_le_add_sqrt' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hx' := Real.sq_sqrt hx
    have hy' := Real.sq_sqrt hy
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y :=
      Real.sqrt_sq (by positivity)

/-- The negative half power is the inverse square root. -/
theorem rpow_neg_half_eq_inv_sqrt {s : ℝ} (hs : 0 ≤ s) :
    s ^ (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
  rw [Real.rpow_neg hs, Real.sqrt_eq_rpow]

/-- The dictionary: natural powers of `s^{-1/2}` are the half-integer powers
of `s`. -/
theorem rpow_neg_half_pow {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (s ^ (-(1 / 2 : ℝ))) ^ k = s ^ (-(k : ℝ) / 2) := by
  rw [← Real.rpow_natCast (s ^ (-(1 / 2 : ℝ))) k, ← Real.rpow_mul hs.le]
  congr 1
  ring

/-- On the frozen corridor `s ≤ 1/4` the reciprocal square root is at least
`2`, so higher powers of it dominate lower ones. -/
theorem two_le_rpow_neg_half {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) :
    (2 : ℝ) ≤ s ^ (-(1 / 2 : ℝ)) := by
  have hsqrt : Real.sqrt s ≤ 1 / 2 := by
    have hq : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    calc Real.sqrt s ≤ Real.sqrt (1 / 4 : ℝ) := Real.sqrt_le_sqrt hs4
      _ = 1 / 2 := hq
  have hspos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  rw [rpow_neg_half_eq_inv_sqrt hs.le]
  rw [le_inv_comm₀ (by norm_num) hspos]
  linarith

/-- Halving the fractional order costs at most a fixed factor in a negative
power. -/
theorem rpow_half_le_two_mul_rpow {s c : ℝ} (hs : 0 < s) {a : ℝ}
    (hc : (2 : ℝ) ^ (-a) ≤ c) :
    (s / 2) ^ a ≤ c * s ^ a := by
  have hsplit : (s / 2 : ℝ) ^ a = (2 : ℝ) ^ (-a) * s ^ a := by
    rw [Real.div_rpow hs.le (by norm_num), Real.rpow_neg (by norm_num)]
    field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hs.le _)

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 ≤ 3 :=
    le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h := Real.log_le_log (Real.exp_pos 1) hexp
  simpa using h

/-- The exact geometric partition factor of the weighted-energy slot at the
frozen pair `(s1, smid) = (s/3, s/2)` is bounded by `2 s^{-1/2}`. -/
theorem dirichletWeightedEnergyFactor_third_half_le {s : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) :
    Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) ≤
      2 * s ^ (-(1 / 2 : ℝ)) := by
  have hdisc : Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1 =
      1 - (3 : ℝ) ^ (-(s / 3)) := by
    unfold Ch02.geometricDiscount
    congr 2
    ring
  have hexp : (3 : ℝ) ^ (-(s / 3)) ≤ (1 + s / 3)⁻¹ := by
    have hpos : (0 : ℝ) < 1 + s / 3 := by linarith
    have hlog : (3 : ℝ) ^ (-(s / 3)) = Real.exp (-(s / 3 * Real.log 3)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    have hmono : Real.exp (-(s / 3 * Real.log 3)) ≤ Real.exp (-(s / 3)) := by
      apply Real.exp_le_exp.mpr
      have hle : s / 3 ≤ s / 3 * Real.log 3 := by
        nlinarith [one_le_log_three]
      linarith
    have hinv : Real.exp (-(s / 3)) ≤ (1 + s / 3)⁻¹ := by
      have hbase : 1 + s / 3 ≤ Real.exp (s / 3) := by
        have h := Real.add_one_le_exp (s / 3)
        linarith
      rw [Real.exp_neg]
      exact inv_anti₀ hpos hbase
    rw [hlog]
    exact hmono.trans hinv
  have hlower : (4 / 13 : ℝ) * s ≤
      Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1 := by
    rw [hdisc]
    have hpos : (0 : ℝ) < 1 + s / 3 := by linarith
    have hstep : (1 + s / 3)⁻¹ ≤ 1 - (4 / 13 : ℝ) * s := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    linarith
  have hdiscpos : (0 : ℝ) <
      Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1 := by
    have hq : (0 : ℝ) < 4 / 13 * s := by linarith
    linarith
  have hfactor :
      Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) =
      ((Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1)⁻¹) ^ (1 / 2 : ℝ) := by
    unfold Section6Dirichlet.dirichletWeightedEnergyFactor
    rw [ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) <
      (Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1)⁻¹ by positivity)]
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)
  rw [hfactor]
  have hinvle : (Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1)⁻¹ ≤
      (13 / 4 : ℝ) * s⁻¹ := by
    have h1 : ((4 / 13 : ℝ) * s)⁻¹ = (13 / 4 : ℝ) * s⁻¹ := by
      field_simp
    rw [← h1]
    exact inv_anti₀ (by linarith) hlower
  calc
    ((Ch02.geometricDiscount (2 * (s / 2 - s / 3)) 1)⁻¹) ^ (1 / 2 : ℝ) ≤
        ((13 / 4 : ℝ) * s⁻¹) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hinvle (by norm_num)
    _ = (13 / 4 : ℝ) ^ (1 / 2 : ℝ) * s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow hs.le,
        ← Real.rpow_neg hs.le]
    _ ≤ 2 * s ^ (-(1 / 2 : ℝ)) := by
      have hconst : (13 / 4 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        rw [← Real.sqrt_eq_rpow]
        have h4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
        calc Real.sqrt (13 / 4 : ℝ) ≤ Real.sqrt (4 : ℝ) :=
              Real.sqrt_le_sqrt (by norm_num)
          _ = 2 := h4
      exact mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hs.le _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
