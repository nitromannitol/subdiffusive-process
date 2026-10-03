module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ResponseWeighting

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The saturated square is controlled by the three separate square budgets.
No sign assumptions are needed. -/
theorem min_one_add_three_sq_le_three_sum_sq (a b c : ℝ) :
    min 1 (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hmin : min 1 (a + b + c) ^ 2 ≤ (a + b + c) ^ 2 := by
    by_cases h : a + b + c ≤ 1
    · rw [min_eq_right h]
    · rw [min_eq_left (le_of_not_ge h)]
      nlinarith [sq_nonneg (a + b + c - 1)]
  have hsum : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  exact hmin.trans hsum

/-- Abstract insertion of the three-term square estimate into the weighted
response bound. -/
theorem split_weighted_transport_budget
    {P Main C v a b c : ℝ} (hv : 0 ≤ v)
    (h : P ≤ Main + 12 * C ^ 2 * v * min 1 (a + b + c) ^ 2) :
    P ≤ Main + 36 * C ^ 2 * v * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hcoef : 0 ≤ 12 * C ^ 2 * v :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) hv
  have hsplit := min_one_add_three_sq_le_three_sum_sq a b c
  have hmul := mul_le_mul_of_nonneg_left hsplit hcoef
  calc
    P ≤ Main + 12 * C ^ 2 * v * min 1 (a + b + c) ^ 2 := h
    _ ≤ Main + 12 * C ^ 2 * v *
        (3 * (a ^ 2 + b ^ 2 + c ^ 2)) := add_le_add le_rfl hmul
    _ = Main + 36 * C ^ 2 * v * (a ^ 2 + b ^ 2 + c ^ 2) := by ring

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact Real.exp_one_lt_d9.le.trans (by norm_num)

/-- A uniform pointwise bound for the quadratic triadic decay kernel. -/
theorem three_rpow_neg_mul_sq_le_two {x : ℝ} (hx : 0 ≤ x) :
    (3 : ℝ) ^ (-x) * x ^ 2 ≤ 2 := by
  have hpoly := Real.pow_div_factorial_le_exp x hx 2
  norm_num [Nat.factorial] at hpoly
  have hsq : x ^ 2 ≤ 2 * Real.exp x := by linarith only [hpoly]
  have hdecay : (3 : ℝ) ^ (-x) ≤ Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right one_le_log_three hx
    nlinarith only [hmul]
  calc
    (3 : ℝ) ^ (-x) * x ^ 2 ≤ Real.exp (-x) * x ^ 2 :=
      mul_le_mul_of_nonneg_right hdecay (sq_nonneg x)
    _ ≤ Real.exp (-x) * (2 * Real.exp x) :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = 2 * (Real.exp (-x) * Real.exp x) := by ring
    _ = 2 := by rw [← Real.exp_add]; norm_num

/-- Rescaled form of the quadratic decay estimate.  It is the pointwise
version of the manuscript's `sup_t` bound before inserting the model estimate
on `tauSq`. -/
theorem three_rpow_neg_mul_drift_sq_le
    {s t tau : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    (3 : ℝ) ^ (-(s * t)) * (tau * t) ^ 2 ≤
      2 * (s⁻¹) ^ 2 * tau ^ 2 := by
  have hx : 0 ≤ s * t := mul_nonneg hs.le ht
  have hcore := three_rpow_neg_mul_sq_le_two hx
  have hscale : tau * t = (tau * s⁻¹) * (s * t) := by
    field_simp [hs.ne']
  calc
    (3 : ℝ) ^ (-(s * t)) * (tau * t) ^ 2 =
        (tau * s⁻¹) ^ 2 *
          ((3 : ℝ) ^ (-(s * t)) * (s * t) ^ 2) := by
      rw [hscale]
      ring
    _ ≤ (tau * s⁻¹) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hcore (sq_nonneg _)
    _ = 2 * (s⁻¹) ^ 2 * tau ^ 2 := by ring

/-- The manuscript's deterministic drift collapse with an explicit universal
constant.  Since it holds for every nonnegative `t`, it supplies the printed
supremum bound. -/
theorem three_rpow_neg_mul_tauSq_sq_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s t : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (ht : 0 ≤ t) :
    (3 : ℝ) ^ (-(s * t)) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * t) ^ 2 ≤
      2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by
  have hs : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hlog : Real.log 2 / 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ M.delta ^ 2 :=
    (tauSq_le_delta_sq M).trans <| by
      exact mul_le_of_le_one_left (sq_nonneg M.delta) hlog
  have htauSq : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ^ 2 ≤
      (M.delta ^ 2) ^ 2 :=
    pow_le_pow_left₀ M.G4.tauSq_pos.le htau 2
  calc
    (3 : ℝ) ^ (-(s * t)) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * t) ^ 2 ≤
      2 * (s⁻¹) ^ 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ^ 2 :=
        three_rpow_neg_mul_drift_sq_le hs ht
    _ ≤ 2 * (s⁻¹) ^ 2 * (M.delta ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left htauSq
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = 2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by ring

/-- Literal supremum form of the manuscript's deterministic drift display. -/
theorem sSup_three_rpow_neg_mul_tauSq_sq_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) :
    sSup {y : ℝ | ∃ t : ℝ, 0 ≤ t ∧
      y = (3 : ℝ) ^ (-(s * t)) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * t) ^ 2} ≤
      2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by
  apply csSup_le
  · exact ⟨0, 0, le_rfl, by norm_num⟩
  · rintro y ⟨t, ht, rfl⟩
    exact three_rpow_neg_mul_tauSq_sq_le M hsLower ht

/-- The weighted local response after splitting the field, shell, and drift
budgets and collapsing the deterministic drift uniformly in the scale gap. -/
theorem weightedPaperScalarProbe_tailAverage_le_split_of_goodEvent_descendant
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (hBdd : BddAbove {a : ℝ | ∃ y ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i y|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i y - omega i 0|) else 1|}) :
    (3 : ℝ) ^ (-(3 / 2) *
          (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        36 * ratioCollapseConstant d ^ 2 *
          ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              longRatioGradientTail m omega ^ 2 +
            (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              supNormOn (cube d n)
                (shellBlock m n
                  (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 +
            2 * (s⁻¹) ^ 2 * M.delta ^ 4) := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let C : ℝ := ratioCollapseConstant d
  let v : ℝ := (3 : ℝ) ^ (-(s * T))
  let S : ℝ := longRatioGradientTail m omega
  let G : ℝ := supNormOn (cube d n)
    (shellBlock m n
      (translatePotentialSample (triadicCubeShift R) omega))
  let D : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * T
  let Main : ℝ := 2 * v *
    section6Response M n n omega (triadicCubeShift R) e
  let Pweighted : ℝ := (3 : ℝ) ^ (-(3 / 2) * (s * T)) *
    paperScalarProbe (originCube d (n : ℤ))
      (aCutoffFamily M L
        (translatePotentialSample (triadicCubeShift R) omega))
      (tailCoefficientCubeAverage M L m omega) e
  have hraw : Pweighted ≤ Main + 12 * C ^ 2 * v * min 1 (S + G + D) ^ 2 := by
    simpa only [Pweighted, Main, C, v, S, G, D, T] using
      weightedPaperScalarProbe_tailAverage_le_of_goodEvent_descendant
        M hnm hmL hsLower hsUpper hj hnj omega hR hann he hgood hBdd
  have hv : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
  have hsplit : Pweighted ≤
      Main + 36 * C ^ 2 * v * (S ^ 2 + G ^ 2 + D ^ 2) :=
    split_weighted_transport_budget hv hraw
  have hdrift : v * D ^ 2 ≤ 2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by
    simpa only [v, D, T] using
      three_rpow_neg_mul_tauSq_sq_le M hsLower (t := T) (by positivity)
  have hbudget : v * (S ^ 2 + G ^ 2 + D ^ 2) ≤
      v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4 := by
    calc
      v * (S ^ 2 + G ^ 2 + D ^ 2) =
          v * S ^ 2 + v * G ^ 2 + v * D ^ 2 := by ring
      _ ≤ v * S ^ 2 + v * G ^ 2 +
          2 * (s⁻¹) ^ 2 * M.delta ^ 4 := add_le_add le_rfl hdrift
  have hscaled : 36 * C ^ 2 * (v * (S ^ 2 + G ^ 2 + D ^ 2)) ≤
      36 * C ^ 2 *
        (v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4) :=
    mul_le_mul_of_nonneg_left hbudget
      (mul_nonneg (by norm_num) (sq_nonneg C))
  have hfinal : Pweighted ≤ Main + 36 * C ^ 2 *
      (v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4) := by
    calc
      Pweighted ≤ Main + 36 * C ^ 2 * v * (S ^ 2 + G ^ 2 + D ^ 2) := hsplit
      _ = Main + 36 * C ^ 2 * (v * (S ^ 2 + G ^ 2 + D ^ 2)) := by ring
      _ ≤ Main + 36 * C ^ 2 *
          (v * S ^ 2 + v * G ^ 2 + 2 * (s⁻¹) ^ 2 * M.delta ^ 4) :=
        add_le_add le_rfl hscaled
  simpa only [Pweighted, Main, C, v, S, G, T] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
