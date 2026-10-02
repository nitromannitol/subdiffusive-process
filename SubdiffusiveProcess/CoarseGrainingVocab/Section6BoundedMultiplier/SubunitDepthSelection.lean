import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitRadiusAbsorption

/-!
# Selecting the below-scale contraction depth

This file isolates the elementary triadic choice needed after the adaptive
small-contrast radius has been selected.  A target radius below the first
available local radius fits at some triadic depth, and the corresponding
Schauder decay is bounded directly by the square root of the target-to-local
radius ratio.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

/-- If a target radius fits below the first local triadic ball, select a
depth whose ball still contains the target.  The second row records the
quantitative price of that choice for the exponent-one-half contraction. -/
theorem exists_subunitContractionDepth
    {d : ℕ} [NeZero d] {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hrFirst : r ≤ R / (12 * (d : ℝ))) :
    ∃ n : ℕ,
      r ≤ (R / 2) / (2 * (d : ℝ)) *
          (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) ∧
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ≤
        Real.sqrt (36 * (d : ℝ) * r / R) := by
  have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  let A := R / (12 * (d : ℝ))
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hx0 : 0 < r / A := div_pos hr hA
  have hx1 : r / A ≤ 1 := (div_le_one hA).2 hrFirst
  obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near_of_lt_one
    hx0 hx1 (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨n, ?_, ?_⟩
  · have hfit : r ≤ A * (1 / 3 : ℝ) ^ n := by
      simpa only [mul_comm] using (div_le_iff₀ hA).1 hnhigh
    have hformula :
        A * (1 / 3 : ℝ) ^ n =
          (R / 2) / (2 * (d : ℝ)) *
            (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_natCast, pow_succ]
      dsimp only [A]
      field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)]
      calc
        3 * (1 / 3 : ℝ) ^ n * 2 ^ 2 * 3 ^ n =
            12 * ((1 / 3 : ℝ) ^ n * 3 ^ n) := by ring
        _ = 12 * ((1 / 3 : ℝ) * 3) ^ n := by rw [mul_pow]
        _ = 12 := by norm_num
    rwa [hformula] at hfit
  · have hpowLt : (1 / 3 : ℝ) ^ n < 3 * (r / A) := by
      have hstep : (1 / 3 : ℝ) ^ n / 3 < r / A := by
        simpa [pow_succ, mul_comm, div_eq_mul_inv] using hnlow
      linarith
    have hpowLe : (1 / 3 : ℝ) ^ n ≤ 3 * (r / A) := hpowLt.le
    have hsqrt := Real.sqrt_le_sqrt hpowLe
    have hleft : Real.sqrt ((1 / 3 : ℝ) ^ n) =
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    have hright : 3 * (r / A) = 36 * (d : ℝ) * r / R := by
      dsimp only [A]
      field_simp
      ring
    rwa [hleft, hright] at hsqrt

/-- Deep below-scale targets can be fed directly to the geometric local
readout at a selected depth.  The final row is the only numerical fact about
that depth needed by the subsequent constant absorption. -/
theorem exists_middleHalfSubcube_selectedSubunitDepth_caccioppoli
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (j : ℕ)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube m z j B')
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    (hfirst : 1 / 2 * (3 : ℝ) ^ (m - j) ≤
      boundedMultiplierLocalRadius M L m z omega /
        (12 * (d : ℝ))) :
    ∃ n : ℕ, ∃ z' : Vec d, ∃ p ∈ shellCoverShifts d m,
      B' = translatedCube d (m - j) z' ∧
      B' ⊆ Metric.ball z'
        ((boundedMultiplierLocalRadius M L m z omega / 2) /
            (2 * (d : ℝ)) *
              (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) ∧
      z' ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall z' (boundedMultiplierLocalRadius M L m z omega) ⊆
        boundedMultiplierCoverCell d m z p ∧
      oscillationOn
          (Metric.ball z'
            ((boundedMultiplierLocalRadius M L m z omega / 2) /
              (2 * (d : ℝ)) *
                (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))))
          (euclideanBallAverageRepresentative h.toFun) ≤
        smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d z'
              (boundedMultiplierLocalRadius M L m z omega) h.toFun
              (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) *
          (boundedMultiplierLocalRadius M L m z omega / 2) *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ∧
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ≤
        Real.sqrt
          (36 * (d : ℝ) * (1 / 2 * (3 : ℝ) ^ (m - j)) /
            boundedMultiplierLocalRadius M L m z omega) := by
  have hR := boundedMultiplierLocalRadius_pos M L m z omega
  have hr : 0 < 1 / 2 * (3 : ℝ) ^ (m - j) := by positivity
  obtain ⟨n, hfit, hdecay⟩ :=
    exists_subunitContractionDepth hR hr hfirst
  obtain ⟨z', p, hp, hB'eq, hsub, hz'cell, hballCell, hcontract⟩ :=
    exists_middleHalfSubcube_localSubunitBall_caccioppoli
      hd M L m z j n hB' omega hthetaCont hb hthetaClose hharm hfit
  exact ⟨n, z', p, hp, hB'eq, hsub, hz'cell, hballCell, hcontract, hdecay⟩

/-- If the first local triadic ball is still smaller than a depth-`k`
target, then `k` is bounded by the square-root radius delay.  This is the
precise shallow branch complementary to `exists_subunitContractionDepth`. -/
theorem three_rpow_depth_lt_of_firstSubunitBall_lt
    {d : ℕ} [NeZero d] {m : ℤ} (hm : 0 < m)
    {R : ℝ} (hR : boundedMultiplierRadiusFloor d /
      (Real.sqrt (m : ℝ) + 1) ≤ R)
    {k : ℕ}
    (hshallow : R / (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (-(k : ℝ))) :
    (3 : ℝ) ^ (k : ℝ) <
      (6 * (d : ℝ) / boundedMultiplierRadiusFloor d) *
        (Real.sqrt (m : ℝ) + 1) := by
  have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hfloor := boundedMultiplierRadiusFloor_pos d
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast hm.le
  have hS : 0 < Real.sqrt (m : ℝ) + 1 := by
    linarith [Real.sqrt_nonneg (m : ℝ)]
  have hden : 0 < 12 * (d : ℝ) := mul_pos (by norm_num) hd
  have hlower : boundedMultiplierRadiusFloor d /
        (Real.sqrt (m : ℝ) + 1) / (12 * (d : ℝ)) ≤
      R / (12 * (d : ℝ)) :=
    div_le_div_of_nonneg_right hR hden.le
  have hstrict : boundedMultiplierRadiusFloor d /
        (Real.sqrt (m : ℝ) + 1) / (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (-(k : ℝ)) := hlower.trans_lt hshallow
  have hpow : 0 < (3 : ℝ) ^ (k : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)] at hstrict
  rw [div_lt_iff₀ hden, div_lt_iff₀ hS] at hstrict
  rw [show (1 / 2 : ℝ) * ((3 : ℝ) ^ (k : ℝ))⁻¹ *
      (12 * (d : ℝ)) * (Real.sqrt (m : ℝ) + 1) =
        6 * (d : ℝ) * (Real.sqrt (m : ℝ) + 1) /
          (3 : ℝ) ^ (k : ℝ) by ring] at hstrict
  rw [lt_div_iff₀ hpow] at hstrict
  calc
    (3 : ℝ) ^ (k : ℝ) <
        6 * (d : ℝ) * (Real.sqrt (m : ℝ) + 1) /
          boundedMultiplierRadiusFloor d := by
      exact (lt_div_iff₀ hfloor).2 (by simpa only [mul_comm] using hstrict)
    _ = (6 * (d : ℝ) / boundedMultiplierRadiusFloor d) *
        (Real.sqrt (m : ℝ) + 1) := by ring

/-- The entire shallow-depth loss is paid by an arbitrarily prescribed
positive reserve in the parent-scale exponent.  The multiplicative price is
dimension-only once the reserve is fixed. -/
theorem shallow_subunit_depth_loss_lt_exponentReserve
    {d : ℕ} [NeZero d] {m : ℤ} (hm : 0 < m)
    {R : ℝ} (hR : boundedMultiplierRadiusFloor d /
      (Real.sqrt (m : ℝ) + 1) ≤ R)
    {k : ℕ}
    (hshallow : R / (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (-(k : ℝ)))
    {c reserve : ℝ} (hcOne : c ≤ 1)
    (hreserve : 0 < reserve)
    (hreserveLog : reserve * Real.log 3 ≤ 1) :
    (3 : ℝ) ^ (c * (k : ℝ)) <
      (6 * (d : ℝ) / boundedMultiplierRadiusFloor d) *
        (reserve * Real.log 3)⁻¹ *
          (3 : ℝ) ^ (reserve * (m : ℝ)) := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hck : c * (k : ℝ) ≤ (k : ℝ) := by nlinarith
  have hpowC : (3 : ℝ) ^ (c * (k : ℝ)) ≤
      (3 : ℝ) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hck
  have hdepth := three_rpow_depth_lt_of_firstSubunitBall_lt
    (d := d) hm hR hshallow
  have hmOne : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hreserveBound := sqrt_add_one_le_inv_mul_three_rpow
    hmOne hreserve hreserveLog
  have hA : 0 < 6 * (d : ℝ) / boundedMultiplierRadiusFloor d := by
    have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
    exact div_pos (mul_pos (by norm_num) hd)
      (boundedMultiplierRadiusFloor_pos d)
  calc
    (3 : ℝ) ^ (c * (k : ℝ)) ≤ (3 : ℝ) ^ (k : ℝ) := hpowC
    _ < (6 * (d : ℝ) / boundedMultiplierRadiusFloor d) *
        (Real.sqrt (m : ℝ) + 1) := hdepth
    _ ≤ (6 * (d : ℝ) / boundedMultiplierRadiusFloor d) *
        ((reserve * Real.log 3)⁻¹ *
          (3 : ℝ) ^ (reserve * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hreserveBound hA.le
    _ = (6 * (d : ℝ) / boundedMultiplierRadiusFloor d) *
        (reserve * Real.log 3)⁻¹ *
          (3 : ℝ) ^ (reserve * (m : ℝ)) := by ring

/-- For a negative parent scale, failure to fit inside the first local ball
can occur only at a dimension-only bounded depth.  The ambient factor `3^m`
cancels exactly. -/
theorem three_pow_depth_lt_of_negativeFirstSubunitBall_lt
    {d : ℕ} [NeZero d] {m : ℤ}
    {R : ℝ} (hR : boundedMultiplierNegativeRadiusFloor d *
      (3 : ℝ) ^ m ≤ R)
    {j : ℕ}
    (hshallow : R / (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (m - (j : ℤ))) :
    (3 : ℝ) ^ j <
      6 * (d : ℝ) / boundedMultiplierNegativeRadiusFloor d := by
  have hdNat : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hfloor := boundedMultiplierNegativeRadiusFloor_pos d
  have hA : 0 < (3 : ℝ) ^ m := by positivity
  have hP : 0 < (3 : ℝ) ^ j := by positivity
  have hden : 0 < 12 * (d : ℝ) := mul_pos (by norm_num) hd
  have hlower : boundedMultiplierNegativeRadiusFloor d * (3 : ℝ) ^ m /
        (12 * (d : ℝ)) ≤ R / (12 * (d : ℝ)) :=
    div_le_div_of_nonneg_right hR hden.le
  have hstrict : boundedMultiplierNegativeRadiusFloor d * (3 : ℝ) ^ m /
        (12 * (d : ℝ)) <
      1 / 2 * (3 : ℝ) ^ (m - (j : ℤ)) := hlower.trans_lt hshallow
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast] at hstrict
  have hscaled : boundedMultiplierNegativeRadiusFloor d <
      6 * (d : ℝ) / (3 : ℝ) ^ j := by
    have hscalePos : 0 < (12 * (d : ℝ)) / (3 : ℝ) ^ m := by
      exact div_pos (mul_pos (by norm_num) hd) hA
    have hmul := mul_lt_mul_of_pos_right hstrict hscalePos
    convert hmul using 1 <;>
      (field_simp [hd.ne', hA.ne', hP.ne'] <;> ring)
  have hcross : boundedMultiplierNegativeRadiusFloor d * (3 : ℝ) ^ j <
      6 * (d : ℝ) := (lt_div_iff₀ hP).1 hscaled
  exact (lt_div_iff₀ hfloor).2 (by simpa only [mul_comm] using hcross)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
