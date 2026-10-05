module

public import SubdiffusiveProcess.CoarseGrainingVocab.Concentration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneScore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialSequenceArithmetic

@[expose] public section

/-!
# Density adapter for the first shell-field event

This file completes the numerical normalization and literal-event reduction
for the one-shell score array from `FieldOneScore`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
  Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem one_sub_fieldOneGeometricBase_ge {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s / 2 ≤ 1 - fieldOneGeometricBase s := by
  have hq := SubdiffusiveProcess.Concentration.three_rpow_neg_le hs hs1
  have hden : 0 < 3 + s := by linarith
  unfold fieldOneGeometricBase
  have hqmul := (le_div_iff₀ hden).mp hq
  nlinarith

theorem tsum_fieldOneGeometricBase_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∑' q : ℕ, fieldOneGeometricBase s ^ q) ≤ 2 / s := by
  have hq0 := fieldOneGeometricBase_nonneg s
  have hq1 := fieldOneGeometricBase_lt_one hs
  have hnorm : ‖fieldOneGeometricBase s‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  have hgap := one_sub_fieldOneGeometricBase_ge hs hs1
  rw [show (1 - fieldOneGeometricBase s)⁻¹ =
      1 / (1 - fieldOneGeometricBase s) by
        exact (one_div _).symm]
  rw [div_le_div_iff₀ (sub_pos.mpr hq1) hs]
  nlinarith

theorem tsum_fieldOneGeometricBase_mul_succ_le
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∑' q : ℕ, fieldOneGeometricBase s ^ q * ((q : ℝ) + 1)) ≤
      6 / s ^ 2 := by
  let Q := fieldOneGeometricBase s
  have hQ0 : 0 ≤ Q := fieldOneGeometricBase_nonneg s
  have hQ1 : Q < 1 := fieldOneGeometricBase_lt_one hs
  have hnorm : ‖Q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hQ0]
  have hsumq : (∑' q : ℕ, (q : ℝ) * Q ^ q) = Q / (1 - Q) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsum1 : (∑' q : ℕ, Q ^ q) = (1 - Q)⁻¹ :=
    tsum_geometric_of_norm_lt_one hnorm
  have hsummableQ : Summable fun q : ℕ => Q ^ q :=
    summable_geometric_of_norm_lt_one hnorm
  have hsummableNQ : Summable fun q : ℕ => (q : ℝ) * Q ^ q :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  change (∑' q : ℕ, Q ^ q * ((q : ℝ) + 1)) ≤ _
  rw [show (fun q : ℕ => Q ^ q * ((q : ℝ) + 1)) =
      fun q : ℕ => (q : ℝ) * Q ^ q + Q ^ q by
    funext q
    ring]
  rw [hsummableNQ.tsum_add hsummableQ, hsumq, hsum1]
  have hgap := one_sub_fieldOneGeometricBase_ge hs hs1
  have hgap0 : 0 < 1 - Q := sub_pos.mpr hQ1
  have hQle : Q ≤ 1 := hQ1.le
  have hfirst : Q / (1 - Q) ^ 2 ≤ 1 / (s / 2) ^ 2 := by
    apply div_le_div₀ (by norm_num) hQle (sq_pos_of_pos (by positivity))
    exact pow_le_pow_left₀ (by positivity) hgap 2
  have hsecond : (1 - Q)⁻¹ ≤ 2 / s := by
    rw [← one_div]
    rw [div_le_div_iff₀ hgap0 hs]
    nlinarith
  have hs2 : s ^ 2 ≤ s := by nlinarith [sq_nonneg s]
  calc
    Q / (1 - Q) ^ 2 + (1 - Q)⁻¹ ≤ 1 / (s / 2) ^ 2 + 2 / s :=
      add_le_add hfirst hsecond
    _ ≤ 6 / s ^ 2 := by
      field_simp [hs.ne']
      nlinarith

theorem sqrt_natSucc_le_sqrt_mul_add_inv {s : ℝ} (hs : 0 < s) (q : ℕ) :
    Real.sqrt ((q : ℝ) + 1) ≤
      Real.sqrt s * ((q : ℝ) + 1) + (Real.sqrt s)⁻¹ := by
  let a := Real.sqrt ((q : ℝ) + 1)
  let b := Real.sqrt s
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 < b := Real.sqrt_pos.2 hs
  have haa : a ^ 2 = (q : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hbb : b ^ 2 = s := Real.sq_sqrt hs.le
  rw [← mul_le_mul_iff_left₀ hb]
  have hsq := sq_nonneg (a * b - 1 / 2)
  dsimp only [a, b] at haa hbb ⊢
  field_simp [hb.ne'] at hsq ⊢
  nlinarith

theorem tsum_fieldOneGeometricBase_mul_sqrt_le
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∑' q : ℕ, fieldOneGeometricBase s ^ q *
        Real.sqrt ((q : ℝ) + 1)) ≤
      8 * (Real.sqrt s)⁻¹ * s⁻¹ := by
  let Q := fieldOneGeometricBase s
  have hQ0 : 0 ≤ Q := fieldOneGeometricBase_nonneg s
  have hQ1 : Q < 1 := fieldOneGeometricBase_lt_one hs
  have hnorm : ‖Q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hQ0]
  have hsumSqrt : Summable fun q : ℕ =>
      Q ^ q * Real.sqrt ((q : ℝ) + 1) :=
    summable_geom_mul_sqrt hQ0 hQ1
  have hsumSucc : Summable fun q : ℕ => Q ^ q * ((q : ℝ) + 1) := by
    have hNQ : Summable fun q : ℕ => (q : ℝ) * Q ^ q :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hsumQ : Summable fun q : ℕ => Q ^ q :=
      summable_geometric_of_norm_lt_one hnorm
    convert hNQ.add hsumQ using 1
    ext q
    ring_nf
  have hsumQ : Summable fun q : ℕ => Q ^ q :=
    summable_geometric_of_norm_lt_one hnorm
  let U : ℕ → ℝ := fun q => Q ^ q *
    (Real.sqrt s * ((q : ℝ) + 1) + (Real.sqrt s)⁻¹)
  have hsumU : Summable U := by
    unfold U
    convert (hsumSucc.mul_left (Real.sqrt s)).add
      (hsumQ.mul_left (Real.sqrt s)⁻¹) using 1
    ext q
    ring
  have hpoint : ∀ q : ℕ, Q ^ q * Real.sqrt ((q : ℝ) + 1) ≤ U q := by
    intro q
    exact mul_le_mul_of_nonneg_left (sqrt_natSucc_le_sqrt_mul_add_inv hs q)
      (pow_nonneg hQ0 q)
  have hsum := hsumSqrt.tsum_le_tsum hpoint hsumU
  have hsumUEq : (∑' q, U q) =
      Real.sqrt s * (∑' q : ℕ, Q ^ q * ((q : ℝ) + 1)) +
        (Real.sqrt s)⁻¹ * (∑' q : ℕ, Q ^ q) := by
    unfold U
    rw [show (fun q : ℕ => Q ^ q *
        (Real.sqrt s * ((q : ℝ) + 1) + (Real.sqrt s)⁻¹)) =
      fun q : ℕ => Real.sqrt s * (Q ^ q * ((q : ℝ) + 1)) +
        (Real.sqrt s)⁻¹ * Q ^ q by
      funext q
      ring]
    rw [(hsumSucc.mul_left _).tsum_add (hsumQ.mul_left _),
      hsumSucc.tsum_mul_left, hsumQ.tsum_mul_left]
  rw [hsumUEq] at hsum
  have hsucc := tsum_fieldOneGeometricBase_mul_succ_le hs hs1
  have hgeom := tsum_fieldOneGeometricBase_le hs hs1
  change (∑' q : ℕ, Q ^ q * Real.sqrt ((q : ℝ) + 1)) ≤ _
  have hsqrt0 := Real.sqrt_nonneg s
  have hinv0 : 0 ≤ (Real.sqrt s)⁻¹ := inv_nonneg.mpr hsqrt0
  have hbound := hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (by simpa only [Q] using hsucc) hsqrt0)
    (mul_le_mul_of_nonneg_left (by simpa only [Q] using hgeom) hinv0))
  calc
    _ ≤ Real.sqrt s * (6 / s ^ 2) + (Real.sqrt s)⁻¹ * (2 / s) := hbound
    _ = 8 * (Real.sqrt s)⁻¹ * s⁻¹ := by
      have hroot := Real.sq_sqrt hs.le
      field_simp [hs.ne', (Real.sqrt_pos.2 hs).ne']
      nlinarith

theorem sqrt_le_exp_half (x : ℝ) (_hx : 0 ≤ x) :
    Real.sqrt x ≤ Real.exp (x / 2) := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact (Real.exp_pos _).le
  · calc
      x ≤ x + 1 := by linarith
      _ ≤ Real.exp x := Real.add_one_le_exp x
      _ = Real.exp (x / 2) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring

theorem fieldOne_outer_decay_sqrt_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (n : ℕ) :
    (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) *
        Real.sqrt ((2 * n : ℕ) + 1) ≤ 4 * s ^ (-(1 / 2 : ℝ)) := by
  have hlog : 1 ≤ Real.log 3 := (SubdiffusiveProcess.Concentration.log_three_gt_one).le
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrpow : (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) ≤
      Real.exp (-(s * (n : ℝ)) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hs.le hn]
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsqrtSplit : Real.sqrt (((2 * n : ℕ) : ℝ) + 1) ≤
      Real.sqrt 2 * Real.sqrt ((n : ℝ) + 1) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith
  have hx : 0 ≤ s * ((n : ℝ) + 1) := by positivity
  have hsqrtProd : Real.sqrt (s * ((n : ℝ) + 1)) =
      Real.sqrt s * Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.sqrt_mul hs.le]
  have hroot := sqrt_le_exp_half (s * ((n : ℝ) + 1)) hx
  rw [hsqrtProd] at hroot
  have hsqrtS : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hmain : Real.exp (-(s * (n : ℝ)) / 2) *
      Real.sqrt ((n : ℝ) + 1) ≤ 2 / Real.sqrt s := by
    rw [le_div_iff₀ hsqrtS]
    calc
      Real.exp (-(s * (n : ℝ)) / 2) * Real.sqrt ((n : ℝ) + 1) *
          Real.sqrt s =
          Real.exp (-(s * (n : ℝ)) / 2) *
            (Real.sqrt s * Real.sqrt ((n : ℝ) + 1)) := by ring
      _ ≤ Real.exp (-(s * (n : ℝ)) / 2) *
            Real.exp (s * ((n : ℝ) + 1) / 2) :=
        mul_le_mul_of_nonneg_left hroot (Real.exp_pos _).le
      _ = Real.exp (s / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
      _ ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.2 (by nlinarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  calc
    (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) * Real.sqrt ((2 * n : ℕ) + 1) ≤
        Real.exp (-(s * (n : ℝ)) / 2) *
          (Real.sqrt 2 * Real.sqrt ((n : ℝ) + 1)) := by gcongr
    _ ≤ 4 / Real.sqrt s := by
      calc
        _ = Real.sqrt 2 *
            (Real.exp (-(s * (n : ℝ)) / 2) * Real.sqrt ((n : ℝ) + 1)) := by ring
        _ ≤ Real.sqrt 2 * (2 / Real.sqrt s) :=
          mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg _)
        _ ≤ 4 / Real.sqrt s := by
          rw [show Real.sqrt 2 * (2 / Real.sqrt s) =
              (2 * Real.sqrt 2) / Real.sqrt s by ring]
          exact div_le_div_of_nonneg_right (by nlinarith) hsqrtS.le
    _ = 4 * s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hs.le, show s ^ (1 / 2 : ℝ) = Real.sqrt s by
        rw [Real.sqrt_eq_rpow]]
      ring

/-- Uniform version of the manuscript's score-scale summation.  The slightly
weaker `s⁻²` bound is sufficient for the source `s⁶` density rate because the
chosen fifth-power moment leaves one spare factor of `s`. -/
theorem tsum_fieldOneScoreTermScale_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hK : 0 < K) (m i : ℕ) :
    (∑' q : ℕ, fieldOneScoreTermScale M s K m i q) ≤
      16 * K * fieldOneGammaDimScale M * (Real.sqrt s)⁻¹ * s⁻¹ := by
  let n := fieldOneIndexDistance m i
  let Q := fieldOneGeometricBase s
  let B := K * (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) * fieldOneGammaDimScale M
  have hQ0 : 0 ≤ Q := fieldOneGeometricBase_nonneg s
  have hQ1 : Q < 1 := fieldOneGeometricBase_lt_one hs
  have hnorm : ‖Q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hQ0]
  have hsumQ : Summable fun q : ℕ => Q ^ q :=
    summable_geometric_of_norm_lt_one hnorm
  have hsumSqrt : Summable fun q : ℕ =>
      Q ^ q * Real.sqrt ((q : ℝ) + 1) :=
    summable_geom_mul_sqrt hQ0 hQ1
  have hsumUpper : Summable fun q : ℕ =>
      B * (Q ^ q * (Real.sqrt ((2 * n : ℕ) + 1) +
        Real.sqrt ((q : ℝ) + 1))) := by
    apply Summable.mul_left
    refine ((hsumQ.mul_left (Real.sqrt ((2 * n : ℕ) + 1))).add hsumSqrt).congr ?_
    intro q
    ring_nf
  have hscaleSummable := summable_fieldOneScoreTermScale M hs hK m i
  have hpoint : ∀ q : ℕ, fieldOneScoreTermScale M s K m i q ≤
      B * (Q ^ q * (Real.sqrt ((2 * n : ℕ) + 1) +
        Real.sqrt ((q : ℝ) + 1))) := by
    intro q
    calc
      fieldOneScoreTermScale M s K m i q ≤
          B * ((3 : ℝ) ^ (-(s * (q : ℝ))) *
            Real.sqrt ((2 * n + q : ℕ) + 1)) := by
        simpa only [B, n] using fieldOneScoreTermScale_le_sqrt M hK.le m i q
      _ ≤ B * (Q ^ q *
          (Real.sqrt ((2 * n : ℕ) + 1) + Real.sqrt ((q : ℝ) + 1))) := by
        have hsqrt : Real.sqrt (((2 * n : ℕ) : ℝ) + q + 1) ≤
            Real.sqrt (((2 * n : ℕ) : ℝ) + 1) + Real.sqrt (q : ℝ) := by
          have := sqrt_add_le
            (show 0 ≤ (((2 * n : ℕ) : ℝ) + 1) by positivity)
            (show 0 ≤ (q : ℝ) by positivity)
          convert this using 1
          all_goals push_cast
          all_goals ring_nf
        have hsqrtq : Real.sqrt (q : ℝ) ≤ Real.sqrt ((q : ℝ) + 1) :=
          Real.sqrt_le_sqrt (by linarith)
        rw [fieldOne_qWeight_eq_pow]
        have hD0 : 0 ≤ fieldOneGammaDimScale M := by
          unfold fieldOneGammaDimScale
          exact mul_nonneg
            (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
            (mul_nonneg (Real.rpow_nonneg (by
              have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
              linarith) _) M.shellPrefix.delta_pos.le)
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _)) hD0)
        have hmul := mul_le_mul_of_nonneg_left
          (hsqrt.trans (add_le_add (le_refl _) hsqrtq)) (pow_nonneg hQ0 q)
        dsimp only [Q] at hmul ⊢
        convert hmul using 1
        all_goals push_cast
        all_goals ring
  have htsum := hscaleSummable.tsum_le_tsum hpoint hsumUpper
  have hsumQle := tsum_fieldOneGeometricBase_le hs hs1
  have hsumSqrtLe := tsum_fieldOneGeometricBase_mul_sqrt_le hs hs1
  have hsumUpperEq :
      (∑' q : ℕ, B * (Q ^ q *
        (Real.sqrt ((2 * n : ℕ) + 1) + Real.sqrt ((q : ℝ) + 1)))) =
        B * (Real.sqrt ((2 * n : ℕ) + 1) * (∑' q : ℕ, Q ^ q) +
          ∑' q : ℕ, Q ^ q * Real.sqrt ((q : ℝ) + 1)) := by
    rw [tsum_mul_left]
    congr 1
    rw [show (fun q : ℕ => Q ^ q *
        (Real.sqrt ((2 * n : ℕ) + 1) + Real.sqrt ((q : ℝ) + 1))) =
      fun q : ℕ => Real.sqrt ((2 * n : ℕ) + 1) * Q ^ q +
        Q ^ q * Real.sqrt ((q : ℝ) + 1) by
      funext q
      ring]
    rw [(hsumQ.mul_left _).tsum_add hsumSqrt, hsumQ.tsum_mul_left]
  rw [hsumUpperEq] at htsum
  have hD0 : 0 ≤ fieldOneGammaDimScale M := by
    unfold fieldOneGammaDimScale
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.rpow_nonneg (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos.le)
  have hB0 : 0 ≤ B := by
    unfold B
    exact mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _)) hD0
  have hbracket : Real.sqrt ((2 * n : ℕ) + 1) * (∑' q : ℕ, Q ^ q) +
      (∑' q : ℕ, Q ^ q * Real.sqrt ((q : ℝ) + 1)) ≤
        Real.sqrt ((2 * n : ℕ) + 1) * (2 / s) +
          8 * (Real.sqrt s)⁻¹ * s⁻¹ := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left (by simpa only [Q] using hsumQle)
        (Real.sqrt_nonneg _))
      (by simpa only [Q] using hsumSqrtLe)
  have houter := fieldOne_outer_decay_sqrt_le hs hs1 n
  have houterOne : (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hs.le hn]
  have hterm1 : (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) *
      Real.sqrt ((2 * n : ℕ) + 1) * (2 / s) ≤
        8 * (Real.sqrt s)⁻¹ * s⁻¹ := by
    rw [div_eq_mul_inv]
    have hrpow : s ^ (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
      rw [Real.rpow_neg hs.le, Real.sqrt_eq_rpow]
    calc
      _ ≤ (4 * s ^ (-(1 / 2 : ℝ))) * (2 * s⁻¹) :=
        mul_le_mul_of_nonneg_right houter (by positivity)
      _ = 8 * (Real.sqrt s)⁻¹ * s⁻¹ := by rw [hrpow]; ring
  have hterm2 : (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) *
      (8 * (Real.sqrt s)⁻¹ * s⁻¹) ≤
      8 * (Real.sqrt s)⁻¹ * s⁻¹ := by
    have hsix : 0 ≤ 8 * (Real.sqrt s)⁻¹ * s⁻¹ := by positivity
    calc
      _ ≤ 1 * (8 * (Real.sqrt s)⁻¹ * s⁻¹) :=
        mul_le_mul_of_nonneg_right houterOne hsix
      _ = 8 * (Real.sqrt s)⁻¹ * s⁻¹ := one_mul _
  calc
    (∑' q : ℕ, fieldOneScoreTermScale M s K m i q) ≤
        B * (Real.sqrt ((2 * n : ℕ) + 1) * (2 / s) +
          8 * (Real.sqrt s)⁻¹ * s⁻¹) :=
      htsum.trans (mul_le_mul_of_nonneg_left hbracket hB0)
    _ ≤ 16 * K * fieldOneGammaDimScale M * (Real.sqrt s)⁻¹ * s⁻¹ := by
      unfold B
      calc
        K * (3 : ℝ) ^ (-(s * (n : ℝ)) / 2) * fieldOneGammaDimScale M *
            (Real.sqrt ((2 * n : ℕ) + 1) * (2 / s) +
              8 * (Real.sqrt s)⁻¹ * s⁻¹) =
            K * fieldOneGammaDimScale M *
              (((3 : ℝ) ^ (-(s * (n : ℝ)) / 2) *
                  Real.sqrt ((2 * n : ℕ) + 1) * (2 / s)) +
                ((3 : ℝ) ^ (-(s * (n : ℝ)) / 2) *
                  (8 * (Real.sqrt s)⁻¹ * s⁻¹))) := by ring
        _ ≤ K * fieldOneGammaDimScale M *
              (8 * (Real.sqrt s)⁻¹ * s⁻¹ +
                8 * (Real.sqrt s)⁻¹ * s⁻¹) :=
          mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2)
            (mul_nonneg hK.le hD0)
        _ ≤ 16 * K * fieldOneGammaDimScale M * (Real.sqrt s)⁻¹ * s⁻¹ := by
          have hinv0 : 0 ≤ (Real.sqrt s)⁻¹ * s⁻¹ := by positivity
          have hKD0 : 0 ≤ K * fieldOneGammaDimScale M := mul_nonneg hK.le hD0
          nlinarith

/-- Gamma-two moment normalization in the unsigned integral convention of
`concentration_for_scales`. -/
theorem lintegral_fieldOneScore_rpow_le_one {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K p : ℝ}
    (hs : 0 < s) (hK : 0 < K) (hp : 1 ≤ p) (m i : ℕ)
    (hnorm : gammaMomentConst 2 * Real.sqrt p *
        (gammaTriangleConst 2 *
          ∑' q : ℕ, fieldOneScoreTermScale M s K m i q) ≤ 1) :
    ∫⁻ omega, ENNReal.ofReal ((fieldOneScore s K m i omega) ^ p)
        ∂M.P.toMeasure ≤ 1 := by
  let A := gammaTriangleConst 2 *
    ∑' q : ℕ, fieldOneScoreTermScale M s K m i q
  have hA : 0 < A := by
    unfold A
    apply mul_pos (gammaTriangleConst_pos (σ := 2))
    exact (summable_fieldOneScoreTermScale M hs hK m i).tsum_pos (fun q => by
      unfold fieldOneScoreTermScale
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg (by norm_num) _))
        (fieldOneCubeMajorantScale_pos M i _).le) 0 (by
          unfold fieldOneScoreTermScale
          exact mul_pos
            (mul_pos (mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _))
              (Real.rpow_pos_of_pos (by norm_num) _))
            (fieldOneCubeMajorantScale_pos M i _))
  have hraw := lintegral_rpow_le_of_isBigOWith_gammaSigma
    (μ := M.P.toMeasure) (Y := fieldOneScore (d := d) s K m i)
    (K := A) (σ := 2) (p := p) (by norm_num) hA hp
    (fieldOneScore_nonneg s K m i)
    ((measurable_fieldOneScore_shellSigma s K m i).mono
      (shellSigma_le i) le_rfl).aemeasurable
    (by simpa only [A] using isBigOWith_gammaTwo_fieldOneScore M hs hK m i)
  refine hraw.trans ?_
  rw [ENNReal.ofReal_le_one]
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hbase : 0 ≤ gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ * A := by
    exact mul_nonneg
      (mul_nonneg (gammaMomentConst_pos (by norm_num)).le
        (Real.rpow_nonneg hp0.le _)) hA.le
  apply Real.rpow_le_one hbase
  · simpa only [A, Real.sqrt_eq_rpow, one_div] using hnorm
  · exact hp0.le

/-- The score-array moment certificate, with the inactive integer rows and
columns discharged definitionally. -/
theorem lintegral_fieldOneScoreArray_rpow_le_one {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K p : ℝ}
    (hs : 0 < s) (hK : 0 < K) (hp : 1 ≤ p)
    (hnorm : ∀ m i : ℕ, gammaMomentConst 2 * Real.sqrt p *
        (gammaTriangleConst 2 *
          ∑' q : ℕ, fieldOneScoreTermScale M s K m i q) ≤ 1) :
    ∀ m i : ℤ,
      ∫⁻ omega, ENNReal.ofReal ((fieldOneScoreArray (d := d) s K m i omega) ^ p)
        ∂M.P.toMeasure ≤ 1 := by
  intro m i
  unfold fieldOneScoreArray
  split_ifs with h
  · exact lintegral_fieldOneScore_rpow_le_one M hs hK hp m.toNat i.toNat
      (hnorm m.toNat i.toNat)
  · rw [Real.zero_rpow (zero_lt_one.trans_le hp).ne']
    simp



theorem ae_summable_fieldOneScoreArray_row {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {t K : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 < K) (m : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure, Summable fun i : ℤ =>
      SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) i *
        fieldOneScoreArray (d := d) t K (m : ℤ) i omega := by
  let U : ℝ := 1 + gammaTriangleConst 2 *
    (16 * K * fieldOneGammaDimScale M * (Real.sqrt t)⁻¹ * t⁻¹)
  have hD0 : 0 ≤ fieldOneGammaDimScale M := by
    unfold fieldOneGammaDimScale
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.rpow_nonneg (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos.le)
  have hU : 0 < U := by
    unfold U
    have hgamma := (gammaTriangleConst_pos (σ := 2)).le
    positivity
  let X : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun i omega =>
    SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (i : ℤ) *
      fieldOneScore t K m i omega
  let a : ℕ → ℝ := fun i =>
    SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (i : ℤ) * U
  have ha : ∀ i, 0 < a i := fun i =>
    mul_pos (SubdiffusiveProcess.Concentration.wt_pos _ _ _) hU
  have hasum : Summable a := by
    unfold a
    have hw := SubdiffusiveProcess.Concentration.summable_wt_half ht ht1 (m : ℤ)
    have hsub : Summable fun i : ℕ =>
        SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (i : ℤ) := by
      simpa only [Function.comp_apply] using!
        hw.comp_injective Int.ofNat_injective
    exact hsub.mul_right U
  have hXnn : ∀ i omega, 0 ≤ X i omega := fun i omega =>
    mul_nonneg (SubdiffusiveProcess.Concentration.wt_nonneg _ _ _)
      (fieldOneScore_nonneg t K m i omega)
  have hXmeas : ∀ i, AEMeasurable (X i) M.P.toMeasure := fun i =>
    (measurable_const.mul ((measurable_fieldOneScore_shellSigma t K m i).mono
      (shellSigma_le i) le_rfl)).aemeasurable
  have hXbig : ∀ i, IsBigOWith M.P.toMeasure (gammaSigma 2) (X i) (a i) := by
    intro i
    have hbase := (isBigOWith_gammaTwo_fieldOneScore M ht hK m i).const_mul
      (SubdiffusiveProcess.Concentration.wt_nonneg (t / 2) (m : ℤ) (i : ℤ))
    apply hbase.mono_scale
    apply mul_le_mul_of_nonneg_left _ (SubdiffusiveProcess.Concentration.wt_nonneg _ _ _)
    calc
      gammaTriangleConst 2 *
          (∑' q : ℕ, fieldOneScoreTermScale M t K m i q) ≤
          gammaTriangleConst 2 *
            (16 * K * fieldOneGammaDimScale M * (Real.sqrt t)⁻¹ * t⁻¹) :=
        mul_le_mul_of_nonneg_left
          (tsum_fieldOneScoreTermScale_le M ht ht1 hK m i)
          (gammaTriangleConst_pos (σ := 2)).le
      _ ≤ U := by unfold U; linarith
  have hnat : ∀ᵐ omega ∂M.P.toMeasure, Summable fun i : ℕ => X i omega :=
    ae_summable_of_isBigOWith_gammaSigma (by norm_num : (0 : ℝ) < 2)
      hXnn hXmeas ha hasum hXbig
  filter_upwards [hnat] with omega homega
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa only [X, fieldOneScoreArray, Int.natCast_nonneg, and_self, ite_true,
      Int.toNat_natCast] using homega
  · have hsingle : (fun i : ℕ =>
        SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (-(i : ℤ)) *
          fieldOneScoreArray (d := d) t K (m : ℤ) (-(i : ℤ)) omega) =
        fun i => if i = 0 then
          SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) 0 * fieldOneScore t K m 0 omega
          else 0 := by
      funext i
      by_cases hi : i = 0
      · subst i
        simp [fieldOneScoreArray]
      · simp [fieldOneScoreArray, hi]
    rw [hsingle]
    exact (hasSum_ite_eq 0 _).summable

private theorem translatedCube_zero_eq_cube {d : ℕ} (r : ℤ) :
    translatedCube d r 0 = cube d r := by
  unfold translatedCube
  simp

theorem fieldOne_idist_natCast (m i : ℕ) :
    SubdiffusiveProcess.Concentration.idist (m : ℤ) (i : ℤ) =
      (fieldOneIndexDistance m i : ℝ) := by
  unfold SubdiffusiveProcess.Concentration.idist fieldOneIndexDistance
  rw [← Int.cast_sub, ← Int.cast_abs, ← Nat.cast_natAbs]

/-- Pointwise manuscript reindexing: a failed literal field-one condition is
dominated by the weighted score row. -/
theorem not_goodFieldOne_imp_lt_Yk_fieldOneScoreArray {d : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {t epsilon K : ℝ}
    (ht : 0 < t) (hK : 0 < K) (hepsilon : 0 < epsilon) (m : ℕ)
    (hscore : ∀ i : ℕ, fieldOneScore (d := d) t K m i omega =
      ∑' q : ℕ, fieldOneScoreTerm t K m i q omega)
    (hqsum : ∀ i : ℕ, Summable fun q : ℕ =>
      fieldOneScoreTerm (d := d) t K m i q omega)
    (hrow : Summable fun i : ℤ =>
      SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) i *
        fieldOneScoreArray (d := d) t K (m : ℤ) i omega)
    (hbad : ¬ GoodFieldOne m 0 epsilon (8 * t) omega) :
    epsilon * K < SubdiffusiveProcess.Concentration.Yk
      (fieldOneScoreArray (d := d) t K) (t / 2) (m : ℤ) omega := by
  unfold GoodFieldOne at hbad
  rw [not_forall] at hbad
  obtain ⟨j, hj⟩ := hbad
  push Not at hj
  rw [show (8 * t * (j : ℝ)) / 8 = t * (j : ℝ) by ring] at hj
  have hliteral : epsilon * K < K * (3 : ℝ) ^ (-(t * (j : ℝ))) *
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        supNormOn (cube d ((m + 1 + j : ℕ) : ℤ)) (fun x =>
          |omega i x| + (3 : ℝ) ^ i *
            euclideanNorm (shellGradient (omega i) x)) := by
    rw [translatedCube_zero_eq_cube] at hj
    have hj' : epsilon * (3 : ℝ) ^ (t * (j : ℝ)) <
        ∑ i ∈ Finset.Icc (m - j) (m + j),
          supNormOn (cube d ((m + 1 + j : ℕ) : ℤ)) (fun x =>
            |omega i x| + (3 : ℝ) ^ i *
              euclideanNorm (shellGradient (omega i) x)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hj
    have hpow : 0 < (3 : ℝ) ^ (t * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_lt_mul_of_pos_left
      (a := K * (3 : ℝ) ^ (-(t * (j : ℝ)))) hj'
      (mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _))
    calc
      epsilon * K = (K * (3 : ℝ) ^ (-(t * (j : ℝ)))) *
          (epsilon * (3 : ℝ) ^ (t * (j : ℝ))) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
        field_simp [hpow.ne']
      _ < (K * (3 : ℝ) ^ (-(t * (j : ℝ)))) *
          (∑ i ∈ Finset.Icc (m - j) (m + j),
            supNormOn (cube d ((m + 1 + j : ℕ) : ℤ)) (fun x =>
              |omega i x| + (3 : ℝ) ^ i *
                euclideanNorm (shellGradient (omega i) x))) := hmul
      _ = _ := by ring
  have hterm (i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j)) :
      K * (3 : ℝ) ^ (-(t * (j : ℝ))) *
          supNormOn (cube d ((m + 1 + j : ℕ) : ℤ)) (fun x =>
            |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x)) ≤
        SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (i : ℤ) *
          fieldOneScoreArray (d := d) t K (m : ℤ) (i : ℤ) omega := by
    have hidist : fieldOneIndexDistance m i ≤ j := by
      rw [Finset.mem_Icc] at hi
      unfold fieldOneIndexDistance
      by_cases hmi : m ≤ i
      · rw [Int.natAbs_natCast_sub_natCast_of_le hmi]
        omega
      · have him : i ≤ m := Nat.le_of_not_ge hmi
        rw [Int.natAbs_natCast_sub_natCast_of_ge him]
        omega
    let q := j - fieldOneIndexDistance m i
    have hqeq : fieldOneIndexDistance m i + q = j := by
      unfold q
      omega
    have hmajor := fieldOne_supNormOn_le_largeCubeShellG2
      (d := d) (i := i) (k := m + 1 + j) omega
    have hscoreTerm : fieldOneScoreTerm t K m i q omega ≤
        fieldOneScore t K m i omega := by
      rw [hscore i]
      exact (hqsum i).le_tsum q (fun q' _ => fieldOneScoreTerm_nonneg hK.le m i q' omega)
    have hactive : 0 ≤ (m : ℤ) ∧ 0 ≤ (i : ℤ) :=
      ⟨Int.natCast_nonneg m, Int.natCast_nonneg i⟩
    rw [fieldOneScoreArray, ite_eq_left hactive, Int.toNat_natCast, Int.toNat_natCast]
    unfold SubdiffusiveProcess.Concentration.wt
    rw [fieldOne_idist_natCast]
    have hcoeff : 0 ≤ K * (3 : ℝ) ^ (-(t * (j : ℝ))) := by positivity
    calc
      _ ≤ K * (3 : ℝ) ^ (-(t * (j : ℝ))) *
          (((d : ℝ) + 1) * largeCubeShellG2 i
            (((m + 1 + j : ℕ) : ℤ) - (i : ℤ)) omega) :=
        mul_le_mul_of_nonneg_left hmajor hcoeff
      _ = (3 : ℝ) ^ (-((t / 2) * (fieldOneIndexDistance m i : ℝ))) *
          fieldOneScoreTerm t K m i q omega := by
        unfold fieldOneScoreTerm
        rw [show m + 1 + (fieldOneIndexDistance m i + q) = m + 1 + j by omega]
        have hqcast : (fieldOneIndexDistance m i : ℝ) + (q : ℝ) = (j : ℝ) := by
          exact_mod_cast hqeq
        have hpoweq : (3 : ℝ) ^ (-(t * (j : ℝ))) =
            (3 : ℝ) ^ (-((t / 2) * (fieldOneIndexDistance m i : ℝ))) *
              ((3 : ℝ) ^ (-(t * (fieldOneIndexDistance m i : ℝ)) / 2) *
                (3 : ℝ) ^ (-(t * (q : ℝ)))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 1
          nlinarith
        rw [hpoweq]
        unfold fieldOneCubeMajorant
        ring
      _ ≤ (3 : ℝ) ^ (-((t / 2) * (fieldOneIndexDistance m i : ℝ))) *
          fieldOneScore t K m i omega :=
        mul_le_mul_of_nonneg_left hscoreTerm (Real.rpow_nonneg (by norm_num) _)
  have hfinite : K * (3 : ℝ) ^ (-(t * (j : ℝ))) *
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        supNormOn (cube d ((m + 1 + j : ℕ) : ℤ)) (fun x =>
          |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x)) ≤
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (i : ℤ) *
          fieldOneScoreArray (d := d) t K (m : ℤ) (i : ℤ) omega := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hterm i hi
  have htoY : (∑ i ∈ Finset.Icc (m - j) (m + j),
        SubdiffusiveProcess.Concentration.wt (t / 2) (m : ℤ) (i : ℤ) *
          fieldOneScoreArray (d := d) t K (m : ℤ) (i : ℤ) omega) ≤
      SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
        (t / 2) (m : ℤ) omega := by
    unfold SubdiffusiveProcess.Concentration.Yk
    let natToInt : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
    let S := (Finset.Icc (m - j) (m + j)).map natToInt
    have hsum := hrow.sum_le_tsum S (fun i _ =>
      mul_nonneg (SubdiffusiveProcess.Concentration.wt_nonneg _ _ _)
        (fieldOneScoreArray_nonneg t K _ _ omega))
    simpa only [S, natToInt, Finset.sum_map, Function.Embedding.coeFn_mk,
      Int.ofNat_eq_natCast] using hsum
  exact hliteral.trans_le (hfinite.trans htoY)

theorem ae_not_goodFieldOne_imp_lt_Yk_fieldOneScoreArray {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {t epsilon K : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 < K) (hepsilon : 0 < epsilon) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ m : ℕ,
      ¬ GoodFieldOne m 0 epsilon (8 * t) omega →
        epsilon * K < SubdiffusiveProcess.Concentration.Yk
          (fieldOneScoreArray (d := d) t K) (t / 2) (m : ℤ) omega := by
  rw [ae_all_iff]
  intro m
  have hscore : ∀ᵐ omega ∂M.P.toMeasure, ∀ i : ℕ,
      fieldOneScore (d := d) t K m i omega =
        ∑' q : ℕ, fieldOneScoreTerm t K m i q omega := by
    rw [ae_all_iff]
    exact fun i => ae_fieldOneScore_eq_tsum M ht hK m i
  have hqsum : ∀ᵐ omega ∂M.P.toMeasure, ∀ i : ℕ,
      Summable fun q : ℕ => fieldOneScoreTerm (d := d) t K m i q omega := by
    rw [ae_all_iff]
    exact fun i => ae_summable_fieldOneScoreTerm M ht hK m i
  filter_upwards [hscore, hqsum,
    ae_summable_fieldOneScoreArray_row M ht ht1 hK m] with omega hs hq hr
  exact not_goodFieldOne_imp_lt_Yk_fieldOneScoreArray omega ht hK hepsilon m hs hq hr

/-- Field-one density concentration after exposing only the scalar parameter
normalizations. -/
theorem measure_goodFieldOne_badDensity_le_of_parameters {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {t epsilon theta K p : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hepsilon : 0 < epsilon)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hK : 0 < K) (hp : 1 ≤ p) (htp : 1 ≤ (t / 2) * p)
    (hthreshold : 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
        (theta / 2) ^ (-1 / p) < epsilon * K)
    (hnorm : ∀ m i : ℕ, gammaMomentConst 2 * Real.sqrt p *
        (gammaTriangleConst 2 *
          ∑' q : ℕ, fieldOneScoreTermScale M t K m i q) ≤ 1)
    (m0 window : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun m => {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldOne m 0 epsilon (8 * t) omega}ᶜ)
        m0 window omega} ≤
      ENNReal.ofReal (Real.exp
        (-((t / 2) * p * (theta / 2)) / 16 * ((window : ℝ) + 1))) := by
  have hconc := SubdiffusiveProcess.Concentration.concentration_for_scales_Cstar
    M.P.toMeasure (fieldOneScoreArray (d := d) t K) hp
    (by positivity : 0 < t / 2) (by linarith : t / 2 ≤ 1) htp
    (by norm_num : 1 ≤ (1 : ℕ))
    (measurable_fieldOneScoreArray t K) (fieldOneScoreArray_nonneg t K)
    (lintegral_fieldOneScoreArray_rpow_le_one M ht hK hp hnorm)
    (columnsIndep_fieldOneScoreArray M t K (by norm_num : 1 ≤ (1 : ℕ)))
    (m0 : ℤ) window (theta / 2) (by positivity) (by linarith)
  let CE : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := {omega | theta / 2 < (1 / ((window : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
        (if 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                (t / 2) k omega then (1 : ℝ) else 0)}
  have hreduce := ae_not_goodFieldOne_imp_lt_Yk_fieldOneScoreArray
    M ht ht1 hK hepsilon
  have hmono : {omega | theta ≤ intervalEventDensity
        (fun m => {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldOne m 0 epsilon (8 * t) omega}ᶜ)
        m0 window omega} ≤ᶠ[ae M.P.toMeasure] CE := by
    filter_upwards [hreduce] with omega hreduce homega
    unfold intervalEventDensity at homega
    change theta / 2 < (1 / ((window : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
        (if 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                (t / 2) k omega then (1 : ℝ) else 0)
    have hcount :
        ∑ k ∈ Finset.Icc m0 (m0 + window),
            (if omega ∈ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldOne k 0 epsilon (8 * t) omega}ᶜ
              then (1 : ℝ) else 0) ≤
          ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                    (t / 2) k omega then (1 : ℝ) else 0) := by
      let natToInt : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
      rw [show Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)) =
          (Finset.Icc m0 (m0 + window)).map natToInt by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_map]
        constructor
        · intro hz
          have hz0 : 0 ≤ z := (show (0 : ℤ) ≤ m0 by omega).trans hz.1
          have hzEq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
          refine ⟨z.toNat, ?_, ?_⟩
          · constructor
            · have hzLower : (m0 : ℤ) ≤ (z.toNat : ℤ) := by
                simpa only [hzEq] using hz.1
              omega
            · have hzUpper : (z.toNat : ℤ) ≤ ((m0 + window : ℕ) : ℤ) := by
                simpa only [hzEq, Nat.cast_add] using hz.2
              omega
          · simp only [natToInt, Function.Embedding.coeFn_mk]
            exact hzEq
        · rintro ⟨k, hk, rfl⟩
          simp only [natToInt, Function.Embedding.coeFn_mk]
          constructor
          · simpa only [Int.ofNat_eq_natCast] using
              (show (m0 : ℤ) ≤ (k : ℤ) by exact_mod_cast hk.1)
          · simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
              (show (k : ℤ) ≤ ((m0 + window : ℕ) : ℤ) by exact_mod_cast hk.2),
        Finset.sum_map]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hbad : omega ∈
          {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldOne k 0 epsilon (8 * t) omega}ᶜ
      · rw [ite_eq_left hbad]
        have hy := hreduce k (by simpa only [Set.mem_compl_iff,
          Set.mem_ofPred_eq, not_not] using hbad)
        have hscore : 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                (t / 2) (k : ℤ) omega := hthreshold.trans hy
        rw [ite_eq_left (by simpa only [natToInt, Function.Embedding.coeFn_mk] using! hscore)]
      · rw [ite_eq_right hbad]
        split_ifs <;> norm_num
    have hcount' :
        (∑ m ∈ Finset.Icc m0 (m0 + window),
          eventIndicator
            ((fun m => {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldOne m 0 epsilon (8 * t) omega}ᶜ) m)
            omega) ≤
          ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                    (t / 2) k omega then (1 : ℝ) else 0) := by
      convert hcount using 1;
        simp only [eventIndicator, Set.mem_compl_iff, Set.mem_ofPred_eq]
    have havg := homega.trans (div_le_div_of_nonneg_right hcount' (by positivity))
    have havg' : theta ≤ (1 / ((window : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
          (if 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
              (theta / 2) ^ (-1 / p) <
                SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                  (t / 2) k omega then (1 : ℝ) else 0) := by
      calc
        theta ≤ (∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * (t / 2)⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk (fieldOneScoreArray (d := d) t K)
                    (t / 2) k omega then (1 : ℝ) else 0)) /
              ((window : ℝ) + 1) := havg
        _ = _ := by ring
    exact (by linarith : theta / 2 < theta).trans_le havg'
  exact (MeasureTheory.measure_mono_ae hmono).trans (by
    simpa only [CE, Nat.cast_one, mul_one] using hconc)

def fieldOneDensityDimFactor (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
    (1 + Real.log 2) ^ (2 : ℝ)⁻¹

def fieldOneDensityBudget (d : ℕ) : ℝ :=
  1 + 32 * gammaMomentConst 2 * gammaTriangleConst 2 *
    expSequenceAmplitude * fieldOneDensityDimFactor d

theorem fieldOneDensityBudget_pos (d : ℕ) : 0 < fieldOneDensityBudget d := by
  unfold fieldOneDensityBudget fieldOneDensityDimFactor
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hG : 0 ≤ ((d : ℝ) + 1) *
      Real.sqrt (shellCoverLogConst * (d : ℝ)) *
        (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg hlog.le _)
  have hterm : 0 ≤ 32 * gammaMomentConst 2 * gammaTriangleConst 2 *
      expSequenceAmplitude *
        (((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
          (1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (gammaMomentConst_pos (by norm_num)).le)
          (gammaTriangleConst_pos (σ := 2)).le)
        (zero_lt_one.trans expSequenceAmplitude_gt_one).le) hG
  linarith

private theorem fieldOne_score_normalized {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s epsilon : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hepsilon : 0 < epsilon)
    (m i : ℕ) :
    gammaMomentConst 2 *
        Real.sqrt ((s ^ 2 * Real.sqrt s * epsilon /
          (fieldOneDensityBudget d * M.delta)) ^ 2) *
      (gammaTriangleConst 2 *
        ∑' q : ℕ, fieldOneScoreTermScale M s
          (2 * expSequenceAmplitude * s⁻¹ * epsilon⁻¹) m i q) ≤ 1 := by
  let A := expSequenceAmplitude
  let B := fieldOneDensityBudget d
  let G := fieldOneDensityDimFactor d
  have hA : 0 < A := zero_lt_one.trans expSequenceAmplitude_gt_one
  have hB : 0 < B := fieldOneDensityBudget_pos d
  have hdelta := M.shellPrefix.delta_pos
  have hK : 0 < 2 * A * s⁻¹ * epsilon⁻¹ := by positivity
  have hsum := tsum_fieldOneScoreTermScale_le M hs hs1 hK m i
  have hGamma : fieldOneGammaDimScale M = G * M.delta := by
    unfold fieldOneGammaDimScale G fieldOneDensityDimFactor
    ring
  have hcore : 32 * gammaMomentConst 2 * gammaTriangleConst 2 * A * G ≤ B := by
    unfold B fieldOneDensityBudget
    linarith
  have hG0 : 0 ≤ G := by
    unfold G fieldOneDensityDimFactor
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    positivity
  have hsqrt : Real.sqrt ((s ^ 2 * Real.sqrt s * epsilon /
      (B * M.delta)) ^ 2) =
      s ^ 2 * Real.sqrt s * epsilon / (B * M.delta) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos]
    positivity
  have hsqrtS : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  calc
    gammaMomentConst 2 *
        Real.sqrt ((s ^ 2 * Real.sqrt s * epsilon / (B * M.delta)) ^ 2) *
      (gammaTriangleConst 2 *
        ∑' q : ℕ, fieldOneScoreTermScale M s
          (2 * A * s⁻¹ * epsilon⁻¹) m i q) ≤
      gammaMomentConst 2 *
        Real.sqrt ((s ^ 2 * Real.sqrt s * epsilon / (B * M.delta)) ^ 2) *
      (gammaTriangleConst 2 *
        (16 * (2 * A * s⁻¹ * epsilon⁻¹) * fieldOneGammaDimScale M *
          (Real.sqrt s)⁻¹ * s⁻¹)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (gammaTriangleConst_pos (σ := 2)).le)
        (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))
    _ = 32 * gammaMomentConst 2 * gammaTriangleConst 2 * A * G / B := by
      rw [hsqrt, hGamma]
      field_simp [hB.ne', hdelta.ne', hepsilon.ne', hs.ne', hsqrtS.ne']
      nlinarith [Real.sq_sqrt hs.le]
    _ ≤ 1 := (div_le_one hB).2 hcore

def fieldOneDensityConst (d : ℕ) : ℝ :=
  1 + 128 * fieldOneDensityBudget d ^ 2

theorem fieldOneDensityConst_pos (d : ℕ) : 0 < fieldOneDensityConst d := by
  unfold fieldOneDensityConst
  positivity

/-- Source-form field/gradient density estimate
`l.bad.scales.for.nabla.gj`. -/
theorem measure_goodFieldOne_badDensity_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {s theta epsilon : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hepsilon : 0 < epsilon) (_hepsilon1 : epsilon ≤ 1)
    (hsmall : fieldOneDensityConst d * s ^ (-6 : ℤ) *
      epsilon⁻¹ ^ 2 * M.delta ^ 2 ≤ theta)
    (m0 window : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun m => {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldOne m 0 epsilon (8 * s) omega}ᶜ)
        m0 window omega} ≤
      ENNReal.ofReal (Real.exp
        (-(s ^ 6 * epsilon ^ 2 * theta /
          (fieldOneDensityConst d * M.delta ^ 2)) *
            ((window : ℝ) + 1))) := by
  let A := expSequenceAmplitude
  let B := fieldOneDensityBudget d
  let C0 := fieldOneDensityConst d
  have hA : 0 < A := zero_lt_one.trans expSequenceAmplitude_gt_one
  have hB : 0 < B := fieldOneDensityBudget_pos d
  have hC0 : 0 < C0 := fieldOneDensityConst_pos d
  have hdelta := M.shellPrefix.delta_pos
  have hbudget : C0 * M.delta ^ 2 ≤ theta * s ^ 6 * epsilon ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsmall
      (mul_nonneg (pow_nonneg hs.le 6) (sq_nonneg epsilon))
    calc
      C0 * M.delta ^ 2 =
          (C0 * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2) *
            (s ^ 6 * epsilon ^ 2) := by
        rw [zpow_neg]
        field_simp [hs.ne', hepsilon.ne']
      _ ≤ theta * (s ^ 6 * epsilon ^ 2) := hmul
      _ = theta * s ^ 6 * epsilon ^ 2 := by ring
  let p : ℝ := (s ^ 2 * Real.sqrt s * epsilon / (B * M.delta)) ^ 2
  have hp0 : 0 < p := by dsimp only [p]; positivity
  have hCtwo : 2 * B ^ 2 ≤ C0 := by
    change 2 * B ^ 2 ≤ 1 + 128 * B ^ 2
    nlinarith [sq_nonneg B]
  have hC64 : 64 * B ^ 2 ≤ C0 := by
    change 64 * B ^ 2 ≤ 1 + 128 * B ^ 2
    nlinarith [sq_nonneg B]
  have hpTheta : 2 / theta ≤ p := by
    rw [div_le_iff₀ htheta]
    dsimp only [p]
    rw [show (s ^ 2 * Real.sqrt s * epsilon / (B * M.delta)) ^ 2 * theta =
      (s ^ 5 * epsilon ^ 2 * theta) / (B ^ 2 * M.delta ^ 2) by
        field_simp [hB.ne', hdelta.ne']
        rw [Real.sq_sqrt hs.le]]
    rw [le_div_iff₀ (mul_pos (sq_pos_of_pos hB) (sq_pos_of_pos hdelta))]
    have hleft : 2 * B ^ 2 * M.delta ^ 2 ≤ C0 * M.delta ^ 2 :=
      mul_le_mul_of_nonneg_right hCtwo (sq_nonneg _)
    have hs65 : s ^ 6 ≤ s ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_right hs1 (pow_nonneg hs.le 5)]
    calc
      2 * (B ^ 2 * M.delta ^ 2) = 2 * B ^ 2 * M.delta ^ 2 := by ring
      _ ≤ C0 * M.delta ^ 2 := hleft
      _ ≤ theta * s ^ 6 * epsilon ^ 2 := hbudget
      _ ≤ s ^ 5 * epsilon ^ 2 * theta := by
        nlinarith [mul_le_mul_of_nonneg_right hs65
          (mul_nonneg htheta.le (sq_nonneg epsilon))]
  have hp : 1 ≤ p := by
    have : 1 ≤ 2 / theta := by
      rw [le_div_iff₀ htheta]
      linarith
    exact this.trans hpTheta
  have hsp : 1 ≤ (s / 2) * p := by
    have htwoOverS : 2 / s ≤ p := by
      dsimp only [p]
      rw [show (s ^ 2 * Real.sqrt s * epsilon / (B * M.delta)) ^ 2 =
        (s ^ 5 * epsilon ^ 2) / (B ^ 2 * M.delta ^ 2) by
          field_simp [hB.ne', hdelta.ne']
          rw [Real.sq_sqrt hs.le]]
      rw [div_le_div_iff₀ hs (mul_pos (sq_pos_of_pos hB) (sq_pos_of_pos hdelta))]
      have hbudgetOne : C0 * M.delta ^ 2 ≤ s ^ 6 * epsilon ^ 2 :=
        hbudget.trans (by
          have hm := mul_le_mul_of_nonneg_right htheta1
            (mul_nonneg (pow_nonneg hs.le 6) (sq_nonneg epsilon))
          nlinarith)
      calc
        2 * (B ^ 2 * M.delta ^ 2) ≤ C0 * M.delta ^ 2 := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hCtwo (sq_nonneg M.delta)
        _ ≤ s ^ 6 * epsilon ^ 2 := hbudgetOne
        _ = s ^ 5 * epsilon ^ 2 * s := by ring
    have hm := mul_le_mul_of_nonneg_left htwoOverS (by positivity : 0 ≤ s / 2)
    calc
      1 = (s / 2) * (2 / s) := by field_simp [hs.ne']
      _ ≤ (s / 2) * p := hm
  have hthreshold : 6 * (s / 2)⁻¹ *
      SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p) <
        epsilon * (2 * A * s⁻¹ * epsilon⁻¹) := by
    have hbase := expSequence_threshold_lt_amplitude htheta htheta1 hpTheta
    have hscale := mul_lt_mul_of_pos_left hbase (inv_pos.mpr (by positivity : 0 < s / 2))
    have hright : epsilon * (2 * A * s⁻¹ * epsilon⁻¹) =
        (s / 2)⁻¹ * A := by
      field_simp [hepsilon.ne']
    rw [hright]
    convert hscale using 1
    all_goals ring
  have hnorm : ∀ m i : ℕ, gammaMomentConst 2 * Real.sqrt p *
      (gammaTriangleConst 2 *
        ∑' q : ℕ, fieldOneScoreTermScale M s
          (2 * A * s⁻¹ * epsilon⁻¹) m i q) ≤ 1 := by
    intro m i
    exact fieldOne_score_normalized M hs hs1 hepsilon m i
  have hraw := measure_goodFieldOne_badDensity_le_of_parameters M hs hs1 hepsilon
    htheta htheta1 (by positivity : 0 < 2 * A * s⁻¹ * epsilon⁻¹)
    hp hsp hthreshold hnorm m0 window
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hrate : (s / 2) * p * (theta / 2) / 16 ≥
      s ^ 6 * epsilon ^ 2 * theta / (C0 * M.delta ^ 2) := by
    dsimp only [p]
    field_simp [hB.ne', hC0.ne', hdelta.ne']
    rw [Real.sq_sqrt hs.le]
    nlinarith [hC64]
  have hw : 0 ≤ (window : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hrate hw
  convert neg_le_neg hmul using 1 <;> ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
