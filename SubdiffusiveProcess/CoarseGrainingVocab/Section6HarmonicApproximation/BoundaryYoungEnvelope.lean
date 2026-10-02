import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCanonicalActiveCell

/-!
# Uniform envelope for the active-cell Young remainder

The prefactor-selected height is child-dependent.  This algebraic lemma
removes its tail coefficient using the one-eighth absorption inequality
before descendant averaging, leaving only squares of the source factor and
the low-frequency remainder.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

/-- Monotonicity of the literal support-aware Young remainder in its fine
tail, low-frequency, and forcing factors. -/
theorem boundaryYoungRemainder_mono
    {C A mu mu' Eh R R' G G' : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hmu : 0 ≤ mu) (hmu' : 0 ≤ mu')
    (_hEh : 0 ≤ Eh) (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hG : 0 ≤ G) (hG' : 0 ≤ G')
    (hmule : mu ≤ mu') (hRle : R ≤ R') (hGle : G ≤ G') :
    4 * (C * A * (Real.sqrt 2 * mu * Real.sqrt Eh + R)) ^ 2 +
        4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 +
          C * G * (Real.sqrt 2 * mu * Real.sqrt Eh + R) ≤
      4 * (C * A * (Real.sqrt 2 * mu' * Real.sqrt Eh + R')) ^ 2 +
        4 * (C * G' * (Real.sqrt 2 * mu')) ^ 2 +
          C * G' * (Real.sqrt 2 * mu' * Real.sqrt Eh + R') := by
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtEh : 0 ≤ Real.sqrt Eh := Real.sqrt_nonneg _
  have hZ : Real.sqrt 2 * mu * Real.sqrt Eh + R ≤
      Real.sqrt 2 * mu' * Real.sqrt Eh + R' := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmule hsqrt2) hsqrtEh) hRle
  have hZ0 : 0 ≤ Real.sqrt 2 * mu * Real.sqrt Eh + R :=
    add_nonneg (mul_nonneg (mul_nonneg hsqrt2 hmu) hsqrtEh) hR
  have hZ0' : 0 ≤ Real.sqrt 2 * mu' * Real.sqrt Eh + R' :=
    add_nonneg (mul_nonneg (mul_nonneg hsqrt2 hmu') hsqrtEh) hR'
  have hCA : 0 ≤ C * A := mul_nonneg hC hA
  have hfirst :
      (C * A * (Real.sqrt 2 * mu * Real.sqrt Eh + R)) ^ 2 ≤
        (C * A * (Real.sqrt 2 * mu' * Real.sqrt Eh + R')) ^ 2 := by
    exact pow_le_pow_left₀ (mul_nonneg hCA hZ0)
      (mul_le_mul_of_nonneg_left hZ hCA) 2
  have hGmu : G * mu ≤ G' * mu' :=
    (mul_le_mul_of_nonneg_left hmule hG).trans
      (mul_le_mul_of_nonneg_right hGle hmu')
  have hsecondBase : C * G * (Real.sqrt 2 * mu) ≤
      C * G' * (Real.sqrt 2 * mu') := by
    have hroot : G * (Real.sqrt 2 * mu) ≤ G' * (Real.sqrt 2 * mu') := by
      nlinarith only [hGmu, hsqrt2]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hroot hC
  have hsecond0 : 0 ≤ C * G * (Real.sqrt 2 * mu) := by positivity
  have hsecond : (C * G * (Real.sqrt 2 * mu)) ^ 2 ≤
      (C * G' * (Real.sqrt 2 * mu')) ^ 2 :=
    pow_le_pow_left₀ hsecond0 hsecondBase 2
  have hcross : C * G * (Real.sqrt 2 * mu * Real.sqrt Eh + R) ≤
      C * G' * (Real.sqrt 2 * mu' * Real.sqrt Eh + R') := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul hGle hZ hZ0 hG') hC
  nlinarith only [hfirst, hsecond, hcross]

/-- Uniform form of the literal three-term Young remainder. -/
theorem boundaryActiveCellYoungRemainder_le
    {a b c g e r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hsmall : a * b ≤ 1 / 8) :
    4 * (a * (b * Real.sqrt e + r)) ^ 2 +
        4 * (c * g * b) ^ 2 + c * g * (b * Real.sqrt e + r) ≤
      (5 / 8 : ℝ) * e +
        (9 / 2 : ℝ) * (c * g * b) ^ 2 +
        (1 / 2 : ℝ) * (c * g) ^ 2 +
        (8 * a ^ 2 + 1 / 2) * r ^ 2 := by
  have hsqrt : (Real.sqrt e) ^ 2 = e := Real.sq_sqrt he
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have habsq : (a * b) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hab0 hsmall 2
  have hsum : (b * Real.sqrt e + r) ^ 2 ≤
      2 * b ^ 2 * e + 2 * r ^ 2 := by
    nlinarith [sq_nonneg (b * Real.sqrt e - r), hsqrt]
  have hfirst : 4 * (a * (b * Real.sqrt e + r)) ^ 2 ≤
      (1 / 8 : ℝ) * e + 8 * a ^ 2 * r ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg a))
    nlinarith only [hscaled, habsq, he]
  have hcrossE : c * g * (b * Real.sqrt e) ≤
      (1 / 2 : ℝ) * (c * g * b) ^ 2 + (1 / 2 : ℝ) * e := by
    nlinarith [sq_nonneg (c * g * b - Real.sqrt e), hsqrt]
  have hcrossR : c * g * r ≤
      (1 / 2 : ℝ) * (c * g) ^ 2 + (1 / 2 : ℝ) * r ^ 2 := by
    nlinarith [sq_nonneg (c * g - r)]
  nlinarith only [hfirst, hcrossE, hcrossR]

/-- Weighted Young envelope for the same literal remainder.  Choosing the
weight to be the local scalar normalizer preserves that normalizer on the
solution/datum square and moves its inverse onto the forcing square.  This is
the normalization-sensitive variant needed in the good-scale boundary
assembly. -/
theorem boundaryYoungRemainder_le_weighted
    {C A mu Eh R G tau : ℝ}
    (hEh : 0 ≤ Eh) (_hR : 0 ≤ R) (_hmu : 0 ≤ mu)
    (htau : 0 < tau) :
    4 * (C * A * (Real.sqrt 2 * mu * Real.sqrt Eh + R)) ^ 2 +
        4 * (C * G * (Real.sqrt 2 * mu)) ^ 2 +
          C * G * (Real.sqrt 2 * mu * Real.sqrt Eh + R) ≤
      (4 * (C * A) ^ 2 + tau / 2) *
          (4 * mu ^ 2 * Eh + 2 * R ^ 2) +
        (4 * (C * Real.sqrt 2 * mu) ^ 2 + C ^ 2 / (2 * tau)) * G ^ 2 := by
  let Z : ℝ := Real.sqrt 2 * mu * Real.sqrt Eh + R
  have hsqrtEh : Real.sqrt Eh ^ 2 = Eh := Real.sq_sqrt hEh
  have hsqrtTwo : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hfirstSq : (Real.sqrt 2 * mu * Real.sqrt Eh) ^ 2 =
      2 * mu ^ 2 * Eh := by
    rw [mul_pow, mul_pow, hsqrtTwo, hsqrtEh]
  have hZ : Z ^ 2 ≤ 4 * mu ^ 2 * Eh + 2 * R ^ 2 := by
    dsimp only [Z]
    nlinarith only [sq_nonneg (Real.sqrt 2 * mu * Real.sqrt Eh - R), hfirstSq]
  have hYoung : C * G * Z ≤ tau / 2 * Z ^ 2 +
      C ^ 2 / (2 * tau) * G ^ 2 := by
    have hsq : 0 ≤ (tau * Z - C * G) ^ 2 := sq_nonneg _
    field_simp [htau.ne'] at hsq ⊢
    nlinarith only [hsq]
  have hcoefZ : 0 ≤ 4 * (C * A) ^ 2 + tau / 2 := by positivity
  have hscaledZ := mul_le_mul_of_nonneg_left hZ hcoefZ
  dsimp only [Z] at hYoung hscaledZ ⊢
  nlinarith only [hYoung, hscaledZ]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
