import SubdiffusiveProcess.Sobolev.VolumeResponseContinuity
import SubdiffusiveProcess.Sobolev.ResponseComparison

/-! Operator-norm comparison of killed inverses of two positive coefficients with a two-sided ratio bound
(the coefficient form of `volumeResponseOperator_sub_norm_le`, which is stated for exponential potentials). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Topology TopologicalSpace SubdiffusiveProcess
open scoped ENNReal InnerProductSpace
noncomputable section
namespace Paper

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- **Quadratic difference bound.**  For two positive coefficients whose ratio lies in `[exp (-D), exp D]`, the quadratic pairing of the
difference of the volume-response operators is bounded by `(exp ‖h - g‖ - 1)` times the pairing of
the reference operator `Gg`, and hence by `(exp ‖h - g‖ - 1) * ‖Gg‖ * ‖f‖²`. -/
theorem aux_calib_volumeResponseOperator_sub_norm_le_quadratic (S : ResponseSpace Ω)
    (ca cb : PositiveCoefficient Ω) (D : ℝ) (hD : 0 ≤ D)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), Real.exp (-D) * ca.val x ≤ cb.val x)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), cb.val x ≤ Real.exp D * ca.val x)
    (f : DomainL2 Ω) :
    |inner ℝ f ((volumeResponseOperator S (cb) -
        volumeResponseOperator S (ca)) f)| ≤
      (Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖ * ‖f‖ ^ 2 := by
  set a : ℝ :=
    inverseResponse S (ca)
      ((sobolevVolumeLoad f).comp S.space.subtypeL) with ha_def
  set b : ℝ :=
    inverseResponse S (cb)
      ((sobolevVolumeLoad f).comp S.space.subtypeL) with hb_def
  have ha : 0 ≤ a := by
    rw [ha_def]
    exact inverseResponse_nonneg S (ca) _
  have hb : 0 ≤ b := by
    rw [hb_def]
    exact inverseResponse_nonneg S (cb) _
  have hcmp := inverseResponse_exp_comparison S ca cb
    ((sobolevVolumeLoad f).comp S.space.subtypeL) D hl hu
  rw [← ha_def, ← hb_def] at hcmp
  have hr : (0 : ℝ) ≤ D := hD
  -- the quadratic pairing of the difference is the difference of the responses
  have hdiff : inner ℝ f ((volumeResponseOperator S (cb) -
      volumeResponseOperator S (ca)) f) = b - a := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, volumeResponseOperator_quadratic,
      volumeResponseOperator_quadratic]
  -- the two one-sided bounds
  have hup : b - a ≤ (Real.exp D - 1) * a := by nlinarith [hcmp.2, ha]
  have hlow : -(b - a) ≤ (Real.exp D - 1) * a := by
    have hineq : 1 - Real.exp (-D) ≤ Real.exp D - 1 := by
      have hmul : Real.exp (-D) * Real.exp D = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hle1 : Real.exp (-D) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
      have hnn : 0 ≤ Real.exp D - 1 := by
        have := Real.one_le_exp hD; linarith
      calc 1 - Real.exp (-D) = Real.exp (-D) * (Real.exp D - 1) := by
            rw [mul_sub, hmul, mul_one]
        _ ≤ 1 * (Real.exp D - 1) := mul_le_mul_of_nonneg_right hle1 hnn
        _ = Real.exp D - 1 := one_mul _
    have h4 : a - b ≤ (1 - Real.exp (-D)) * a := by nlinarith [hcmp.1]
    have h3 : (1 - Real.exp (-D)) * a ≤ (Real.exp D - 1) * a :=
      mul_le_mul_of_nonneg_right hineq ha
    have hneg : -(b - a) = a - b := by ring
    rw [hneg]
    exact h4.trans h3
  have habs : |b - a| ≤ (Real.exp D - 1) * a := by
    rw [abs_le]
    exact ⟨by linarith [hlow], hup⟩
  -- bound the response at `g` by the operator norm and `‖f‖²`
  have ha_le : a ≤ ‖volumeResponseOperator S (ca)‖ * ‖f‖ ^ 2 := by
    have hquad := volumeResponseOperator_quadratic S (ca) f
    have h1 : a = inner ℝ f (volumeResponseOperator S (ca) f) := by
      rw [ha_def]
      exact hquad.symm
    calc a = inner ℝ f (volumeResponseOperator S (ca) f) := h1
      _ ≤ |inner ℝ f (volumeResponseOperator S (ca) f)| := le_abs_self _
      _ ≤ ‖f‖ * ‖volumeResponseOperator S (ca) f‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖volumeResponseOperator S (ca)‖ * ‖f‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖volumeResponseOperator S (ca)‖ * ‖f‖ ^ 2 := by ring
  rw [hdiff]
  calc |b - a| ≤ (Real.exp D - 1) * a := habs
    _ ≤ (Real.exp D - 1) *
          (‖volumeResponseOperator S (ca)‖ * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ha_le (by
          have := Real.one_le_exp hD; linarith)
    _ = (Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖ * ‖f‖ ^ 2 := by
        ring

/-- **Operator-norm difference bound.**  The difference of the volume-response operators at two
`L∞` potentials is bounded in operator norm by `2 * (exp ‖h - g‖ - 1) * ‖Gg‖`, via polarization
on the unit ball. -/
theorem calib_volumeResponseOperator_sub_norm_le (S : ResponseSpace Ω)
    (ca cb : PositiveCoefficient Ω) (D : ℝ) (hD : 0 ≤ D)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), Real.exp (-D) * ca.val x ≤ cb.val x)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), cb.val x ≤ Real.exp D * ca.val x) :
    ‖volumeResponseOperator S (cb) -
        volumeResponseOperator S (ca)‖ ≤
      2 * (Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖ := by
  set A : DomainL2 Ω →L[ℝ] DomainL2 Ω :=
    volumeResponseOperator S (cb) -
      volumeResponseOperator S (ca) with hA_def
  have hsymA : ∀ x y : DomainL2 Ω, inner ℝ (A x) y = inner ℝ x (A y) := by
    intro x y
    have h1 := volumeResponseOperator_symm S (cb) x y
    have h2 := volumeResponseOperator_symm S (ca) x y
    rw [hA_def]
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [← real_inner_comm (volumeResponseOperator S (cb) x) y,
      ← real_inner_comm (volumeResponseOperator S (ca) x) y, h1, h2]
  have hCnn : 0 ≤ (Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖ :=
    mul_nonneg (by have := Real.one_le_exp hD; linarith) (norm_nonneg _)
  have hbound : ∀ x y : DomainL2 Ω, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (A y)| ≤ 2 * ((Real.exp D - 1) *
        ‖volumeResponseOperator S (ca)‖) := by
    intro x y hx hy
    have hpol := SubdiffusiveProcess.Probability.aux_polarization A hsymA x y
    have hq1 := aux_calib_volumeResponseOperator_sub_norm_le_quadratic S ca cb D hD hl hu (x + y)
    have hq2 := aux_calib_volumeResponseOperator_sub_norm_le_quadratic S ca cb D hD hl hu (x - y)
    rw [← hA_def] at hq1 hq2
    have hnorm1 : ‖x + y‖ ^ 2 ≤ 4 := by
      nlinarith [norm_add_le x y, hx, hy, norm_nonneg (x + y)]
    have hnorm2 : ‖x - y‖ ^ 2 ≤ 4 := by
      nlinarith [norm_sub_le x y, hx, hy, norm_nonneg (x - y)]
    have hb1 : |inner ℝ (x + y) (A (x + y))| ≤
        ((Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖) * 4 :=
      hq1.trans (mul_le_mul_of_nonneg_left hnorm1 hCnn)
    have hb2 : |inner ℝ (x - y) (A (x - y))| ≤
        ((Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖) * 4 :=
      hq2.trans (mul_le_mul_of_nonneg_left hnorm2 hCnn)
    have htri : |inner ℝ (x + y) (A (x + y)) - inner ℝ (x - y) (A (x - y))| ≤
        ((Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖) * 4 +
          ((Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖) * 4 :=
      (abs_sub _ _).trans (add_le_add hb1 hb2)
    calc |inner ℝ x (A y)|
        = |4 * inner ℝ x (A y)| / 4 := by
          rw [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
          ring
      _ = |inner ℝ (x + y) (A (x + y)) - inner ℝ (x - y) (A (x - y))| / 4 := by rw [hpol]
      _ ≤ (((Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖) * 4 +
            ((Real.exp D - 1) * ‖volumeResponseOperator S (ca)‖) * 4) / 4 :=
          div_le_div_of_nonneg_right htri (by norm_num)
      _ = 2 * ((Real.exp D - 1) *
            ‖volumeResponseOperator S (ca)‖) := by ring
  have hMnn : 0 ≤ 2 * ((Real.exp D - 1) *
      ‖volumeResponseOperator S (ca)‖) := mul_nonneg (by norm_num) hCnn
  have hmain : ‖A‖ ≤ 2 * ((Real.exp D - 1) *
      ‖volumeResponseOperator S (ca)‖) :=
    SubdiffusiveProcess.Probability.aux_opNorm_le_of_inner hMnn hbound
  rw [hA_def] at hmain
  simpa only [mul_assoc] using hmain


end Paper
