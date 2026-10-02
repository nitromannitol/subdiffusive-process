import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SlopeStabilityEndpoints

/-!
# Normalized averaging prices on subcubes

These lemmas isolate the crude `r^{-d/2}` price incurred when a normalized
`L^2` quantity on a unit cube is restricted to a side-`r` subcube.  They are
pure measure theory and do not use an elliptic regularity input.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- Mean comparison on arbitrary finite-measure nested windows. -/
theorem abs_averageOn_subset_sub_averageOn_le
    {Q P : Set (Vec d)} {f : Vec d → ℝ}
    (hPmeas : MeasurableSet P) (hsub : P ⊆ Q)
    (hQtop : volume Q ≠ ⊤) (hQpos : 0 < (volume Q).toReal)
    (hPpos : 0 < (volume P).toReal)
    (hf : IntegrableOn f Q)
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) Q) :
    |averageOn P f - averageOn Q f| ≤
      Real.sqrt ((volume Q).toReal / (volume P).toReal) *
        normalizedL2On Q (fun x ↦ f x - averageOn Q f) := by
  let A := averageOn Q f
  have hfP : IntegrableOn f P := hf.mono_set hsub
  have hPtop : volume P ≠ ⊤ := by
    exact ne_of_lt ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.mpr hQtop))
  have hconstP : IntegrableOn (fun _ : Vec d ↦ A) P :=
    integrableOn_const hPtop
  have hcenterP : IntegrableOn (fun x ↦ f x - A) P := hfP.sub hconstP
  have hcenterSqQ : IntegrableOn (fun x ↦ (f x - A) ^ 2) Q := by
    have hlinear : IntegrableOn (fun x ↦ 2 * A * f x) Q :=
      hf.const_mul (2 * A)
    have hconstSq : IntegrableOn (fun _ : Vec d ↦ A ^ 2) Q :=
      integrableOn_const hQtop
    have hfun : (fun x ↦ (f x - A) ^ 2) =
        fun x ↦ f x ^ 2 - 2 * A * f x + A ^ 2 := by
      funext x
      ring
    rw [hfun]
    exact (hf2.sub hlinear).add hconstSq
  have havg : averageOn P (fun x ↦ f x - A) = averageOn P f - A := by
    unfold averageOn volumeAverage
    rw [integral_sub hfP hconstP, setIntegral_const, smul_eq_mul,
      measureReal_def]
    have hne : (volume P).toReal ≠ 0 := hPpos.ne'
    field_simp
  rw [← havg]
  exact (abs_volumeAverage_le_normalizedL2On hPmeas hPpos hcenterP
    (hcenterSqQ.mono_set hsub)).trans
      (normalizedL2On_le_of_subset hsub
        hQpos hPpos hcenterSqQ)

/-- The square-root volume ratio for a side-`r` subcube is exactly
`r^{-d/2}`. -/
theorem sqrt_inv_pow_eq_rpow_neg_natCast_div_two {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((r ^ d)⁻¹) = r ^ (-(d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.inv_rpow (pow_nonneg hr.le d),
    ← Real.rpow_natCast]
  rw [← Real.rpow_mul hr.le]
  rw [← Real.rpow_neg hr.le]
  congr 1
  ring

/-- Restriction from a unit axis cube to a side-`r` axis subcube, with the
literal square-root volume price.  This is `r^{-d/2}` before elementary
power simplification. -/
theorem normalizedL2On_subcube_le_sqrt_inv_pow
    {z p : Vec d} {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} (hsub : axisCube p r ⊆ axisCube z 1)
    (hint : IntegrableOn (fun x ↦ f x ^ 2) (axisCube z 1)) :
    normalizedL2On (axisCube p r) f ≤
      Real.sqrt ((r ^ d)⁻¹) * normalizedL2On (axisCube z 1) f := by
  have hQ : 0 < (volume (axisCube z 1)).toReal :=
    volume_axisCube_toReal_pos z (by norm_num)
  have hP : 0 < (volume (axisCube p r)).toReal :=
    volume_axisCube_toReal_pos p hr
  have h := normalizedL2On_le_of_subset hsub hQ hP hint
  have hratio : (volume (axisCube z 1)).toReal /
      (volume (axisCube p r)).toReal = (r ^ d)⁻¹ := by
    rw [volume_axisCube_toReal z (by norm_num),
      volume_axisCube_toReal p hr.le]
    norm_num
  rwa [hratio] at h

/-- Restriction to a side-`r` subcube with the explicit `r^{-d/2}` factor. -/
theorem normalizedL2On_subcube_le_rpow
    {z p : Vec d} {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} (hsub : axisCube p r ⊆ axisCube z 1)
    (hint : IntegrableOn (fun x ↦ f x ^ 2) (axisCube z 1)) :
    normalizedL2On (axisCube p r) f ≤
      r ^ (-(d : ℝ) / 2) * normalizedL2On (axisCube z 1) f := by
  rw [← sqrt_inv_pow_eq_rpow_neg_natCast_div_two hr]
  exact normalizedL2On_subcube_le_sqrt_inv_pow hr hsub hint

/-- A subcube mean differs from the ambient mean by at most the same
`r^{-d/2}` restriction price times the ambient centered normalized `L^2`
oscillation. -/
theorem abs_averageOn_subcube_sub_averageOn_unitCube_le
    {z p : Vec d} {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} (hsub : axisCube p r ⊆ axisCube z 1)
    (hf : IntegrableOn f (axisCube z 1))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (axisCube z 1)) :
    |averageOn (axisCube p r) f - averageOn (axisCube z 1) f| ≤
      Real.sqrt ((r ^ d)⁻¹) *
        normalizedL2On (axisCube z 1)
          (fun x ↦ f x - averageOn (axisCube z 1) f) := by
  let Q := axisCube z 1
  let P := axisCube p r
  let A := averageOn Q f
  have hQtop : volume Q ≠ ⊤ := volume_axisCube_ne_top z 1
  have hPmeas : MeasurableSet P := measurableSet_axisCube p r
  have hPpos : 0 < (volume P).toReal := volume_axisCube_toReal_pos p hr
  have hfP : IntegrableOn f P := hf.mono_set hsub
  have hconstP : IntegrableOn (fun _ : Vec d ↦ A) P :=
    integrableOn_const (volume_axisCube_ne_top p r)
  have hcenterP : IntegrableOn (fun x ↦ f x - A) P := hfP.sub hconstP
  have hcenterSqQ : IntegrableOn (fun x ↦ (f x - A) ^ 2) Q := by
    have hlinear : IntegrableOn (fun x ↦ 2 * A * f x) Q :=
      hf.const_mul (2 * A)
    have hconstSq : IntegrableOn (fun _ : Vec d ↦ A ^ 2) Q :=
      integrableOn_const hQtop
    have hfun : (fun x ↦ (f x - A) ^ 2) =
        fun x ↦ f x ^ 2 - 2 * A * f x + A ^ 2 := by
      funext x
      ring
    rw [hfun]
    exact (hf2.sub hlinear).add hconstSq
  have havg : averageOn P (fun x ↦ f x - A) = averageOn P f - A := by
    unfold averageOn volumeAverage
    rw [integral_sub hfP hconstP, setIntegral_const, smul_eq_mul,
      measureReal_def]
    have hne : (volume P).toReal ≠ 0 := hPpos.ne'
    field_simp
  rw [← havg]
  exact (abs_volumeAverage_le_normalizedL2On hPmeas hPpos hcenterP
    (hcenterSqQ.mono_set hsub)).trans
      (normalizedL2On_subcube_le_sqrt_inv_pow hr hsub hcenterSqQ)

/-- Mean comparison with the explicit `r^{-d/2}` averaging price. -/
theorem abs_averageOn_subcube_sub_averageOn_unitCube_le_rpow
    {z p : Vec d} {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} (hsub : axisCube p r ⊆ axisCube z 1)
    (hf : IntegrableOn f (axisCube z 1))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (axisCube z 1)) :
    |averageOn (axisCube p r) f - averageOn (axisCube z 1) f| ≤
      r ^ (-(d : ℝ) / 2) *
        normalizedL2On (axisCube z 1)
          (fun x ↦ f x - averageOn (axisCube z 1) f) := by
  rw [← sqrt_inv_pow_eq_rpow_neg_natCast_div_two hr]
  exact abs_averageOn_subcube_sub_averageOn_unitCube_le hr hsub hf hf2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
