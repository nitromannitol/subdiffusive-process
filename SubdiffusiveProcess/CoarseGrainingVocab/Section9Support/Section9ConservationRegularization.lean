import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRadial
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationCalculus

/-! Bounded regularizations of the Euclidean quadratic Lyapunov function. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec contDiff_vecNormSq
open Filter Topology SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

theorem hasDerivAt_regularizedQuadratic {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    HasDerivAt (fun t : ℝ ↦ (1 + t) / (1 + eps * (1 + t)))
      (((1 + eps * (1 + q))⁻¹) ^ 2) q := by
  have hV : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 q := (hasDerivAt_id q).const_add 1
  have hden : HasDerivAt (fun t : ℝ ↦ 1 + eps * (1 + t)) eps q :=
    by simpa only [mul_one] using (hV.const_mul eps).const_add 1
  have hpos : 0 < 1 + eps * (1 + q) := by positivity
  have hne : 1 + eps * (1 + q) ≠ 0 := by linarith
  have hq' := HasDerivAt.div hV hden hne
  refine HasDerivAt.congr_deriv hq' ?_
  field_simp
  ring

theorem hasDerivAt_regularizedQuadraticD {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    HasDerivAt (fun t : ℝ ↦ ((1 + eps * (1 + t))⁻¹) ^ 2)
      (-2 * eps * ((1 + eps * (1 + q))⁻¹) ^ 3) q := by
  set f : ℝ → ℝ := fun t ↦ 1 + eps * (1 + t) with hf
  have hden : HasDerivAt f eps q :=
    by simpa only [mul_one] using (((hasDerivAt_id q).const_add 1).const_mul eps).const_add 1
  have hq0 : 1 + eps * (1 + q) ≠ 0 := by positivity
  have hne : f q ≠ 0 := by
    simp only [hf]
    exact hq0
  have h := (hden.inv hne).pow 2
  refine HasDerivAt.congr_deriv h ?_
  norm_num only [hf, Pi.inv_apply]
  field_simp [hq0]

theorem contDiff_regularizedQuadraticComplement {d : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d ↦ (eps * (1 + eps * (1 + vecNormSq x)))⁻¹) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d ↦ eps * (1 + eps * (1 + vecNormSq x))) := by
    apply ContDiff.mul contDiff_const
    apply ContDiff.add contDiff_const
    exact ContDiff.mul contDiff_const
      (ContDiff.add contDiff_const (contDiff_vecNormSq))
  refine ContDiff.inv hf ?_
  intro x
  have hq := vecNormSq_nonneg x
  positivity

theorem regularizedComplement_le_radial {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    (eps * (1 + eps * (1 + q)))⁻¹ ≤ (eps⁻¹) ^ 2 * (1 + q)⁻¹ := by
  have h1 : 0 < eps ^ 2 * (1 + q) :=
    mul_pos (pow_pos heps 2) (by linarith)
  have h2 : eps ^ 2 * (1 + q) ≤ eps * (1 + eps * (1 + q)) := by
    have hr : eps * (1 + eps * (1 + q)) = eps + eps ^ 2 * (1 + q) := by ring
    rw [hr]
    exact le_add_of_nonneg_left (le_of_lt heps)
  have h3 := inv_anti₀ h1 h2
  simpa only [mul_inv, inv_pow] using h3

theorem coeffFluxDiv_const_add {d : ℕ} (c w : Vec d → ℝ) (A : ℝ) (x : Vec d) :
    coeffFluxDiv c (fun y ↦ A + w y) x = coeffFluxDiv c w x := by
  simp only [coeffFluxDiv, euclideanCoordDeriv, fderiv_const_add]

theorem regularizedQuadratic_eq_const_sub {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    (1 + q) / (1 + eps * (1 + q)) =
      eps⁻¹ - (eps * (1 + eps * (1 + q)))⁻¹ := by
  have h1 : eps ≠ 0 := heps.ne'
  have hd : 1 + eps * (1 + q) ≠ 0 := by positivity
  have e1 : eps⁻¹ = (1 + eps * (1 + q)) * (eps * (1 + eps * (1 + q)))⁻¹ := by
    rw [mul_inv, mul_comm eps⁻¹ (1 + eps * (1 + q))⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hd, one_mul]
  have e2 : eps * (eps * (1 + eps * (1 + q)))⁻¹ = (1 + eps * (1 + q))⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  symm
  calc eps⁻¹ - (eps * (1 + eps * (1 + q)))⁻¹
      = (1 + q) * (eps * (eps * (1 + eps * (1 + q)))⁻¹) := by
        rw [e1]; ring
    _ = (1 + q) / (1 + eps * (1 + q)) := by
        rw [e2, div_eq_mul_inv]

theorem radialBarrier_two {d : ℕ} (x : Vec d) :
    radialBarrier 1 2 x = (1 + vecNormSq x)⁻¹ := by
  unfold radialBarrier radialProfile
  norm_num [Real.rpow_neg_one]

theorem regularized_square_decay {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    (1 + q) * ((1 + eps * (1 + q))⁻¹)^2 ≤
      (eps⁻¹)^2 * (1 + q)⁻¹ := by
  have hV : 0 < 1 + q := by positivity
  have hs : 0 < 1 + eps * (1 + q) := by positivity
  have hne : eps ≠ 0 := ne_of_gt heps
  field_simp
  nlinarith [sq_nonneg (eps * (1 + q))]

theorem regularized_cube_decay {eps q cw B : ℝ}
    (heps : 0 < eps) (hq : 0 ≤ q) (hcw : 0 ≤ cw) (hB : 0 ≤ B)
    (hb : cw ≤ B * (1 + q)) :
    eps * q * cw * ((1 + eps * (1 + q))⁻¹)^3 ≤
      B * (eps⁻¹)^2 * (1 + q)⁻¹ := by
  set V := 1 + q with hVdef
  set s := 1 + eps * V with hsdef
  have hV : 0 < V := by rw [hVdef]; linarith
  have hEV : 0 < eps * V := mul_pos heps hV
  have hs : 0 < s := by rw [hsdef]; linarith
  have hqV : q ≤ V := by rw [hVdef]; linarith
  have hle : eps * V ≤ s := by rw [hsdef]; linarith
  have hcube : (eps * V)^3 ≤ s^3 := pow_le_pow_left₀ (le_of_lt hEV) hle 3
  have hc : eps^3 * V^3 ≤ s^3 := by
    calc eps^3 * V^3 = (eps * V)^3 := by ring
      _ ≤ s^3 := hcube
  have hstep : eps * V * V * (s⁻¹)^3 ≤ (eps⁻¹)^2 * V⁻¹ := by
    field_simp
    nlinarith [hc]
  have hX : 0 ≤ (s⁻¹)^3 := by positivity
  have hqcw : q * cw ≤ B * (V * V) := by
    calc q * cw ≤ V * cw := mul_le_mul_of_nonneg_right hqV hcw
      _ ≤ V * (B * V) := mul_le_mul_of_nonneg_left hb (le_of_lt hV)
      _ = B * (V * V) := by ring
  have hstep1 : eps * (q * cw) ≤ eps * (B * (V * V)) :=
    mul_le_mul_of_nonneg_left hqcw (le_of_lt heps)
  have hstep2 : eps * (q * cw) * (s⁻¹)^3 ≤ eps * (B * (V * V)) * (s⁻¹)^3 :=
    mul_le_mul_of_nonneg_right hstep1 hX
  calc eps * q * cw * (s⁻¹)^3
      = eps * (q * cw) * (s⁻¹)^3 := by ring
    _ ≤ eps * (B * (V * V)) * (s⁻¹)^3 := hstep2
    _ = B * (eps * V * V * (s⁻¹)^3) := by ring
    _ ≤ B * ((eps⁻¹)^2 * V⁻¹) := mul_le_mul_of_nonneg_left hstep hB
    _ = B * (eps⁻¹)^2 * V⁻¹ := by ring

theorem regularized_flux_algebra (a q b r eps z d : ℝ) :
    (2*a^2*z+b*(4*q*(-2*eps*a^3)+2*d*a^2))/r =
      ((2*d*b+2*z)/r)*a^2-8*eps*q*(b/r)*a^3 := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem regularized_drift_le {eps q cw v C : ℝ}
    (heps : 0 < eps) (hq : 0 ≤ q) (hcw : 0 ≤ cw) (hC : 0 ≤ C)
    (hv : v ≤ C * (1 + q)) :
    v * ((1 + eps * (1 + q))⁻¹)^2 -
      8 * eps * q * cw * ((1 + eps * (1 + q))⁻¹)^3 ≤
      C * ((1 + q) / (1 + eps * (1 + q))) := by
  have hs1 : 1 ≤ 1 + eps * (1 + q) := by
    nlinarith [mul_nonneg heps.le (show 0 ≤ 1 + q by linarith)]
  have hspos : 0 < 1 + eps * (1 + q) := by positivity
  have hsub : 0 ≤ 8 * eps * q * cw * ((1 + eps * (1 + q))⁻¹)^3 := by
    positivity
  have h2 : 0 ≤ ((1 + eps * (1 + q))⁻¹)^2 := by positivity
  have hinv : (1 + eps * (1 + q))⁻¹ ≤ 1 := (inv_le_one₀ hspos).2 hs1
  have hinv2 : ((1 + eps * (1 + q))⁻¹)^2 ≤ (1 + eps * (1 + q))⁻¹ := by
    nlinarith [inv_nonneg.mpr hspos.le]
  have hCq : 0 ≤ C * (1 + q) := by positivity
  calc v * ((1 + eps * (1 + q))⁻¹)^2 -
        8 * eps * q * cw * ((1 + eps * (1 + q))⁻¹)^3
      ≤ v * ((1 + eps * (1 + q))⁻¹)^2 := by linarith
    _ ≤ C * (1 + q) * ((1 + eps * (1 + q))⁻¹)^2 :=
        mul_le_mul_of_nonneg_right hv h2
    _ ≤ C * (1 + q) * (1 + eps * (1 + q))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv2 hCq
    _ = C * ((1 + q) / (1 + eps * (1 + q))) := by ring

noncomputable def regularizedComplementC0 {d : ℕ} (eps : ℝ) (heps : 0 < eps) :
    C₀(Vec d, ℝ) :=
  dominatedC0
    (fun x => (eps * (1 + eps * (1 + vecNormSq x)))⁻¹)
    (contDiff_regularizedQuadraticComplement heps).continuous
    (radialBarrierC0 2 (by norm_num))
    ((eps⁻¹) ^ 2)
    (by
      intro x
      have hpos : 0 ≤ vecNormSq x := vecNormSq_nonneg x
      have h1 := regularizedComplement_le_radial heps (vecNormSq_nonneg x)
      calc ‖(eps * (1 + eps * (1 + vecNormSq x)))⁻¹‖
          = (eps * (1 + eps * (1 + vecNormSq x)))⁻¹ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (eps⁻¹) ^ 2 * (1 + vecNormSq x)⁻¹ := h1
        _ = (eps⁻¹) ^ 2 * radialBarrier 1 2 x := by rw [radialBarrier_two])

theorem norm_regularized_flux_decay {eps q cw v A B : ℝ}
    (heps : 0 < eps) (hq : 0 ≤ q) (hcw : 0 ≤ cw) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hv : |v| ≤ A*(1+q)) (hb : cw ≤ B*(1+q)) :
    |v*((1+eps*(1+q))⁻¹)^2-8*eps*q*cw*((1+eps*(1+q))⁻¹)^3| ≤
      (A+8*B)*(eps⁻¹)^2*(1+q)⁻¹ := by
  have hs2 : 0 ≤ ((1+eps*(1+q))⁻¹)^2 := by positivity
  have h1 : |v*((1+eps*(1+q))⁻¹)^2| ≤ A*(eps⁻¹)^2*(1+q)⁻¹ := by
    rw [abs_mul, abs_of_nonneg hs2]
    calc |v| * ((1+eps*(1+q))⁻¹)^2 ≤ A*(1+q)*((1+eps*(1+q))⁻¹)^2 := by
          nlinarith [hv, hs2]
      _ ≤ A*(eps⁻¹)^2*(1+q)⁻¹ := by
          have h := mul_le_mul_of_nonneg_left (regularized_square_decay heps hq) hA
          linarith
  have h2 : |8*eps*q*cw*((1+eps*(1+q))⁻¹)^3| ≤ 8*B*(eps⁻¹)^2*(1+q)⁻¹ := by
    have hn : 0 ≤ 8*eps*q*cw*((1+eps*(1+q))⁻¹)^3 := by positivity
    rw [abs_of_nonneg hn]
    linarith [regularized_cube_decay heps hq hcw hB hb]
  calc |v*((1+eps*(1+q))⁻¹)^2 - 8*eps*q*cw*((1+eps*(1+q))⁻¹)^3|
      ≤ |v*((1+eps*(1+q))⁻¹)^2| + |8*eps*q*cw*((1+eps*(1+q))⁻¹)^3| := abs_sub _ _
    _ ≤ (A+8*B)*(eps⁻¹)^2*(1+q)⁻¹ := by linarith

theorem tendsto_regularizedQuadratic (q : ℝ) :
    Tendsto (fun n : ℕ ↦ (1+q)/(1+(1/((n:ℝ)+1))*(1+q))) atTop (nhds (1+q)) := by
  have h1 : Tendsto (fun n : ℕ ↦ (1/((n:ℝ)+1))) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ ↦ (1/((n:ℝ)+1))*(1+q)) atTop (nhds 0) :=
    by simpa only [zero_mul] using h1.mul_const (1 + q)
  have h3 : Tendsto (fun n : ℕ ↦ 1 + (1/((n:ℝ)+1))*(1+q)) atTop (nhds (1:ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add h2
  have h4 : Tendsto (fun n : ℕ ↦ (1+q)/(1+(1/((n:ℝ)+1))*(1+q))) atTop
      (nhds ((1+q : ℝ)/(1:ℝ))) :=
    (tendsto_const_nhds (x := (1+q : ℝ))).div h3 (by norm_num)
  simpa using h4

theorem regularizedQuadratic_nonneg_le {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    0 ≤ (1+q)/(1+eps*(1+q)) ∧ (1+q)/(1+eps*(1+q)) ≤ 1+q := by
  have hden : 0 < 1 + eps * (1 + q) := by
    nlinarith [mul_nonneg heps.le (add_nonneg zero_le_one hq)]
  constructor
  · exact div_nonneg (add_nonneg zero_le_one hq) (le_of_lt hden)
  · rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg heps.le (add_nonneg zero_le_one hq)]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
