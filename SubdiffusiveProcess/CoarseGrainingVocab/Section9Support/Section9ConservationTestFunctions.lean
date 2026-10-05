module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRegularization

@[expose] public section

/-! Operations on bounded classical test functions. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec contDiff_vecNormSq
open Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

noncomputable def translateC0 {d : ℕ} (x : Vec d) (f : C₀(Vec d, ℝ)) : C₀(Vec d, ℝ) := by
  exact f.comp ((Homeomorph.subRight x).toCocompactMap)

theorem c0_square_affine {d : ℕ} (A : ℝ) (f : C₀(Vec d, ℝ)) (x : Vec d) :
    (A+f x)^2 = A^2 + ((2*A) • f + f*f) x := by
  have h : ((2*A) • f + f*f) x = (2*A) * f x + f x * f x := by
    simp [Pi.add_apply, Pi.smul_apply]
  rw [h]
  ring

theorem hasDerivAt_distanceRegularization {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    HasDerivAt (fun t : ℝ ↦ t/(1+eps*t)) (((1+eps*q)⁻¹)^2) q := by
  have hnum : HasDerivAt (fun t : ℝ ↦ t) 1 q := hasDerivAt_id q
  have hden : HasDerivAt (fun t : ℝ ↦ 1 + eps * t) eps q := by
    simpa only [mul_one] using (hnum.const_mul eps).const_add 1
  have hne : (1 + eps * q) ≠ 0 := by positivity
  have h := hnum.div hden hne
  convert h using 1
  field_simp
  ring

theorem hasDerivAt_distanceRegularizationD {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    HasDerivAt (fun t : ℝ ↦ ((1+eps*t)⁻¹)^2) (-2*eps*((1+eps*q)⁻¹)^3) q := by
  have hne : (1:ℝ) + eps * q ≠ 0 := by
    have hmul : 0 ≤ eps * q := mul_nonneg heps.le hq
    linarith
  have hd : HasDerivAt (fun t : ℝ ↦ 1 + eps * t) eps q :=
    by simpa only [mul_one] using! ((hasDerivAt_id q).const_mul eps).const_add 1
  have h2 := (hd.inv hne).pow 2
  convert! h2 using 1
  norm_num only [Nat.reduceSub, pow_one, mul_one, Pi.inv_apply]
  field_simp [hne]

theorem distanceComplement_le_radial {eps q : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (hq : 0 ≤ q) :
    (eps*(1+eps*q))⁻¹ ≤ (eps⁻¹)^2*(1+q)⁻¹ := by
  have h1 : 0 < eps^2 * (1 + q) :=
    mul_pos (pow_pos heps 2) (by linarith)
  have h3 : eps^2 ≤ eps :=
    by simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right heps1 heps.le
  have h2 : eps^2 * (1 + q) ≤ eps * (1 + eps * q) := by
    nlinarith [h3]
  simpa only [mul_inv, inv_pow] using inv_anti₀ h1 h2

theorem coeffFluxDiv_translate {d : ℕ} (c w : Vec d → ℝ) (x z : Vec d) :
    coeffFluxDiv (fun y ↦ c (x+y)) (fun y ↦ w (x+y)) z = coeffFluxDiv c w (x+z) := by
  rw [coeffFluxDiv, coeffFluxDiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [euclideanCoordDeriv, fderiv_comp_add_left]
  exact congrArg (fun L : Vec d →L[ℝ] ℝ ↦ L (basisVec i))
    (fderiv_comp_add_left (𝕜 := ℝ) (f := fun y ↦ c y * (fderiv ℝ w y) (basisVec i)) (x := z) x)

theorem euclideanGradient_translate {d : ℕ} (c : Vec d → ℝ) (x z : Vec d) :
    euclideanGradient (fun y ↦ c (x+y)) z = euclideanGradient c (x+z) := by
  funext i
  simp only [euclideanGradient, euclideanCoordDeriv, fderiv_comp_add_left]

theorem translateC0_apply {d : ℕ} (x y : Vec d) (f : C₀(Vec d, ℝ)) :
    translateC0 x f y = f (y-x) := by
  rfl

theorem hasDerivAt_squareDistanceRegularization {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    HasDerivAt (fun t : ℝ ↦ (t/(1+eps*t))^2) (2*q*((1+eps*q)⁻¹)^3) q := by
  have h1 := hasDerivAt_distanceRegularization heps hq
  have h2 := h1.pow 2
  refine h2.congr_deriv ?_
  norm_num only [Nat.reduceSub, pow_one]
  simp only [div_eq_mul_inv]
  ring

theorem coeffFluxDiv_comp_centeredVecNormSq {d : ℕ} {c : Vec d → ℝ}
    {F Fprime Fsecond : ℝ → ℝ} (hc : Differentiable ℝ c)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (Fprime t) t)
    (hFprime : ∀ t, 0 ≤ t → HasDerivAt Fprime (Fsecond t) t) (x y : Vec d) :
    coeffFluxDiv c (fun z ↦ F (vecNormSq (z-x))) y =
      2*Fprime (vecNormSq (y-x))*vecDot (y-x) (euclideanGradient c y) +
      c y*(4*vecNormSq (y-x)*Fsecond (vecNormSq (y-x))+2*(d:ℝ)*Fprime (vecNormSq (y-x))) := by
  have hc' : Differentiable ℝ (fun y => c (x + y)) :=
    hc.comp (Differentiable.add (differentiable_const x) differentiable_id)
  have h1 := coeffFluxDiv_translate c (fun u => F (vecNormSq (u - x))) x (y - x)
  simp only [add_sub_cancel_left, add_sub_cancel] at h1
  rw [← h1, coeffFluxDiv_compVecNormSq hc' hF hFprime]
  simp only [euclideanGradient_translate c, add_sub_cancel]

theorem contDiff_distanceComplement {d : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d ↦ (eps*(1+eps*vecNormSq x))⁻¹) := by
  apply ContDiff.inv _ (fun x => ?_)
  · exact (contDiff_const.mul ((contDiff_const.add (contDiff_const.mul contDiff_vecNormSq))))
  · intro h
    have h1 : 0 < 1 + eps * vecNormSq x := by
      have : 0 ≤ eps * vecNormSq x := by
        apply mul_nonneg _ (vecNormSq_nonneg x)
        exact le_of_lt heps
      linarith
    have : 0 < eps * (1 + eps * vecNormSq x) := by
      apply mul_pos heps h1
    exact (ne_of_gt this) h

theorem tendsto_distanceRegularization (q : ℝ) :
    Tendsto (fun n : ℕ ↦ q/(1+(1/((n:ℝ)+1))*q)) atTop (nhds q) := by
  have h := tendsto_regularizedQuadratic (q-1)
  have he : 1+(q-1)=q := by ring
  simpa only [he] using h

theorem paired_flux_algebra (d b s q rho eps : ℝ) :
    (2*(2*q*((1+eps*q)⁻¹)^3)*s+b*(4*q*(2*((1+eps*q)⁻¹)^3-6*eps*q*((1+eps*q)⁻¹)^4)+2*d*(2*q*((1+eps*q)⁻¹)^3)))/rho =
      2*(q/(1+eps*q))*((2*((1+eps*q)⁻¹)^2*s+b*(4*q*(-2*eps*((1+eps*q)⁻¹)^3)+2*d*((1+eps*q)⁻¹)^2))/rho)+8*q*(b/rho)*((1+eps*q)⁻¹)^4 := by
  by_cases h : 1 + eps*q = 0
  · simp [h]
  · by_cases hr : rho = 0
    · simp [hr]
    · field_simp
      ring

theorem distanceRegularization_eq_const_sub {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    q/(1+eps*q) = eps⁻¹-(eps*(1+eps*q))⁻¹ := by
  have hn : 1+eps*q ≠ 0 := by positivity
  field_simp
  ring

noncomputable def distanceComplementC0 {d : ℕ} (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    C₀(Vec d, ℝ) :=
  dominatedC0 (fun x : Vec d => (eps * (1 + eps * vecNormSq x))⁻¹)
    (contDiff_distanceComplement heps).continuous
    (radialBarrierC0 2 (by norm_num)) (eps⁻¹ ^ 2)
    (by
      intro x
      change |(eps * (1 + eps * vecNormSq x))⁻¹| ≤ _ * radialBarrier 1 2 x
      have hq := vecNormSq_nonneg x
      rw [abs_of_nonneg (by positivity), radialBarrier_two]
      exact distanceComplement_le_radial heps heps1 hq)

theorem square_distance_drift_le {eps q a cw u C B : ℝ}
    (heps : 0 < eps) (hq : 0 ≤ q) (ha : 0 ≤ a) (hcw : 0 ≤ cw)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hu : u ≤ C*(a+q/(1+eps*q))) (hb : cw ≤ B*(a+q)) :
    2*(q/(1+eps*q))*u+8*q*cw*((1+eps*q)⁻¹)^4 ≤
      (2*C+8*B)*(a*(q/(1+eps*q))+(q/(1+eps*q))^2) := by
  have _ := hC
  have _ := hcw
  rw [div_eq_mul_inv] at hu ⊢
  set h := (1+eps*q)⁻¹ with hh
  have ep : 0 < 1 + eps*q := by nlinarith
  have hpos : 0 < h := inv_pos.mpr ep
  have hle : h ≤ 1 := (inv_le_one₀ ep).2 (by nlinarith)
  have hnn : 0 ≤ h := le_of_lt hpos
  have h2nn : 0 ≤ h*h := mul_nonneg hnn hnn
  have hsq : h*h ≤ h := by nlinarith
  have h2le1 : h*h ≤ 1 := le_trans hsq hle
  have h4 : h^4 ≤ h*h := by nlinarith [h2le1, h2nn]
  have h4h : h^4 ≤ h := le_trans h4 hsq
  have aq0 : 0 ≤ a*q := mul_nonneg ha hq
  have q20 : 0 ≤ q*q := mul_nonneg hq hq
  have t1 : 2*(q*h)*u ≤ 2*C*(a*(q*h)+(q*h)^2) := by
    calc 2*(q*h)*u ≤ 2*(q*h)*(C*(a+q*h)) :=
          mul_le_mul_of_nonneg_left hu (by nlinarith)
      _ = 2*C*(a*(q*h)+(q*h)^2) := by ring
  have t2 : 8*q*cw*h^4 ≤ 8*B*(a*(q*h)+(q*h)^2) := by
    calc 8*q*cw*h^4 = (8*q)*(cw*h^4) := by ring
      _ ≤ (8*q)*(B*(a+q)*h^4) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hb (pow_nonneg hnn 4)) (by linarith)
      _ = 8*B*(a*(q*h^4)+q^2*h^4) := by ring
      _ ≤ 8*B*(a*(q*h)+q^2*h^2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            nlinarith [mul_le_mul_of_nonneg_right h4h aq0,
                       mul_le_mul_of_nonneg_right h4 q20]
      _ = 8*B*(a*(q*h)+(q*h)^2) := by ring
  have rhs : (2*C+8*B)*(a*(q*h)+(q*h)^2)
      = 2*C*(a*(q*h)+(q*h)^2) + 8*B*(a*(q*h)+(q*h)^2) := by ring
  linarith [t1, t2, rhs]

theorem distanceRegularization_nonneg_le {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    0 ≤ q/(1+eps*q) ∧ q/(1+eps*q) ≤ q ∧ q/(1+eps*q) ≤ eps⁻¹ := by
  have h1 : 0 < 1 + eps * q := by positivity
  refine ⟨div_nonneg hq h1.le, ?_, ?_⟩
  · rw [div_le_iff₀ h1]
    have h2 : 0 ≤ eps * q * q := mul_nonneg (mul_nonneg heps.le hq) hq
    nlinarith
  · rw [div_le_iff₀ h1]
    have h2 : eps⁻¹ * (1 + eps * q) = eps⁻¹ + q := by field_simp
    have h3 : 0 ≤ eps⁻¹ := inv_nonneg.2 heps.le
    linarith

theorem distance_decay_scalar {eps q a : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (hq : 0 ≤ q) (ha : 1 ≤ a) :
    (a+q)*((1+eps*q)⁻¹)^2 ≤ a*(eps⁻¹)^2*(1+q)⁻¹ := by
  have hq2 : 0 ≤ eps * q := mul_nonneg heps.le hq
  have hpos1 : 0 < 1 + eps * q := by linarith
  have hY : 0 < 1 + q := by linarith
  have hX : 0 < (1 + eps * q) ^ 2 := pow_pos hpos1 2
  have hE : 0 < eps ^ 2 := pow_pos heps 2
  have hEY : 0 < eps ^ 2 * (1 + q) := mul_pos hE hY
  have hw : 0 ≤ 1 + eps + 2 * eps * q := by linarith
  have v1 : 0 ≤ a * (1 - eps) * (1 + eps + 2 * eps * q) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans ha) (sub_nonneg.mpr heps1)) hw
  have u2 : 0 ≤ eps * eps * q * (1 + q) * (a - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_self_nonneg eps) hq) hY.le) (sub_nonneg.mpr ha)
  have hkey : (a + q) * (eps ^ 2 * (1 + q)) ≤ a * (1 + eps * q) ^ 2 := by
    nlinarith [v1, u2]
  have hR : a * (eps ^ 2)⁻¹ * (1 + q)⁻¹ = a * ((eps ^ 2) * (1 + q))⁻¹ := by
    rw [mul_inv]
    ring
  rw [inv_pow, inv_pow, hR, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_iff₀ hX, div_mul_eq_mul_div, le_div_iff₀ hEY]
  exact hkey

theorem coeffFluxDiv_centeredNormSq {d : ℕ} {c : Vec d → ℝ} (hc : Differentiable ℝ c) (x y : Vec d) :
    coeffFluxDiv c (fun z ↦ vecNormSq (z-x)) y =
      2*(d:ℝ)*c y+2*vecDot (y-x) (euclideanGradient c y) := by
  have h := coeffFluxDiv_comp_centeredVecNormSq hc
    (F := fun t : ℝ => t) (Fprime := fun _ => 1) (Fsecond := fun _ => 0)
    (fun t _ => hasDerivAt_id t) (fun t _ => hasDerivAt_const t (1:ℝ)) x y
  simp only [mul_zero, mul_one] at h
  rw [h]
  ring

theorem distance_flux_algebra (d b s q rho eps : ℝ) :
    (2*((1+eps*q)⁻¹)^2*s+b*(4*q*(-2*eps*((1+eps*q)⁻¹)^3)+2*d*((1+eps*q)⁻¹)^2))/rho =
      ((2*d*b+2*s)/rho)*((1+eps*q)⁻¹)^2-8*eps*q*(b/rho)*((1+eps*q)⁻¹)^3 := by
  simp only [div_eq_mul_inv]
  ring

theorem distance_drift_le {eps q a cw v C : ℝ}
    (heps : 0 < eps) (hq : 0 ≤ q) (ha : 0 ≤ a) (hcw : 0 ≤ cw) (hC : 0 ≤ C)
    (hv : v ≤ C*(a+q)) :
    v*((1+eps*q)⁻¹)^2-8*eps*q*cw*((1+eps*q)⁻¹)^3 ≤ C*(a+q/(1+eps*q)) := by
  set r := (1+eps*q)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (inv_le_one₀ (show 0 < 1+eps*q by positivity)).2 (by nlinarith [mul_nonneg heps.le hq])
  have h2 : r^2 ≤ r := by nlinarith [sq_nonneg r]
  have h21 := h2.trans hr1
  have h1 : C*a*r^2 ≤ C*a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h21 (mul_nonneg hC ha)
  have hq2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hq)
  have hv2 := mul_le_mul_of_nonneg_right hv (sq_nonneg r)
  have hterm : 0 ≤ 8*eps*q*cw*r^3 := by positivity
  simp only [div_eq_mul_inv]
  nlinarith

theorem carre_distance_decay {eps q a cw B : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hq : 0 ≤ q) (ha : 1 ≤ a) (hcw : 0 ≤ cw) (hB : 0 ≤ B) (hb : cw ≤ B*(a+q)) :
    |8*q*cw*((1+eps*q)⁻¹)^4| ≤ 8*B*a*(eps⁻¹)^3*(1+q)⁻¹ := by
  set r : ℝ := (1+eps*q)⁻¹ with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (inv_le_one₀ (show 0<1+eps*q by positivity)).2 (by nlinarith [mul_nonneg heps.le hq])
  have hreg := distanceRegularization_nonneg_le heps hq
  have hqr : q*r ≤ eps⁻¹ := by
    have h2 := hreg.2.2
    rw [div_eq_mul_inv, ← hrdef] at h2
    exact h2
  have hrr : r*r ≤ r := by nlinarith [hr1, hr0]
  have hqr2 : q*r*r ≤ eps⁻¹ := by
    have h1 : q*r*r ≤ q*r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 (mul_nonneg hq hr0)
    linarith [hqr, h1]
  have habs : |8*q*cw*r^4| = 8*q*cw*r^4 := abs_of_nonneg (by positivity)
  have hscale : 0 ≤ 8*eps⁻¹*r^2 := by positivity
  have h3 := mul_le_mul_of_nonneg_right hb hscale
  have hdec := distance_decay_scalar heps heps1 hq ha
  have hmul : 0 ≤ 8*B*eps⁻¹ := by positivity
  have h4 := mul_le_mul_of_nonneg_left hdec hmul
  calc |8*q*cw*((1+eps*q)⁻¹)^4| = 8*q*cw*r^4 := habs
    _ = 8*cw*r^2*(q*r*r) := by ring
    _ ≤ 8*cw*r^2*eps⁻¹ := by
        exact mul_le_mul_of_nonneg_left hqr2 (by positivity)
    _ ≤ 8*B*(a+q)*r^2*eps⁻¹ := by nlinarith [h3]
    _ ≤ 8*eps⁻¹*B*(a*eps⁻¹^2*(1+q)⁻¹) := by nlinarith [h4]
    _ = 8*B*a*(eps⁻¹)^3*(1+q)⁻¹ := by ring

theorem hasDerivAt_squareDistanceRegularizationD {eps q : ℝ} (heps : 0 < eps) (hq : 0 ≤ q) :
    HasDerivAt (fun t : ℝ ↦ 2*t*((1+eps*t)⁻¹)^3)
      (2*((1+eps*q)⁻¹)^3-6*eps*q*((1+eps*q)⁻¹)^4) q := by
  have hden : HasDerivAt (fun t : ℝ => 1 + eps * t) eps q := by
    simpa only [mul_one] using! ((hasDerivAt_id q).const_mul eps).const_add 1
  have hn : (1:ℝ) + eps * q ≠ 0 := ne_of_gt (by positivity)
  have h := ((hasDerivAt_id q).const_mul 2).mul ((hden.inv hn).pow 3)
  convert! h using 1
  norm_num only [Nat.reduceSub, pow_one, mul_one, Pi.pow_apply, Pi.inv_apply, id_eq]
  field_simp [hn]
  ring

theorem norm_distance_flux_decay {eps q a cw v C B : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hq : 0 ≤ q) (ha : 1 ≤ a)
    (hcw : 0 ≤ cw) (hC : 0 ≤ C) (hB : 0 ≤ B) (hv : |v| ≤ C*(a+q)) (hb : cw ≤ B*(a+q)) :
    |v*((1+eps*q)⁻¹)^2-8*eps*q*cw*((1+eps*q)⁻¹)^3| ≤
      (C+8*B)*a*(eps⁻¹)^2*(1+q)⁻¹ := by
  have hnnq : 0 ≤ eps*q := mul_nonneg heps.le hq
  have haq : 0 ≤ a+q := by linarith
  have hp : (0:ℝ) < 1+eps*q := by linarith
  have hr0 : 0 ≤ (1+eps*q)⁻¹ := le_of_lt (inv_pos.mpr hp)
  have hr2 : 0 ≤ ((1+eps*q)⁻¹)^2 := pow_nonneg hr0 2
  have hr3 : 0 ≤ ((1+eps*q)⁻¹)^3 := pow_nonneg hr0 3
  -- Step 1: eps*q*r ≤ 1
  have hkey : eps*q*(1+eps*q)⁻¹ ≤ 1 := by
    have h : eps*q*(1+eps*q)⁻¹ = eps*q/(1+eps*q) := by field_simp
    rw [h]
    exact (div_le_one hp).mpr (by linarith)
  -- Step 2: triangle inequality
  have hstep2 : |v*((1+eps*q)⁻¹)^2 - 8*eps*q*cw*((1+eps*q)⁻¹)^3|
      ≤ |v| *((1+eps*q)⁻¹)^2 + 8*eps*q*cw*((1+eps*q)⁻¹)^3 := by
    calc |v*((1+eps*q)⁻¹)^2 - 8*eps*q*cw*((1+eps*q)⁻¹)^3|
        ≤ |v*((1+eps*q)⁻¹)^2| + |8*eps*q*cw*((1+eps*q)⁻¹)^3| := abs_sub _ _
      _ = |v| *((1+eps*q)⁻¹)^2 + 8*eps*q*cw*((1+eps*q)⁻¹)^3 := by
          rw [abs_mul, abs_of_nonneg hr2,
            abs_of_nonneg (show 0≤8*eps*q*cw*((1+eps*q)⁻¹)^3 by positivity)]
  -- Step 3: bound each piece
  have h1 : |v| *((1+eps*q)⁻¹)^2 ≤ C*(a+q)*((1+eps*q)⁻¹)^2 :=
    mul_le_mul_of_nonneg_right hv hr2
  have h2 : 8*eps*q*cw*((1+eps*q)⁻¹)^3 ≤ 8*B*(a+q)*((1+eps*q)⁻¹)^2 := by
    calc 8*eps*q*cw*((1+eps*q)⁻¹)^3
        ≤ 8*eps*q*(B*(a+q))*((1+eps*q)⁻¹)^3 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb (by positivity)) hr3
      _ ≤ 8*(B*(a+q))*((1+eps*q)⁻¹)^2 := by
          have h : 8*eps*q*(B*(a+q))*((1+eps*q)⁻¹)^3
              = 8*(B*(a+q))*((1+eps*q)⁻¹)^2*(eps*q*(1+eps*q)⁻¹) := by ring
          rw [h]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hkey (by positivity : 0≤8*(B*(a+q))*((1+eps*q)⁻¹)^2)
      _ = 8*B*(a+q)*((1+eps*q)⁻¹)^2 := by ring
  have h3 : C*(a+q)*((1+eps*q)⁻¹)^2 + 8*B*(a+q)*((1+eps*q)⁻¹)^2
      = (C+8*B)*(a+q)*((1+eps*q)⁻¹)^2 := by ring
  have hbound : |v*((1+eps*q)⁻¹)^2 - 8*eps*q*cw*((1+eps*q)⁻¹)^3|
      ≤ (C+8*B)*(a+q)*((1+eps*q)⁻¹)^2 :=
    by linarith [hstep2, h1, h2, h3]
  -- Step 4: scale the distance decay scalar
  have hC8 : 0 ≤ C+8*B := add_nonneg hC (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB)
  calc |v*((1+eps*q)⁻¹)^2 - 8*eps*q*cw*((1+eps*q)⁻¹)^3|
      ≤ (C+8*B)*(a+q)*((1+eps*q)⁻¹)^2 := hbound
    _ ≤ (C+8*B)*a*(eps⁻¹)^2*(1+q)⁻¹ := by
        have h4 := mul_le_mul_of_nonneg_left (distance_decay_scalar heps heps1 hq ha) hC8
        have e1 : (C+8*B)*(a+q)*((1+eps*q)⁻¹)^2
            = (C+8*B)*((a+q)*((1+eps*q)⁻¹)^2) := by ring
        have e2 : (C+8*B)*a*(eps⁻¹)^2*(1+q)⁻¹
            = (C+8*B)*(a*(eps⁻¹)^2*(1+q)⁻¹) := by ring
        rw [e1, e2]
        exact h4

theorem contDiff_c0_square_affine {d : ℕ} (w : C₀(Vec d, ℝ))
    (hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ)) (A : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (((2*A) • w+w*w) : Vec d → ℝ) := by
  exact (hw.const_smul (2*A)).add (hw.mul hw)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
