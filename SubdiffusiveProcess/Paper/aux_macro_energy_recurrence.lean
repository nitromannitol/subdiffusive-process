import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.aux_source_primitive
import SubdiffusiveProcess.Paper.aux_macro_moment_bank
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.lem_primitive
import SubdiffusiveProcess.Paper.quadratic_inverse_response
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Sobolev.WeakGradientUpstream
import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import Homogenization.Sobolev.H1.BasicLemmas

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise Distributions
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

attribute [local instance] Classical.propDecidable

-- ===== MER01_Geometry =====
/-- A centred cube dilated by `s > 0` is the centred cube of the dilated centre and side. -/
theorem aux_aux_macro_energy_recurrence_cube_smul {d : ℕ} (z : SpatialCoordinates d) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (h' : 0 < s * r) :
    (centeredCube (s • z) (s * r) h' : Set (SpatialCoordinates d)) =
      s • (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  change Metric.ball (s • z) (s * r / 2) = s • Metric.ball z (r / 2)
  rw [_root_.smul_ball hs.ne' z (r / 2), Real.norm_eq_abs, abs_of_pos hs, mul_div_assoc]

/-- The unit-side special case (the physical image of `centeredCube z 1`). -/
theorem aux_aux_macro_energy_recurrence_cube_smul_one {d : ℕ} (z : SpatialCoordinates d) {s : ℝ}
    (hs : 0 < s) (h1 : (0 : ℝ) < 1) (h' : 0 < s) :
    (centeredCube (s • z) s h' : Set (SpatialCoordinates d)) =
      s • (centeredCube z 1 h1 : Set (SpatialCoordinates d)) := by
  change Metric.ball (s • z) (s / 2) = s • Metric.ball z (1 / 2)
  rw [_root_.smul_ball hs.ne' z (1 / 2), Real.norm_eq_abs, abs_of_pos hs, mul_one_div]

/-- Dilation of a ball-cube intersection. -/
theorem aux_aux_macro_energy_recurrence_ball_inter_smul {d : ℕ} (x : SpatialCoordinates d) (ρ : ℝ)
    (A : Set (SpatialCoordinates d)) {s : ℝ} (hs : 0 < s) :
    s • (Metric.ball x ρ ∩ A) = Metric.ball (s • x) (s * ρ) ∩ s • A := by
  rw [Set.smul_set_inter₀ hs.ne', _root_.smul_ball hs.ne', Real.norm_eq_abs, abs_of_pos hs]

/-- Pull an almost-everywhere statement on a dilated set back to the original set. -/
theorem aux_aux_macro_energy_recurrence_ae_pull {d : ℕ} {s : ℝ} (hs : 0 < s) {A B : Set (SpatialCoordinates d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : B = s • A)
    {p : SpatialCoordinates d → Prop} (h : ∀ᵐ y ∂volume.restrict B, p y) :
    ∀ᵐ x ∂volume.restrict A, p (s • x) := by
  rw [ae_restrict_iff' hB] at h
  rw [ae_restrict_iff' hA]
  filter_upwards [(Measure.quasiMeasurePreserving_smul
    (volume : Measure (SpatialCoordinates d)) hs.ne').ae h] with x hx hxA
  apply hx
  rw [hAB]
  exact Set.smul_mem_smul_set hxA

/-- Push an almost-everywhere statement on a set to its dilate, reading it at `s⁻¹ • y`. -/
theorem aux_aux_macro_energy_recurrence_ae_push {d : ℕ} {s : ℝ} (hs : 0 < s) {A B : Set (SpatialCoordinates d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : B = s • A)
    {p : SpatialCoordinates d → Prop} (h : ∀ᵐ x ∂volume.restrict A, p x) :
    ∀ᵐ y ∂volume.restrict B, p (s⁻¹ • y) := by
  have hBA : A = s⁻¹ • B := by
    rw [hAB, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  exact aux_aux_macro_energy_recurrence_ae_pull (inv_pos.2 hs) hB hA hBA h

/-- Change of variables on a dilated set. -/
theorem aux_aux_macro_energy_recurrence_setIntegral_smul {d : ℕ} {s : ℝ} (hs : 0 < s) (A : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) :
    ∫ y in s • A, f y = s ^ d * ∫ x in A, f (s • x) := by
  rw [Measure.setIntegral_comp_smul_of_pos (volume : Measure (SpatialCoordinates d)) f A hs,
    Module.finrank_fin_fun, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'),
    one_mul]

/-- Real volume of a dilated set. -/
theorem aux_aux_macro_energy_recurrence_volume_real_smul {d : ℕ} {s : ℝ} (hs : 0 < s) (A : Set (SpatialCoordinates d)) :
    volume.real (s • A) = s ^ d * volume.real A := by
  rw [Measure.real, Measure.addHaar_smul, Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (pow_pos hs d)]
  rfl

/-- Localized integrals over a dilated domain. `∫ y in s • S, f y ∂(vol|s•A)` is
`s^d ∫ x in S, f (s x) ∂(vol|A)`. -/
theorem aux_aux_macro_energy_recurrence_setIntegral_restrict_smul {d : ℕ} {s : ℝ} (hs : 0 < s)
    {A S : Set (SpatialCoordinates d)} (hS : MeasurableSet S)
    (hsS : MeasurableSet (s • S)) (f : SpatialCoordinates d → ℝ) :
    ∫ y in s • S, f y ∂(volume.restrict (s • A)) =
      s ^ d * ∫ x in S, f (s • x) ∂(volume.restrict A) := by
  rw [Measure.restrict_restrict hsS, Measure.restrict_restrict hS,
    ← Set.smul_set_inter₀ hs.ne', aux_aux_macro_energy_recurrence_setIntegral_smul hs]

/-- The same over the whole dilated domain. -/
theorem aux_aux_macro_energy_recurrence_integral_restrict_smul {d : ℕ} {s : ℝ} (hs : 0 < s)
    (A : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    ∫ y in s • A, f y = s ^ d * ∫ x in A, f (s • x) :=
  aux_aux_macro_energy_recurrence_setIntegral_smul hs A f

-- ===== MER02_Transport =====
theorem aux_aux_macro_energy_recurrence_cast_H1_toFun {d : ℕ} {U V : Set (SpatialCoordinates d)} (hUV : U = V)
    (u : Homogenization.H1Function U) : (hUV ▸ u).toFun = u.toFun := by
  subst hUV; rfl

theorem aux_aux_macro_energy_recurrence_cast_H1_grad {d : ℕ} {U V : Set (SpatialCoordinates d)} (hUV : U = V)
    (u : Homogenization.H1Function U) : (hUV ▸ u).grad = u.grad := by
  subst hUV; rfl

theorem aux_aux_macro_energy_recurrence_cast_H10_toFun {d : ℕ} {U V : Set (SpatialCoordinates d)} (hUV : U = V)
    (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  subst hUV; rfl

theorem aux_aux_macro_energy_recurrence_cast_H10_grad {d : ℕ} {U V : Set (SpatialCoordinates d)} (hUV : U = V)
    (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.grad = u.toH1Function.grad := by
  subst hUV; rfl

/-- Weak-graph transport along a dilation. -/
theorem aux_aux_macro_energy_recurrence_weak_unscale {d : ℕ} {Ω Ω' : Opens (SpatialCoordinates d)} {a : ℝ}
    (ha : 0 < a) (hΩ : (Ω : Set (SpatialCoordinates d)) = a • (Ω' : Set (SpatialCoordinates d)))
    (v : weakSobolevGraph Ω) :
    ∃ w : weakSobolevGraph Ω',
      ((w : SobolevData Ω').1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Ω' : Set (SpatialCoordinates d))]
        (fun y => ((v : SobolevData Ω).1 : SpatialCoordinates d → ℝ) (a • y)) ∧
      ∀ i : Fin d, ((w : SobolevData Ω').2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Ω' : Set (SpatialCoordinates d))]
        (fun y => a * ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) (a • y)) := by
  obtain ⟨u, hu, hgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph v
  let uS : Homogenization.H1Function (a • (Ω' : Set (SpatialCoordinates d))) := hΩ ▸ u
  let u1 : Homogenization.H1Function (Ω' : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.unscale ha uS
  obtain ⟨w, hw, hwgrad⟩ := SubdiffusiveProcess.Lane4.exists_weakSobolevGraph_of_nativeH1
    (Om := Ω') u1
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw] with y hy
    rw [hy]
    change uS.toFun (a • y) = _
    rw [aux_aux_macro_energy_recurrence_cast_H1_toFun hΩ u]
    exact congrFun hu (a • y)
  · intro i
    filter_upwards [hwgrad i] with y hy
    rw [hy]
    change (a • uS.grad (a • y)) i = _
    rw [aux_aux_macro_energy_recurrence_cast_H1_grad hΩ u, hgrad]
    rfl

/-- Killed-graph transport along a dilation. -/
theorem aux_aux_macro_energy_recurrence_killed_unscale {d : ℕ} {Ω Ω' : Opens (SpatialCoordinates d)} {a : ℝ}
    (ha : 0 < a) (hΩ : (Ω : Set (SpatialCoordinates d)) = a • (Ω' : Set (SpatialCoordinates d)))
    (v : killedSobolevGraph Ω) :
    ∃ w : killedSobolevGraph Ω',
      ((w : SobolevData Ω').1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Ω' : Set (SpatialCoordinates d))]
        (fun y => ((v : SobolevData Ω).1 : SpatialCoordinates d → ℝ) (a • y)) ∧
      ∀ i : Fin d, ((w : SobolevData Ω').2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Ω' : Set (SpatialCoordinates d))]
        (fun y => a * ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) (a • y)) := by
  obtain ⟨u, hu, hgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph v
  let uS : Homogenization.H10Function (a • (Ω' : Set (SpatialCoordinates d))) := hΩ ▸ u
  let u1 : Homogenization.H10Function (Ω' : Set (SpatialCoordinates d)) :=
    Homogenization.H10Function.unscale ha uS
  obtain ⟨w, hw, hwgrad⟩ := SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10
    (Ω := Ω') u1
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw] with y hy
    rw [hy]
    change (Homogenization.H10Function.unscale ha uS).toH1Function.toFun y = _
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_toFun, aux_aux_macro_energy_recurrence_cast_H10_toFun hΩ u]
    exact congrFun hu (a • y)
  · intro i
    filter_upwards [hwgrad i] with y hy
    rw [hy]
    change (Homogenization.H10Function.unscale ha uS).toH1Function.grad y i = _
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_grad, aux_aux_macro_energy_recurrence_cast_H10_grad hΩ u, hgrad]
    rfl

-- ===== MER03_Scaling =====
theorem aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (u v : SobolevData Ω) :
    sobolevCoefficientForm a u v = ∑ i : Fin d,
      ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x * (u.2 i x * v.2 i x) := by
  change weightedGradientForm a.val (sobolevGradient u) (sobolevGradient v) = _
  rw [weightedGradientForm_apply]
  rfl

/-- Integral over a dilated open domain, stated with the domain as an `Opens`. -/
theorem aux_aux_macro_energy_recurrence_integral_T {d : ℕ} {s : ℝ} (hs : 0 < s) {Q T : Opens (SpatialCoordinates d)}
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ) :
    ∫ y in (T : Set (SpatialCoordinates d)), f y =
      s ^ d * ∫ x in (Q : Set (SpatialCoordinates d)), f (s • x) := by
  rw [hT]; exact aux_aux_macro_energy_recurrence_setIntegral_smul hs _ f

theorem aux_aux_macro_energy_recurrence_setIntegral_T {d : ℕ} {s : ℝ} (hs : 0 < s) {Q T : Opens (SpatialCoordinates d)}
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S) (hsS : MeasurableSet (s • S))
    (f : SpatialCoordinates d → ℝ) :
    ∫ y in s • S, f y ∂(volume.restrict (T : Set (SpatialCoordinates d))) =
      s ^ d * ∫ x in S, f (s • x) ∂(volume.restrict (Q : Set (SpatialCoordinates d))) := by
  rw [hT]; exact aux_aux_macro_energy_recurrence_setIntegral_restrict_smul hs hS hsS f

/-- Pulled-back coefficient identity: `aT (s x) = c⁻¹ a' x` a.e. on `Q`. -/
theorem aux_aux_macro_energy_recurrence_coef_pull {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s c : ℝ}
    (hc : 0 < c) (aT : PositiveCoefficient T) (a' : PositiveCoefficient Q)
    (hcoef : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      a'.val x = c * aT.val (s • x)) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      aT.val (s • x) = c⁻¹ * a'.val x := by
  filter_upwards [hcoef] with x hx
  rw [hx, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Pulled-back gradient identity: `U.2 i (s x) = s⁻¹ * u.2 i x` a.e. on `Q`. -/
theorem aux_aux_macro_energy_recurrence_grad_pull {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s : ℝ} (hs : 0 < s)
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (U : SobolevData T) (u : SobolevData Q) (i : Fin d)
    (hU : ((U.2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => s⁻¹ * (u.2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y)) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (U.2 i : SpatialCoordinates d → ℝ) (s • x) = s⁻¹ * (u.2 i : SpatialCoordinates d → ℝ) x := by
  have h := aux_aux_macro_energy_recurrence_ae_pull hs Q.isOpen.measurableSet T.isOpen.measurableSet hT hU
  filter_upwards [h] with x hx
  rw [hx, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- Local energy scaling. -/
theorem aux_aux_macro_energy_recurrence_localEnergy_scale {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (aT : PositiveCoefficient T) (a' : PositiveCoefficient Q)
    (hcoef : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      a'.val x = c * aT.val (s • x))
    (U : SobolevData T) (u : SobolevData Q)
    (hU : ∀ i : Fin d, ((U.2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => s⁻¹ * (u.2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y))
    {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S) (hsS : MeasurableSet (s • S)) :
    localGradientEnergy aT hsS (sobolevGradient U) =
      c⁻¹ * s ^ d * (s⁻¹) ^ 2 * localGradientEnergy a' hS (sobolevGradient u) := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aux_aux_macro_energy_recurrence_setIntegral_T hs hT hS hsS]
  have hae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))).restrict S,
      aT.val (s • x) * ((sobolevGradient U) i (s • x)) ^ 2 =
        c⁻¹ * (s⁻¹) ^ 2 * (a'.val x * ((sobolevGradient u) i x) ^ 2) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [aux_aux_macro_energy_recurrence_coef_pull hc aT a' hcoef, aux_aux_macro_energy_recurrence_grad_pull hs hT U u i (hU i)]
      with x h1 h2
    change aT.val (s • x) * ((U.2 i : SpatialCoordinates d → ℝ) (s • x)) ^ 2 =
      c⁻¹ * (s⁻¹) ^ 2 * (a'.val x * ((u.2 i : SpatialCoordinates d → ℝ) x) ^ 2)
    rw [h1, h2]
    ring
  rw [integral_congr_ae hae, integral_const_mul]
  ring

/-- Bilinear-form scaling. -/
theorem aux_aux_macro_energy_recurrence_form_scale {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (aT : PositiveCoefficient T) (a' : PositiveCoefficient Q)
    (hcoef : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      a'.val x = c * aT.val (s • x))
    (U Φ : SobolevData T) (u ψ : SobolevData Q)
    (hU : ∀ i : Fin d, ((U.2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => s⁻¹ * (u.2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y))
    (hΦ : ∀ i : Fin d, ((ψ.2 i : DomainL2 Q) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => s * (Φ.2 i : SpatialCoordinates d → ℝ) (s • x)) :
    sobolevCoefficientForm aT U Φ =
      c⁻¹ * s ^ d * (s⁻¹) ^ 2 * sobolevCoefficientForm a' u ψ := by
  rw [aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply, aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aux_aux_macro_energy_recurrence_integral_T hs hT]
  have hae : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      aT.val (s • x) * ((U.2 i : SpatialCoordinates d → ℝ) (s • x) *
          (Φ.2 i : SpatialCoordinates d → ℝ) (s • x)) =
        c⁻¹ * (s⁻¹) ^ 2 * (a'.val x * ((u.2 i : SpatialCoordinates d → ℝ) x *
          (ψ.2 i : SpatialCoordinates d → ℝ) x)) := by
    filter_upwards [aux_aux_macro_energy_recurrence_coef_pull hc aT a' hcoef, aux_aux_macro_energy_recurrence_grad_pull hs hT U u i (hU i),
      hΦ i] with x h1 h2 h3
    rw [h1, h2, h3]
    field_simp
  rw [integral_congr_ae hae, integral_const_mul]
  ring

-- ===== MER04_Source =====
/-- The Newtonian primitive of `lem_primitive` (paper `mfd:lem-primitive`). -/
def aux_aux_macro_energy_recurrence_newton {d : ℕ} (f : SpatialCoordinates d → ℝ) :
    SpatialCoordinates d → Fin d → ℝ :=
  fun x i =>
    ((d : ℝ) * (volume {w : SpatialCoordinates d |
      Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
      ∫ y, (if x = y then 0 else
        (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y

/-- `lem_primitive`, repackaged: weak identity and the `C^{1/2}` modulus up to distance `R`. -/
theorem aux_aux_macro_energy_recurrence_newton_props {d : ℕ} (hd : 2 ≤ d) :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
      (f : SpatialCoordinates d → ℝ), MemLp f (⊤ : ℝ≥0∞) volume →
      (∀ᵐ x ∂volume, x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) →
      (∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∑ i : Fin d, ∫ x, aux_aux_macro_energy_recurrence_newton f x i * fderiv ℝ φ x (Pi.single i 1)) =
            -∫ x, f x * φ x) ∧
      (∀ x y : SpatialCoordinates d, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
        Real.sqrt (∑ i : Fin d, (aux_aux_macro_energy_recurrence_newton f x i - aux_aux_macro_energy_recurrence_newton f y i) ^ 2) ≤
          Ch * Real.sqrt R * (eLpNormEssSup f volume).toReal *
            Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) := by
  obtain ⟨C_log, C_holder, C_cube, _, hCh, _, hprim⟩ := lem_primitive d hd
  refine ⟨C_holder, hCh, fun R hR z f hmem hsupp => ?_⟩
  have h := hprim R hR z f hmem hsupp
  obtain ⟨hid, hlog, hcmp, _⟩ := h
  exact ⟨hid, fun x y hxy => (hlog x y hxy).trans (hcmp x y hxy)⟩

/-- Coordinates are dominated by the Euclidean norm. -/
theorem aux_aux_macro_energy_recurrence_abs_le_sqrt_sum {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    |v i| ≤ Real.sqrt (∑ j : Fin d, (v j) ^ 2) :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => (v j) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- Euclidean distance inside a closed cube of side `R` is at most `d * R`. -/
theorem aux_aux_macro_energy_recurrence_closedCube_dist_le {d : ℕ} (hd : 1 ≤ d) (y : SpatialCoordinates d) {R : ℝ}
    (hR : 0 < R) {x x' : SpatialCoordinates d}
    (hx : x ∈ (closedCube y R hR : Set (SpatialCoordinates d)))
    (hx' : x' ∈ (closedCube y R hR : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ j : Fin d, (x j - x' j) ^ 2) ≤ d * R := by
  have hj : ∀ j : Fin d, (x j - x' j) ^ 2 ≤ R ^ 2 := by
    intro j
    have h1 : |x j - y j| ≤ R / 2 := by
      have := norm_le_pi_norm (x - y) j
      have hx2 : dist x y ≤ R / 2 := hx
      rw [dist_eq_norm] at hx2
      simpa [Real.norm_eq_abs] using this.trans hx2
    have h2 : |x' j - y j| ≤ R / 2 := by
      have := norm_le_pi_norm (x' - y) j
      have hx2 : dist x' y ≤ R / 2 := hx'
      rw [dist_eq_norm] at hx2
      simpa [Real.norm_eq_abs] using this.trans hx2
    have h3 : |x j - x' j| ≤ R := by
      have := abs_sub_le (x j) (y j) (x' j)
      rw [abs_sub_comm (y j) (x' j)] at this
      linarith
    calc (x j - x' j) ^ 2 = |x j - x' j| ^ 2 := (sq_abs _).symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hsum : (∑ j : Fin d, (x j - x' j) ^ 2) ≤ ((d : ℝ) * R) ^ 2 := by
    calc (∑ j : Fin d, (x j - x' j) ^ 2) ≤ ∑ _j : Fin d, R ^ 2 := Finset.sum_le_sum fun j _ => hj j
      _ = (d : ℝ) * R ^ 2 := by simp
      _ ≤ ((d : ℝ) * R) ^ 2 := by
        have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [sq_nonneg R]
  calc Real.sqrt (∑ j : Fin d, (x j - x' j) ^ 2) ≤ Real.sqrt (((d : ℝ) * R) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = (d : ℝ) * R := Real.sqrt_sq (by positivity)

/-- The primitive of a bounded source supported in a cube: half-Hölder on the closed cube with
the scaled bound, square-integrable on the open cube, and the weak identity for test functions
of the open cube. -/
theorem aux_aux_macro_energy_recurrence_primitive_on_cube {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (yT : SpatialCoordinates d) (RT : ℝ) (hRT : 0 < RT)
      (f : SpatialCoordinates d → ℝ) (K : ℝ), 0 ≤ K → Measurable f → (∀ x, |f x| ≤ K) →
      (∀ x, x ∉ (centeredCube yT RT hRT : Set (SpatialCoordinates d)) → f x = 0) →
      (∀ i : Fin d, IsHolderOn (1 / 2) (closedCube yT RT hRT : Set (SpatialCoordinates d))
        (fun x => aux_aux_macro_energy_recurrence_newton f x i)) ∧
      halfHolderSeminorm (centeredCube yT RT hRT : Set (SpatialCoordinates d))
          (aux_aux_macro_energy_recurrence_newton f) ≤ Cp * Real.sqrt RT * K ∧
      (∀ i : Fin d, MemLp (fun x => aux_aux_macro_energy_recurrence_newton f x i) 2
        (volume.restrict (centeredCube yT RT hRT : Set (SpatialCoordinates d)))) ∧
      (∀ φ : 𝓓(centeredCube yT RT hRT, ℝ),
        (∑ i : Fin d, ∫ x in (centeredCube yT RT hRT : Set (SpatialCoordinates d)),
            aux_aux_macro_energy_recurrence_newton f x i * fderiv ℝ φ x (Pi.single i 1)) =
          -∫ x in (centeredCube yT RT hRT : Set (SpatialCoordinates d)), f x * φ x) := by
  obtain ⟨Ch, hCh, hN⟩ := aux_aux_macro_energy_recurrence_newton_props hd
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  refine ⟨Ch * Real.sqrt d, mul_pos hCh (Real.sqrt_pos.2 (by linarith)), ?_⟩
  intro yT RT hRT f K hK hfm hfb hfs
  set R' : ℝ := (d : ℝ) * RT with hR'
  have hR'pos : 0 < R' := mul_pos (by linarith) hRT
  -- the source is supported in the enlarged closed cube
  have hsub : (centeredCube yT RT hRT : Set (SpatialCoordinates d)) ⊆
      (closedCube yT R' hR'pos : Set (SpatialCoordinates d)) := by
    intro x hx
    have hx' : dist x yT < RT / 2 := hx
    change dist x yT ≤ R' / 2
    have : RT / 2 ≤ R' / 2 := by rw [hR']; nlinarith
    linarith
  have hmem : MemLp f (⊤ : ℝ≥0∞) volume :=
    memLp_top_of_bound hfm.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfb x)
  have hsupp : ∀ᵐ x ∂volume, x ∉ (closedCube yT R' hR'pos : Set (SpatialCoordinates d)) →
      f x = 0 :=
    Filter.Eventually.of_forall fun x hx => hfs x (fun h => hx (hsub h))
  obtain ⟨hid, hmod⟩ := hN R' hR'pos yT f hmem hsupp
  have hKeff : (eLpNormEssSup f volume).toReal ≤ K := by
    have hle : eLpNormEssSup f volume ≤ ENNReal.ofReal K :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hfb x)
    exact ENNReal.toReal_le_of_le_ofReal hK hle
  set g := aux_aux_macro_energy_recurrence_newton f with hg
  set M : ℝ := Ch * Real.sqrt R' * K with hM
  have hM0 : 0 ≤ M := by positivity
  -- the modulus on the closed cube, with the effective constant `M`
  have hmodK : ∀ x ∈ (closedCube yT RT hRT : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube yT RT hRT : Set (SpatialCoordinates d)),
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        M * Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
    intro x hx y hy
    have hxy := aux_aux_macro_energy_recurrence_closedCube_dist_le hd1 yT hRT hx hy
    refine (hmod x y (by rw [hR']; exact hxy)).trans ?_
    have : Ch * Real.sqrt R' * (eLpNormEssSup f volume).toReal ≤ M :=
      mul_le_mul_of_nonneg_left hKeff (by positivity)
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  -- coordinatewise Hölder quotient bound
  have hquot : ∀ i : Fin d, ∀ x ∈ (closedCube yT RT hRT : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube yT RT hRT : Set (SpatialCoordinates d)), x ≠ y →
      |g x i - g y i| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ) ≤ M := by
    intro i x hx y hy hxy
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hcon; push_neg at hcon; exact hxy (funext hcon)
      exact (abs_pos.2 (sub_ne_zero.2 hj)).trans_le
        (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun j => x j - y j) j)
    rw [← Real.sqrt_eq_rpow, div_le_iff₀ (Real.sqrt_pos.2 hpos)]
    exact (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun i => g x i - g y i) i).trans (hmodK x hx y hy)
  have hMd : M = Ch * Real.sqrt d * Real.sqrt RT * K := by
    rw [hM, hR', Real.sqrt_mul (by linarith)]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨M, ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    exact hquot i x hx y hy hxy
  · rw [← hMd]
    refine Real.sSup_le ?_ hM0
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hxc := centeredCube_subset_closedCube yT hRT hx
    have hyc := centeredCube_subset_closedCube yT hRT hy
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hcon; push_neg at hcon; exact hxy (funext hcon)
      exact (abs_pos.2 (sub_ne_zero.2 hj)).trans_le
        (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun j => x j - y j) j)
    rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)]
    exact hmodK x hxc y hyc
  · intro i
    -- continuity on the closed cube from the Hölder modulus, then boundedness
    have hcont : ContinuousOn (fun x => g x i)
        (closedCube yT RT hRT : Set (SpatialCoordinates d)) := by
      have hH : HolderOnWith (⟨M * (d : ℝ) ^ (1 / 4 : ℝ) + 1, by positivity⟩ : ℝ≥0)
          (1 / 2 : ℝ≥0) (fun x => g x i)
          (closedCube yT RT hRT : Set (SpatialCoordinates d)) := by
        intro x hx y hy
        rw [edist_dist, edist_dist, Real.dist_eq]
        have hxy_sup : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤
            Real.sqrt d * dist x y := by
          have hj : ∀ j : Fin d, (x j - y j) ^ 2 ≤ (dist x y) ^ 2 := by
            intro j
            have := dist_le_pi_dist x y j
            rw [Real.dist_eq] at this
            calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
              _ ≤ (dist x y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
              ≤ Real.sqrt (∑ _j : Fin d, (dist x y) ^ 2) :=
                Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hj j)
            _ = Real.sqrt d * dist x y := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]
        have h1 : |g x i - g y i| ≤ M * Real.sqrt (Real.sqrt d * dist x y) :=
          (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun i => g x i - g y i) i).trans
            ((hmodK x hx y hy).trans (mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt hxy_sup) hM0))
        have h2 : M * Real.sqrt (Real.sqrt d * dist x y) =
            M * (d : ℝ) ^ (1 / 4 : ℝ) * (dist x y) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
          norm_num; ring
        have h3 : |g x i - g y i| ≤ (M * (d : ℝ) ^ (1 / 4 : ℝ) + 1) *
            (dist x y) ^ (1 / 2 : ℝ) := by
          rw [h2] at h1
          refine h1.trans ?_
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _)
        rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
        calc ENNReal.ofReal |g x i - g y i|
            ≤ ENNReal.ofReal ((M * (d : ℝ) ^ (1 / 4 : ℝ) + 1) * (dist x y) ^ (1 / 2 : ℝ)) :=
              ENNReal.ofReal_le_ofReal h3
          _ = _ := by
              rw [ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      exact hH.continuousOn (by norm_num)
    have hbdd : ∃ B : ℝ, ∀ x ∈ (closedCube yT RT hRT : Set (SpatialCoordinates d)),
        ‖g x i‖ ≤ B := by
      obtain ⟨B, hB⟩ := (closedCube yT RT hRT).isCompact.exists_bound_of_continuousOn hcont
      exact ⟨B, hB⟩
    obtain ⟨B, hB⟩ := hbdd
    refine MemLp.of_bound ((hcont.mono (centeredCube_subset_closedCube yT hRT)).aestronglyMeasurable
      (centeredCube yT RT hRT).isOpen.measurableSet) B ?_
    filter_upwards [ae_restrict_mem (centeredCube yT RT hRT).isOpen.measurableSet] with x hx
    exact hB x (centeredCube_subset_closedCube yT hRT hx)
  · intro φ
    have hφs : tsupport (φ : SpatialCoordinates d → ℝ) ⊆
        (centeredCube yT RT hRT : Set (SpatialCoordinates d)) := φ.tsupport_subset
    have hφc : HasCompactSupport (φ : SpatialCoordinates d → ℝ) := φ.hasCompactSupport
    have hφd : ContDiff ℝ ∞ (φ : SpatialCoordinates d → ℝ) := φ.contDiff
    have h1 := hid φ hφd hφc
    have hL : ∀ i : Fin d, ∫ x in (centeredCube yT RT hRT : Set (SpatialCoordinates d)),
        g x i * fderiv ℝ φ x (Pi.single i 1) = ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1) := by
      intro i
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have : fderiv ℝ (φ : SpatialCoordinates d → ℝ) x = 0 := by
        by_contra hne
        exact hx (hφs (support_fderiv_subset ℝ hne))
      rw [this]; simp
    have hR : ∫ x in (centeredCube yT RT hRT : Set (SpatialCoordinates d)), f x * φ x =
        ∫ x, f x * φ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hfs x hx, zero_mul]
    rw [Finset.sum_congr rfl fun i _ => hL i, hR]
    exact h1

/-- Density: a weak identity against test functions extends to the killed graph. -/
theorem aux_aux_macro_energy_recurrence_identity_killed {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (G : Fin d → DomainL2 Ω) (fL : DomainL2 Ω)
    (h : ∀ φ : 𝓓(Ω, ℝ), (∑ i : Fin d, inner ℝ (G i) (testPartialL2 φ i)) =
      -inner ℝ fL (testL2 φ)) :
    ∀ Φ ∈ killedSobolevGraph Ω,
      inner ℝ (WithLp.toLp 2 G : HilbertGradient Ω) (sobolevGradient Φ) =
        -sobolevVolumeLoad fL Φ := by
  let Λ₁ : SobolevData Ω →L[ℝ] ℝ :=
    (innerSL ℝ (WithLp.toLp 2 G : HilbertGradient Ω)).comp sobolevGradient
  let Λ₂ : SobolevData Ω →L[ℝ] ℝ := -sobolevVolumeLoad fL
  have hclosed : IsClosed {Φ : SobolevData Ω | Λ₁ Φ = Λ₂ Φ} :=
    isClosed_eq Λ₁.continuous Λ₂.continuous
  have hrange : ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) :
      Set (SobolevData Ω)) ⊆ {Φ : SobolevData Ω | Λ₁ Φ = Λ₂ Φ} := by
    rintro Φ ⟨φ, rfl⟩
    change inner ℝ (WithLp.toLp 2 G : HilbertGradient Ω)
        (sobolevGradient (smoothSobolevData φ)) = -sobolevVolumeLoad fL (smoothSobolevData φ)
    rw [PiLp.inner_apply]
    change (∑ i : Fin d, inner ℝ (G i) (testPartialL2 φ i)) = -inner ℝ fL (testL2 φ)
    exact h φ
  intro Φ hΦ
  have hΦ' : Φ ∈ closure ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) :
      Set (SobolevData Ω)) := by
    simpa [killedSobolevGraph, Submodule.topologicalClosure_coe] using hΦ
  exact (hclosed.closure_subset_iff.2 hrange) hΦ'

-- ===== MER05_Equation =====
/-- The weak equation, transported: `𝓔_{aT}(U, Φ) = ∫_T c⁻¹ s⁻² F(s⁻¹ y) Φ(y) dy`. -/
theorem aux_aux_macro_energy_recurrence_equation_T {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (aT : PositiveCoefficient T) (a' : PositiveCoefficient Q)
    (hcoef : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      a'.val x = c * aT.val (s • x))
    (F : SpatialCoordinates d → ℝ) (b u' : weakSobolevGraph Q)
    (hsol : SolvesDirichlet a' F b u') (U : SobolevData T)
    (hU : ∀ i : Fin d, ((U.2 i : DomainL2 T) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => s⁻¹ * ((u' : SobolevData Q).2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y))
    (Φ : killedSobolevGraph T) :
    sobolevCoefficientForm aT U (Φ : SobolevData T) =
      ∫ y in (T : Set (SpatialCoordinates d)),
        (c⁻¹ * (s⁻¹) ^ 2 * F (s⁻¹ • y)) * (Φ : SobolevData T).1 y := by
  obtain ⟨ψ, hψ1, hψ2⟩ := aux_aux_macro_energy_recurrence_killed_unscale hs hT Φ
  rw [aux_aux_macro_energy_recurrence_form_scale hs hc hT aT a' hcoef U (Φ : SobolevData T) (u' : SobolevData Q)
    (ψ : SobolevData Q) hU hψ2, hsol.2 ψ, aux_aux_macro_energy_recurrence_integral_T hs hT]
  have hae : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (c⁻¹ * (s⁻¹) ^ 2 * F (s⁻¹ • s • x)) * ((Φ : SobolevData T).1 : _ → ℝ) (s • x) =
        c⁻¹ * (s⁻¹) ^ 2 * (F x * ((ψ : SobolevData Q).1 : _ → ℝ) x) := by
    filter_upwards [hψ1] with x hx
    rw [hx, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    ring
  rw [integral_congr_ae hae, integral_const_mul]
  ring

/-- Measurable bounded version of the rescaled source, supported in `T`. -/
theorem aux_aux_macro_energy_recurrence_source_clamp {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s : ℝ}
    (hs : 0 < s)
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (F : SpatialCoordinates d → ℝ) (Kf κ : ℝ) (hKf : 0 ≤ Kf) (hκ : 0 ≤ κ)
    (hFm : AEMeasurable F (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |F x| ≤ Kf) :
    ∃ f : SpatialCoordinates d → ℝ, Measurable f ∧ (∀ y, |f y| ≤ κ * Kf) ∧
      (∀ y, y ∉ (T : Set (SpatialCoordinates d)) → f y = 0) ∧
      f =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))] fun y => κ * F (s⁻¹ • y) := by
  set Fm := hFm.mk F with hFmdef
  have hFmm : Measurable Fm := hFm.measurable_mk
  let B : SpatialCoordinates d → ℝ := fun y =>
    max (-(κ * Kf)) (min (κ * Kf) (κ * Fm (s⁻¹ • y)))
  have hB : Measurable B :=
    measurable_const.max (measurable_const.min
      (measurable_const.mul (hFmm.comp (measurable_const_smul s⁻¹))))
  refine ⟨T.carrier.indicator B, hB.indicator T.isOpen.measurableSet, ?_, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ (T : Set (SpatialCoordinates d))
    · change |(T : Set (SpatialCoordinates d)).indicator B y| ≤ _
      rw [Set.indicator_of_mem hy]
      have h0 : 0 ≤ κ * Kf := mul_nonneg hκ hKf
      refine abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    · change |(T : Set (SpatialCoordinates d)).indicator B y| ≤ _
      rw [Set.indicator_of_notMem hy, abs_zero]
      exact mul_nonneg hκ hKf
  · intro y hy
    change (T : Set (SpatialCoordinates d)).indicator B y = 0
    rw [Set.indicator_of_notMem hy]
  · have h1 := aux_aux_macro_energy_recurrence_ae_push hs Q.isOpen.measurableSet T.isOpen.measurableSet hT
      hFm.ae_eq_mk
    have h2 := aux_aux_macro_energy_recurrence_ae_push hs Q.isOpen.measurableSet T.isOpen.measurableSet hT hFb
    filter_upwards [h1, h2, ae_restrict_mem T.isOpen.measurableSet] with y hy1 hy2 hyT
    change (T : Set (SpatialCoordinates d)).indicator B y = _
    rw [Set.indicator_of_mem hyT]
    change max (-(κ * Kf)) (min (κ * Kf) (κ * Fm (s⁻¹ • y))) = _
    rw [hFmdef, ← hy1]
    have hb := abs_le.1 hy2
    have hlo : -(κ * Kf) ≤ κ * F (s⁻¹ • y) := by nlinarith
    have hhi : κ * F (s⁻¹ • y) ≤ κ * Kf := mul_le_mul_of_nonneg_left hb.2 hκ
    rw [min_eq_right hhi, max_eq_right hlo]

/-- The real `L²` inner product as an integral of the product of representatives. -/
theorem aux_aux_macro_energy_recurrence_inner_eq_integral {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f g : DomainL2 Ω) :
    inner ℝ f g = ∫ x in (Ω : Set (SpatialCoordinates d)),
      (f : SpatialCoordinates d → ℝ) x * (g : SpatialCoordinates d → ℝ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-- **The physical Dirichlet problem.** From a solution on `Q` we get, on the cube
`T = centeredCube yT RT hRT = s • Q`, the physical solution `U`, the half-Hölder source field `g`
with its `L²` class `hgrad`, and the energy-density equation form. -/
theorem aux_aux_macro_energy_recurrence_physical_problem {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (Q : Opens (SpatialCoordinates d)) (yT : SpatialCoordinates d)
      (RT : ℝ) (hRT : 0 < RT) (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
      (hT : (centeredCube yT RT hRT : Set (SpatialCoordinates d)) =
        s • (Q : Set (SpatialCoordinates d)))
      (aT : PositiveCoefficient (centeredCube yT RT hRT)) (a' : PositiveCoefficient Q),
      (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        a'.val x = c * aT.val (s • x)) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (Q : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
      ∀ (b u' : weakSobolevGraph Q), SolvesDirichlet a' F b u' →
      ∀ (U : SobolevData (centeredCube yT RT hRT)),
      (∀ i : Fin d, ((U.2 i : DomainL2 (centeredCube yT RT hRT)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube yT RT hRT : Set (SpatialCoordinates d))]
        fun y => s⁻¹ * ((u' : SobolevData Q).2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y)) →
      ∃ (g : SpatialCoordinates d → Fin d → ℝ)
        (hgrad : HilbertGradient (centeredCube yT RT hRT)),
        (∀ i : Fin d, ((hgrad i : DomainL2 (centeredCube yT RT hRT)) :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube yT RT hRT : Set (SpatialCoordinates d))]
            fun x => g x i) ∧
        (∀ i : Fin d, IsHolderOn (1 / 2)
          (closedCube yT RT hRT : Set (SpatialCoordinates d)) (fun x => g x i)) ∧
        halfHolderSeminorm (centeredCube yT RT hRT : Set (SpatialCoordinates d)) g ≤
          Cp * Real.sqrt RT * (c⁻¹ * (s⁻¹) ^ 2 * Kf) ∧
        (∀ Φ : killedSobolevGraph (centeredCube yT RT hRT),
          sobolevCoefficientForm aT U (Φ : SobolevData _) =
            -inner ℝ hgrad
              (subspaceGradient (killedSobolevGraph (centeredCube yT RT hRT)) Φ)) := by
  obtain ⟨Cp, hCp, hprim⟩ := aux_aux_macro_energy_recurrence_primitive_on_cube hd
  refine ⟨Cp, hCp, ?_⟩
  intro Q yT RT hRT s c hs hc hT aT a' hcoef F Kf hKf hFm hFb b u' hsol U hU
  have hκ : 0 ≤ c⁻¹ * (s⁻¹) ^ 2 := by positivity
  obtain ⟨f, hfm, hfb, hfs, hfae⟩ :=
    aux_aux_macro_energy_recurrence_source_clamp hs hT F Kf (c⁻¹ * (s⁻¹) ^ 2) hKf hκ hFm hFb
  have hK : 0 ≤ c⁻¹ * (s⁻¹) ^ 2 * Kf := mul_nonneg hκ hKf
  obtain ⟨hhol, hsemi, hmemg, hid⟩ := hprim yT RT hRT f _ hK hfm hfb hfs
  let G : Fin d → DomainL2 (centeredCube yT RT hRT) := fun i => (hmemg i).toLp _
  have hmemf : MemLp f 2 (volume.restrict ((centeredCube yT RT hRT) : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hfm.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfb y)
  let fL : DomainL2 (centeredCube yT RT hRT) := hmemf.toLp f
  refine ⟨aux_aux_macro_energy_recurrence_newton f, WithLp.toLp 2 G, fun i => (hmemg i).coeFn_toLp, hhol, hsemi, ?_⟩
  -- the identity against test functions, in `L²` form
  have htest : ∀ φ : 𝓓((centeredCube yT RT hRT), ℝ), (∑ i : Fin d, inner ℝ (G i) (testPartialL2 φ i)) =
      -inner ℝ fL (testL2 φ) := by
    intro φ
    have hsum : ∀ i : Fin d, inner ℝ (G i) (testPartialL2 φ i) =
        ∫ x in ((centeredCube yT RT hRT) : Set (SpatialCoordinates d)),
          aux_aux_macro_energy_recurrence_newton f x i * fderiv ℝ φ x (Pi.single i 1) := by
      intro i
      rw [aux_aux_macro_energy_recurrence_inner_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [(hmemg i).coeFn_toLp, testPartialL2_coeFn φ i] with x h1 h2
      rw [h1, h2]
    have hf : inner ℝ fL (testL2 φ) = ∫ x in ((centeredCube yT RT hRT) : Set (SpatialCoordinates d)), f x * φ x := by
      rw [aux_aux_macro_energy_recurrence_inner_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hmemf.coeFn_toLp, testL2_coeFn φ] with x h1 h2
      rw [h1, h2]
    rw [Finset.sum_congr rfl fun i _ => hsum i, hf]
    exact hid φ
  intro Φ
  have hk := aux_aux_macro_energy_recurrence_identity_killed G fL htest (Φ : SobolevData (centeredCube yT RT hRT)) Φ.2
  change sobolevCoefficientForm aT U (Φ : SobolevData (centeredCube yT RT hRT)) =
    -inner ℝ (WithLp.toLp 2 G : HilbertGradient (centeredCube yT RT hRT)) (sobolevGradient (Φ : SobolevData (centeredCube yT RT hRT)))
  rw [hk, neg_neg, sobolevVolumeLoad_apply,
    aux_aux_macro_energy_recurrence_equation_T hs hc hT aT a' hcoef F b u' hsol U hU Φ]
  refine integral_congr_ae ?_
  filter_upwards [hfae, hmemf.coeFn_toLp] with y h1 h2
  rw [h2, h1]

-- ===== MER06_Datum =====
/-- The weak gradient of a datum with a `C¹` representative is the classical gradient. -/
theorem aux_aux_macro_energy_recurrence_datum_grad {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ 1 φ) (b : weakSobolevGraph Ω)
    (hb : ((b : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] φ)
    (hmem : ∀ i : Fin d, MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ∀ i : Fin d, ((b : SobolevData Ω).2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => fderiv ℝ φ x (Pi.single i 1) := by
  let G : Fin d → DomainL2 Ω := fun i => (hmem i).toLp _
  have hz : ((b : SobolevData Ω).1, G) ∈ weakSobolevGraph Ω := by
    rw [mem_weakSobolevGraph_iff_hasWeakGradientOn]
    intro i
    have h0 := Homogenization.HasWeakGradientOn.of_contDiff (U := (Ω : Set (SpatialCoordinates d)))
      hφ i
    exact SubdiffusiveProcess.Lane4.hasWeakPartialDerivOn_congr_ae hb.symm
      (hmem i).coeFn_toLp.symm h0
  have hbG : (b : SobolevData Ω).2 = G := by
    have hb' : ((b : SobolevData Ω).1, (b : SobolevData Ω).2) ∈ weakSobolevGraph Ω := b.2
    exact weakSobolevGraph_gradient_unique hb' hz
  intro i
  rw [hbG]
  exact (hmem i).coeFn_toLp

/-- The scaled datum gradient. -/
def aux_aux_macro_energy_recurrence_gh {d : ℕ} (φ : SpatialCoordinates d → ℝ) (s : ℝ) :
    SpatialCoordinates d → Fin d → ℝ :=
  fun y i => s⁻¹ * fderiv ℝ φ (s⁻¹ • y) (Pi.single i 1)

/-- Operator-norm control of a coordinate derivative. -/
theorem aux_aux_macro_energy_recurrence_fderiv_coord_le {d : ℕ} (L : SpatialCoordinates d →L[ℝ] ℝ) (i : Fin d) :
    |L (Pi.single i 1)| ≤ ‖L‖ := by
  have h := L.le_opNorm (Pi.single i 1)
  rw [Real.norm_eq_abs] at h
  have hn : ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg L))

/-- Euclidean norm of the coordinate vector of a functional. -/
theorem aux_aux_macro_energy_recurrence_sqrt_sum_coord_le {d : ℕ} (L : SpatialCoordinates d →L[ℝ] ℝ) :
    Real.sqrt (∑ i : Fin d, (L (Pi.single i 1)) ^ 2) ≤ Real.sqrt d * ‖L‖ := by
  have h : (∑ i : Fin d, (L (Pi.single i 1)) ^ 2) ≤ (d : ℝ) * ‖L‖ ^ 2 := by
    calc (∑ i : Fin d, (L (Pi.single i 1)) ^ 2) ≤ ∑ _i : Fin d, ‖L‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc (L (Pi.single i 1)) ^ 2 = |L (Pi.single i 1)| ^ 2 := (sq_abs _).symm
            _ ≤ ‖L‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (aux_aux_macro_energy_recurrence_fderiv_coord_le L i) 2
      _ = (d : ℝ) * ‖L‖ ^ 2 := by simp
  calc Real.sqrt (∑ i : Fin d, (L (Pi.single i 1)) ^ 2) ≤ Real.sqrt ((d : ℝ) * ‖L‖ ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt d * ‖L‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- **Datum bounds.** Half-Hölder regularity of `gh` on the closed physical cube, and the
scaled-norm bound `halfHolderNorm s T gh ≤ s⁻¹ d C_φ`. -/
theorem aux_aux_macro_energy_recurrence_gh_bounds {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
    {s : ℝ} (hs : 0 < s) (hs' : 0 < s)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ 2 φ) (Cφ : ℝ)
    (hC : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ) :
    (∀ i : Fin d, IsHolderOn (1 / 2) (closedCube (s • z) s hs' : Set (SpatialCoordinates d))
      (fun y => aux_aux_macro_energy_recurrence_gh φ s y i)) ∧
    halfHolderNorm s (centeredCube (s • z) s hs' : Set (SpatialCoordinates d))
        (aux_aux_macro_energy_recurrence_gh φ s) ≤ s⁻¹ * d * Cφ := by
  set K : Set (SpatialCoordinates d) := (closedCube z 1 h1 : Set (SpatialCoordinates d)) with hK
  have hKc : IsCompact K := (closedCube z 1 h1).isCompact
  have hKconv : Convex ℝ K := convex_closedBall z (1 / 2)
  have hD1 : Continuous (fun x => ‖fderiv ℝ φ x‖) :=
    (hφ.continuous_fderiv (by norm_num)).norm
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hD2 : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ φ) x‖) :=
    (hφ1.continuous_fderiv (by norm_num)).norm
  set B1 : Set ℝ := {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ φ x‖} with hB1
  set B2 : Set ℝ := {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ (fderiv ℝ φ) x‖} with hB2
  have hB1b : BddAbove B1 := by
    refine (hKc.bddAbove_image hD1.continuousOn).mono ?_
    rintro v ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  have hB2b : BddAbove B2 := by
    refine (hKc.bddAbove_image hD2.continuousOn).mono ?_
    rintro v ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  set S1 := sSup B1 with hS1
  set S2 := sSup B2 with hS2
  have hS1x : ∀ x ∈ K, ‖fderiv ℝ φ x‖ ≤ S1 := fun x hx => le_csSup hB1b ⟨x, hx, rfl⟩
  have hS2x : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ S2 := fun x hx => le_csSup hB2b ⟨x, hx, rfl⟩
  have hS10 : 0 ≤ S1 := Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact norm_nonneg _)
  have hS20 : 0 ≤ S2 := Real.sSup_nonneg (by
    rintro v ⟨x, _, rfl⟩; exact norm_nonneg (fderiv ℝ (fderiv ℝ φ) x))
  have hA0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ K, v = |φ x|} :=
    Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact abs_nonneg _)
  have hSC : S1 + S2 ≤ Cφ := by
    have : c2Norm K φ = sSup {v : ℝ | ∃ x ∈ K, v = |φ x|} + S1 + S2 := rfl
    linarith
  have hmv : ∀ x ∈ K, ∀ x' ∈ K, ‖fderiv ℝ φ x - fderiv ℝ φ x'‖ ≤ S2 * ‖x - x'‖ := by
    intro x hx x' hx'
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ φ)
      (fun w _ => hφ1.differentiable (by norm_num) w) hS2x hKconv hx' hx
  -- membership transport
  have hmemK : ∀ y ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)), s⁻¹ • y ∈ K := by
    intro y hy
    change dist (s⁻¹ • y) z ≤ 1 / 2
    have hy' : dist y (s • z) ≤ s / 2 := hy
    have : s⁻¹ • y - z = s⁻¹ • (y - s • z) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs),
      ← dist_eq_norm]
    calc s⁻¹ * dist y (s • z) ≤ s⁻¹ * (s / 2) := mul_le_mul_of_nonneg_left hy' (by positivity)
      _ = 1 / 2 := by field_simp
  -- Euclidean difference of `gh` values
  have hdiff : ∀ y ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)),
      ∀ y' ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)),
      Real.sqrt (∑ i : Fin d, (aux_aux_macro_energy_recurrence_gh φ s y i - aux_aux_macro_energy_recurrence_gh φ s y' i) ^ 2) ≤
        (s⁻¹) ^ 2 * Real.sqrt d * S2 * Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2) := by
    intro y hy y' hy'
    set L : SpatialCoordinates d →L[ℝ] ℝ := fderiv ℝ φ (s⁻¹ • y) - fderiv ℝ φ (s⁻¹ • y')
    have hcoord : ∀ i : Fin d, aux_aux_macro_energy_recurrence_gh φ s y i - aux_aux_macro_energy_recurrence_gh φ s y' i =
        s⁻¹ * L (Pi.single i 1) := by
      intro i; simp only [aux_aux_macro_energy_recurrence_gh, L, ContinuousLinearMap.sub_apply]; ring
    have hsum : Real.sqrt (∑ i : Fin d, (aux_aux_macro_energy_recurrence_gh φ s y i - aux_aux_macro_energy_recurrence_gh φ s y' i) ^ 2) =
        s⁻¹ * Real.sqrt (∑ i : Fin d, (L (Pi.single i 1)) ^ 2) := by
      simp only [hcoord, mul_pow]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hL : ‖L‖ ≤ S2 * (s⁻¹ * Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) := by
      refine (hmv _ (hmemK y hy) _ (hmemK y' hy')).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hS20
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
      simpa [Real.norm_eq_abs] using aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun j => y j - y' j) j
    rw [hsum]
    calc s⁻¹ * Real.sqrt (∑ i : Fin d, (L (Pi.single i 1)) ^ 2)
        ≤ s⁻¹ * (Real.sqrt d * ‖L‖) :=
          mul_le_mul_of_nonneg_left (aux_aux_macro_energy_recurrence_sqrt_sum_coord_le L) (by positivity)
      _ ≤ s⁻¹ * (Real.sqrt d * (S2 * (s⁻¹ * Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)))) := by
          gcongr
      _ = _ := by ring
  have hdiam : ∀ y ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)),
      ∀ y' ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)),
      Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2) ≤ d * s :=
    fun y hy y' hy' => aux_aux_macro_energy_recurrence_closedCube_dist_le hd (s • z) hs' hy hy'
  -- the Hölder quotient bound, with constant `M`
  set M : ℝ := (s⁻¹) ^ 2 * Real.sqrt d * S2 * Real.sqrt (d * s) with hM
  have hM0 : 0 ≤ M := by positivity
  have hquot : ∀ y ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)),
      ∀ y' ∈ (closedCube (s • z) s hs' : Set (SpatialCoordinates d)), y ≠ y' →
      Real.sqrt (∑ i : Fin d, (aux_aux_macro_energy_recurrence_gh φ s y i - aux_aux_macro_energy_recurrence_gh φ s y' i) ^ 2) /
        Real.sqrt (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ≤ M := by
    intro y hy y' hy' hne
    set e := Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2) with he
    have hepos : 0 < e := by
      obtain ⟨j, hj⟩ : ∃ j, y j ≠ y' j := by
        by_contra hcon; push_neg at hcon; exact hne (funext hcon)
      exact (abs_pos.2 (sub_ne_zero.2 hj)).trans_le
        (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun j => y j - y' j) j)
    rw [div_le_iff₀ (Real.sqrt_pos.2 hepos)]
    refine (hdiff y hy y' hy').trans ?_
    have hee : e = Real.sqrt e * Real.sqrt e := (Real.mul_self_sqrt hepos.le).symm
    have hse : Real.sqrt e ≤ Real.sqrt (d * s) := Real.sqrt_le_sqrt (hdiam y hy y' hy')
    calc (s⁻¹) ^ 2 * Real.sqrt d * S2 * e
        = (s⁻¹) ^ 2 * Real.sqrt d * S2 * Real.sqrt e * Real.sqrt e := by
          rw [mul_assoc ((s⁻¹) ^ 2 * Real.sqrt d * S2), ← hee]
      _ ≤ (s⁻¹) ^ 2 * Real.sqrt d * S2 * Real.sqrt (d * s) * Real.sqrt e := by
          gcongr
  refine ⟨fun i => ⟨M, ?_⟩, ?_⟩
  · rintro v ⟨y, hy, y', hy', hne, rfl⟩
    have h1' := hquot y hy y' hy' hne
    have hpos : 0 < Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2) := by
      obtain ⟨j, hj⟩ : ∃ j, y j ≠ y' j := by
        by_contra hcon; push_neg at hcon; exact hne (funext hcon)
      exact (abs_pos.2 (sub_ne_zero.2 hj)).trans_le
        (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun j => y j - y' j) j)
    rw [← Real.sqrt_eq_rpow]
    refine le_trans ?_ h1'
    exact div_le_div_of_nonneg_right
      (aux_aux_macro_energy_recurrence_abs_le_sqrt_sum (fun i => aux_aux_macro_energy_recurrence_gh φ s y i - aux_aux_macro_energy_recurrence_gh φ s y' i) i)
      (Real.sqrt_nonneg _)
  · -- the sup part and the seminorm part
    have hsup : sSup {v : ℝ | ∃ y ∈ (centeredCube (s • z) s hs' : Set (SpatialCoordinates d)),
        v = Real.sqrt (∑ i : Fin d, (aux_aux_macro_energy_recurrence_gh φ s y i) ^ 2)} ≤ s⁻¹ * Real.sqrt d * S1 := by
      refine Real.sSup_le ?_ (by positivity)
      rintro v ⟨y, hy, rfl⟩
      have hyK := hmemK y (centeredCube_subset_closedCube (s • z) hs' hy)
      have : Real.sqrt (∑ i : Fin d, (aux_aux_macro_energy_recurrence_gh φ s y i) ^ 2) =
          s⁻¹ * Real.sqrt (∑ i : Fin d, (fderiv ℝ φ (s⁻¹ • y) (Pi.single i 1)) ^ 2) := by
        simp only [aux_aux_macro_energy_recurrence_gh, mul_pow]
        rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      rw [this, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (aux_aux_macro_energy_recurrence_sqrt_sum_coord_le _).trans
        (mul_le_mul_of_nonneg_left (hS1x _ hyK) (Real.sqrt_nonneg _))
    have hsemi : halfHolderSeminorm (centeredCube (s • z) s hs' : Set (SpatialCoordinates d))
        (aux_aux_macro_energy_recurrence_gh φ s) ≤ M := by
      refine Real.sSup_le ?_ hM0
      rintro v ⟨y, hy, y', hy', hne, rfl⟩
      exact hquot y (centeredCube_subset_closedCube (s • z) hs' hy) y'
        (centeredCube_subset_closedCube (s • z) hs' hy') hne
    have hsM : Real.sqrt s * M = s⁻¹ * d * S2 := by
      rw [hM, Real.sqrt_mul (Nat.cast_nonneg _)]
      have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
      have hdd : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg _)
      calc Real.sqrt s * ((s⁻¹) ^ 2 * Real.sqrt d * S2 * (Real.sqrt d * Real.sqrt s))
          = (s⁻¹) ^ 2 * (Real.sqrt s * Real.sqrt s) * (Real.sqrt d * Real.sqrt d) * S2 := by ring
        _ = (s⁻¹) ^ 2 * s * d * S2 := by rw [hss, hdd]
        _ = s⁻¹ * d * S2 := by
            rw [show (s⁻¹) ^ 2 * s = s⁻¹ by rw [sq, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]]
    have hsqd : Real.sqrt (d : ℝ) ≤ d := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      calc Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ) * d) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = d := Real.sqrt_mul_self (by linarith)
    change sSup _ + Real.sqrt s * halfHolderSeminorm _ _ ≤ _
    calc _ ≤ s⁻¹ * Real.sqrt d * S1 + Real.sqrt s * M :=
          add_le_add hsup (mul_le_mul_of_nonneg_left hsemi (Real.sqrt_nonneg _))
      _ = s⁻¹ * Real.sqrt d * S1 + s⁻¹ * d * S2 := by rw [hsM]
      _ ≤ s⁻¹ * d * S1 + s⁻¹ * d * S2 := by
          gcongr
      _ = s⁻¹ * d * (S1 + S2) := by ring
      _ ≤ s⁻¹ * d * Cφ := mul_le_mul_of_nonneg_left hSC (by positivity)

-- ===== MER07_Stability =====
/-- Existence of the Dirichlet solution (Lax–Milgram through the response machinery). -/
theorem aux_aux_macro_energy_recurrence_exists_solution {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hFm : AEMeasurable F (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (b : weakSobolevGraph Ω) :
    ∃ u' : weakSobolevGraph Ω, SolvesDirichlet a F b u' := by
  let S := killedResponseSpace hP
  have hmem : MemLp F 2 (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hFm.aestronglyMeasurable Kf (by
      filter_upwards [hFb] with x hx; simpa [Real.norm_eq_abs] using hx)
  let fL : DomainL2 Ω := hmem.toLp F
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad fL).comp S.space.subtypeL
  let w : S.space := responseSolution S a L
  let m : weakSobolevGraph Ω := dirichletMinimizer S a b
  refine ⟨⟨(m : SobolevData Ω) + (w : SobolevData Ω),
    (weakSobolevGraph Ω).add_mem m.2 (S.le_weak w.2)⟩, ?_, ?_⟩
  · change (m : SobolevData Ω) + (w : SobolevData Ω) - (b : SobolevData Ω) ∈
      killedSobolevGraph Ω
    have h1 : (m : SobolevData Ω) - (b : SobolevData Ω) ∈ killedSobolevGraph Ω :=
      dirichletMinimizer_mem_affine S a b
    have h2 : (w : SobolevData Ω) ∈ killedSobolevGraph Ω := w.2
    have := (killedSobolevGraph Ω).add_mem h1 h2
    convert this using 1
    abel
  · intro ψ
    change sobolevCoefficientForm a ((m : SobolevData Ω) + (w : SobolevData Ω))
      (ψ : SobolevData Ω) = _
    rw [map_add, ContinuousLinearMap.add_apply]
    have he : sobolevCoefficientForm a (m : SobolevData Ω) (ψ : SobolevData Ω) = 0 :=
      dirichletMinimizer_euler S a b ψ
    have hr : sobolevCoefficientForm a (w : SobolevData Ω) (ψ : SobolevData Ω) = L ψ :=
      responseSolution_spec S a L ψ
    rw [he, hr, zero_add]
    change sobolevVolumeLoad fL (ψ : SobolevData Ω) = _
    rw [sobolevVolumeLoad_apply]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]

theorem aux_aux_macro_energy_recurrence_form_sub_left {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (x y z : SobolevData Ω) :
    sobolevCoefficientForm a (x - y) z =
      sobolevCoefficientForm a x z - sobolevCoefficientForm a y z := by
  rw [map_sub]
  rfl

/-- Pointwise AM-GM used in the stability estimate. -/
theorem aux_aux_macro_energy_recurrence_amgm (e u w η lam : ℝ) (hlam : 0 < lam) (he : |e| ≤ η) :
    e * u * w ≤ η ^ 2 / lam * u ^ 2 + lam / 4 * w ^ 2 := by
  have h0 : 0 ≤ η := (abs_nonneg e).trans he
  have h1 : e * u * w ≤ η * (|u| * |w|) := by
    calc e * u * w ≤ |e * u * w| := le_abs_self _
      _ = |e| * (|u| * |w|) := by rw [abs_mul, abs_mul, mul_assoc]
      _ ≤ η * (|u| * |w|) := mul_le_mul_of_nonneg_right he (by positivity)
  have h2 : 0 ≤ (η * |u| - lam * |w| / 2) ^ 2 := sq_nonneg _
  have h3 : η * (|u| * |w|) ≤ η ^ 2 / lam * u ^ 2 + lam / 4 * w ^ 2 := by
    have hu : |u| ^ 2 = u ^ 2 := sq_abs u
    have hw : |w| ^ 2 = w ^ 2 := sq_abs w
    rw [← hu, ← hw]
    have key : lam * (η * (|u| * |w|)) ≤ lam * (η ^ 2 / lam * |u| ^ 2 + lam / 4 * |w| ^ 2) := by
      have : lam * (η ^ 2 / lam * |u| ^ 2 + lam / 4 * |w| ^ 2) =
          η ^ 2 * |u| ^ 2 + lam ^ 2 / 4 * |w| ^ 2 := by
        field_simp
      rw [this]
      nlinarith [h2]
    exact le_of_mul_le_mul_left key hlam
  exact h1.trans h3

/-- Squared `L²` gradient size. -/
def aux_aux_macro_energy_recurrence_gradSq {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (v : SobolevData Ω) : ℝ :=
  ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)), ((v.2 i : SpatialCoordinates d → ℝ) x) ^ 2

theorem aux_aux_macro_energy_recurrence_integrable_sq {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (f : DomainL2 Ω) :
    Integrable (fun x => ((f : SpatialCoordinates d → ℝ) x) ^ 2)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have := L2.integrable_inner (𝕜 := ℝ) f f
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

theorem aux_aux_macro_energy_recurrence_integrable_weighted {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) (f g : DomainL2 Ω) :
    Integrable (fun x => a x * ((f : SpatialCoordinates d → ℝ) x *
      (g : SpatialCoordinates d → ℝ) x)) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  refine (integrable_weighted_inner a f g).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem aux_aux_macro_energy_recurrence_gradSq_nonneg {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (v : SobolevData Ω) :
    0 ≤ aux_aux_macro_energy_recurrence_gradSq v :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

/-- **Stability (paper Step 6).** Two solutions with the same data and nearby coefficients. -/
theorem aux_aux_macro_energy_recurrence_stability {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (A a' : PositiveCoefficient Ω) (lam η : ℝ) (hlam : 0 < lam)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), lam ≤ A.val x)
    (hη : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |a'.val x - A.val x| ≤ η)
    (hηl : η ≤ lam / 2)
    (F : SpatialCoordinates d → ℝ) (b u u' : weakSobolevGraph Ω)
    (hu : SolvesDirichlet A F b u) (hu' : SolvesDirichlet a' F b u') :
    aux_aux_macro_energy_recurrence_gradSq ((u : SobolevData Ω) - (u' : SobolevData Ω)) ≤
      4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω) := by
  set w : SobolevData Ω := (u : SobolevData Ω) - (u' : SobolevData Ω) with hwdef
  have hwk : w ∈ killedSobolevGraph Ω := by
    have := (killedSobolevGraph Ω).sub_mem hu.1 hu'.1
    rwa [sub_sub_sub_cancel_right] at this
  let wk : killedSobolevGraph Ω := ⟨w, hwk⟩
  -- the energy identity for the difference
  have hid : sobolevCoefficientForm a' w w =
      sobolevCoefficientForm a' (u : SobolevData Ω) w -
        sobolevCoefficientForm A (u : SobolevData Ω) w := by
    have e1 : sobolevCoefficientForm A (u : SobolevData Ω) w =
        sobolevCoefficientForm a' (u' : SobolevData Ω) w := by
      rw [show w = (wk : SobolevData Ω) from rfl, hu.2 wk, hu'.2 wk]
    rw [e1]
    exact aux_aux_macro_energy_recurrence_form_sub_left a' _ _ w
  have hdiff : sobolevCoefficientForm a' (u : SobolevData Ω) w -
      sobolevCoefficientForm A (u : SobolevData Ω) w =
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        (a'.val x - A.val x) * ((u : SobolevData Ω).2 i x * w.2 i x) := by
    rw [aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply, aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_sub (aux_aux_macro_energy_recurrence_integrable_weighted _ _ _) (aux_aux_macro_energy_recurrence_integrable_weighted _ _ _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- lower bound
  have hlow : lam / 2 * aux_aux_macro_energy_recurrence_gradSq w ≤ sobolevCoefficientForm a' w w := by
    rw [aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply, aux_aux_macro_energy_recurrence_gradSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_mono_ae ((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _)
      (aux_aux_macro_energy_recurrence_integrable_weighted _ _ _) ?_
    filter_upwards [hA, hη] with x hx1 hx2
    have : lam / 2 ≤ a'.val x := by
      have := (abs_le.1 hx2).1
      linarith
    calc lam / 2 * (w.2 i x) ^ 2 ≤ a'.val x * (w.2 i x) ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = a'.val x * (w.2 i x * w.2 i x) := by ring
  -- upper bound
  have hup : (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        (a'.val x - A.val x) * ((u : SobolevData Ω).2 i x * w.2 i x)) ≤
      η ^ 2 / lam * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω) + lam / 4 * aux_aux_macro_energy_recurrence_gradSq w := by
    rw [aux_aux_macro_energy_recurrence_gradSq, aux_aux_macro_energy_recurrence_gradSq, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _) ((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _)]
    have hint : Integrable (fun x => (a'.val x - A.val x) *
        ((u : SobolevData Ω).2 i x * w.2 i x)) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
      refine ((aux_aux_macro_energy_recurrence_integrable_weighted a'.val ((u : SobolevData Ω).2 i) (w.2 i)).sub
        (aux_aux_macro_energy_recurrence_integrable_weighted A.val ((u : SobolevData Ω).2 i) (w.2 i))).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]; ring
    refine integral_mono_ae hint (((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _).add
      ((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _)) ?_
    filter_upwards [hη] with x hx
    have := aux_aux_macro_energy_recurrence_amgm (a'.val x - A.val x) ((u : SobolevData Ω).2 i x) (w.2 i x) η lam hlam hx
    simpa [mul_assoc] using this
  have hW0 := aux_aux_macro_energy_recurrence_gradSq_nonneg w
  have hU0 := aux_aux_macro_energy_recurrence_gradSq_nonneg (u : SobolevData Ω)
  have key : lam / 4 * aux_aux_macro_energy_recurrence_gradSq w ≤ η ^ 2 / lam * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω) := by
    have := hlow.trans (hid ▸ hdiff ▸ hup)
    linarith
  have hfinal : aux_aux_macro_energy_recurrence_gradSq w ≤ 4 / lam * (η ^ 2 / lam * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω)) := by
    have h4 : 0 < lam / 4 := by positivity
    rw [show 4 / lam * (η ^ 2 / lam * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω)) =
      (η ^ 2 / lam * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω)) / (lam / 4) by field_simp]
    rw [le_div_iff₀ h4]
    linarith
  calc aux_aux_macro_energy_recurrence_gradSq w ≤ 4 / lam * (η ^ 2 / lam * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω)) := hfinal
    _ = 4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData Ω) := by
        field_simp

/-- Local energy is at most `Λ` times the squared gradient size. -/
theorem aux_aux_macro_energy_recurrence_localEnergy_le_gradSq {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (Λ : ℝ)
    (hΛ : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ Λ)
    {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S) (v : SobolevData Ω) :
    localGradientEnergy a hS (sobolevGradient v) ≤ Λ * aux_aux_macro_energy_recurrence_gradSq v := by
  rw [localGradientEnergy_eq_integral, aux_aux_macro_energy_recurrence_gradSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← integral_const_mul]
  have hnn : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x :=
    positiveCoefficient_ae_nonneg a
  calc (∫ x in S, a.val x * ((sobolevGradient v) i x) ^ 2
        ∂volume.restrict (Ω : Set (SpatialCoordinates d)))
      ≤ ∫ x, a.val x * ((sobolevGradient v) i x) ^ 2
          ∂volume.restrict (Ω : Set (SpatialCoordinates d)) := by
        refine setIntegral_le_integral ?_ ?_
        · refine (aux_aux_macro_energy_recurrence_integrable_weighted a.val (v.2 i) (v.2 i)).congr
            (Filter.Eventually.of_forall fun x => ?_)
          change a.val x * (v.2 i x * v.2 i x) = a.val x * (v.2 i x) ^ 2
          ring
        · filter_upwards [hnn] with x hx
          exact mul_nonneg hx (sq_nonneg _)
    _ ≤ ∫ x, Λ * ((v.2 i : SpatialCoordinates d → ℝ) x) ^ 2
          ∂volume.restrict (Ω : Set (SpatialCoordinates d)) := by
        refine integral_mono_ae ?_ ((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _) ?_
        · refine (aux_aux_macro_energy_recurrence_integrable_weighted a.val (v.2 i) (v.2 i)).congr
            (Filter.Eventually.of_forall fun x => ?_)
          change a.val x * (v.2 i x * v.2 i x) = a.val x * (v.2 i x) ^ 2
          ring
        · filter_upwards [hΛ] with x hx
          exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- Quadratic triangle inequality for local energies of data. -/
theorem aux_aux_macro_energy_recurrence_localEnergy_sub_le {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {S : Set (SpatialCoordinates d)} (hS : MeasurableSet S)
    (u v : SobolevData Ω) :
    localGradientEnergy a hS (sobolevGradient u) ≤
      2 * localGradientEnergy a hS (sobolevGradient v) +
        2 * localGradientEnergy a hS (sobolevGradient (u - v)) := by
  have h := localGradientEnergy_sub_le a hS (sobolevGradient u) (sobolevGradient v)
  rwa [← map_sub] at h

-- ===== MER08_Child =====
/-- The repaired `energy_density` field (upstream `HolderRegularityConclusions` clause 2
normalization of the boundary-datum term). -/
def aux_aux_macro_energy_recurrence_DensityChild {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) : Prop :=
  ∀ (L : ℕ) (om : BilateralField d) (alpha : ℝ), M.delta ≤ Sreg.C⁻¹ →
    alpha ∈ Sreg.alphaRange →
    ∀ (m : ℕ) (y : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (g : SpatialCoordinates d → Fin d → ℝ)
      (hgrad : HilbertGradient (centeredCube y (3 ^ m) hR)),
      (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR :
          Set (SpatialCoordinates d))] fun x => g x i) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => g x i)) →
    ∀ (h u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR))
      (gh : SpatialCoordinates d → Fin d → ℝ),
      (∀ i : Fin d,
        (sobolevGradient (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) i :
            SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            (fun x => gh x i)) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => gh x i)) →
      (∀ φ : killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR),
        sobolevCoefficientForm (Sreg.cutoffOn L om y (3 ^ m) hR)
            (u : SobolevData _) (φ : SobolevData _) =
          -inner ℝ hgrad
            (subspaceGradient (killedSobolevGraph (centeredCube y (3 ^ m) hR)) φ)) →
      ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) -
          (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR))) ∈
        killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR) →
    ∀ (x : SpatialCoordinates d), x ∈ centeredCube y ((3 : ℝ) ^ m) hR →
    ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - Sreg.prefixLen L alpha m y om →
      normalizedEnergyNorm (Sreg.cutoffOn L om y (3 ^ m) hR)
          ((isOpen_ball (x := x) (ε := (3 : ℝ) ^ n / 2)).measurableSet.inter
            (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData _)) ≤
        Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
          (normalizedEnergyNorm (Sreg.cutoffOn L om y (3 ^ m) hR)
              (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet
              (sobolevGradient (u : SobolevData _)) +
            Real.sqrt (Sreg.refAvg L m y om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
              halfHolderSeminorm
                (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) +
        (if x ∈ (centeredCube y ((3 : ℝ) ^ ((m : ℤ) - 1)) (by positivity) :
            Set (SpatialCoordinates d)) then 0 else
          Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) * Real.sqrt (Sreg.refAvg L m y om) *
            halfHolderNorm ((3 : ℝ) ^ m)
              (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
              gh)

/-- Local energy depends on the set only through its value. -/
theorem aux_aux_macro_energy_recurrence_localEnergy_congr {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s t : Set (SpatialCoordinates d)} (hst : s = t)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g = localGradientEnergy a ht g := by
  subst hst; rfl

/-- `3^(N/2) = √(3^N)`. -/
theorem aux_aux_macro_energy_recurrence_rpow_half (N : ℕ) : (3 : ℝ) ^ ((N : ℝ) / 2) = Real.sqrt ((3 : ℝ) ^ N) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-- Volume of a sup-ball intersected with a set. -/
theorem aux_aux_macro_energy_recurrence_ball_inter_volume_le {d : ℕ} (y : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (A : Set (SpatialCoordinates d)) :
    volume.real (Metric.ball y r ∩ A) ≤ (2 * r) ^ d := by
  have hb : volume (Metric.ball y r) = ENNReal.ofReal ((2 * r) ^ d) := by
    rw [Real.volume_pi_ball y hr]; simp
  have hle : volume (Metric.ball y r ∩ A) ≤ volume (Metric.ball y r) :=
    measure_mono Set.inter_subset_left
  have hfin : volume (Metric.ball y r) ≠ ⊤ := by rw [hb]; exact ENNReal.ofReal_ne_top
  calc volume.real (Metric.ball y r ∩ A) ≤ volume.real (Metric.ball y r) :=
        ENNReal.toReal_mono hfin hle
    _ = (2 * r) ^ d := by
        rw [Measure.real, hb, ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)]

theorem aux_aux_macro_energy_recurrence_ball_inter_volume_pos {d : ℕ} (y : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {A : Set (SpatialCoordinates d)} (hA : IsOpen A) (hy : y ∈ A) :
    0 < volume.real (Metric.ball y r ∩ A) := by
  have hpos : 0 < volume (Metric.ball y r ∩ A) :=
    (Metric.isOpen_ball.inter hA).measure_pos volume ⟨y, Metric.mem_ball_self hr, hy⟩
  have hfin : volume (Metric.ball y r ∩ A) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
    rw [Real.volume_pi_ball y hr]; exact ENNReal.ofReal_ne_top
  exact ENNReal.toReal_pos hpos.ne' hfin

/-- Squaring the one-centre inequality. -/
theorem aux_aux_macro_energy_recurrence_sq_algebra (EB VB K a b c c0 : ℝ) (hEB : 0 ≤ EB) (hVB : 0 < VB)
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc0 : 0 ≤ c0) (hc0c : c0 ≤ K * c)
    (hI : Real.sqrt (EB / VB) ≤ K * (a + b) + c0) :
    EB ≤ VB * (3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  have hc : 0 ≤ K * c := hc0.trans hc0c
  have h1 : Real.sqrt (EB / VB) ≤ K * (a + b + c) := by
    calc Real.sqrt (EB / VB) ≤ K * (a + b) + c0 := hI
      _ ≤ K * (a + b) + K * c := by linarith
      _ = K * (a + b + c) := by ring
  have h2 : EB / VB ≤ (K * (a + b + c)) ^ 2 := by
    have hq : 0 ≤ EB / VB := div_nonneg hEB hVB.le
    calc EB / VB = (Real.sqrt (EB / VB)) ^ 2 := (Real.sq_sqrt hq).symm
      _ ≤ (K * (a + b + c)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have h3 : (K * (a + b + c)) ^ 2 ≤ 3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
    calc (K * (a + b + c)) ^ 2 = K ^ 2 * (a + b + c) ^ 2 := by ring
      _ ≤ K ^ 2 * (3 * (a ^ 2 + b ^ 2 + c ^ 2)) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg K)
      _ = 3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
  have h4 : EB / VB ≤ 3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := h2.trans h3
  rwa [div_le_iff₀ hVB, mul_comm] at h4

/-- A `C¹` function has square-integrable partial derivatives on a set inside a compact. -/
theorem aux_aux_macro_energy_recurrence_memLp_fderiv {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (K : Compacts (SpatialCoordinates d)) (hΩK : (Ω : Set (SpatialCoordinates d)) ⊆ K)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ 1 φ) (i : Fin d) :
    MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have hc : Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨B, hB⟩ := K.isCompact.exists_bound_of_continuousOn hc.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    refine isFiniteMeasure_restrict.2 ?_
    exact ne_top_of_le_ne_top K.isCompact.measure_lt_top.ne (measure_mono hΩK)
  refine MemLp.of_bound hc.aestronglyMeasurable B ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hB x (hΩK hx)

-- ===== MER09_Finite =====
/-- The Dirichlet condition survives the physical transport. -/
theorem aux_aux_macro_energy_recurrence_dirichlet_push {d : ℕ} {Q T : Opens (SpatialCoordinates d)} {s : ℝ}
    (hs : 0 < s)
    (hT : (T : Set (SpatialCoordinates d)) = s • (Q : Set (SpatialCoordinates d)))
    (hQT : (Q : Set (SpatialCoordinates d)) = s⁻¹ • (T : Set (SpatialCoordinates d)))
    (u' b : weakSobolevGraph Q)
    (hub : (u' : SobolevData Q) - (b : SobolevData Q) ∈ killedSobolevGraph Q)
    (U hh : weakSobolevGraph T)
    (hU1 : ((U : SobolevData T).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => ((u' : SobolevData Q).1 : SpatialCoordinates d → ℝ) (s⁻¹ • y))
    (hU2 : ∀ i : Fin d, ((U : SobolevData T).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => s⁻¹ * ((u' : SobolevData Q).2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y))
    (hh1 : ((hh : SobolevData T).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) (s⁻¹ • y))
    (hh2 : ∀ i : Fin d, ((hh : SobolevData T).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (T : Set (SpatialCoordinates d))]
      fun y => s⁻¹ * ((b : SobolevData Q).2 i : SpatialCoordinates d → ℝ) (s⁻¹ • y)) :
    (U : SobolevData T) - (hh : SobolevData T) ∈ killedSobolevGraph T := by
  obtain ⟨W, hW1, hW2⟩ := aux_aux_macro_energy_recurrence_killed_unscale (inv_pos.2 hs) hQT
    (⟨(u' : SobolevData Q) - (b : SobolevData Q), hub⟩ : killedSobolevGraph Q)
  have hpush1 := aux_aux_macro_energy_recurrence_ae_push hs Q.isOpen.measurableSet T.isOpen.measurableSet hT
    (Lp.coeFn_sub ((u' : SobolevData Q).1) ((b : SobolevData Q).1))
  have hEq : (U : SobolevData T) - (hh : SobolevData T) = (W : SobolevData T) := by
    refine Prod.ext ?_ (funext fun i => ?_)
    · apply Lp.ext
      filter_upwards [Lp.coeFn_sub ((U : SobolevData T).1) ((hh : SobolevData T).1), hU1, hh1,
        hW1, hpush1] with y e1 e2 e3 e4 e5
      change ((U : SobolevData T).1 - (hh : SobolevData T).1 : DomainL2 T) y = _
      rw [e1, Pi.sub_apply, e2, e3, e4]
      change _ = ((u' : SobolevData Q).1 - (b : SobolevData Q).1 : DomainL2 Q) (s⁻¹ • y)
      rw [e5, Pi.sub_apply]
    · have hpush2 := aux_aux_macro_energy_recurrence_ae_push hs Q.isOpen.measurableSet T.isOpen.measurableSet hT
        (Lp.coeFn_sub ((u' : SobolevData Q).2 i) ((b : SobolevData Q).2 i))
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub ((U : SobolevData T).2 i) ((hh : SobolevData T).2 i), hU2 i,
        hh2 i, hW2 i, hpush2] with y e1 e2 e3 e4 e5
      change ((U : SobolevData T).2 i - (hh : SobolevData T).2 i : DomainL2 T) y = _
      rw [e1, Pi.sub_apply, e2, e3, e4]
      change _ = s⁻¹ * ((u' : SobolevData Q).2 i - (b : SobolevData Q).2 i : DomainL2 Q) (s⁻¹ • y)
      rw [e5, Pi.sub_apply]
      ring
  rw [hEq]
  exact W.2

/-- `halfHolderNorm` and `halfHolderSeminorm` are nonnegative. -/
theorem aux_aux_macro_energy_recurrence_halfHolderSeminorm_nonneg {d k : ℕ} (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin k → ℝ) : 0 ≤ halfHolderSeminorm S g :=
  Real.sSup_nonneg (by
    rintro v ⟨x, _, y, _, _, rfl⟩
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem aux_aux_macro_energy_recurrence_halfHolderNorm_nonneg {d k : ℕ} (r : ℝ) (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin k → ℝ) : 0 ≤ halfHolderNorm r S g :=
  add_nonneg (Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (aux_aux_macro_energy_recurrence_halfHolderSeminorm_nonneg S g))

/-- The pure-algebra tail of the finite estimate. -/
theorem aux_aux_macro_energy_recurrence_finite_algebra (d : ℕ) (ΓB ΓQ form VB VT K a b c s cc refA Cp Kf Cφ gS hN pw : ℝ)
    (hs : 0 < s) (hcc : 0 < cc) (hrefA : 0 < refA) (hVT : VT = s ^ d)
    (hVBle : VB ≤ pw) (hpw : 0 ≤ pw)
    (hEB : cc⁻¹ * s ^ d * (s⁻¹) ^ 2 * ΓB ≤ VB * (3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2)))
    (ha : a ^ 2 = cc⁻¹ * s ^ d * (s⁻¹) ^ 2 * ΓQ / VT) (hΓQ : ΓQ ≤ form)
    (hb : b ^ 2 = refA⁻¹ * s * gS ^ 2) (hgS0 : 0 ≤ gS)
    (hgS : gS ≤ Cp * Real.sqrt s * (cc⁻¹ * (s⁻¹) ^ 2 * Kf))
    (hc : c ^ 2 = refA * hN ^ 2) (hN0 : 0 ≤ hN) (hNle : hN ≤ s⁻¹ * d * Cφ) :
    ΓB ≤ 3 * K ^ 2 * (pw / s ^ d) *
      (form + Cp ^ 2 * (cc * refA)⁻¹ * Kf ^ 2 + (d : ℝ) ^ 2 * (cc * refA) * Cφ ^ 2) := by
  have hsd : 0 < s ^ d := pow_pos hs _
  have hpre : 0 < cc⁻¹ * s ^ d * (s⁻¹) ^ 2 := by positivity
  have ha' : a ^ 2 ≤ cc⁻¹ * (s⁻¹) ^ 2 * form := by
    rw [ha, hVT]
    have : cc⁻¹ * s ^ d * (s⁻¹) ^ 2 * ΓQ / s ^ d = cc⁻¹ * (s⁻¹) ^ 2 * ΓQ := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hΓQ (by positivity)
  have hb' : b ^ 2 ≤ cc⁻¹ * (s⁻¹) ^ 2 * (Cp ^ 2 * (cc * refA)⁻¹ * Kf ^ 2) := by
    rw [hb]
    have hg2 : gS ^ 2 ≤ (Cp * Real.sqrt s * (cc⁻¹ * (s⁻¹) ^ 2 * Kf)) ^ 2 :=
      pow_le_pow_left₀ hgS0 hgS 2
    have hss : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
    calc refA⁻¹ * s * gS ^ 2 ≤ refA⁻¹ * s * (Cp * Real.sqrt s * (cc⁻¹ * (s⁻¹) ^ 2 * Kf)) ^ 2 :=
          mul_le_mul_of_nonneg_left hg2 (by positivity)
      _ = cc⁻¹ * (s⁻¹) ^ 2 * (Cp ^ 2 * (cc * refA)⁻¹ * Kf ^ 2) := by
          rw [mul_pow, mul_pow, hss]
          field_simp
  have hc' : c ^ 2 ≤ cc⁻¹ * (s⁻¹) ^ 2 * ((d : ℝ) ^ 2 * (cc * refA) * Cφ ^ 2) := by
    rw [hc]
    have hN2 : hN ^ 2 ≤ (s⁻¹ * d * Cφ) ^ 2 := pow_le_pow_left₀ hN0 hNle 2
    calc refA * hN ^ 2 ≤ refA * (s⁻¹ * d * Cφ) ^ 2 := mul_le_mul_of_nonneg_left hN2 hrefA.le
      _ = cc⁻¹ * (s⁻¹) ^ 2 * ((d : ℝ) ^ 2 * (cc * refA) * Cφ ^ 2) := by field_simp
  obtain ⟨X, hX⟩ : ∃ X : ℝ,
      X = form + Cp ^ 2 * (cc * refA)⁻¹ * Kf ^ 2 + (d : ℝ) ^ 2 * (cc * refA) * Cφ ^ 2 :=
    ⟨_, rfl⟩
  rw [← hX]
  have habc : a ^ 2 + b ^ 2 + c ^ 2 ≤ cc⁻¹ * (s⁻¹) ^ 2 * X := by
    rw [hX, mul_add, mul_add]
    linarith
  have hK2 : 0 ≤ 3 * K ^ 2 := by positivity
  have habc0 : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have h1 : cc⁻¹ * s ^ d * (s⁻¹) ^ 2 * ΓB ≤ pw * (3 * K ^ 2 * (cc⁻¹ * (s⁻¹) ^ 2 * X)) := by
    refine hEB.trans ?_
    calc VB * (3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2))
        ≤ pw * (3 * K ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2)) :=
          mul_le_mul_of_nonneg_right hVBle (mul_nonneg hK2 habc0)
      _ ≤ pw * (3 * K ^ 2 * (cc⁻¹ * (s⁻¹) ^ 2 * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habc hK2) hpw
  have h2 : pw * (3 * K ^ 2 * (cc⁻¹ * (s⁻¹) ^ 2 * X)) =
      (cc⁻¹ * s ^ d * (s⁻¹) ^ 2) * (3 * K ^ 2 * (pw / s ^ d) * X) := by
    field_simp
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hpre

-- ===== MER10_FiniteMain =====
/-- The statement of the finite-infrared one-centre estimate, for a primitive constant `Cp`. -/
def aux_aux_macro_energy_recurrence_FE {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) : Prop :=
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M),
      aux_aux_macro_energy_recurrence_DensityChild Sreg →
      ∀ (L : ℕ) (om' : BilateralField d) (alpha : ℝ), M.delta ≤ Sreg.C⁻¹ →
        alpha ∈ Sreg.alphaRange →
      ∀ (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
        (a' : PositiveCoefficient (centeredCube z 1 h1)) (c : ℝ), 0 < c →
        (∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
          a'.val x = c * (Sreg.cutoffOn L om' ((3 : ℝ) ^ N • z) (3 ^ N) hR).val
            ((3 : ℝ) ^ N • x)) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
          |F x| ≤ Kf) →
      ∀ (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ), ContDiff ℝ 2 φ →
        c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ →
      ∀ (b u' : weakSobolevGraph (centeredCube z 1 h1)),
        ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ →
        SolvesDirichlet a' F b u' →
      ∀ x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d)), ∀ n : ℕ,
        (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen L alpha N ((3 : ℝ) ^ N • z) om' →
        localGradientEnergy a'
            (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
              MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
                (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
            (sobolevGradient (u' : SobolevData (centeredCube z 1 h1))) ≤
          3 * (Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n))) ^ 2 *
            (((3 : ℝ) ^ n) ^ d / ((3 : ℝ) ^ N) ^ d) *
            (sobolevCoefficientForm a' (u' : SobolevData _) (u' : SobolevData _) +
              Cp ^ 2 * (c * Sreg.refAvg L N ((3 : ℝ) ^ N • z) om')⁻¹ * Kf ^ 2 +
              (d : ℝ) ^ 2 * (c * Sreg.refAvg L N ((3 : ℝ) ^ N • z) om') * Cφ ^ 2)

/-- **Finite-infrared one-centre estimate** (paper `eq:mfd-macro`, lines 619-625), from the
repaired energy-density field. -/
theorem aux_aux_macro_energy_recurrence_finite_estimate {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cp : ℝ, 0 < Cp ∧ aux_aux_macro_energy_recurrence_FE (d := d) Cp := by
  obtain ⟨Cp, hCp, hphys⟩ := aux_aux_macro_energy_recurrence_physical_problem hd
  refine ⟨Cp, hCp, ?_⟩
  unfold aux_aux_macro_energy_recurrence_FE
  intro M Sreg hchild L om' alpha hδ hα N z h1 hR a' c hc hcoef F Kf hKf hFm hFb φ Cφ hφ hCφ
    b u' hb hsol x hx n hn
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hT : (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) =
      (3 : ℝ) ^ N • (centeredCube z 1 h1 : Set (SpatialCoordinates d)) :=
    aux_aux_macro_energy_recurrence_cube_smul_one z hR h1 hR
  have hQT : (centeredCube z 1 h1 : Set (SpatialCoordinates d)) =
      ((3 : ℝ) ^ N)⁻¹ • (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
        Set (SpatialCoordinates d)) := by
    rw [hT, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  -- physical transports of the solution and of the datum
  obtain ⟨U, hU1, hU2⟩ := aux_aux_macro_energy_recurrence_weak_unscale (inv_pos.2 hR) hQT u'
  obtain ⟨hh, hh1, hh2⟩ := aux_aux_macro_energy_recurrence_weak_unscale (inv_pos.2 hR) hQT b
  have hDir := aux_aux_macro_energy_recurrence_dirichlet_push hR hT hQT u' b hsol.1 U hh hU1 hU2 hh1 hh2
  -- the physical equation and source primitive
  have hPP := hphys (centeredCube z 1 h1) ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR ((3 : ℝ) ^ N) c
    hR hc hT (Sreg.cutoffOn L om' ((3 : ℝ) ^ N • z) (3 ^ N) hR) a' hcoef F Kf hKf hFm hFb b u'
    hsol (U : SobolevData _) hU2
  obtain ⟨g, hgrad, hgi, hgH, hgS, heq⟩ := hPP
  -- the datum
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hbgrad := aux_aux_macro_energy_recurrence_datum_grad φ hφ1 b hb
    (fun i => aux_aux_macro_energy_recurrence_memLp_fderiv (closedCube z 1 h1) (centeredCube_subset_closedCube z h1)
      φ hφ1 i)
  have hghtie : ∀ i : Fin d,
      (sobolevGradient (hh : SobolevData (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR)) i :
          SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
          Set (SpatialCoordinates d))] (fun y => aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N) y i) := by
    intro i
    have hp := aux_aux_macro_energy_recurrence_ae_push hR (centeredCube z 1 h1).isOpen.measurableSet
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet hT (hbgrad i)
    filter_upwards [hh2 i, hp] with y e1 e2
    change ((hh : SobolevData (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR)).2 i :
      SpatialCoordinates d → ℝ) y = _
    rw [e1, e2]
    rfl
  obtain ⟨hghH, hghN⟩ := aux_aux_macro_energy_recurrence_gh_bounds hd1 z h1 hR hR φ hφ Cφ hCφ
  have hxT : (3 : ℝ) ^ N • x ∈
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) := by
    rw [hT]; exact Set.smul_mem_smul_set hx
  -- apply the repaired energy-density field
  have hI := hchild L om' alpha hδ hα N ((3 : ℝ) ^ N • z) hR g hgrad hgi hgH hh U
    (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N)) hghtie hghH heq hDir ((3 : ℝ) ^ N • x) hxT n hn
  -- names for the pieces
  obtain ⟨aT, haT⟩ : ∃ aT : PositiveCoefficient
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR),
      aT = Sreg.cutoffOn L om' ((3 : ℝ) ^ N • z) (3 ^ N) hR := ⟨_, rfl⟩
  rw [← haT] at hI hcoef
  -- ball geometry
  have hball : (3 : ℝ) ^ N • (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
      (centeredCube z 1 h1 : Set (SpatialCoordinates d))) =
      Metric.ball ((3 : ℝ) ^ N • x) ((3 : ℝ) ^ n / 2) ∩
        (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) := by
    rw [aux_aux_macro_energy_recurrence_ball_inter_smul x _ _ hR, ← hT, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  have hSmeas : MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
      (centeredCube z 1 h1 : Set (SpatialCoordinates d))) :=
    isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet
  have hsSmeas : MeasurableSet ((3 : ℝ) ^ N • (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
      (centeredCube z 1 h1 : Set (SpatialCoordinates d)))) := by
    rw [hball]
    exact isOpen_ball.measurableSet.inter
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet
  have hsQmeas : MeasurableSet ((3 : ℝ) ^ N • (centeredCube z 1 h1 : Set (SpatialCoordinates d))) := by
    rw [← hT]; exact (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet
  -- energy scalings
  have hEB := aux_aux_macro_energy_recurrence_localEnergy_scale hR hc hT aT a' hcoef (U : SobolevData _)
    (u' : SobolevData _) hU2 hSmeas hsSmeas
  rw [aux_aux_macro_energy_recurrence_localEnergy_congr aT hball hsSmeas
    (isOpen_ball.measurableSet.inter
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet)] at hEB
  have hET := aux_aux_macro_energy_recurrence_localEnergy_scale hR hc hT aT a' hcoef (U : SobolevData _)
    (u' : SobolevData _) hU2 (centeredCube z 1 h1).isOpen.measurableSet hsQmeas
  rw [aux_aux_macro_energy_recurrence_localEnergy_congr aT hT.symm hsQmeas
    (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet] at hET
  -- unfold the normalized norms in the field inequality
  unfold normalizedEnergyNorm at hI
  rw [hEB, hET] at hI
  have hVB := aux_aux_macro_energy_recurrence_ball_inter_volume_pos ((3 : ℝ) ^ N • x)
    (by positivity : (0 : ℝ) < (3 : ℝ) ^ n / 2)
    (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen hxT
  have hVBle := aux_aux_macro_energy_recurrence_ball_inter_volume_le ((3 : ℝ) ^ N • x)
    (by positivity : (0 : ℝ) < (3 : ℝ) ^ n / 2)
    (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
  have hVT := centeredCube_volume_real ((3 : ℝ) ^ N • z) hR
  have hrefA := Sreg.refAvg_pos L N ((3 : ℝ) ^ N • z) om'
  have hK0 : 0 ≤ Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n)) :=
    mul_nonneg Sreg.C_pos.le (Real.rpow_nonneg (by norm_num) _)
  have hΓB0 : 0 ≤ localGradientEnergy a' hSmeas (sobolevGradient (u' : SobolevData _)) :=
    localGradientEnergy_nonneg _ _ _
  have hΓQ0 : 0 ≤ localGradientEnergy a' (centeredCube z 1 h1).isOpen.measurableSet
      (sobolevGradient (u' : SobolevData _)) := localGradientEnergy_nonneg _ _ _
  have hpre0 : 0 ≤ c⁻¹ * ((3 : ℝ) ^ N) ^ d * (((3 : ℝ) ^ N)⁻¹) ^ 2 := by positivity
  -- the field inequality in the form of `aux_aux_macro_energy_recurrence_sq_algebra`
  have hIc : Real.sqrt (c⁻¹ * ((3 : ℝ) ^ N) ^ d * (((3 : ℝ) ^ N)⁻¹) ^ 2 *
        localGradientEnergy a' hSmeas (sobolevGradient (u' : SobolevData _)) /
        volume.real (Metric.ball ((3 : ℝ) ^ N • x) ((3 : ℝ) ^ n / 2) ∩
          (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)))) ≤
      (Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n))) *
        (Real.sqrt (c⁻¹ * ((3 : ℝ) ^ N) ^ d * (((3 : ℝ) ^ N)⁻¹) ^ 2 *
            localGradientEnergy a' (centeredCube z 1 h1).isOpen.measurableSet
              (sobolevGradient (u' : SobolevData _)) /
            volume.real (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
              Set (SpatialCoordinates d))) +
          Real.sqrt (Sreg.refAvg L N ((3 : ℝ) ^ N • z) om')⁻¹ * (3 : ℝ) ^ ((N : ℝ) / 2) *
            halfHolderSeminorm (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
              Set (SpatialCoordinates d)) g) +
      (if (3 : ℝ) ^ N • x ∈ (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ ((N : ℤ) - 1))
          (by positivity) : Set (SpatialCoordinates d)) then 0 else
        Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n)) *
          Real.sqrt (Sreg.refAvg L N ((3 : ℝ) ^ N • z) om') *
          halfHolderNorm ((3 : ℝ) ^ N)
            (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
            (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N))) := hI
  have hc0 : 0 ≤ (if (3 : ℝ) ^ N • x ∈ (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ ((N : ℤ) - 1))
          (by positivity) : Set (SpatialCoordinates d)) then (0 : ℝ) else
        Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n)) *
          Real.sqrt (Sreg.refAvg L N ((3 : ℝ) ^ N • z) om') *
          halfHolderNorm ((3 : ℝ) ^ N)
            (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
            (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N))) := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg _))
        (aux_aux_macro_energy_recurrence_halfHolderNorm_nonneg _ _ _)
  have hc0c : (if (3 : ℝ) ^ N • x ∈ (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ ((N : ℤ) - 1))
          (by positivity) : Set (SpatialCoordinates d)) then (0 : ℝ) else
        Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n)) *
          Real.sqrt (Sreg.refAvg L N ((3 : ℝ) ^ N • z) om') *
          halfHolderNorm ((3 : ℝ) ^ N)
            (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
            (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N))) ≤
      (Sreg.C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n))) *
        (Real.sqrt (Sreg.refAvg L N ((3 : ℝ) ^ N • z) om') *
          halfHolderNorm ((3 : ℝ) ^ N)
            (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
            (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N))) := by
    split_ifs
    · exact mul_nonneg hK0 (mul_nonneg (Real.sqrt_nonneg _) (aux_aux_macro_energy_recurrence_halfHolderNorm_nonneg _ _ _))
    · rw [mul_assoc]
  have hsq := aux_aux_macro_energy_recurrence_sq_algebra _ _ _ _ _ _ _ (mul_nonneg hpre0 hΓB0) hVB hK0
    (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg
      (by norm_num) _)) (aux_aux_macro_energy_recurrence_halfHolderSeminorm_nonneg _ _)) hc0 hc0c hIc
  -- the algebra
  have hmain := aux_aux_macro_energy_recurrence_finite_algebra d
    (localGradientEnergy a' hSmeas (sobolevGradient (u' : SobolevData _)))
    (localGradientEnergy a' (centeredCube z 1 h1).isOpen.measurableSet
      (sobolevGradient (u' : SobolevData _)))
    (sobolevCoefficientForm a' (u' : SobolevData _) (u' : SobolevData _))
    _ _ _ _ _ _ ((3 : ℝ) ^ N) c (Sreg.refAvg L N ((3 : ℝ) ^ N • z) om') Cp Kf Cφ
    (halfHolderSeminorm (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR :
      Set (SpatialCoordinates d)) g)
    (halfHolderNorm ((3 : ℝ) ^ N)
      (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d))
      (aux_aux_macro_energy_recurrence_gh φ ((3 : ℝ) ^ N)))
    ((2 * ((3 : ℝ) ^ n / 2)) ^ d)
    hR hc hrefA hVT hVBle (by positivity) hsq
    (by rw [Real.sq_sqrt (by
          exact div_nonneg (mul_nonneg hpre0 hΓQ0) (by rw [hVT]; positivity))])
    ((localGradientEnergy_le _ _ _).trans_eq rfl)
    (by
      rw [mul_pow, mul_pow, Real.sq_sqrt (inv_nonneg.2 hrefA.le), aux_aux_macro_energy_recurrence_rpow_half,
        Real.sq_sqrt (by positivity)])
    (aux_aux_macro_energy_recurrence_halfHolderSeminorm_nonneg _ _) hgS
    (by rw [mul_pow, Real.sq_sqrt hrefA.le])
    (aux_aux_macro_energy_recurrence_halfHolderNorm_nonneg _ _ _) hghN
  have hpw : (2 * ((3 : ℝ) ^ n / 2)) ^ d = ((3 : ℝ) ^ n) ^ d := by
    congr 1; ring
  rw [hpw] at hmain
  exact hmain

-- ===== MER11_Reference =====
/-- The spatially relabelled field of the physical rescaling. -/
def aux_aux_macro_energy_recurrence_relabel {d : ℕ} (N : ℕ) (om : BilateralField d) : BilateralField d :=
  fun j => ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
      continuous_const.smul continuous_id⟩ : C(SpatialCoordinates d, SpatialCoordinates d))
    (om (j - (N : ℤ)))

theorem aux_aux_macro_energy_recurrence_relabel_apply {d : ℕ} (om : BilateralField d) (N : ℕ) (j : ℤ)
    (y : SpatialCoordinates d) :
    (aux_aux_macro_energy_recurrence_relabel N om j) ((3 : ℝ) ^ N • y) = om (j - (N : ℤ)) y := by
  change (om (j - (N : ℤ))) ((3 : ℝ) ^ (-(N : ℤ)) • (3 : ℝ) ^ N • y) = _
  rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]

/-- The bottom `N+1` layers of the relabelled field are the layers `0, -1, …, -N`. -/
theorem aux_aux_macro_energy_recurrence_reflect_sum {d : ℕ} (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    ∑ j ∈ Finset.range (N + 1), (om ((j : ℤ) - (N : ℤ))) x =
      ∑ j ∈ Finset.range (N + 1), (om (-Int.ofNat j)) x := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  congr 2
  rw [show N + 1 - 1 - j = N - j by omega, Nat.cast_sub hjN, Int.ofNat_eq_natCast]
  ring

/-- `c · refAvg` as an integral over the working cube. -/
theorem aux_aux_macro_energy_recurrence_reference_eq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N L' : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (aFin : PositiveCoefficient (centeredCube z 1 h1)) (cFin : ℝ)
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val x = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om) ((3 : ℝ) ^ N • z)
        (3 ^ N) hR).val ((3 : ℝ) ^ N • x)) :
    cFin * Sreg.refAvg (N + L') N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) =
      ∫ x in (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        aFin.val x * (Real.exp (H om x) / cutoffCoefficient M H om N x) := by
  have hT : (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR : Set (SpatialCoordinates d)) =
      (3 : ℝ) ^ N • (centeredCube z 1 h1 : Set (SpatialCoordinates d)) :=
    aux_aux_macro_energy_recurrence_cube_smul_one z hR h1 hR
  rw [Sreg.refAvg_eq (N + L') N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) hR,
    centeredCube_volume_real, aux_aux_macro_energy_recurrence_integral_T hR hT]
  have hmin : min N (N + L') = N := min_eq_left (Nat.le_add_right N L')
  have hminR : min ((N : ℝ)) (((N + L' : ℕ) : ℝ)) = (N : ℝ) :=
    min_eq_left (by exact_mod_cast Nat.le_add_right N L')
  simp only [hmin, hminR]
  -- pull back the layer formula of the cutoff coefficient
  have hcut := aux_aux_macro_energy_recurrence_ae_pull hR (centeredCube z 1 h1).isOpen.measurableSet
    (centeredCube ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR).isOpen.measurableSet hT
    (Sreg.cutoffOn_eq (N + L') (aux_aux_macro_energy_recurrence_relabel N om) ((3 : ℝ) ^ N • z) ((3 : ℝ) ^ N) hR)
  rw [inv_mul_cancel_left₀ (by positivity : ((3 : ℝ) ^ N) ^ d ≠ 0), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hcoef, hcut] with x hx1 hx2
  rw [hx1, hx2]
  simp only [aux_aux_macro_energy_recurrence_relabel_apply, cutoffCoefficient, cutoffPotential]
  rw [aux_aux_macro_energy_recurrence_reflect_sum]
  have hpos := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  rw [div_eq_mul_inv, mul_inv, inv_inv, ← Real.exp_neg]
  have e1 : Real.exp (∑ j ∈ Finset.range (N + L' + 1), (om ((j : ℤ) - (N : ℤ))) x -
        ∑ j ∈ Finset.range (N + 1), (om (-Int.ofNat j)) x -
        (((N + L' : ℕ) : ℝ) - (N : ℝ)) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (∑ j ∈ Finset.range (N + L' + 1), (om ((j : ℤ) - (N : ℤ))) x -
          ((N + L' : ℕ) + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        (Real.exp (H om x) * Real.exp (-((H om) x + ∑ j ∈ Finset.range (N + 1),
          (om (-Int.ofNat j)) x - ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [e1]
  ring

/-- **Reference bounds.** Both `ρ = c · refAvg` and `ρ⁻¹` are at most `2 Kr`. -/
theorem aux_aux_macro_energy_recurrence_reference_bounds {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N L' : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (aFin : PositiveCoefficient (centeredCube z 1 h1)) (cFin : ℝ)
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val x = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om) ((3 : ℝ) ^ N • z)
        (3 ^ N) hR).val ((3 : ℝ) ^ N • x))
    (lam η Kr : ℝ) (hlam : 0 < lam) (hηl : η ≤ lam / 2)
    (hA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hη : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val x - cutoffCoefficient M H om N x| ≤ η)
    (hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)), Real.exp |H om x| ≤ Kr) :
    cFin * Sreg.refAvg (N + L') N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ 2 * Kr ∧
      (cFin * Sreg.refAvg (N + L') N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))⁻¹ ≤ 2 * Kr := by
  rw [aux_aux_macro_energy_recurrence_reference_eq Sreg H om N L' z h1 hR aFin cFin hcoef]
  set Q : Set (SpatialCoordinates d) := (centeredCube z 1 h1 : Set (SpatialCoordinates d))
    with hQ
  have hKr1 : 1 ≤ Kr := (Real.one_le_exp (abs_nonneg (H om z))).trans
    (hKr z (Metric.mem_closedBall_self (by norm_num)))
  have hKr0 : 0 < Kr := lt_of_lt_of_le one_pos hKr1
  set g : SpatialCoordinates d → ℝ :=
    fun x => aFin.val x * (Real.exp (H om x) / cutoffCoefficient M H om N x) with hg
  -- pointwise bounds on the working cube
  have hbd : ∀ᵐ x ∂volume.restrict Q, (2 * Kr)⁻¹ ≤ g x ∧ g x ≤ 3 / 2 * Kr := by
    filter_upwards [hη, ae_restrict_mem (centeredCube z 1 h1).isOpen.measurableSet] with x hx hxQ
    have hxK : x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)) :=
      centeredCube_subset_closedCube z h1 hxQ
    have hAx := hA x hxK
    have hApos : 0 < cutoffCoefficient M H om N x := lt_of_lt_of_le hlam hAx
    have hratio_lo : 1 / 2 ≤ aFin.val x / cutoffCoefficient M H om N x := by
      rw [le_div_iff₀ hApos]
      have := (abs_le.1 hx).1
      linarith
    have hratio_hi : aFin.val x / cutoffCoefficient M H om N x ≤ 3 / 2 := by
      rw [div_le_iff₀ hApos]
      have := (abs_le.1 hx).2
      linarith
    have hE_hi : Real.exp (H om x) ≤ Kr :=
      (Real.exp_le_exp.2 (le_abs_self _)).trans (hKr x hxK)
    have hE_lo : Kr⁻¹ ≤ Real.exp (H om x) := by
      have h1' : Real.exp (-|H om x|) ≤ Real.exp (H om x) :=
        Real.exp_le_exp.2 (neg_abs_le _)
      have h2' : Kr⁻¹ ≤ Real.exp (-|H om x|) := by
        rw [Real.exp_neg]
        exact inv_anti₀ (Real.exp_pos _) (hKr x hxK)
      exact h2'.trans h1'
    have hgx : g x = (aFin.val x / cutoffCoefficient M H om N x) * Real.exp (H om x) := by
      rw [hg]; ring
    rw [hgx]
    constructor
    · calc (2 * Kr)⁻¹ = 1 / 2 * Kr⁻¹ := by rw [mul_inv]; ring
        _ ≤ (aFin.val x / cutoffCoefficient M H om N x) * Real.exp (H om x) :=
            mul_le_mul hratio_lo hE_lo (inv_nonneg.2 hKr0.le) (by linarith)
    · exact mul_le_mul hratio_hi hE_hi (Real.exp_pos _).le (by norm_num)
  haveI : IsFiniteMeasure (volume.restrict Q) := by rw [hQ]; infer_instance
  have hvol0 : volume.real Q = 1 := by
    rw [hQ, centeredCube_volume_real]; norm_num
  have hvol : (volume.restrict Q).real univ = 1 := by
    rw [Measure.real, Measure.restrict_apply_univ]; exact hvol0
  have hmeas : AEStronglyMeasurable g (volume.restrict Q) := by
    have h1m : AEStronglyMeasurable (fun x => aFin.val x) (volume.restrict Q) :=
      (Lp.aestronglyMeasurable aFin.val)
    have h2m : Continuous (fun x => Real.exp (H om x) / cutoffCoefficient M H om N x) := by
      refine (Real.continuous_exp.comp (H om).continuous).div ?_ ?_
      · refine continuous_const.mul (Real.continuous_exp.comp ?_)
        exact Continuous.sub (Continuous.add (H om).continuous
          (continuous_finset_sum _ fun j _ => (om (-(Int.ofNat j))).continuous)) continuous_const
      · intro x
        exact (mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)).ne'
    exact h1m.mul h2m.aestronglyMeasurable
  have hint : Integrable g (volume.restrict Q) := by
    refine (memLp_top_of_bound hmeas (3 / 2 * Kr) ?_).integrable le_top
    filter_upwards [hbd] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [hx.1, hx.2, inv_pos.2 (mul_pos two_pos hKr0)]
  have hup : ∫ x in Q, g x ≤ 3 / 2 * Kr := by
    have := integral_mono_ae hint (integrable_const (3 / 2 * Kr)) (hbd.mono fun x hx => hx.2)
    rwa [integral_const, smul_eq_mul, hvol, one_mul] at this
  have hlo : (2 * Kr)⁻¹ ≤ ∫ x in Q, g x := by
    have := integral_mono_ae (integrable_const (2 * Kr)⁻¹) hint (hbd.mono fun x hx => hx.1)
    rwa [integral_const, smul_eq_mul, hvol, one_mul] at this
  refine ⟨hup.trans (by linarith), ?_⟩
  have hpos : 0 < ∫ x in Q, g x := lt_of_lt_of_le (inv_pos.2 (mul_pos two_pos hKr0)) hlo
  calc (∫ x in Q, g x)⁻¹ ≤ ((2 * Kr)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (mul_pos two_pos hKr0)) hlo
    _ = 2 * Kr := inv_inv _

-- ===== MER12_Core =====


theorem aux_aux_macro_energy_recurrence_coeff_ae {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N z hr).val y = cutoffCoefficient M H om N y := by
  let Ω := centeredCube z r hr
  letI : Fact (((Ω : Set (SpatialCoordinates d)) ⊆ closedCube z r hr)) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hexp := expPotentialCoefficient_coeFn (compactPotentialToLp (Ω := Ω) (closedCube z r hr)
      (continuousPositiveLog (cutoffCoefficientCM M H om N z hr)
        (cutoffCoefficientCM_pos M H om N z hr) -
        ContinuousMap.const (closedCube z r hr) (Real.log 1)))
  have hroot := compactPotentialToLp_on_domain (Ω := Ω) (closedCube z r hr)
      (continuousPositiveLog (cutoffCoefficientCM M H om N z hr)
        (cutoffCoefficientCM_pos M H om N z hr) -
        ContinuousMap.const (closedCube z r hr) (Real.log 1))
  filter_upwards [hexp, hroot, ae_restrict_mem Ω.isOpen.measurableSet] with y hy1 hy2 hyΩ
  change (normalizedContinuousPositiveCoefficient (Ω := Ω) (closedCube z r hr)
    (cutoffCoefficientCM M H om N z hr) (cutoffCoefficientCM_pos M H om N z hr) 1 one_pos).val y = _
  unfold normalizedContinuousPositiveCoefficient
  rw [hy1, hy2 hyΩ]
  change Real.exp (Real.log (cutoffCoefficientCM M H om N z hr ⟨y, _⟩) - Real.log 1) = _
  rw [Real.log_one, sub_zero, Real.exp_log (cutoffCoefficientCM_pos M H om N z hr _)]
  rfl

theorem aux_aux_macro_energy_recurrence_form_le_gradSq {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (Λ : ℝ)
    (hΛ : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ Λ)
    (v : SobolevData Ω) :
    sobolevCoefficientForm a v v ≤ Λ * aux_aux_macro_energy_recurrence_gradSq v := by
  rw [aux_aux_macro_energy_recurrence_sobolevCoefficientForm_apply, aux_aux_macro_energy_recurrence_gradSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← integral_const_mul]
  refine integral_mono_ae (aux_aux_macro_energy_recurrence_integrable_weighted _ _ _)
    ((aux_aux_macro_energy_recurrence_integrable_sq _).const_mul _) ?_
  filter_upwards [hΛ] with x hx
  calc a.val x * (v.2 i x * v.2 i x) = a.val x * (v.2 i x) ^ 2 := by ring
    _ ≤ Λ * (v.2 i x) ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)

theorem aux_aux_macro_energy_recurrence_gradSq_sub_comm {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (x y : SobolevData Ω) : aux_aux_macro_energy_recurrence_gradSq (x - y) = aux_aux_macro_energy_recurrence_gradSq (y - x) := by
  unfold aux_aux_macro_energy_recurrence_gradSq
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (x.2 i) (y.2 i), Lp.coeFn_sub (y.2 i) (x.2 i)] with p h1 h2
  change ((x.2 i - y.2 i : DomainL2 Ω) p) ^ 2 = ((y.2 i - x.2 i : DomainL2 Ω) p) ^ 2
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply]
  ring

/-- The real-number energy chain of the truncation removal. -/
theorem aux_aux_macro_energy_recurrence_energy_chain (ΓAu ΓAu' ΓAw Γa'u' fa'u' fAu' fAu fAw W P ρ Kr Cp Kf Cφ dd Λ : ℝ)
    (hΓ1 : ΓAu ≤ 2 * ΓAu' + 2 * ΓAw) (hΓ2 : ΓAu' ≤ 2 * Γa'u') (hΓ3 : ΓAw ≤ Λ * W)
    (hfin : Γa'u' ≤ P * (fa'u' + Cp ^ 2 * ρ⁻¹ * Kf ^ 2 + dd ^ 2 * ρ * Cφ ^ 2))
    (hP : 0 ≤ P) (hρ : ρ ≤ 2 * Kr) (hρi : ρ⁻¹ ≤ 2 * Kr) (hρ0 : 0 < ρ)
    (hf1 : fa'u' ≤ 2 * fAu') (hf2 : fAu' ≤ 2 * fAu + 2 * fAw) (hf3 : fAw ≤ Λ * W) :
    ΓAu ≤ 16 * P * fAu + 8 * P * Kr * (Cp ^ 2 * Kf ^ 2 + dd ^ 2 * Cφ ^ 2) +
      (16 * P + 2) * Λ * W := by
  have hK1 : Cp ^ 2 * ρ⁻¹ * Kf ^ 2 ≤ Cp ^ 2 * (2 * Kr) * Kf ^ 2 := by
    have := mul_le_mul_of_nonneg_left hρi (sq_nonneg Cp)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg Kf)
  have hK2 : dd ^ 2 * ρ * Cφ ^ 2 ≤ dd ^ 2 * (2 * Kr) * Cφ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hρ (sq_nonneg dd)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg Cφ)
  have hbr : fa'u' + Cp ^ 2 * ρ⁻¹ * Kf ^ 2 + dd ^ 2 * ρ * Cφ ^ 2 ≤
      2 * (2 * fAu + 2 * (Λ * W)) + 2 * Kr * (Cp ^ 2 * Kf ^ 2 + dd ^ 2 * Cφ ^ 2) := by
    nlinarith
  have hfin' : Γa'u' ≤ P * (2 * (2 * fAu + 2 * (Λ * W)) +
      2 * Kr * (Cp ^ 2 * Kf ^ 2 + dd ^ 2 * Cφ ^ 2)) :=
    hfin.trans (mul_le_mul_of_nonneg_left hbr hP)
  nlinarith

-- ===== MER13_Passage =====
/-- The scale factor `3 C² 3^{2(1-α)(N-n)} (3^n/3^N)^d` of the one-centre estimate. -/
def aux_aux_macro_energy_recurrence_P {d : ℕ} (C alpha : ℝ) (N n : ℕ) : ℝ :=
  3 * (C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n))) ^ 2 * (((3 : ℝ) ^ n) ^ d / ((3 : ℝ) ^ N) ^ d)

theorem aux_aux_macro_energy_recurrence_P_nonneg {d : ℕ} (C alpha : ℝ) (N n : ℕ) : 0 ≤ aux_aux_macro_energy_recurrence_P (d := d) C alpha N n := by
  unfold aux_aux_macro_energy_recurrence_P; positivity

/-- One prefix-good infrared cutoff. -/
theorem aux_aux_macro_energy_recurrence_core_step {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (alpha : ℝ) (hδ : M.delta ≤ Sreg.C⁻¹)
    (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Λ Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hΛA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      cutoffCoefficient M H om N x ≤ Λ)
    (hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)), Real.exp |H om x| ≤ Kr)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
    (n : ℕ) (L' : ℕ) (aFin : PositiveCoefficient (centeredCube z 1 h1)) (cFin : ℝ)
    (hcF : 0 < cFin)
    (hcoef : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val y = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om) ((3 : ℝ) ^ N • z)
        (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (η : ℝ) (hηl : η ≤ lam / 2)
    (hη : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - cutoffCoefficient M H om N y| < η)
    (hn : (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om)) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
        (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
          MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
        (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
            (u : SobolevData _) (u : SobolevData _) +
        8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n * Kr *
          (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) +
        (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
          (4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) := by
  obtain ⟨A, hAdef⟩ : ∃ A : PositiveCoefficient (centeredCube z 1 h1),
      A = cutoffPositiveCoefficient M H om N z h1 := ⟨_, rfl⟩
  rw [← hAdef] at hu ⊢
  have hAae : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      A.val y = cutoffCoefficient M H om N y := by
    rw [hAdef]; exact aux_aux_macro_energy_recurrence_coeff_ae M H om N z h1
  have hmem := ae_restrict_mem (μ := volume) (centeredCube z 1 h1).isOpen.measurableSet
  have hAl : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ A.val y := by
    filter_upwards [hAae, hmem] with y h1' h2'
    rw [h1']; exact hlamA y (centeredCube_subset_closedCube z h1 h2')
  have hAL : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      A.val y ≤ Λ := by
    filter_upwards [hAae, hmem] with y h1' h2'
    rw [h1']; exact hΛA y (centeredCube_subset_closedCube z h1 h2')
  have hη' : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - A.val y| ≤ η := by
    filter_upwards [hAae, hη] with y h1' h2'
    rw [h1']; exact h2'.le
  have hA2 : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      A.val y ≤ 2 * aFin.val y := by
    filter_upwards [hAl, hη'] with y h1' h2'
    have := (abs_le.1 h2').1
    linarith
  have ha2 : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val y ≤ 2 * A.val y := by
    filter_upwards [hAl, hη'] with y h1' h2'
    have := (abs_le.1 h2').2
    linarith
  have hP := aux_aux_macro_moment_bank_killed_poincare hd z 1 h1
  obtain ⟨u', hu'⟩ := aux_aux_macro_energy_recurrence_exists_solution hP aFin F Kf hFm hFb b
  have hfin := hFE M Sreg hchild (N + L') (aux_aux_macro_energy_recurrence_relabel N om) alpha hδ hα N z h1 hR aFin cFin
    hcF hcoef F Kf hKf hFm hFb φ Cφ hφ hCφ b u' hb hu' x hx n hn
  have href := aux_aux_macro_energy_recurrence_reference_bounds Sreg H om N L' z h1 hR aFin cFin hcoef lam η Kr hlam hηl
    hlamA (hη.mono fun y hy => hy.le) hKr
  have hstab := aux_aux_macro_energy_recurrence_stability A aFin lam η hlam hAl hη' hηl F b u u' hu hu'
  have hB : MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
      (centeredCube z 1 h1 : Set (SpatialCoordinates d))) :=
    isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet
  have hΓ1 := aux_aux_macro_energy_recurrence_localEnergy_sub_le A hB (u : SobolevData _) (u' : SobolevData _)
  have hΓ2 := localGradientEnergy_le_mul A aFin 2 hA2 hB
    (sobolevGradient (u' : SobolevData (centeredCube z 1 h1)))
  have hΓ3 := aux_aux_macro_energy_recurrence_localEnergy_le_gradSq A Λ hAL hB
    ((u : SobolevData (centeredCube z 1 h1)) - (u' : SobolevData _))
  have hf1 : sobolevCoefficientForm aFin (u' : SobolevData _) (u' : SobolevData _) ≤
      2 * sobolevCoefficientForm A (u' : SobolevData _) (u' : SobolevData _) :=
    weightedGradientForm_le_mul aFin A 2 ha2 _
  have hf2 := bilinear_quadratic_sub_le (sobolevCoefficientForm A)
    (sobolevCoefficientForm_symm A) (sobolevCoefficientForm_nonneg A)
    (u' : SobolevData (centeredCube z 1 h1)) (u : SobolevData _)
  have hf3 : sobolevCoefficientForm A ((u' : SobolevData (centeredCube z 1 h1)) -
        (u : SobolevData (centeredCube z 1 h1)))
      ((u' : SobolevData (centeredCube z 1 h1)) - (u : SobolevData (centeredCube z 1 h1))) ≤
      Λ * aux_aux_macro_energy_recurrence_gradSq ((u : SobolevData (centeredCube z 1 h1)) -
        (u' : SobolevData (centeredCube z 1 h1))) := by
    rw [aux_aux_macro_energy_recurrence_gradSq_sub_comm]
    exact aux_aux_macro_energy_recurrence_form_le_gradSq A Λ hAL _
  have hρ0 : 0 < cFin * Sreg.refAvg (N + L') N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) :=
    mul_pos hcF (Sreg.refAvg_pos _ _ _ _)
  have hchain := aux_aux_macro_energy_recurrence_energy_chain _ _ _ _ _ _ _ _ _ _ _ Kr Cp Kf Cφ (d : ℝ) Λ hΓ1 hΓ2 hΓ3
    hfin (aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n) href.1 href.2 hρ0 hf1 hf2 hf3
  have hΛ0 : 0 ≤ Λ := by
    have := (hlamA z (Metric.mem_closedBall_self (by norm_num))).trans
      (hΛA z (Metric.mem_closedBall_self (by norm_num)))
    linarith
  have hcoefP : 0 ≤ (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ :=
    mul_nonneg (by linarith [aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n]) hΛ0
  unfold aux_aux_macro_energy_recurrence_P at hchain ⊢
  calc _ ≤ _ := hchain
    _ ≤ _ := by
      gcongr

/-- **The one-centre estimate for the actual coefficient** (η → 0 along prefix-good cutoffs). -/
theorem aux_aux_macro_energy_recurrence_core {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (alpha : ℝ) (hδ : M.delta ≤ Sreg.C⁻¹)
    (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Λ Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hΛA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      cutoffCoefficient M H om N x ≤ Λ)
    (hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)), Real.exp |H om x| ≤ Kr)
    (aFin : ℕ → PositiveCoefficient (centeredCube z 1 h1))
    (hfinc : ∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (aFin L').val y = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om)
          ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        |(aFin L').val y - cutoffCoefficient M H om N y| < ε)
    (P0 : ℕ) (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
    (n : ℕ) (hn : (n : ℤ) ≤ (N : ℤ) - P0) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
        (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
          MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
        (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
            (u : SobolevData _) (u : SobolevData _) +
        8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n * Kr *
          (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) := by
  have hΛ0 : 0 ≤ Λ := by
    have := (hlamA z (Metric.mem_closedBall_self (by norm_num))).trans
      (hΛA z (Metric.mem_closedBall_self (by norm_num)))
    linarith
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    have := aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n
    have := aux_aux_macro_energy_recurrence_gradSq_nonneg (u : SobolevData (centeredCube z 1 h1))
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (lam / 2) (Real.sqrt (ε / (Kc + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (half_pos hlam) (Real.sqrt_pos.2 (div_pos hε (by linarith)))
  have hηl : η ≤ lam / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηsq : Kc * η ^ 2 ≤ ε := by
    have h1' : η ^ 2 ≤ ε / (Kc + 1) := by
      have : η ≤ Real.sqrt (ε / (Kc + 1)) := by rw [hηdef]; exact min_le_right _ _
      calc η ^ 2 ≤ (Real.sqrt (ε / (Kc + 1))) ^ 2 := pow_le_pow_left₀ hη0.le this 2
        _ = ε / (Kc + 1) := Real.sq_sqrt (div_nonneg hε.le (by linarith))
    calc Kc * η ^ 2 ≤ Kc * (ε / (Kc + 1)) := mul_le_mul_of_nonneg_left h1' hKc0
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  obtain ⟨L₀, hL₀⟩ := hconv η hη0
  obtain ⟨L', hL'1, hL'2⟩ := hpre L₀
  obtain ⟨cFin, hcF, hcoef⟩ := hfinc L'
  have hn' : (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) := by
    have : (Sreg.prefixLen (N + L') alpha N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤
        (P0 : ℤ) := by exact_mod_cast hL'2
    linarith
  have hstep := aux_aux_macro_energy_recurrence_core_step hd Cp hFE M Sreg hchild alpha hδ hα H om N z h1 hR lam Λ Kr hlam
    hlamA hΛA hKr F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu x hx n L' (aFin L') cFin hcF hcoef η hηl
    (hL₀ L' hL'1) hn'
  have heq : (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) =
      Kc * η ^ 2 := by
    rw [hKc]; ring
  rw [heq] at hstep
  linarith

-- ===== MER14_Helpers =====
/-- The scale factor is a power of the scale ratio: `P = 3 C² (3^{n-N})^{t₀}`,
`t₀ = d - 2 + 2α`. -/
theorem aux_aux_macro_energy_recurrence_P_eq {d : ℕ} (C alpha : ℝ) (N n : ℕ) :
    aux_aux_macro_energy_recurrence_P (d := d) C alpha N n =
      3 * C ^ 2 * ((3 : ℝ) ^ ((n : ℝ) - N)) ^ ((d : ℝ) - 2 + 2 * alpha) := by
  unfold aux_aux_macro_energy_recurrence_P
  have h3 : (0 : ℝ) < 3 := by norm_num
  have e1 : ((3 : ℝ) ^ n) ^ d / ((3 : ℝ) ^ N) ^ d = (3 : ℝ) ^ (((n : ℝ) - N) * d) := by
    rw [← div_pow, ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_natCast (3 : ℝ) N,
      ← Real.rpow_sub h3, ← Real.rpow_natCast, ← Real.rpow_mul h3.le]
  have e2 : (C * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n))) ^ 2 =
      C ^ 2 * (3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n) * 2) := by
    rw [mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ ((1 - alpha) * ((N : ℝ) - n))) 2,
      ← Real.rpow_mul h3.le]
    norm_num
  have e3 : ((3 : ℝ) ^ ((n : ℝ) - N)) ^ ((d : ℝ) - 2 + 2 * alpha) =
      (3 : ℝ) ^ (((n : ℝ) - N) * ((d : ℝ) - 2 + 2 * alpha)) := (Real.rpow_mul h3.le _ _).symm
  have e4 : ((n : ℝ) - N) * ((d : ℝ) - 2 + 2 * alpha) =
      (1 - alpha) * ((N : ℝ) - n) * 2 + ((n : ℝ) - N) * d := by ring
  rw [e1, e2, e3, e4, Real.rpow_add h3]
  ring

/-- The scale factor at a selected triadic radius is at most `3 C² 6^{t₀} ρ^{t₁}`. -/
theorem aux_aux_macro_energy_recurrence_P_le {d : ℕ} (C t1 ρ : ℝ) (N n : ℕ) (hd : (2 : ℝ) ≤ d)
    (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h6 : (3 : ℝ) ^ ((n : ℝ) - N) ≤ 6 * ρ) :
    aux_aux_macro_energy_recurrence_P (d := d) C (1 - ((d : ℝ) - t1) / 4) N n ≤
      3 * C ^ 2 * (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * ρ ^ t1 := by
  have ht0' : (d : ℝ) - 2 + 2 * (1 - ((d : ℝ) - t1) / 4) = ((d : ℝ) + t1) / 2 := by ring
  have ht00 : 0 ≤ ((d : ℝ) + t1) / 2 := by linarith
  have ht0t1 : t1 ≤ ((d : ℝ) + t1) / 2 := by linarith
  rw [aux_aux_macro_energy_recurrence_P_eq, ht0', mul_assoc (3 * C ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ((3 : ℝ) ^ ((n : ℝ) - N)) ^ (((d : ℝ) + t1) / 2) ≤ (6 * ρ) ^ (((d : ℝ) + t1) / 2) :=
        Real.rpow_le_rpow (by positivity) h6 ht00
    _ = (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * ρ ^ (((d : ℝ) + t1) / 2) :=
        Real.mul_rpow (by norm_num) hρ.le
    _ ≤ (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * ρ ^ t1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 ht0t1) (by positivity)

/-- `C_p² K_f² + d² C_φ² ≤ (C_p² + d²)(K_f + C_φ)²` for nonnegative `K_f, C_φ`. -/
theorem aux_aux_macro_energy_recurrence_sq_split (Cp D Kf Cφ : ℝ) (hKf : 0 ≤ Kf) (hCφ : 0 ≤ Cφ) :
    Cp ^ 2 * Kf ^ 2 + D ^ 2 * Cφ ^ 2 ≤ (Cp ^ 2 + D ^ 2) * (Kf + Cφ) ^ 2 := by
  have h : (Cp ^ 2 + D ^ 2) * (Kf + Cφ) ^ 2 - (Cp ^ 2 * Kf ^ 2 + D ^ 2 * Cφ ^ 2) =
      Cp ^ 2 * (Cφ * (2 * Kf + Cφ)) + D ^ 2 * (Kf * (Kf + 2 * Cφ)) := by ring
  have h1 : 0 ≤ Cp ^ 2 * (Cφ * (2 * Kf + Cφ)) := by positivity
  have h2 : 0 ≤ D ^ 2 * (Kf * (Kf + 2 * Cφ)) := by positivity
  linarith

/-- Dyadic (triadic) radius selection between the wavelength and the prefix scale. -/
theorem aux_aux_macro_energy_recurrence_select_n (N P : ℕ) (ρ : ℝ) (hρN : (3 : ℝ) ^ (-(N : ℤ)) ≤ ρ)
    (hρP : ρ < ((3 : ℝ) ^ P)⁻¹ / 2) :
    ∃ n : ℕ, (n : ℤ) ≤ (N : ℤ) - P ∧ ρ ≤ ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2) ∧
      (3 : ℝ) ^ ((n : ℝ) - N) ≤ 6 * ρ := by
  have h3N : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hzpow : (3 : ℝ) ^ (-(N : ℤ)) = ((3 : ℝ) ^ N)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hzpow] at hρN
  have hPN : P ≤ N := by
    by_contra hcon
    push_neg at hcon
    have : ((3 : ℝ) ^ P)⁻¹ ≤ ((3 : ℝ) ^ N)⁻¹ :=
      inv_anti₀ h3N (pow_le_pow_right₀ (by norm_num) hcon.le)
    have h2 : ((3 : ℝ) ^ P)⁻¹ / 2 < ((3 : ℝ) ^ P)⁻¹ := half_lt_self (by positivity)
    linarith
  have hex : ∃ n : ℕ, ρ ≤ ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2) := by
    refine ⟨N - P, ?_⟩
    have : ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ (N - P) / 2) = ((3 : ℝ) ^ P)⁻¹ / 2 := by
      rw [pow_sub₀ _ (by norm_num) hPN]
      field_simp
    rw [this]; exact hρP.le
  classical
  let n := Nat.find hex
  have hn : ρ ≤ ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2) := Nat.find_spec hex
  have hnle : n ≤ N - P := Nat.find_min' hex (by
    have : ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ (N - P) / 2) = ((3 : ℝ) ^ P)⁻¹ / 2 := by
      rw [pow_sub₀ _ (by norm_num) hPN]
      field_simp
    rw [this]; exact hρP.le)
  have hn0 : n ≠ 0 := by
    intro h0
    have h := hn
    rw [h0, pow_zero] at h
    have : ((3 : ℝ) ^ N)⁻¹ * (1 / 2) < ((3 : ℝ) ^ N)⁻¹ := by
      have := inv_pos.2 h3N; linarith
    linarith
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  have hmlt : ¬ ρ ≤ ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ m / 2) :=
    Nat.find_min hex (by omega)
  push_neg at hmlt
  refine ⟨n, ?_, hn, ?_⟩
  · have : (n : ℤ) ≤ ((N - P : ℕ) : ℤ) := by exact_mod_cast hnle
    rw [Nat.cast_sub hPN] at this
    exact this
  · have h3 : (0 : ℝ) < 3 := by norm_num
    rw [Real.rpow_sub h3, Real.rpow_natCast, Real.rpow_natCast, hm, pow_succ]
    have : (3 : ℝ) ^ m * 3 / (3 : ℝ) ^ N = 6 * (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ m / 2)) := by
      field_simp; ring
    rw [this]
    linarith

/-- Local energy is monotone in the set. -/
theorem aux_aux_macro_energy_recurrence_localEnergy_mono {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s t : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g ≤ localGradientEnergy a ht g := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
  refine Finset.sum_le_sum fun i _ => ?_
  have hnn : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x * (g i x) ^ 2 := by
    filter_upwards [positiveCoefficient_ae_nonneg a] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hint : Integrable (fun x => a.val x * (g i x) ^ 2)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    refine (aux_aux_macro_energy_recurrence_integrable_weighted a.val (g i) (g i)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    change a.val x * (g i x * g i x) = a.val x * (g i x) ^ 2
    ring
  exact setIntegral_mono_set hint.integrableOn (ae_restrict_of_ae hnn)
    (Filter.Eventually.of_forall hst)

/-- The physical cutoff coefficient does not see how its centre and side are written. -/
theorem aux_aux_macro_energy_recurrence_cutoffOn_congr {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (L : ℕ)
    {om om' : BilateralField d} (hom : om = om') {y y' : SpatialCoordinates d} (hy : y = y')
    {R R' : ℝ} (hRR : R = R') (hR : 0 < R) (hR' : 0 < R') {p p' : SpatialCoordinates d}
    (hp : p = p') :
    (Sreg.cutoffOn L om y R hR).val p = (Sreg.cutoffOn L om' y' R' hR').val p' := by
  subst hom hy hRR hp; rfl

/-- The continuous cutoff coefficient. -/
theorem aux_aux_macro_energy_recurrence_cutoffCoefficient_continuous {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    Continuous (cutoffCoefficient M H om N) := by
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact Continuous.sub
    (Continuous.add (H om).continuous
      (continuous_finset_sum _ fun j _ => (om (-(Int.ofNat j))).continuous))
    continuous_const

theorem aux_aux_macro_energy_recurrence_cutoffCoefficient_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffCoefficient M H om N x :=
  mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- Two-sided bounds of the continuous cutoff coefficient on the closed cube. -/
theorem aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) :
    ∃ lam Λ : ℝ, 0 < lam ∧
      (∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
        lam ≤ cutoffCoefficient M H om N x) ∧
      (∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
        cutoffCoefficient M H om N x ≤ Λ) := by
  have hc := aux_aux_macro_energy_recurrence_cutoffCoefficient_continuous M H om N
  have hK := (closedCube z 1 h1).isCompact
  have hne : (closedCube z 1 h1 : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (by norm_num)⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  obtain ⟨x1, hx1, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  exact ⟨cutoffCoefficient M H om N x0, cutoffCoefficient M H om N x1,
    aux_aux_macro_energy_recurrence_cutoffCoefficient_pos M H om N x0, fun x hx => hmin hx, fun x hx => hmax hx⟩

-- ===== MER15_Final =====
/-- The recurrence constant: the initial-scale factor `2^{t₁}` and the one-centre factor. -/
def aux_aux_macro_energy_recurrence_Z (C Cp t1 : ℝ) (d : ℕ) : ℝ :=
  max ((2 : ℝ) ^ t1)
    (3 * C ^ 2 * (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * (16 + 8 * (Cp ^ 2 + (d : ℝ) ^ 2)))

theorem aux_aux_macro_energy_recurrence_Z_nonneg (C Cp t1 : ℝ) (d : ℕ) : 0 ≤ aux_aux_macro_energy_recurrence_Z C Cp t1 d :=
  le_max_of_le_left (Real.rpow_nonneg (by norm_num) _)

/-- Closing arithmetic of the one-centre case. -/
theorem aux_aux_macro_energy_recurrence_onecentre_close (d : ℕ) (C Cp t1 ρ Kf Cφ Kmac Efull Eloc P : ℝ)
    (hP0 : 0 ≤ P) (hPle : P ≤ 3 * C ^ 2 * (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * ρ ^ t1)
    (hKf : 0 ≤ Kf) (hCφ : 0 ≤ Cφ) (hK0 : 0 ≤ Kmac) (hρt : 0 ≤ ρ ^ t1)
    (hfA : Efull ≤ Kmac * (Kf + Cφ) ^ 2)
    (hcore : Eloc ≤ 16 * P * Efull + 8 * P * Kmac * (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2)) :
    Eloc ≤ aux_aux_macro_energy_recurrence_Z C Cp t1 d * (ρ ^ t1 * (Kmac * (Kf + Cφ) ^ 2)) := by
  have hW : 0 ≤ Kmac * (Kf + Cφ) ^ 2 := mul_nonneg hK0 (sq_nonneg _)
  have hc16 : 0 ≤ 16 + 8 * (Cp ^ 2 + (d : ℝ) ^ 2) := by positivity
  have e1 : 16 * P * Efull ≤ 16 * P * (Kmac * (Kf + Cφ) ^ 2) :=
    mul_le_mul_of_nonneg_left hfA (by positivity)
  have e2 : 8 * P * Kmac * (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) ≤
      8 * P * Kmac * ((Cp ^ 2 + (d : ℝ) ^ 2) * (Kf + Cφ) ^ 2) :=
    mul_le_mul_of_nonneg_left (aux_aux_macro_energy_recurrence_sq_split Cp d Kf Cφ hKf hCφ) (by positivity)
  calc Eloc ≤ 16 * P * Efull + 8 * P * Kmac * (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) := hcore
    _ ≤ 16 * P * (Kmac * (Kf + Cφ) ^ 2) +
        8 * P * Kmac * ((Cp ^ 2 + (d : ℝ) ^ 2) * (Kf + Cφ) ^ 2) := add_le_add e1 e2
    _ = P * (16 + 8 * (Cp ^ 2 + (d : ℝ) ^ 2)) * (Kmac * (Kf + Cφ) ^ 2) := by ring
    _ ≤ (3 * C ^ 2 * (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * ρ ^ t1) *
        (16 + 8 * (Cp ^ 2 + (d : ℝ) ^ 2)) * (Kmac * (Kf + Cφ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPle hc16) hW
    _ = (3 * C ^ 2 * (6 : ℝ) ^ (((d : ℝ) + t1) / 2) * (16 + 8 * (Cp ^ 2 + (d : ℝ) ^ 2))) *
        (ρ ^ t1 * (Kmac * (Kf + Cφ) ^ 2)) := by ring
    _ ≤ aux_aux_macro_energy_recurrence_Z C Cp t1 d * (ρ ^ t1 * (Kmac * (Kf + Cφ) ^ 2)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hρt hW)

/-- Closing arithmetic of the initial-scale case `ρ ≥ 3^{-P₀}/2`. -/
theorem aux_aux_macro_energy_recurrence_initial_close (d : ℕ) (C Cp t1 ρ X Efull Eloc : ℝ) (P0 : ℕ)
    (ht10 : 0 < t1) (hρ : 0 < ρ) (hcase : ((3 : ℝ) ^ P0)⁻¹ / 2 ≤ ρ) (hX0 : 0 ≤ X)
    (hglob : Eloc ≤ Efull) (hsrc : (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Efull ≤ X) :
    Eloc ≤ aux_aux_macro_energy_recurrence_Z C Cp t1 d * (ρ ^ t1 * X) := by
  have h3pos : 0 < (3 : ℝ) ^ (t1 * (P0 : ℝ)) := by positivity
  have hρt : 0 ≤ ρ ^ t1 := Real.rpow_nonneg hρ.le _
  have hfA' : Efull ≤ ((3 : ℝ) ^ (t1 * (P0 : ℝ)))⁻¹ * X := by
    rw [inv_mul_eq_div, le_div_iff₀ h3pos, mul_comm]
    exact hsrc
  have hpow : ((3 : ℝ) ^ (t1 * (P0 : ℝ)))⁻¹ ≤ (2 : ℝ) ^ t1 * ρ ^ t1 := by
    have e1 : ((3 : ℝ) ^ (t1 * (P0 : ℝ)))⁻¹ = (((3 : ℝ) ^ P0)⁻¹) ^ t1 := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        mul_comm t1 (P0 : ℝ)]
    rw [e1, ← Real.mul_rpow (by norm_num) hρ.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) ht10.le
  calc Eloc ≤ Efull := hglob
    _ ≤ ((3 : ℝ) ^ (t1 * (P0 : ℝ)))⁻¹ * X := hfA'
    _ ≤ (2 : ℝ) ^ t1 * ρ ^ t1 * X := mul_le_mul_of_nonneg_right hpow hX0
    _ ≤ aux_aux_macro_energy_recurrence_Z C Cp t1 d * (ρ ^ t1 * X) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hρt hX0)

theorem aux_aux_macro_energy_recurrence_c2Norm_nonneg {d : ℕ} (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact abs_nonneg _)
  · exact Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact norm_nonneg (fderiv ℝ f x))
  · exact Real.sSup_nonneg (by
      rintro v ⟨x, _, rfl⟩; exact norm_nonneg (fderiv ℝ (fderiv ℝ f) x))

/-- **The recurrence for one good sample.** -/
theorem aux_aux_macro_energy_recurrence_recurrence_om {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (N : ℕ) (hR : (0 : ℝ) < 3 ^ N)
    (aFin : ℕ → PositiveCoefficient (centeredCube z 1 h1))
    (hfinc : ∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (aFin L').val y = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om)
          ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        |(aFin L').val y - cutoffCoefficient M H om N y| < ε)
    (P0 : ℕ) (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (Kmac : ℝ)
    (hKref : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Real.exp (|H om x|) ≤ Kmac)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (hKsrc : (3 : ℝ) ^ (t1 * (P0 : ℝ)) *
      sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
        (u : SobolevData (centeredCube z 1 h1)) (u : SobolevData (centeredCube z 1 h1)) ≤
      Kmac * (Kf + Cφ) ^ 2)
    (x : SpatialCoordinates d) (ρ R : ℝ)
    (hx : x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d))) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hR1 : R ≤ 1) (hρN : (3 : ℝ) ^ (-(N : ℤ)) ≤ ρ) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
        (s := Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d * ((ρ / R) ^ t1 *
        localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
          (s := Metric.ball x R ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) +
        ρ ^ t1 * Kmac * (Kf + Cφ) ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := lt_of_le_of_lt (by linarith only [hdR] : (0 : ℝ) ≤ (d : ℝ) - 1) ht1
  have h3P : 1 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
  have hfA0 := sobolevCoefficientForm_nonneg (cutoffPositiveCoefficient M H om N z h1)
    (u : SobolevData (centeredCube z 1 h1))
  have hfA : sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
      (u : SobolevData (centeredCube z 1 h1)) (u : SobolevData (centeredCube z 1 h1)) ≤
      Kmac * (Kf + Cφ) ^ 2 := (le_mul_of_one_le_left hfA0 h3P).trans hKsrc
  have hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      Real.exp |H om x| ≤ Kmac := fun x hx =>
    (le_mul_of_one_le_left (Real.exp_pos _).le h3P).trans (hKref x hx)
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hX0 : 0 ≤ Kmac * (Kf + Cφ) ^ 2 := hfA0.trans hfA
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg.C Cp t1 d
  have hBR0 : 0 ≤ localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
      (s := Metric.ball x R ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) :=
    localGradientEnergy_nonneg _ _ _
  have hρR0 : 0 ≤ (ρ / R) ^ t1 := Real.rpow_nonneg (div_nonneg hρ.le (hρ.le.trans hρR)) _
  -- it suffices to bound by `Z ρ^{t₁} K (K_f + C_φ)²`
  suffices hmain : localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
      (s := Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d * (ρ ^ t1 * (Kmac * (Kf + Cφ) ^ 2)) by
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hZ0)
    rw [mul_assoc (ρ ^ t1) Kmac]
    exact le_add_of_nonneg_left (mul_nonneg hρR0 hBR0)
  have hρ1 : ρ ≤ 1 := hρR.trans hR1
  have hρt : 0 ≤ ρ ^ t1 := Real.rpow_nonneg hρ.le _
  by_cases hcase : ((3 : ℝ) ^ P0)⁻¹ / 2 ≤ ρ
  · -- initial scales: the global energy bound
    refine aux_aux_macro_energy_recurrence_initial_close d Sreg.C Cp t1 ρ (Kmac * (Kf + Cφ) ^ 2) _ _ P0 ht10 hρ hcase hX0
      ?_ hKsrc
    exact localGradientEnergy_le _ _ _
  · -- scales between the wavelength and the prefix: the one-centre estimate
    push_neg at hcase
    obtain ⟨n, hnP, hρn, h6⟩ := aux_aux_macro_energy_recurrence_select_n N P0 ρ hρN hcase
    obtain ⟨lam, Λ, hlam, hlamA, hΛA⟩ := aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds M H om N z h1
    have hcore := aux_aux_macro_energy_recurrence_core hd Cp hFE M Sreg hchild (1 - ((d : ℝ) - t1) / 4) hδ hα H om N z h1
      hR lam Λ Kmac hlam hlamA hΛA hKr aFin hfinc hconv P0 hpre F Kf hKf hFm hFb φ Cφ hφ hCφ b u
      hb hu x hx n hnP
    have hmono := aux_aux_macro_energy_recurrence_localEnergy_mono (cutoffPositiveCoefficient M H om N z h1)
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
        MeasurableSet (Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
        MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
          (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
      (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hρn))
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1)))
    have hK0 : 0 ≤ Kmac := (Real.exp_pos _).le.trans (hKr z (Metric.mem_closedBall_self
      (by norm_num)))
    exact aux_aux_macro_energy_recurrence_onecentre_close d Sreg.C Cp t1 ρ Kf Cφ Kmac _ _ _
      (aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n)
      (aux_aux_macro_energy_recurrence_P_le (d := d) Sreg.C t1 ρ N n hdR ht1 ht1' hρ hρ1 h6)
      hKf hCφ0 hK0 hρt hfA (hmono.trans hcore)

/-- **The frozen recurrence from the repaired energy-density field** (one extra hypothesis,
`aux_aux_macro_energy_recurrence_DensityChild Sreg`, inserted after `M.delta ≤ delta0`). -/
theorem aux_aux_macro_energy_recurrence_main_of_child :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      aux_aux_macro_energy_recurrence_DensityChild Sreg →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → r = 1 →
      (hphysical :
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ),
            let relabel : ℕ → BilateralField d → BilateralField d := fun N' omega j =>
              ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d =>
                    (3 : ℝ) ^ (-(N' : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (omega (j - (N' : ℤ)))
            ∃ aFin : ℕ → PositiveCoefficient (centeredCube z r hr),
              (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
                ∀ᵐ y ∂volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d)),
                  (aFin L').val y =
                    cFin *
                      (Sreg.cutoffOn (N + L') (relabel N om)
                        ((3 : ℝ) ^ (N : ℤ) • z)
                        ((3 : ℝ) ^ (N : ℤ) * r) (by positivity)).val
                        ((3 : ℝ) ^ (N : ℤ) • y)) ∧
              (∀ ε : ℝ, 0 < ε →
                ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
                  ∀ᵐ y ∂volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d)),
                    |(aFin L').val y -
                        cutoffCoefficient M H om N y| < ε)) →
      ∀ (Lmac : ℕ → BilateralField d → ℕ),
        (hprefix : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
          ∃ L' : ℕ, L0 ≤ L' ∧
            Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
              ((3 : ℝ) ^ N • z)
              (fun j => ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (om (j - (N : ℤ)))) ≤ Lmac N om) →
      ∀ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        ((∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i))) →
        (hKsource : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (u : SobolevData (centeredCube z r hr))
                (u : SobolevData (centeredCube z r hr)) ≤
                Kmac N om * (Kf + Cphi) ^ 2) →
        (hKreference : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x, x ∈ closedCube z r hr →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) →
        ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            ∀ (x : SpatialCoordinates d) (rho R : ℝ),
              x ∈ centeredCube z r hr → 0 < rho → rho ≤ R → R ≤ 1 →
              (3 : ℝ) ^ (-(N : ℤ)) ≤ rho →
              localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                  (s := Metric.ball x rho ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter
                    (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                Z * ((rho / R) ^ t1 *
                  localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                    (s := Metric.ball x R ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter
                      (centeredCube z r hr).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (centeredCube z r hr))) +
                  rho ^ t1 * Kmac N om * (Kf + Cphi) ^ 2) := by
  intro d hd _ _ E P X S t1 k ps ht1 ht1' hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 ≤ t1 := by linarith
  have hthr0 := aux_aux_macro_moment_bank_threshold (d := d) t1 1 ht1 ht1' ht10 le_rfl
  obtain ⟨dA, hdA, hthr⟩ := hthr0
  have hFE0 := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  obtain ⟨Cp, hCp, hFE⟩ := hFE0
  refine ⟨dA, hdA, ?_⟩
  intro M Rm Sreg It H hH hδ hchild z r hr hr1 hreq hphysical Lmac hprefix Kmac Cbound hKmom
    hKsource hKreference
  have hthrM := hthr M Sreg hδ
  obtain ⟨hδC, hα, -⟩ := hthrM
  subst hreq
  refine ⟨aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d, aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _, ?_⟩
  filter_upwards [hphysical, hprefix, hKsource, hKreference] with om hphys hpre hKs hKr
  intro N F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu x ρ R hx hρ hρR hR1 hρN
  have hR : (0 : ℝ) < 3 ^ N := by positivity
  have hphN := hphys N
  obtain ⟨aFin, hfin1, hfin2⟩ := hphN
  have hfinc : ∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 hr : Set (SpatialCoordinates d)),
        (aFin L').val y = cFin * (Sreg.cutoffOn (N + L') (aux_aux_macro_energy_recurrence_relabel N om)
          ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y) := by
    intro L'
    obtain ⟨cFin, hcF, hae⟩ := hfin1 L'
    refine ⟨cFin, hcF, ?_⟩
    filter_upwards [hae] with y hy
    rw [hy]
    congr 1
    exact aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg (N + L') rfl (by rw [zpow_natCast])
      (by rw [zpow_natCast, mul_one]) _ _ (by rw [zpow_natCast])
  exact aux_aux_macro_energy_recurrence_recurrence_om hd Cp hFE M Sreg hchild t1 ht1 ht1' hδC hα H om z hr N hR aFin
    hfinc hfin2 (Lmac N om) (hpre N) (Kmac N om) (hKr N)
    F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu (hKs N F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu)
    x ρ R hx hρ hρR hR1 hρN




theorem aux_macro_energy_recurrence :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 → r = 1 →
      (hphysical :
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ),
            let relabel : ℕ → BilateralField d → BilateralField d := fun N' omega j =>
              ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d =>
                    (3 : ℝ) ^ (-(N' : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (omega (j - (N' : ℤ)))
            ∃ aFin : ℕ → PositiveCoefficient (centeredCube z r hr),
              (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
                ∀ᵐ y ∂volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d)),
                  (aFin L').val y =
                    cFin *
                      (Sreg.cutoffOn (N + L') (relabel N om)
                        ((3 : ℝ) ^ (N : ℤ) • z)
                        ((3 : ℝ) ^ (N : ℤ) * r) (by positivity)).val
                        ((3 : ℝ) ^ (N : ℤ) • y)) ∧
              (∀ ε : ℝ, 0 < ε →
                ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
                  ∀ᵐ y ∂volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d)),
                    |(aFin L').val y -
                        cutoffCoefficient M H om N y| < ε)) →
      ∀ (Lmac : ℕ → BilateralField d → ℕ),
        (hprefix : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N L0 : ℕ,
          ∃ L' : ℕ, L0 ≤ L' ∧
            Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t1) / 4) N
              ((3 : ℝ) ^ N • z)
              (fun j => ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (om (j - (N : ℤ)))) ≤ Lmac N om) →
      ∀ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        ((∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i))) →
        (hKsource : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) *
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (u : SobolevData (centeredCube z r hr))
                (u : SobolevData (centeredCube z r hr)) ≤
                Kmac N om * (Kf + Cphi) ^ 2) →
        (hKreference : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x, x ∈ closedCube z r hr →
            (3 : ℝ) ^ (t1 * (Lmac N om : ℝ)) * Real.exp (|H om x|) ≤ Kmac N om) →
        ∃ Z : ℝ, 0 ≤ Z ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            ∀ (x : SpatialCoordinates d) (rho R : ℝ),
              x ∈ centeredCube z r hr → 0 < rho → rho ≤ R → R ≤ 1 →
              (3 : ℝ) ^ (-(N : ℤ)) ≤ rho →
              localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                  (s := Metric.ball x rho ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter
                    (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                Z * ((rho / R) ^ t1 *
                  localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                    (s := Metric.ball x R ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter
                      (centeredCube z r hr).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (centeredCube z r hr))) +
                  rho ^ t1 * Kmac N om * (Kf + Cphi) ^ 2) := by
  intro d hd _ _ E P X S t1 k ps ht1 ht1' hps
  have h := aux_aux_macro_energy_recurrence_main_of_child d hd E P X S t1 k ps ht1 ht1' hps
  obtain ⟨δ0, hδ0, hmain⟩ := h
  exact ⟨δ0, hδ0, fun M Rm Sreg It H hH hδ => hmain M Rm Sreg It H hH hδ Sreg.energy_density⟩

end Paper
