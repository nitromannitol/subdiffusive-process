module

public import SubdiffusiveProcess.Paper.lem_localized_perturbation
public import SubdiffusiveProcess.Paper.cor_14_gradient_sharp_energy
public import SubdiffusiveProcess.Paper.cor_14_form_variation
public import SubdiffusiveProcess.Paper.cor_14_form_sharp_energy
public import SubdiffusiveProcess.Paper.cor_14_form_comparison
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.PotentialPerturbation
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

lemma aux_cor_14_exp_coefficient (s : ℝ) :
    (s * Real.exp s) ^ 2 / Real.exp (-s) = s ^ 2 * Real.exp (3 * s) := by
  rw [div_eq_iff (Real.exp_ne_zero _)]
  calc
    (s * Real.exp s) ^ 2 = s ^ 2 * (Real.exp s * Real.exp s) := by ring
    _ = s ^ 2 * (Real.exp (3 * s) * Real.exp (-s)) := by
      congr 1
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1 ; ring
    _ = s ^ 2 * Real.exp (3 * s) * Real.exp (-s) := by ring

lemma aux_cor_14_exp_response_bound {s : ℝ} (hs : 0 ≤ s) :
    s * Real.exp s + (s * Real.exp s) ^ 2 / Real.exp (-s) ≤
      2 * s * Real.exp (4 * s) := by
  rw [aux_cor_14_exp_coefficient]
  have hse : s ≤ Real.exp s := by
    have := Real.add_one_le_exp s
    linarith
  have h1 : s * Real.exp s ≤ s * Real.exp (4 * s) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hs])) hs
  have h2 : s ^ 2 * Real.exp (3 * s) ≤ s * Real.exp (4 * s) := by
    have h3 : s * Real.exp (3 * s) ≤ Real.exp s * Real.exp (3 * s) :=
      mul_le_mul_of_nonneg_right hse (Real.exp_pos _).le
    rw [← Real.exp_add] at h3
    calc
      s ^ 2 * Real.exp (3 * s) = s * (s * Real.exp (3 * s)) := by ring
      _ ≤ s * Real.exp (s + 3 * s) := mul_le_mul_of_nonneg_left h3 hs
      _ = s * Real.exp (4 * s) := by rw [show s + 3 * s = 4 * s by ring]
  calc
    s * Real.exp s + s ^ 2 * Real.exp (3 * s) ≤
        s * Real.exp (4 * s) + s * Real.exp (4 * s) := add_le_add h1 h2
    _ = 2 * s * Real.exp (4 * s) := by ring

lemma aux_cor_14_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (B : Set α) (g : α → ℝ) (hg : Measurable g) (S : ℝ)
    (hS : ∀ x, |g x| ≤ S) (hμ : μ B ≠ ⊤) :
    |∫ x in B, (Real.exp (g x) - 1) ∂μ| ≤
      S * Real.exp S * (μ B).toReal := by
  have hI : IntegrableOn (fun x => Real.exp (g x) - 1) B μ :=
    Measure.integrableOn_of_bounded hμ
      ((hg.exp.sub measurable_const).aestronglyMeasurable)
      (M := S * Real.exp S) (by
        filter_upwards [] with x
        exact abs_exp_sub_one_le_bound (hS x))
  calc
    |∫ x in B, (Real.exp (g x) - 1) ∂μ| ≤
        ∫ x in B, |Real.exp (g x) - 1| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in B, S * Real.exp S ∂μ := by
      apply integral_mono_ae hI.norm (integrableOn_const hμ)
      filter_upwards [] with x
      exact abs_exp_sub_one_le_bound (hS x)
    _ = S * Real.exp S * (μ B).toReal := by
      simp [integral_const, Measure.real, smul_eq_mul, mul_comm]

lemma aux_cor_14_rescale_bound {s m A : ℝ}
    (hcoef : (s * Real.exp s) ^ 2 / Real.exp (-s) = s ^ 2 * Real.exp (3 * s))
    (hA : A ≤ (s * Real.exp s) ^ 2 / Real.exp (-s) * m) :
    A ≤ s ^ 2 * Real.exp (3 * s) * m := by
  calc
    A ≤ (s * Real.exp s) ^ 2 / Real.exp (-s) * m := hA
    _ = s ^ 2 * Real.exp (3 * s) * m := by rw [hcoef]

lemma aux_cor_14_form_energy_bounds {S mass X Y : ℝ} (hS : 0 ≤ S)
    (hmass : 0 ≤ mass) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXsqrt : Real.sqrt X ≤
      (Real.exp (S / 2) - Real.exp (-S / 2)) * Real.sqrt mass)
    (hYsqrt : Real.sqrt Y ≤ 2 * Real.exp (S / 2) * Real.sqrt mass) :
    X ≤ S ^ 2 * Real.exp (3 * S) * mass ∧
      Y ≤ 4 * Real.exp S * mass := by
  have he : Real.exp (S / 2) - Real.exp (-S / 2) ≤
      S * Real.exp (S / 2) := by
    have hneg : 1 - Real.exp (-S) ≤ S := by
      have := Real.add_one_le_exp (-S)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hneg (Real.exp_pos (S / 2)).le
    calc
      Real.exp (S / 2) - Real.exp (-S / 2) =
          (1 - Real.exp (-S)) * Real.exp (S / 2) := by
            rw [sub_mul, one_mul, ← Real.exp_add]
            congr 1 ; ring
      _ ≤ S * Real.exp (S / 2) := hmul
  have h1 : (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 ≤
      S ^ 2 * Real.exp S := by
    have h2 : Real.exp (-S / 2) ≤ Real.exp (S / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hsquare : (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 ≤
        (S * Real.exp (S / 2)) ^ 2 :=
      (sq_le_sq₀ (sub_nonneg.mpr h2)
        (mul_nonneg hS (Real.exp_pos _).le)).2 he
    calc
      (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 ≤
          (S * Real.exp (S / 2)) ^ 2 := hsquare
      _ = S ^ 2 * Real.exp S := by
        rw [mul_pow]
        calc
          S ^ 2 * Real.exp (S / 2) ^ 2 =
              S ^ 2 * (Real.exp (S / 2) * Real.exp (S / 2)) := by
                rw [show Real.exp (S / 2) ^ 2 =
                    Real.exp (S / 2) * Real.exp (S / 2) by rw [pow_two]]
          _ = S ^ 2 * Real.exp S := by rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp S ≤ Real.exp (3 * S) :=
    Real.exp_le_exp.mpr (by linarith)
  have hC : 0 ≤ Real.exp (S / 2) - Real.exp (-S / 2) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hXrhs : 0 ≤ (Real.exp (S / 2) - Real.exp (-S / 2)) * Real.sqrt mass :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  have hYrhs : 0 ≤ 2 * Real.exp (S / 2) * Real.sqrt mass := by positivity
  constructor
  · calc
      X = (Real.sqrt X) ^ 2 := by rw [Real.sq_sqrt hX]
      _ ≤ ((Real.exp (S / 2) - Real.exp (-S / 2)) * Real.sqrt mass) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) hXrhs).2 hXsqrt
      _ = (Real.exp (S / 2) - Real.exp (-S / 2)) ^ 2 * mass := by
        rw [mul_pow, Real.sq_sqrt hmass]
      _ ≤ S ^ 2 * Real.exp S * mass :=
        mul_le_mul_of_nonneg_right h1 hmass
      _ ≤ S ^ 2 * Real.exp (3 * S) * mass := by
        apply mul_le_mul_of_nonneg_right _ hmass
        exact mul_le_mul_of_nonneg_left h3 (sq_nonneg S)
  · calc
      Y = (Real.sqrt Y) ^ 2 := by rw [Real.sq_sqrt hY]
      _ ≤ (2 * Real.exp (S / 2) * Real.sqrt mass) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) hYrhs).2 hYsqrt
      _ = 4 * Real.exp S * mass := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hmass]
        have hexp : Real.exp (S / 2) ^ 2 = Real.exp S := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring

lemma aux_cor_14_upper_energy {s mass x : ℝ} (hmass : 0 ≤ mass) (hx : 0 ≤ x)
    (hroot : Real.sqrt x ≤ 2 * Real.exp (s / 2) * Real.sqrt mass) :
    x ≤ 4 * Real.exp s * mass := by
  have hrhs : 0 ≤ 2 * Real.exp (s / 2) * Real.sqrt mass := by positivity
  calc
    x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt hx]
    _ ≤ (2 * Real.exp (s / 2) * Real.sqrt mass) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs).2 hroot
    _ = 4 * Real.exp s * mass := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hmass]
      have hexp : Real.exp (s / 2) ^ 2 = Real.exp s := by
        calc
          Real.exp (s / 2) ^ 2 = Real.exp (s / 2) * Real.exp (s / 2) := by rw [pow_two]
          _ = Real.exp s := by rw [← Real.exp_add]; congr 1; ring
      rw [hexp]
      ring

lemma aux_cor_14_response_bounds :
    ∀ (d : ℕ) (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
        (h g : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))))
        (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
        (_hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          x ∉ B → g x = 0),
      ∀ L : S.space →L[ℝ] ℝ,
        responseForm S (expPotentialCoefficient (h + g))
            (responseSolution S (expPotentialCoefficient (h + g)) L -
              responseSolution S (expPotentialCoefficient h) L)
            (responseSolution S (expPotentialCoefficient (h + g)) L -
              responseSolution S (expPotentialCoefficient h) L) ≤
          ‖g‖ ^ 2 * Real.exp (3 * ‖g‖) *
            localGradientEnergy (expPotentialCoefficient h) hB
              (subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) ∧
        localGradientEnergy (expPotentialCoefficient (h + g)) hB
            (subspaceGradient S.space
              (responseSolution S (expPotentialCoefficient (h + g)) L)) ≤
          4 * Real.exp ‖g‖ * localGradientEnergy (expPotentialCoefficient h) hB
            (subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) ∧
        |inverseResponse S (expPotentialCoefficient (h + g)) L -
            inverseResponse S (expPotentialCoefficient h) L| ≤
          2 * ‖g‖ * Real.exp (4 * ‖g‖) * localGradientEnergy (expPotentialCoefficient h) hB
            (subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) := by
  intro d Q S h g B hB hsupp L
  have hs : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
  have hw : Measurable (fun x : SpatialCoordinates d => Real.exp (g x)) :=
    Real.measurable_exp.comp (Lp.stronglyMeasurable g).measurable
  have hweight : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (expPotentialCoefficient (h + g)).val x =
        Real.exp (g x) * (expPotentialCoefficient h).val x := by
    filter_upwards [expPotentialCoefficient_coeFn h, expPotentialCoefficient_coeFn (h + g),
      Lp.coeFn_add h g] with x hh hhg hadd
    rw [hhg, hadd, Pi.add_apply, Real.exp_add, hh, mul_comm]
  have hbounds : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      Real.exp (-‖g‖) ≤ Real.exp (g x) ∧ Real.exp (g x) ≤ Real.exp ‖g‖ ∧
      |Real.exp (g x) - 1| ≤ ‖g‖ * Real.exp ‖g‖ ∧ (x ∉ B → Real.exp (g x) = 1) := by
    filter_upwards [boundedPotential_ae_bound g, hsupp] with x hbound hzero
    refine ⟨Real.exp_le_exp.mpr (by have := (abs_le.mp hbound).1; linarith),
      Real.exp_le_exp.mpr (abs_le.mp hbound).2,
      abs_exp_sub_one_le_bound hbound, fun hx => by rw [hzero hx, Real.exp_zero]⟩
  obtain ⟨hlem1, hlem2, hlem3⟩ :=
    (lem_localized_perturbation d Q S (expPotentialCoefficient h)
      (expPotentialCoefficient (h + g)) (fun x => Real.exp (g x)) hw B hB
      (Real.exp (-‖g‖)) (Real.exp ‖g‖) (‖g‖ * Real.exp ‖g‖) (Real.exp_pos _)
      (Real.exp_le_exp.mpr (by linarith)) (mul_nonneg hs (Real.exp_pos _).le)
      hweight hbounds).1 L
  obtain ⟨hsh1, hsh2⟩ :=
    (cor_14_gradient_sharp_energy d Q S h g B hB hsupp).1 L
  have hm : (0 : ℝ) ≤ localGradientEnergy (expPotentialCoefficient h) hB
      (subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) :=
    localGradientEnergy_nonneg _ hB _
  have hmv : (0 : ℝ) ≤ localGradientEnergy (expPotentialCoefficient (h + g)) hB
      (subspaceGradient S.space (responseSolution S (expPotentialCoefficient (h + g)) L)) :=
    localGradientEnergy_nonneg _ hB _
  have haeq := aux_cor_14_exp_coefficient ‖g‖
  have hb := aux_cor_14_exp_response_bound hs
  refine ⟨?_, ?_, ?_⟩
  · exact aux_cor_14_rescale_bound haeq hlem1
  · exact aux_cor_14_upper_energy hm hmv hsh2
  · calc
      |inverseResponse S (expPotentialCoefficient (h + g)) L -
            inverseResponse S (expPotentialCoefficient h) L|
          ≤ ((‖g‖ * Real.exp ‖g‖) + (‖g‖ * Real.exp ‖g‖) ^ 2 /
              Real.exp (-‖g‖)) * localGradientEnergy (expPotentialCoefficient h) hB
              (subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) :=
        hlem3
      _ ≤ (2 * ‖g‖ * Real.exp (4 * ‖g‖)) *
            localGradientEnergy (expPotentialCoefficient h) hB
              (subspaceGradient S.space (responseSolution S (expPotentialCoefficient h) L)) :=
        mul_le_mul_of_nonneg_right hb hm

lemma aux_cor_14_boundary_bounds :
    ∀ (d : ℕ) (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
        (h g : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))))
        (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
        (_hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          x ∉ B → g x = 0),
      ∀ f : weakSobolevGraph Q,
        sobolevCoefficientForm (expPotentialCoefficient (h + g))
            ((dirichletMinimizer S (expPotentialCoefficient (h + g)) f).val -
              (dirichletMinimizer S (expPotentialCoefficient h) f).val)
            ((dirichletMinimizer S (expPotentialCoefficient (h + g)) f).val -
              (dirichletMinimizer S (expPotentialCoefficient h) f).val) ≤
          ‖g‖ ^ 2 * Real.exp (3 * ‖g‖) *
            localGradientEnergy (expPotentialCoefficient h) hB
              (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) f).val) ∧
        localGradientEnergy (expPotentialCoefficient (h + g)) hB
            (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient (h + g)) f).val) ≤
          4 * Real.exp ‖g‖ * localGradientEnergy (expPotentialCoefficient h) hB
            (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) f).val) ∧
        |dirichletResponse S (expPotentialCoefficient (h + g)) f -
            dirichletResponse S (expPotentialCoefficient h) f| ≤
          2 * ‖g‖ * Real.exp (4 * ‖g‖) * localGradientEnergy (expPotentialCoefficient h) hB
            (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) f).val) := by
  intro d Q S h g B hB hsupp f
  have hs : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
  have hw : Measurable (fun x : SpatialCoordinates d => Real.exp (g x)) :=
    Real.measurable_exp.comp (Lp.stronglyMeasurable g).measurable
  have hweight : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (expPotentialCoefficient (h + g)).val x =
        Real.exp (g x) * (expPotentialCoefficient h).val x := by
    filter_upwards [expPotentialCoefficient_coeFn h, expPotentialCoefficient_coeFn (h + g),
      Lp.coeFn_add h g] with x hh hhg hadd
    rw [hhg, hadd, Pi.add_apply, Real.exp_add, hh, mul_comm]
  have hbounds : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      Real.exp (-‖g‖) ≤ Real.exp (g x) ∧ Real.exp (g x) ≤ Real.exp ‖g‖ ∧
      |Real.exp (g x) - 1| ≤ ‖g‖ * Real.exp ‖g‖ ∧ (x ∉ B → Real.exp (g x) = 1) := by
    filter_upwards [boundedPotential_ae_bound g, hsupp] with x hbound hzero
    refine ⟨Real.exp_le_exp.mpr (by have := (abs_le.mp hbound).1; linarith),
      Real.exp_le_exp.mpr (abs_le.mp hbound).2,
      abs_exp_sub_one_le_bound hbound, fun hx => by rw [hzero hx, Real.exp_zero]⟩
  obtain ⟨hlem1, hlem2, hlem3⟩ :=
    (lem_localized_perturbation d Q S (expPotentialCoefficient h)
      (expPotentialCoefficient (h + g)) (fun x => Real.exp (g x)) hw B hB
      (Real.exp (-‖g‖)) (Real.exp ‖g‖) (‖g‖ * Real.exp ‖g‖) (Real.exp_pos _)
      (Real.exp_le_exp.mpr (by linarith)) (mul_nonneg hs (Real.exp_pos _).le)
      hweight hbounds).2 f
  obtain ⟨hsh1, hsh2⟩ :=
    (cor_14_gradient_sharp_energy d Q S h g B hB hsupp).2 f
  have hm : (0 : ℝ) ≤ localGradientEnergy (expPotentialCoefficient h) hB
      (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) f).val) :=
    localGradientEnergy_nonneg _ hB _
  have hmv : (0 : ℝ) ≤ localGradientEnergy (expPotentialCoefficient (h + g)) hB
      (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient (h + g)) f).val) :=
    localGradientEnergy_nonneg _ hB _
  have haeq := aux_cor_14_exp_coefficient ‖g‖
  have hb := aux_cor_14_exp_response_bound hs
  refine ⟨?_, ?_, ?_⟩
  · exact aux_cor_14_rescale_bound haeq hlem1
  · exact aux_cor_14_upper_energy hm hmv hsh2
  · calc
      |dirichletResponse S (expPotentialCoefficient (h + g)) f -
            dirichletResponse S (expPotentialCoefficient h) f|
          ≤ ((‖g‖ * Real.exp ‖g‖) + (‖g‖ * Real.exp ‖g‖) ^ 2 /
              Real.exp (-‖g‖)) * localGradientEnergy (expPotentialCoefficient h) hB
              (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) f).val) :=
        hlem3
      _ ≤ (2 * ‖g‖ * Real.exp (4 * ‖g‖)) *
            localGradientEnergy (expPotentialCoefficient h) hB
              (sobolevGradient (dirichletMinimizer S (expPotentialCoefficient h) f).val) :=
        mul_le_mul_of_nonneg_right hb hm

theorem cor_14 :
    (∀ (d : ℕ) (Q : Opens (SpatialCoordinates d))
        (S : ResponseSpace Q)
        (h g : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))))
        (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
        (_hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ B → g x = 0)
        (L : S.space →L[ℝ] ℝ)
        (f : weakSobolevGraph Q),
      let a := expPotentialCoefficient h
      let b := expPotentialCoefficient (h + g)
      let s := ‖g‖
      (let u := responseSolution S a L
       let v := responseSolution S b L
       let m := localGradientEnergy a hB (subspaceGradient S.space u)
       responseForm S b (v - u) (v - u) ≤ s ^ 2 * Real.exp (3 * s) * m ∧
         localGradientEnergy b hB (subspaceGradient S.space v) ≤ 4 * Real.exp s * m ∧
         |inverseResponse S b L - inverseResponse S a L| ≤ 2 * s * Real.exp (4 * s) * m) ∧
      (let u := dirichletMinimizer S a f
       let v := dirichletMinimizer S b f
       let m := localGradientEnergy a hB (sobolevGradient u.val)
       sobolevCoefficientForm b (v.val - u.val) (v.val - u.val) ≤
            s ^ 2 * Real.exp (3 * s) * m ∧
         localGradientEnergy b hB (sobolevGradient v.val) ≤ 4 * Real.exp s * m ∧
         |dirichletResponse S b f - dirichletResponse S a f| ≤
           2 * s * Real.exp (4 * s) * m) ∧
      (∀ p q : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))),
         Real.exp (-‖p - q‖) * inverseResponse S (expPotentialCoefficient q) L ≤
             inverseResponse S (expPotentialCoefficient p) L ∧
           inverseResponse S (expPotentialCoefficient p) L ≤
             Real.exp ‖p - q‖ * inverseResponse S (expPotentialCoefficient q) L) ∧
      (∀ p q : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))),
         Real.exp (-‖p - q‖) * dirichletResponse S (expPotentialCoefficient q) f ≤
             dirichletResponse S (expPotentialCoefficient p) f ∧
           dirichletResponse S (expPotentialCoefficient p) f ≤
             Real.exp ‖p - q‖ * dirichletResponse S (expPotentialCoefficient q) f)) ∧
    (∀ (d : ℕ) (Q : Opens (SpatialCoordinates d))
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      let q := centeredCube z r hr;
      (closure (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))) →
      (∀ (E Eg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (Gammag : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg),
        Eg.domain = E.domain →
        ∀ (V0 : Submodule ℝ (DomainL2 Q)),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (q : Set (SpatialCoordinates d)) V0 →
        ∀ (g : SpatialCoordinates d → ℝ), Measurable g →
        ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
        B ⊆ (q : Set (SpatialCoordinates d)) → (∀ x, x ∉ B → g x = 0) →
        ∀ (S : ℝ), IsLUB (Set.range (fun x => |g x|)) S →
        BddAbove (Set.range (fun x => |g x|)) →
        (∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          Gammag.measure v A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)) →
        (∀ (u ug : DomainL2 Q), u ∈ E.domain → ug ∈ Eg.domain → ug - u ∈ V0 →
          (∀ v ∈ E.domain, v - u ∈ V0 →
            (Gamma.measure u q).toReal ≤ (Gamma.measure v q).toReal) →
          (∀ v ∈ Eg.domain, v - u ∈ V0 →
            (Gammag.measure ug q).toReal ≤ (Gammag.measure v q).toReal) →
          let R := (Gamma.measure u q).toReal;
          let Rg := (Gammag.measure ug q).toReal;
          let mass := (Gamma.measure u B).toReal;
          (Gammag.measure (ug - u) q).toReal ≤ S ^ 2 * Real.exp (3 * S) * mass ∧
            (Gammag.measure ug B).toReal ≤ 4 * Real.exp S * mass ∧
            |Rg - R| ≤ 2 * S * Real.exp (4 * S) * mass ∧
            (Real.exp (-S) * R ≤ Rg ∧ Rg ≤ Real.exp S * R) ∧
            Rg - R = (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u)) -
              (Gammag.measure (ug - u) q).toReal) ∧
        (∀ (f : DomainL2 Q) (u ug : DomainL2 Q), u ∈ V0 → ug ∈ V0 →
          (∀ v ∈ V0, _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v)
              (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = inner ℝ f v) →
          (∀ v ∈ V0, _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gammag.cross ug v)
              (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = inner ℝ f v) →
          let R := inner ℝ f u;
          let Rg := inner ℝ f ug;
          let mass := (Gamma.measure u B).toReal;
          (Gammag.measure (ug - u) q).toReal ≤ S ^ 2 * Real.exp (3 * S) * mass ∧
            (Gammag.measure ug B).toReal ≤ 4 * Real.exp S * mass ∧
            |Rg - R| ≤ 2 * S * Real.exp (4 * S) * mass ∧
            (Real.exp (-S) * R ≤ Rg ∧ Rg ≤ Real.exp S * R) ∧
            Rg - R = (Gammag.measure (ug - u) q).toReal -
              (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u))))) := by
  constructor
  · intro d Q S h g B hB hsupp L f
    dsimp only
    have hresp := aux_cor_14_response_bounds d Q S h g B hB hsupp L
    have hbound := aux_cor_14_boundary_bounds d Q S h g B hB hsupp f
    refine ⟨hresp, hbound, ?_, ?_⟩
    · intro p q
      rw [norm_sub_rev p q]
      exact inverseResponse_potential_comparison S L q p
    · intro p q
      rw [norm_sub_rev p q]
      exact dirichletResponse_potential_comparison S f q p
  · intro d Q z r hr
    dsimp only
    let q := centeredCube z r hr
    change (closure (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))) → _
    intro hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB hBq hgz S hS hbdd hmeas
    have : Nonempty (SpatialCoordinates d) := ⟨0⟩
    have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS.1 ⟨Classical.arbitrary _, rfl⟩)
    refine ⟨?_, ?_⟩
    · intro u ug hu hug hdiff hminu hminug
      have hvar :=
        (cor_14_form_variation d Q z r hr hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB
          hBq hgz S hS hbdd hmeas).1 u ug hu hug hdiff hminu hminug
      have hv_sgn := hvar.1
      have hv_eq := hvar.2
      obtain ⟨hsh1, hsh2⟩ :=
        cor_14_form_sharp_energy d Q z r hr hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB
          hBq hgz S hS hbdd hmeas u ug hu hug hdiff hv_sgn
      have hcmp :=
        (cor_14_form_comparison d Q z r hr hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB
          hBq hgz S hS hbdd hmeas).1 u ug hu hug hdiff hminu hminug
      have hm0 : (0 : ℝ) ≤ (Gamma.measure u B).toReal := ENNReal.toReal_nonneg
      have hmc : (0 : ℝ) ≤ (Gammag.measure (ug - u) q).toReal := ENNReal.toReal_nonneg
      have hmg : (0 : ℝ) ≤ (Gammag.measure ug B).toReal := ENNReal.toReal_nonneg
      have henergy := aux_cor_14_form_energy_bounds hS0 hm0 hmc hmg hsh1 hsh2
      have hb := aux_cor_14_exp_response_bound hS0
      rw [aux_cor_14_exp_coefficient] at hb
      have hI := aux_cor_14_integral_bound (Gamma.measure u) B g hg S
        (fun x => hS.1 ⟨x, rfl⟩) (Gamma.measure_ne_top hu B)
      have hresp : |(Gammag.measure ug q).toReal - (Gamma.measure u q).toReal| ≤
          2 * S * Real.exp (4 * S) * (Gamma.measure u B).toReal := by
        calc
          |(Gammag.measure ug q).toReal - (Gamma.measure u q).toReal| =
              |(∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u)) -
                (Gammag.measure (ug - u) q).toReal| := by rw [hv_eq]
          _ ≤ |(∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u))| +
                |(Gammag.measure (ug - u) q).toReal| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u))
                0 (Gammag.measure (ug - u) q).toReal)
          _ ≤ S * Real.exp S * (Gamma.measure u B).toReal +
                S ^ 2 * Real.exp (3 * S) * (Gamma.measure u B).toReal :=
            add_le_add hI (by simpa [abs_of_nonneg hmc] using henergy.1)
          _ = (S * Real.exp S + S ^ 2 * Real.exp (3 * S)) *
                (Gamma.measure u B).toReal := by ring
          _ ≤ 2 * S * Real.exp (4 * S) * (Gamma.measure u B).toReal := by
            exact mul_le_mul_of_nonneg_right hb hm0
      exact ⟨henergy.1, henergy.2, hresp, hcmp, hv_eq⟩
    · intro f u ug hu hug hdu hdug
      have hvar :=
        (cor_14_form_variation d Q z r hr hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB
          hBq hgz S hS hbdd hmeas).2 f u ug hu hug hdu hdug
      have hv_sgn := hvar.1
      have hv_eq := hvar.2
      have hcmp :=
        (cor_14_form_comparison d Q z r hr hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB
          hBq hgz S hS hbdd hmeas).2 f u ug hu hug hdu hdug
      obtain ⟨hsh1, hsh2⟩ :=
        cor_14_form_sharp_energy d Q z r hr hsub E Eg Gamma Gammag hdom V0 hkill g hg B hB
          hBq hgz S hS hbdd hmeas u ug (hkill.le_domain hu) (by
            rw [hdom]
            exact hkill.le_domain hug) (V0.sub_mem hug hu) hv_sgn
      have hm0 : (0 : ℝ) ≤ (Gamma.measure u B).toReal := ENNReal.toReal_nonneg
      have hmc : (0 : ℝ) ≤ (Gammag.measure (ug - u) q).toReal := ENNReal.toReal_nonneg
      have hmg : (0 : ℝ) ≤ (Gammag.measure ug B).toReal := ENNReal.toReal_nonneg
      have henergy := aux_cor_14_form_energy_bounds hS0 hm0 hmc hmg hsh1 hsh2
      have hb := aux_cor_14_exp_response_bound hS0
      rw [aux_cor_14_exp_coefficient] at hb
      have hI := aux_cor_14_integral_bound (Gamma.measure u) B g hg S
        (fun x => hS.1 ⟨x, rfl⟩) (Gamma.measure_ne_top (hkill.le_domain hu) B)
      have hresp : |inner ℝ f ug - inner ℝ f u| ≤
          2 * S * Real.exp (4 * S) * (Gamma.measure u B).toReal := by
        calc
          |inner ℝ f ug - inner ℝ f u| =
              |(Gammag.measure (ug - u) q).toReal -
                (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u))| := by rw [hv_eq]
          _ ≤ |(Gammag.measure (ug - u) q).toReal| +
                |(∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u))| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (Gammag.measure (ug - u) q).toReal 0
                (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u)))
          _ ≤ S ^ 2 * Real.exp (3 * S) * (Gamma.measure u B).toReal +
                S * Real.exp S * (Gamma.measure u B).toReal :=
            add_le_add (by simpa [abs_of_nonneg hmc] using henergy.1) hI
          _ = (S * Real.exp S + S ^ 2 * Real.exp (3 * S)) *
                (Gamma.measure u B).toReal := by ring
          _ ≤ 2 * S * Real.exp (4 * S) * (Gamma.measure u B).toReal := by
            exact mul_le_mul_of_nonneg_right hb hm0
      exact ⟨henergy.1, henergy.2, hresp, hcmp, hv_eq⟩

end SubdiffusiveProcess.Paper
