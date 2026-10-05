module

public import SubdiffusiveProcess.DirichletForm.FOTResolventConstruction

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

omit [TopologicalSpace X] in
/-- The positive quadratic functional at a finite resolvent parameter. -/
theorem resolvent_energy_nonneg [_instPreserved0 : TopologicalSpace X] {m : Measure X} (F : _root_.SubdiffusiveProcess.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {u φ uφ u2 : Lp ℝ 2 m} (hφ0 : 0 ≤ᵐ[m] φ)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x) (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    0 ≤ α * ⟪u - α • G u, uφ⟫ - (1 / 2 : ℝ) * α * ⟪u2 - α • G u2, φ⟫ := by
  let v := u - α • G u
  let w := u2 - α • G u2
  have hk : 0 ≤ᵐ[m] fun x => v x * uφ x - (1 / 2 : ℝ) * (w x * φ x) := by
    filter_upwards [Lp.coeFn_sub u (α • G u), Lp.coeFn_sub u2 (α • G u2),
      Lp.coeFn_smul α (G u), Lp.coeFn_smul α (G u2), hφ0, hprod, hsq,
      resolvent_square_le_general F hα hG hsq] with x h1 h2 h3 h4 h0 hp hs hj
    change 0 ≤ (u - α • G u) x * uφ x - (1 / 2 : ℝ) * ((u2 - α • G u2) x * φ x)
    simp only [h1, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, smul_eq_mul, hp, hs]
    have he : (u x - α * (G u) x) * (u x * φ x) -
        (1 / 2 : ℝ) * ((u x ^ 2 - α * (G u2) x) * φ x) =
        (1 / 2 : ℝ) * φ x * ((u x - α * (G u) x) ^ 2 +
          (α * (G u2) x - (α * (G u) x) ^ 2)) := by ring
    rw [he]
    exact mul_nonneg (mul_nonneg (by norm_num) h0)
      (add_nonneg (sq_nonneg _) (sub_nonneg.mpr hj))
  have hi := integral_nonneg_of_ae hk
  rw [integral_sub (integrable_mul_Lp v uφ) ((integrable_mul_Lp w φ).const_mul (1 / 2)),
    integral_const_mul, ← inner_eq_integral_mul, ← inner_eq_integral_mul] at hi
  change 0 ≤ α * ⟪v, uφ⟫ - (1 / 2 : ℝ) * α * ⟪w, φ⟫
  nlinarith [mul_nonneg hα.le hi]

theorem core_functional_nonneg (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X} (_h : Data F U)
    {u φ uφ u2 : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hφ : F.toClosedForm.MemCoreOn U φ) (hφ0 : 0 ≤ᵐ[m] φ)
    (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x) (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    0 ≤ F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ := by
  choose G hG using fun n : ℕ => exists_resolvent F ((n : ℝ) + 1) (by positivity)
  have h1 := tendsto_resolvent_form F hG hu.1 huφ
  have h2 := tendsto_resolvent_form F hG hu2 hφ.1
  have ht := h1.sub (h2.const_mul (1 / 2))
  apply ge_of_tendsto ht
  filter_upwards [] with n
  simpa only [mul_assoc] using
    resolvent_energy_nonneg F (by positivity : 0 < (n : ℝ) + 1) (hG n) hφ0 hprod hsq

omit [TopologicalSpace X] in
theorem resolvent_energy_bound [_instPreserved0 : TopologicalSpace X] {m : Measure X} (F : _root_.SubdiffusiveProcess.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {u φ uφ u2 : Lp ℝ 2 m} {M : ℝ} (hM : 0 ≤ M)
    (hφM : ∀ᵐ x ∂m, |φ x| ≤ M)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x) (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    |α * ⟪u - α • G u, uφ⟫ - (1 / 2 : ℝ) * α * ⟪u2 - α • G u2, φ⟫| ≤
      M * (α * ⟪u - α • G u, u⟫) := by
  let R := α • G u
  let S := α • G u2
  let q : X → ℝ := fun x => u x ^ 2 - 2 * (u x * R x) + S x
  have hu20 : 0 ≤ᵐ[m] u2 := by
    filter_upwards [hsq] with x hx
    rw [hx]
    positivity
  have hu2i : Integrable (⇑u2) m := (Lp.memLp u).integrable_sq.congr hsq.symm
  have hSi : Integrable (⇑S) m := (resolvent_integrable F hα hG hu20 hu2i).1
  have hSbound : ∫ x, S x ∂m ≤ ∫ x, u x ^ 2 ∂m := by
    have hb := (resolvent_integrable F hα hG hu20 hu2i).2
    rwa [integral_congr_ae hsq] at hb
  have hqi : Integrable q m :=
    ((Lp.memLp u).integrable_sq.sub ((integrable_mul_Lp u R).const_mul 2)).add hSi
  have hq0 : 0 ≤ᵐ[m] q := by
    filter_upwards [Lp.coeFn_smul α (G u), Lp.coeFn_smul α (G u2),
      resolvent_square_le_general F hα hG hsq] with x h1 h2 hj
    change 0 ≤ u x ^ 2 - 2 * (u x * (α • G u) x) + (α • G u2) x
    simp only [h1, h2, Pi.smul_apply, smul_eq_mul]
    nlinarith [sq_nonneg (u x - α * (G u) x)]
  have hqbound : ∫ x, q x ∂m ≤ 2 * ⟪u - R, u⟫ := by
    have hsubi : Integrable (fun x => u x ^ 2 - 2 * (u x * R x)) m :=
      (Lp.memLp u).integrable_sq.sub ((integrable_mul_Lp u R).const_mul 2)
    have he : ∫ x, q x ∂m = ‖u‖ ^ 2 - 2 * ⟪u, R⟫ + ∫ x, S x ∂m := by
      rw [norm_sq_eq_integral, inner_eq_integral_mul, ← integral_const_mul,
        ← integral_sub (Lp.memLp u).integrable_sq ((integrable_mul_Lp u R).const_mul 2),
        ← integral_add hsubi hSi]
    rw [he, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm u R]
    rw [← norm_sq_eq_integral] at hSbound
    linarith
  let v := u - R
  let w := u2 - S
  let k : X → ℝ := fun x => v x * uφ x - (1 / 2 : ℝ) * (w x * φ x)
  have hk : ∀ᵐ x ∂m, k x = (1 / 2 : ℝ) * φ x * q x := by
    filter_upwards [Lp.coeFn_sub u R, Lp.coeFn_sub u2 S, hprod, hsq] with x h1 h2 hp hs
    simp only [k, v, w, q, h1, h2, Pi.sub_apply, hp, hs]
    ring
  have hi := norm_integral_le_of_norm_le (f := k) (hqi.const_mul (M / 2)) (by
    filter_upwards [hk, hφM, hq0] with x hx hφ h0
    rw [hx, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg h0]
    nlinarith [mul_le_mul_of_nonneg_right hφ h0])
  have hki : Integrable k m :=
    (integrable_mul_Lp v uφ).sub ((integrable_mul_Lp w φ).const_mul (1 / 2))
  have he : ∫ x, k x ∂m = ⟪v, uφ⟫ - (1 / 2 : ℝ) * ⟪w, φ⟫ := by
    rw [integral_sub (integrable_mul_Lp v uφ) ((integrable_mul_Lp w φ).const_mul (1 / 2)),
      integral_const_mul, ← inner_eq_integral_mul, ← inner_eq_integral_mul]
  rw [he, Real.norm_eq_abs, integral_const_mul] at hi
  change |α * ⟪v, uφ⟫ - (1 / 2 : ℝ) * α * ⟪w, φ⟫| ≤ M * (α * ⟪u - R, u⟫)
  rw [show α * ⟪v, uφ⟫ - (1 / 2 : ℝ) * α * ⟪w, φ⟫ =
    α * (⟪v, uφ⟫ - (1 / 2 : ℝ) * ⟪w, φ⟫) by ring,
    abs_mul, abs_of_pos hα]
  nlinarith [mul_le_mul_of_nonneg_left hi hα.le,
    mul_le_mul_of_nonneg_left hqbound (mul_nonneg hα.le hM)]

theorem core_functional_bound (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X} (_h : Data F U)
    {u φ uφ u2 : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hφ : F.toClosedForm.MemCoreOn U φ) {M : ℝ} (hM : 0 ≤ M)
    (hφM : ∀ᵐ x ∂m, |φ x| ≤ M) (huφ : uφ ∈ F.domain) (hu2 : u2 ∈ F.domain)
    (hprod : ⇑uφ =ᵐ[m] fun x => u x * φ x) (hsq : ⇑u2 =ᵐ[m] fun x => u x ^ 2) :
    |F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ| ≤ M * F.form u u := by
  choose G hG using fun n : ℕ => exists_resolvent F ((n : ℝ) + 1) (by positivity)
  have h1 := tendsto_resolvent_form F hG hu.1 huφ
  have h2 := tendsto_resolvent_form F hG hu2 hφ.1
  have h3 := tendsto_resolvent_form F hG hu.1 hu.1
  apply le_of_tendsto_of_tendsto ((h1.sub (h2.const_mul (1 / 2))).abs) (h3.const_mul M)
  filter_upwards [] with n
  simpa only [mul_assoc] using
    resolvent_energy_bound F (by positivity : 0 < (n : ℝ) + 1) (hG n) hM hφM hprod hsq


end SubdiffusiveProcess.DirichletForm.FOTConstruction
