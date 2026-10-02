import SubdiffusiveProcess.DirichletForm.FOTEnergyFamily

open MeasureTheory Filter Set Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- The upper half of the sub-Markov estimate also applies to signed inputs. -/
theorem resolvent_upper_bound (F : _root_.DirichletForm m) {α : ℝ} (hα : 0 < α)
    {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hG : IsResolvent F.toClosedForm α G)
    {f : Lp ℝ 2 m} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ᵐ x ∂m, f x ≤ c) :
    ∀ᵐ x ∂m, α * (G f) x ≤ c := by
  let T : ℝ → ℝ := fun s => min s (c / α)
  have hT : LipschitzWith 1 T := LipschitzWith.id.min_const _
  have hcα : 0 ≤ c / α := div_nonneg hc hα.le
  have hT0 : T 0 = 0 := min_eq_left hcα
  have heq := resolvent_fixed_of_contraction F hα hG hT hT0 (by
    filter_upwards [hf] with x hx
    change α * min ((G f) x) (c / α) ^ 2 -
        2 * (f x * min ((G f) x) (c / α)) ≤ _
    by_cases hz : (G f) x ≤ c / α
    · rw [min_eq_left hz]
    · rw [min_eq_right (le_of_not_ge hz)]
      have hzc : 0 ≤ (G f) x - c / α := sub_nonneg.mpr (le_of_not_ge hz)
      have hprod := mul_nonneg hzc (sub_nonneg.mpr hx)
      have hcEq : α * (c / α) = c := mul_div_cancel₀ c hα.ne'
      nlinarith [mul_nonneg hα.le (sq_nonneg ((G f) x - c / α))])
  have hrep := hT.coeFn_compLp hT0 (G f)
  rw [← heq] at hrep
  filter_upwards [hrep] with x hx
  rw [hx]
  exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hα.le).trans_eq
    (mul_div_cancel₀ c hα.ne')

/-- Quadratic distance comparison for a Lipschitz composition, at the resolvent level. -/
theorem resolvent_lipschitz_distance_le (F : _root_.DirichletForm m)
    {α : ℝ} (hα : 0 < α) {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hG : IsResolvent F.toClosedForm α G) {T : ℝ → ℝ} {L : ℝ≥0}
    (hT : LipschitzWith L T) (hT0 : T 0 = 0)
    {u u2 w w2 : Lp ℝ 2 m}
    (hu2 : ⇑u2 =ᵐ[m] fun x => u x ^ 2)
    (hw : ⇑w =ᵐ[m] fun x => T (u x))
    (hw2 : ⇑w2 =ᵐ[m] fun x => w x ^ 2) :
    ∀ᵐ x ∂m,
      w x ^ 2 - 2 * (w x * (α * (G w) x)) + α * (G w2) x ≤
        (L : ℝ) ^ 2 * (u x ^ 2 - 2 * (u x * (α * (G u) x)) + α * (G u2) x) := by
  have hsq : ∀ a b : ℝ, (T a - T b) ^ 2 ≤ (L : ℝ) ^ 2 * (a - b) ^ 2 := by
    intro a b
    have h := hT.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at h
    have hs := mul_le_mul h h (abs_nonneg _) (mul_nonneg L.coe_nonneg (abs_nonneg _))
    nlinarith [sq_abs (T a - T b), sq_abs (a - b)]
  have hq : ∀ s : ℚ, ∀ᵐ x ∂m,
      α * (G w2) x - 2 * T s * (α * (G w) x) -
        (L : ℝ) ^ 2 * (α * (G u2) x) +
          2 * (L : ℝ) ^ 2 * (s : ℝ) * (α * (G u) x) ≤
        (L : ℝ) ^ 2 * (s : ℝ) ^ 2 - T s ^ 2 := by
    intro s
    let p := w2 - (2 * T s) • w - (L : ℝ) ^ 2 • u2 +
      (2 * (L : ℝ) ^ 2 * (s : ℝ)) • u
    have hp : ∀ᵐ x ∂m, p x ≤ (L : ℝ) ^ 2 * (s : ℝ) ^ 2 - T s ^ 2 := by
      filter_upwards [Lp.coeFn_add (w2 - (2 * T s) • w - (L : ℝ) ^ 2 • u2)
        ((2 * (L : ℝ) ^ 2 * (s : ℝ)) • u),
        Lp.coeFn_sub (w2 - (2 * T s) • w) ((L : ℝ) ^ 2 • u2),
        Lp.coeFn_sub w2 ((2 * T s) • w), Lp.coeFn_smul (2 * T s) w,
        Lp.coeFn_smul ((L : ℝ) ^ 2) u2,
        Lp.coeFn_smul (2 * (L : ℝ) ^ 2 * (s : ℝ)) u, hu2, hw, hw2]
        with x h1 h2 h3 h4 h5 h6 h7 h8 h9
      change (w2 - (2 * T s) • w - (L : ℝ) ^ 2 • u2 +
        (2 * (L : ℝ) ^ 2 * (s : ℝ)) • u) x ≤ _
      simp only [h1, h2, h3, h4, h5, h6, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, h7, h9, h8]
      nlinarith [hsq (u x) s]
    have hc : 0 ≤ (L : ℝ) ^ 2 * (s : ℝ) ^ 2 - T s ^ 2 := by
      have h := hsq s 0
      rw [hT0, sub_zero, sub_zero] at h
      exact sub_nonneg.mpr h
    have hGp : G p = G w2 - (2 * T s) • G w - (L : ℝ) ^ 2 • G u2 +
        (2 * (L : ℝ) ^ 2 * (s : ℝ)) • G u := by
      simp only [p, map_add, map_sub, map_smul]
    have hb := resolvent_upper_bound F hα hG hc hp
    rw [hGp] at hb
    filter_upwards [hb, Lp.coeFn_add (G w2 - (2 * T s) • G w - (L : ℝ) ^ 2 • G u2)
        ((2 * (L : ℝ) ^ 2 * (s : ℝ)) • G u),
      Lp.coeFn_sub (G w2 - (2 * T s) • G w) ((L : ℝ) ^ 2 • G u2),
      Lp.coeFn_sub (G w2) ((2 * T s) • G w), Lp.coeFn_smul (2 * T s) (G w),
      Lp.coeFn_smul ((L : ℝ) ^ 2) (G u2),
      Lp.coeFn_smul (2 * (L : ℝ) ^ 2 * (s : ℝ)) (G u)] with x hb h1 h2 h3 h4 h5 h6
    simp only [h1, h2, h3, h4, h5, h6, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at hb
    nlinarith only [hb]
  filter_upwards [ae_all_iff.mpr hq, hw] with x hx hwx
  let P : ℝ → ℝ := fun s =>
    (L : ℝ) ^ 2 * s ^ 2 - T s ^ 2 -
      (α * (G w2) x - 2 * T s * (α * (G w) x) -
        (L : ℝ) ^ 2 * (α * (G u2) x) +
          2 * (L : ℝ) ^ 2 * s * (α * (G u) x))
  have hPc : Continuous P := by
    have hTc := hT.continuous
    dsimp [P]
    fun_prop
  have hclosed : IsClosed {s : ℝ | 0 ≤ P s} := isClosed_le continuous_const hPc
  have hrange : range (fun s : ℚ => (s : ℝ)) ⊆ {s : ℝ | 0 ≤ P s} := by
    rintro _ ⟨s, rfl⟩
    exact sub_nonneg.mpr (hx s)
  have hall := hclosed.closure_subset_iff.mpr hrange
  rw [Rat.denseRange_cast.closure_range] at hall
  have h := hall (mem_univ (u x))
  dsimp only [P, mem_setOf_eq] at h
  rw [hwx]
  nlinarith only [h]

/-- Lipschitz domination of the positive energy functional before taking its limit. -/
theorem resolvent_lipschitz_functional_le (F : _root_.DirichletForm m)
    {α : ℝ} (hα : 0 < α) {G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hG : IsResolvent F.toClosedForm α G) {T : ℝ → ℝ} {L : ℝ≥0}
    (hT : LipschitzWith L T) (hT0 : T 0 = 0)
    {u u2 w w2 φ uφ wφ : Lp ℝ 2 m} (hφ : 0 ≤ᵐ[m] φ)
    (hu2 : ⇑u2 =ᵐ[m] fun x => u x ^ 2)
    (hw : ⇑w =ᵐ[m] fun x => T (u x))
    (hw2 : ⇑w2 =ᵐ[m] fun x => w x ^ 2)
    (huφ : ⇑uφ =ᵐ[m] fun x => u x * φ x)
    (hwφ : ⇑wφ =ᵐ[m] fun x => w x * φ x) :
    α * ⟪w - α • G w, wφ⟫ - (1 / 2 : ℝ) * α * ⟪w2 - α • G w2, φ⟫ ≤
      (L : ℝ) ^ 2 *
        (α * ⟪u - α • G u, uφ⟫ - (1 / 2 : ℝ) * α * ⟪u2 - α • G u2, φ⟫) := by
  have hp : ∀ᵐ x ∂m,
      (w - α • G w) x * wφ x - (1 / 2 : ℝ) * ((w2 - α • G w2) x * φ x) ≤
        (L : ℝ) ^ 2 *
          ((u - α • G u) x * uφ x - (1 / 2 : ℝ) * ((u2 - α • G u2) x * φ x)) := by
    filter_upwards [resolvent_lipschitz_distance_le F hα hG hT hT0 hu2 hw hw2,
      hφ, hu2, hw2, huφ, hwφ,
      Lp.coeFn_sub w (α • G w), Lp.coeFn_smul α (G w),
      Lp.coeFn_sub w2 (α • G w2), Lp.coeFn_smul α (G w2),
      Lp.coeFn_sub u (α • G u), Lp.coeFn_smul α (G u),
      Lp.coeFn_sub u2 (α • G u2), Lp.coeFn_smul α (G u2)]
      with x hd h0 hu2 hw2 huφ hwφ h1 h2 h3 h4 h5 h6 h7 h8
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hu2, hw2, huφ, hwφ]
    nlinarith only [mul_le_mul_of_nonneg_right hd h0]
  have hi := integral_mono_ae
    ((integrable_mul_Lp (w - α • G w) wφ).sub
      ((integrable_mul_Lp (w2 - α • G w2) φ).const_mul (1 / 2)))
    (((integrable_mul_Lp (u - α • G u) uφ).sub
      ((integrable_mul_Lp (u2 - α • G u2) φ).const_mul (1 / 2))).const_mul ((L : ℝ) ^ 2)) hp
  simp only [Pi.sub_apply, integral_const_mul,
    integral_sub (integrable_mul_Lp (w - α • G w) wφ)
      ((integrable_mul_Lp (w2 - α • G w2) φ).const_mul (1 / 2)),
    integral_sub (integrable_mul_Lp (u - α • G u) uφ)
      ((integrable_mul_Lp (u2 - α • G u2) φ).const_mul (1 / 2)),
    ← inner_eq_integral_mul] at hi
  nlinarith only [mul_le_mul_of_nonneg_left hi hα.le]

end DirichletForm.FOTConstruction
