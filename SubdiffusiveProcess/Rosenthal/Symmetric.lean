import SubdiffusiveProcess.Rosenthal.SignAverage

/-!
# Khintchine's inequality for symmetric independent families

If `D_1,…,D_N` are independent and each `D_i` has the same law as `-D_i`, then the law of `(D_i)` is invariant
under every coordinate sign flip, so `E|∑ D_i|^p` equals the average over sign vectors of `E|∑ ε_i D_i|^p`;
the finite sign average bound of `SignAverage` gives
`E|∑ D_i|^p ≤ 2 e^{-p/2} p^{p/2} E (∑ D_i²)^{p/2}`  (in `[0,∞]`).
-/

namespace SubdiffusiveProcess.Rosenthal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- The coordinate sign flip. -/
def flipSigns (s : ι → Bool) (x : ι → ℝ) : ι → ℝ := fun i => sgn (s i) * x i

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_flipSigns (s : ι → Bool) : Measurable (flipSigns s) :=
  measurable_pi_lambda _ (fun i => (measurable_const.mul (measurable_pi_apply i)))

omit [DecidableEq ι] in
theorem measurePreserving_flipSigns {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (D i)) (hsym : ∀ i, IdentDistrib (D i) (fun ω => -D i ω) μ μ)
    (s : ι → Bool) :
    MeasurePreserving (flipSigns s) (Measure.pi fun i => μ.map (D i)) (Measure.pi fun i => μ.map (D i)) := by
  haveI : ∀ i, IsProbabilityMeasure (μ.map (D i)) := fun i =>
    Measure.isProbabilityMeasure_map (hmeas i).aemeasurable
  have h : ∀ i, MeasurePreserving (fun x : ℝ => sgn (s i) * x) (μ.map (D i)) (μ.map (D i)) := by
    intro i
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    cases hs : s i
    · have e : (fun x : ℝ => sgn false * x) = fun x => -x := by
        funext x; simp [sgn]
      rw [e]
      have h1 : (μ.map (D i)).map (fun x : ℝ => -x) = μ.map (fun ω => -D i ω) := by
        rw [Measure.map_map measurable_neg (hmeas i)]; rfl
      rw [h1]
      exact (hsym i).map_eq.symm
    · have e : (fun x : ℝ => sgn true * x) = id := by
        funext x; simp [sgn]
      rw [e, Measure.map_id]
  exact measurePreserving_pi (fun i => μ.map (D i)) (fun i => μ.map (D i)) h

omit [DecidableEq ι] in
/-- Invariance of expectations under coordinate sign flips. -/
theorem lintegral_flipSigns_eq {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (D i)) (hind : iIndepFun D μ)
    (hsym : ∀ i, IdentDistrib (D i) (fun ω => -D i ω) μ μ)
    (G : (ι → ℝ) → ℝ≥0∞) (hG : Measurable G) (s : ι → Bool) :
    ∫⁻ ω, G (flipSigns s (fun i => D i ω)) ∂μ = ∫⁻ ω, G (fun i => D i ω) ∂μ := by
  have hF : Measurable (fun ω i => D i ω) := measurable_pi_lambda _ hmeas
  have hν : μ.map (fun ω i => D i ω) = Measure.pi (fun i => μ.map (D i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)).mp hind
  have h1 : ∫⁻ ω, G (flipSigns s (fun i => D i ω)) ∂μ =
      ∫⁻ x, G (flipSigns s x) ∂(μ.map (fun ω i => D i ω)) := by
    exact (lintegral_map (f := fun x => G (flipSigns s x)) (hG.comp (measurable_flipSigns s)) hF).symm
  have h2 : ∫⁻ ω, G (fun i => D i ω) ∂μ = ∫⁻ x, G x ∂(μ.map (fun ω i => D i ω)) := by
    rw [lintegral_map hG hF]
  rw [h1, h2, hν]
  exact (measurePreserving_flipSigns hmeas hsym s).lintegral_comp hG

/-- **Khintchine's inequality for symmetric independent families**, in `[0,∞]`. -/
theorem lintegral_abs_sum_rpow_le_of_symm {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (D i)) (hind : iIndepFun D μ)
    (hsym : ∀ i, IdentDistrib (D i) (fun ω => -D i ω) μ μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (|∑ i, D i ω| ^ p) ∂μ ≤
      ENNReal.ofReal (2 * Real.exp (-p / 2) * p ^ (p / 2)) *
        ∫⁻ ω, ENNReal.ofReal ((∑ i, D i ω ^ 2) ^ (p / 2)) ∂μ := by
  set G : (ι → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (|∑ i, x i| ^ p) with hG
  have hsumm : Measurable (fun x : ι → ℝ => ∑ i, x i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply (X := fun _ : ι => ℝ) i)
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp (hsumm.abs.pow_const p)
  have hcard : (Fintype.card (ι → Bool) : ℝ≥0∞) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]; push_cast; rfl
  set L : ℝ≥0∞ := ∫⁻ ω, G (fun i => D i ω) ∂μ with hL
  have hsum : (2 : ℝ≥0∞) ^ Fintype.card ι * L = ∫⁻ ω, ∑ s : ι → Bool, G (flipSigns s (fun i => D i ω)) ∂μ := by
    have hms : ∀ s : ι → Bool, Measurable (fun ω => G (flipSigns s (fun i => D i ω))) := fun s =>
      hGm.comp ((measurable_flipSigns s).comp (measurable_pi_lambda _ hmeas))
    rw [lintegral_finset_sum _ (fun s _ => hms s)]
    simp_rw [lintegral_flipSigns_eq hmeas hind hsym G hGm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hpt : ∀ ω, ∑ s : ι → Bool, G (flipSigns s (fun i => D i ω)) ≤
      (2 : ℝ≥0∞) ^ Fintype.card ι * (ENNReal.ofReal (2 * Real.exp (-p / 2) * p ^ (p / 2)) *
        ENNReal.ofReal ((∑ i, D i ω ^ 2) ^ (p / 2))) := by
    intro ω
    have h := sum_abs_signs_rpow_le (fun i => D i ω) hp
    calc ∑ s : ι → Bool, G (flipSigns s (fun i => D i ω))
        = ENNReal.ofReal (∑ s : ι → Bool, |∑ i, sgn (s i) * D i ω| ^ p) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
          rfl
      _ ≤ ENNReal.ofReal (2 ^ Fintype.card ι * ((2 * Real.exp (-p / 2) * p ^ (p / 2)) *
            (∑ i, D i ω ^ 2) ^ (p / 2))) := ENNReal.ofReal_le_ofReal h
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (by norm_num)]
          simp
  have hcancel : (2 : ℝ≥0∞) ^ Fintype.card ι * L ≤ (2 : ℝ≥0∞) ^ Fintype.card ι *
      (ENNReal.ofReal (2 * Real.exp (-p / 2) * p ^ (p / 2)) *
        ∫⁻ ω, ENNReal.ofReal ((∑ i, D i ω ^ 2) ^ (p / 2)) ∂μ) := by
    rw [hsum]
    calc ∫⁻ ω, ∑ s : ι → Bool, G (flipSigns s (fun i => D i ω)) ∂μ
        ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ Fintype.card ι * (ENNReal.ofReal (2 * Real.exp (-p / 2) * p ^ (p / 2)) *
            ENNReal.ofReal ((∑ i, D i ω ^ 2) ^ (p / 2))) ∂μ := lintegral_mono hpt
      _ = _ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).mp hcancel

end SubdiffusiveProcess.Rosenthal
