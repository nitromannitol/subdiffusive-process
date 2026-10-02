import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.ProductMeasure
import SubdiffusiveProcess.Probability.LayerInfluenceTransfer

/-! Hölder assembly of the coarse-layer influence bound.

If the resampling difference `D` on `μ ⊗ μ` is dominated by `(A₁ + A₂) · C_D Δ e^{C_D (A₁ + A₂)}`, where `A`
has sub-Gaussian `L^p` and exponential moments of size `C₁ a`, then `‖D‖_p ≤ C a Δ` with an explicit
constant depending only on `C₁, C_D, p`.  This is the moment-absorption step of `prop-conc` Step 3 for layers
coarser than the cell (anchored oscillation times relative variation); the endpoint gap `Δ` factors out. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace Paper
noncomputable section

/-- `‖exp(c A)‖_q ≤ B` from the exponential moment of order `q c`. -/
theorem aux_prop_conc_coarse_layer_holder_expnorm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → ℝ) (c q B : ℝ) (hq : 1 ≤ q) (hB : 1 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((q * c) * A ω)) ∂μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => Real.exp (c * A ω)) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hqne : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm hqne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
  have hpt : ∀ ω, ‖Real.exp (c * A ω)‖ₑ ^ q = ENNReal.ofReal (Real.exp ((q * c) * A ω)) := by
    intro ω
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ← Real.exp_mul]
    congr 2
    ring
  simp_rw [hpt]
  have h1 : (∫⁻ ω, ENNReal.ofReal (Real.exp ((q * c) * A ω)) ∂μ) ^ (1 / q) ≤
      (ENNReal.ofReal B) ^ (1 / q) :=
    ENNReal.rpow_le_rpow h (by positivity)
  refine h1.trans ?_
  calc (ENNReal.ofReal B) ^ (1 / q) ≤ (ENNReal.ofReal B) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by simpa using hB) (by
          rw [div_le_one hq0]; exact hq)
    _ = ENNReal.ofReal B := ENNReal.rpow_one _

/-- The coarse-layer Hölder assembly. -/
theorem prop_conc_coarse_layer_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℝ) (hAm : Measurable A)
    (C1 a : ℝ) (hC1 : 0 < C1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hLp : ∀ p' : ℝ≥0∞, p' ≠ ⊤ → 2 ≤ p' →
      eLpNorm A p' μ ≤ ENNReal.ofReal (C1 * a * Real.sqrt p'.toReal))
    (hExp : ∀ lam : ℝ, 0 ≤ lam →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * A ω)) ∂μ ≤
        ENNReal.ofReal (2 * Real.exp ((C1 * a) ^ 2 * lam ^ 2 / 4)))
    (p CD Δ : ℝ) (hp : 2 ≤ p) (hCD : 0 < CD) (hΔ : 0 ≤ Δ)
    (D : Ω × Ω → ℝ)
    (hD : ∀ᵐ q ∂(μ.prod μ),
      |D q| ≤ (A q.1 + A q.2) * (CD * Δ * Real.exp (CD * (A q.1 + A q.2)))) :
    eLpNorm D (ENNReal.ofReal p) (μ.prod μ) ≤
      ENNReal.ofReal ((2 * C1 * Real.sqrt (2 * p) * a) *
        (CD * Δ * (2 * Real.exp (C1 ^ 2 * (4 * p * CD) ^ 2 / 4)))) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have h2p1 : (1 : ℝ≥0∞) ≤ 2 * ENNReal.ofReal p := by
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hp1
      _ = 1 * ENNReal.ofReal p := (one_mul _).symm
      _ ≤ 2 * ENNReal.ofReal p := by gcongr; norm_num
  have h2p : 2 * ENNReal.ofReal p = ENNReal.ofReal (2 * p) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  let A1 : Ω × Ω → ℝ := fun q => A q.1
  let A2 : Ω × Ω → ℝ := fun q => A q.2
  have hA1m : Measurable A1 := hAm.comp measurable_fst
  have hA2m : Measurable A2 := hAm.comp measurable_snd
  have hfst : MeasurePreserving Prod.fst (μ.prod μ) μ := measurePreserving_fst
  have hsnd : MeasurePreserving Prod.snd (μ.prod μ) μ := measurePreserving_snd
  let U : Ω × Ω → ℝ := fun q => A q.1 + A q.2
  let V : Ω × Ω → ℝ := fun q => CD * Δ * Real.exp (CD * (A q.1 + A q.2))
  have hUm : AEStronglyMeasurable U (μ.prod μ) := (hA1m.add hA2m).aestronglyMeasurable
  have hVm : AEStronglyMeasurable V (μ.prod μ) :=
    (measurable_const.mul (measurable_const.mul (hA1m.add hA2m)).exp).aestronglyMeasurable
  -- norm of U
  have hU : eLpNorm U (2 * ENNReal.ofReal p) (μ.prod μ) ≤
      ENNReal.ofReal (2 * C1 * Real.sqrt (2 * p) * a) := by
    have hA1 : eLpNorm A1 (2 * ENNReal.ofReal p) (μ.prod μ) =
        eLpNorm A (2 * ENNReal.ofReal p) μ :=
      eLpNorm_comp_measurePreserving hAm.aestronglyMeasurable hfst
    have hA2 : eLpNorm A2 (2 * ENNReal.ofReal p) (μ.prod μ) =
        eLpNorm A (2 * ENNReal.ofReal p) μ :=
      eLpNorm_comp_measurePreserving hAm.aestronglyMeasurable hsnd
    have hbound : eLpNorm A (2 * ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C1 * a * Real.sqrt (2 * p)) := by
      have := hLp (2 * ENNReal.ofReal p) (by rw [h2p]; exact ENNReal.ofReal_ne_top)
        (by rw [h2p]; simpa using ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ 2 * p by linarith))
      rw [h2p]
      rwa [h2p, ENNReal.toReal_ofReal (by linarith)] at this
    calc eLpNorm U (2 * ENNReal.ofReal p) (μ.prod μ)
        ≤ eLpNorm A1 (2 * ENNReal.ofReal p) (μ.prod μ) +
            eLpNorm A2 (2 * ENNReal.ofReal p) (μ.prod μ) :=
          eLpNorm_add_le hA1m.aestronglyMeasurable hA2m.aestronglyMeasurable h2p1
      _ ≤ ENNReal.ofReal (C1 * a * Real.sqrt (2 * p)) +
            ENNReal.ofReal (C1 * a * Real.sqrt (2 * p)) := by
          rw [hA1, hA2]; exact add_le_add hbound hbound
      _ = ENNReal.ofReal (2 * C1 * Real.sqrt (2 * p) * a) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  -- norm of V
  set Bp : ℝ := 2 * Real.exp (C1 ^ 2 * (4 * p * CD) ^ 2 / 4) with hBp
  have hBp1 : 1 ≤ Bp := by
    have : (1 : ℝ) ≤ Real.exp (C1 ^ 2 * (4 * p * CD) ^ 2 / 4) :=
      Real.one_le_exp (by positivity)
    rw [hBp]; linarith
  have hexpnorm : ∀ (Bi : ℝ), Bi = Bp →
      eLpNorm (fun ω => Real.exp ((2 * CD) * A ω)) (2 * ENNReal.ofReal p) μ ≤
        ENNReal.ofReal Bp := by
    intro Bi _
    rw [h2p]
    refine aux_prop_conc_coarse_layer_holder_expnorm μ A (2 * CD) (2 * p) Bp
      (by linarith) hBp1 ?_
    have h := hExp ((2 * p) * (2 * CD)) (by positivity)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hle : (C1 * a) ^ 2 * ((2 * p) * (2 * CD)) ^ 2 / 4 ≤ C1 ^ 2 * (4 * p * CD) ^ 2 / 4 := by
      have e : ((2 * p) * (2 * CD)) = 4 * p * CD := by ring
      rw [e]
      have ha2 : a ^ 2 ≤ 1 := by nlinarith
      have : (C1 * a) ^ 2 ≤ C1 ^ 2 := by
        rw [mul_pow]; nlinarith [sq_nonneg C1]
      have h4 : 0 ≤ (4 * p * CD) ^ 2 := sq_nonneg _
      nlinarith
    rw [hBp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by norm_num)
  have hV : eLpNorm V (2 * ENNReal.ofReal p) (μ.prod μ) ≤
      ENNReal.ofReal (CD * Δ * Bp) := by
    let e1 : Ω × Ω → ℝ := fun q => Real.exp ((2 * CD) * A q.1)
    let e2 : Ω × Ω → ℝ := fun q => Real.exp ((2 * CD) * A q.2)
    have he1m : Measurable e1 := (measurable_const.mul hA1m).exp
    have he2m : Measurable e2 := (measurable_const.mul hA2m).exp
    let W : Ω × Ω → ℝ := fun q => (CD * Δ / 2) * (e1 q + e2 q)
    have hVW : ∀ q, ‖V q‖ ≤ ‖W q‖ := by
      intro q
      have hpos : 0 ≤ V q := by positivity
      have hposW : 0 ≤ W q := by
        have : 0 ≤ e1 q + e2 q := add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
        positivity
      rw [Real.norm_of_nonneg hpos, Real.norm_of_nonneg hposW]
      have hamgm : Real.exp (CD * (A q.1 + A q.2)) ≤ (e1 q + e2 q) / 2 := by
        have hx := Real.exp_pos (CD * A q.1)
        have hy := Real.exp_pos (CD * A q.2)
        have hs : Real.exp (CD * (A q.1 + A q.2)) = Real.exp (CD * A q.1) * Real.exp (CD * A q.2) := by
          rw [← Real.exp_add]; ring_nf
        have h1 : e1 q = Real.exp (CD * A q.1) * Real.exp (CD * A q.1) := by
          simp only [e1]; rw [← Real.exp_add]; ring_nf
        have h2 : e2 q = Real.exp (CD * A q.2) * Real.exp (CD * A q.2) := by
          simp only [e2]; rw [← Real.exp_add]; ring_nf
        rw [hs, h1, h2]
        nlinarith [sq_nonneg (Real.exp (CD * A q.1) - Real.exp (CD * A q.2))]
      have : V q = (CD * Δ) * Real.exp (CD * (A q.1 + A q.2)) := rfl
      rw [this]
      have hCDΔ : 0 ≤ CD * Δ := by positivity
      calc CD * Δ * Real.exp (CD * (A q.1 + A q.2)) ≤ CD * Δ * ((e1 q + e2 q) / 2) :=
            mul_le_mul_of_nonneg_left hamgm hCDΔ
        _ = W q := by simp only [W]; ring
    have he1 : eLpNorm e1 (2 * ENNReal.ofReal p) (μ.prod μ) ≤ ENNReal.ofReal Bp := by
      have : eLpNorm e1 (2 * ENNReal.ofReal p) (μ.prod μ) =
          eLpNorm (fun ω => Real.exp ((2 * CD) * A ω)) (2 * ENNReal.ofReal p) μ :=
        eLpNorm_comp_measurePreserving (g := fun ω => Real.exp ((2 * CD) * A ω))
          (measurable_const.mul hAm).exp.aestronglyMeasurable hfst
      rw [this]; exact hexpnorm Bp rfl
    have he2 : eLpNorm e2 (2 * ENNReal.ofReal p) (μ.prod μ) ≤ ENNReal.ofReal Bp := by
      have : eLpNorm e2 (2 * ENNReal.ofReal p) (μ.prod μ) =
          eLpNorm (fun ω => Real.exp ((2 * CD) * A ω)) (2 * ENNReal.ofReal p) μ :=
        eLpNorm_comp_measurePreserving (g := fun ω => Real.exp ((2 * CD) * A ω))
          (measurable_const.mul hAm).exp.aestronglyMeasurable hsnd
      rw [this]; exact hexpnorm Bp rfl
    have hWnorm : eLpNorm W (2 * ENNReal.ofReal p) (μ.prod μ) ≤ ENNReal.ofReal (CD * Δ * Bp) := by
      have hsum : eLpNorm (fun q => e1 q + e2 q) (2 * ENNReal.ofReal p) (μ.prod μ) ≤
          ENNReal.ofReal Bp + ENNReal.ofReal Bp :=
        (eLpNorm_add_le he1m.aestronglyMeasurable he2m.aestronglyMeasurable h2p1).trans
          (add_le_add he1 he2)
      have hW : eLpNorm W (2 * ENNReal.ofReal p) (μ.prod μ) =
          ENNReal.ofReal (CD * Δ / 2) *
            eLpNorm (fun q => e1 q + e2 q) (2 * ENNReal.ofReal p) (μ.prod μ) := by
        have := eLpNorm_const_smul (μ := μ.prod μ) (p := 2 * ENNReal.ofReal p) (c := CD * Δ / 2)
          (f := fun q => e1 q + e2 q)
        simpa [W, smul_eq_mul, Real.enorm_eq_ofReal (show 0 ≤ CD * Δ / 2 by positivity),
          Pi.smul_def] using this
      rw [hW]
      calc ENNReal.ofReal (CD * Δ / 2) *
            eLpNorm (fun q => e1 q + e2 q) (2 * ENNReal.ofReal p) (μ.prod μ)
          ≤ ENNReal.ofReal (CD * Δ / 2) * (ENNReal.ofReal Bp + ENNReal.ofReal Bp) :=
            mul_le_mul_right hsum _
        _ = ENNReal.ofReal (CD * Δ * Bp) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    exact (eLpNorm_mono (fun q => hVW q)).trans hWnorm
  have h := SubdiffusiveProcess.Probability.eLpNorm_le_of_ae_abs_le_mul hUm hVm
    (D := D) hD hp1 ENNReal.ofReal_ne_top hU hV
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]

end
end Paper
