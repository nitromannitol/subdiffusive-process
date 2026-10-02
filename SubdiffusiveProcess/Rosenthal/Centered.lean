import SubdiffusiveProcess.Rosenthal.Symmetric
import Homogenization.Probability.IndependentSums.Rosenthal
import Homogenization.Probability.IndependentSums.MomentCalculus

/-!
# `L^p` bound for a centered independent sum by the square function

For independent `f_i ∈ L^p` (`p ≥ 1`):
`‖∑ (f_i - E f_i)‖_p ≤ 2 K_p ‖(∑ f_i²)^{1/2}‖_p` in `[0,∞]`, `K_p = (2 e^{-p/2} p^{p/2})^{1/p}`.
Proof: library symmetrization to `f_i(ω₁) - f_i(ω₂)` on `Ω × Ω`, Khintchine for the symmetric independent
differences, and Minkowski for the `ℓ²`-norm.
-/

namespace SubdiffusiveProcess.Rosenthal

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Homogenization.IndependentSums

/-- The Khintchine constant `K_p = (2 e^{-p/2} p^{p/2})^{1/p}`. -/
noncomputable def khintchineConst (p : ℝ) : ℝ := (2 * Real.exp (-p / 2) * p ^ (p / 2)) ^ (1 / p)

/-- Triangle inequality for the Euclidean norm on `ι → ℝ`. -/
theorem sqrt_sum_sq_sub_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    Real.sqrt (∑ i, (a i - b i) ^ 2) ≤ Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) := by
  set A : ℝ := ∑ i, a i ^ 2 with hA
  set B : ℝ := ∑ i, b i ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have h1 : |∑ i, a i * b i| ≤ Real.sqrt A * Real.sqrt B := by
    calc |∑ i, a i * b i| = Real.sqrt ((∑ i, a i * b i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B
  have h1' := abs_le.mp h1
  have h2 : ∑ i, (a i - b i) ^ 2 = A + B - 2 * ∑ i, a i * b i := by
    have : ∀ i, (a i - b i) ^ 2 = a i ^ 2 + b i ^ 2 - 2 * (a i * b i) := fun i => by ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [h2]
  nlinarith [Real.sq_sqrt hA0, Real.sq_sqrt hB0]

theorem sqrt_rpow_eq {x : ℝ} (hx : 0 ≤ x) {p : ℝ} : Real.sqrt x ^ p = x ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1; ring

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Minkowski for the square function of the independent-copy difference. -/
theorem lintegral_diff_root_le {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (f i)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, ENNReal.ofReal ((∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2)) ∂(μ.prod μ)) ^ (1 / p) ≤
      2 * (∫⁻ ω, ENNReal.ofReal ((∑ i, f i ω ^ 2) ^ (p / 2)) ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set gf : Ω → ℝ := fun ω => Real.sqrt (∑ i, f i ω ^ 2) with hgf
  have hgfm : Measurable gf :=
    (Finset.measurable_sum _ (fun i _ => (hmeas i).pow_const 2)).sqrt
  have hgf0 : ∀ ω, 0 ≤ gf ω := fun ω => Real.sqrt_nonneg _
  have hgfp : ∀ ω, gf ω ^ p = (∑ i, f i ω ^ 2) ^ (p / 2) := fun ω =>
    sqrt_rpow_eq (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hpt : ∀ ω : Ω × Ω, ENNReal.ofReal ((∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2)) ≤
      (ENNReal.ofReal (gf ω.1) + ENNReal.ofReal (gf ω.2)) ^ p := by
    intro ω
    have h1 : Real.sqrt (∑ i, (f i ω.1 - f i ω.2) ^ 2) ≤ gf ω.1 + gf ω.2 :=
      sqrt_sum_sq_sub_le (fun i => f i ω.1) (fun i => f i ω.2)
    have h2 : (∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2) ≤ (gf ω.1 + gf ω.2) ^ p := by
      rw [← sqrt_rpow_eq (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      exact Real.rpow_le_rpow (Real.sqrt_nonneg _) h1 hp0.le
    calc ENNReal.ofReal ((∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2))
        ≤ ENNReal.ofReal ((gf ω.1 + gf ω.2) ^ p) := ENNReal.ofReal_le_ofReal h2
      _ = (ENNReal.ofReal (gf ω.1 + gf ω.2)) ^ p :=
          (ENNReal.ofReal_rpow_of_nonneg (add_nonneg (hgf0 _) (hgf0 _)) hp0.le).symm
      _ = _ := by rw [ENNReal.ofReal_add (hgf0 _) (hgf0 _)]
  have hF1 : Measurable (fun ω : Ω × Ω => ENNReal.ofReal (gf ω.1)) :=
    ENNReal.measurable_ofReal.comp (hgfm.comp measurable_fst)
  have hF2 : Measurable (fun ω : Ω × Ω => ENNReal.ofReal (gf ω.2)) :=
    ENNReal.measurable_ofReal.comp (hgfm.comp measurable_snd)
  have hint1 : ∫⁻ ω : Ω × Ω, (ENNReal.ofReal (gf ω.1)) ^ p ∂(μ.prod μ) =
      ∫⁻ ω, ENNReal.ofReal ((∑ i, f i ω ^ 2) ^ (p / 2)) ∂μ := by
    have := (measurePreserving_fst (μ := μ) (ν := μ)).lintegral_comp
      (f := fun ω : Ω => (ENNReal.ofReal (gf ω)) ^ p)
      ((ENNReal.measurable_ofReal.comp hgfm).pow_const p)
    rw [this]
    refine lintegral_congr (fun ω => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (hgf0 ω) hp0.le, hgfp]
  have hint2 : ∫⁻ ω : Ω × Ω, (ENNReal.ofReal (gf ω.2)) ^ p ∂(μ.prod μ) =
      ∫⁻ ω, ENNReal.ofReal ((∑ i, f i ω ^ 2) ^ (p / 2)) ∂μ := by
    have := (measurePreserving_snd (μ := μ) (ν := μ)).lintegral_comp
      (f := fun ω : Ω => (ENNReal.ofReal (gf ω)) ^ p)
      ((ENNReal.measurable_ofReal.comp hgfm).pow_const p)
    rw [this]
    refine lintegral_congr (fun ω => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (hgf0 ω) hp0.le, hgfp]
  calc (∫⁻ ω, ENNReal.ofReal ((∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2)) ∂(μ.prod μ)) ^ (1 / p)
      ≤ (∫⁻ ω : Ω × Ω, (ENNReal.ofReal (gf ω.1) + ENNReal.ofReal (gf ω.2)) ^ p ∂(μ.prod μ)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by positivity)
    _ ≤ (∫⁻ ω : Ω × Ω, (ENNReal.ofReal (gf ω.1)) ^ p ∂(μ.prod μ)) ^ (1 / p) +
        (∫⁻ ω : Ω × Ω, (ENNReal.ofReal (gf ω.2)) ^ p ∂(μ.prod μ)) ^ (1 / p) :=
        ENNReal.lintegral_Lp_add_le (f := fun ω : Ω × Ω => ENNReal.ofReal (gf ω.1))
          (g := fun ω : Ω × Ω => ENNReal.ofReal (gf ω.2)) hF1.aemeasurable hF2.aemeasurable hp
    _ = 2 * (∫⁻ ω, ENNReal.ofReal ((∑ i, f i ω ^ 2) ^ (p / 2)) ∂μ) ^ (1 / p) := by
        rw [hint1, hint2, two_mul]

/-- **Symmetrization + Khintchine.**  `‖∑ (f_i - E f_i)‖_p ≤ 2 K_p ‖(∑ f_i²)^{1/2}‖_p` in `[0,∞]`. -/
theorem lintegral_centered_root_le [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (f i)) (hind : iIndepFun f μ) {p : ℝ} (hp : 1 ≤ p)
    (hLp : ∀ i, Integrable (fun ω => |f i ω| ^ p) μ) :
    (∫⁻ ω, ENNReal.ofReal (|∑ i, (f i ω - ∫ x, f i x ∂μ)| ^ p) ∂μ) ^ (1 / p) ≤
      ENNReal.ofReal (khintchineConst p) * 2 *
        (∫⁻ ω, ENNReal.ofReal ((∑ i, f i ω ^ 2) ^ (p / 2)) ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hf_int : ∀ i, Integrable (f i) μ := fun i =>
    integrable_of_integrable_abs_rpow hp (hmeas i) (hLp i)
  have hsum_int : Integrable (fun ω => |∑ i ∈ Finset.univ, f i ω| ^ p) μ :=
    integrable_abs_finsetSum_rpow hp (fun i _ => hmeas i) (fun i _ => hLp i)
  have hsymm_int := integrable_abs_symmetrizedFinsetSum_rpow_of_integrable_abs_finsetSum_rpow
    (μ := μ) hp (fun i _ => hmeas i) hsum_int
  have hreal := integral_abs_centeredFinsetSum_rpow_le_integral_abs_symmetrizedFinsetSum_rpow
    (μ := μ) (X := f) (s := Finset.univ) hp (fun i _ => hf_int i) hsymm_int
  have hC_int : Integrable (fun ω => |∑ i, (f i ω - ∫ x, f i x ∂μ)| ^ p) μ :=
    integrable_abs_finsetSum_rpow (f := fun i ω => f i ω - ∫ x, f i x ∂μ) (s := Finset.univ) hp
      (fun i _ => (hmeas i).sub_const _)
      (fun i _ => integrable_abs_sub_integral_rpow_of_integrable_abs_rpow hp (hmeas i) (hLp i))
  have hC : ∫⁻ ω, ENNReal.ofReal (|∑ i, (f i ω - ∫ x, f i x ∂μ)| ^ p) ∂μ =
      ENNReal.ofReal (∫ ω, |∑ i, (f i ω - ∫ x, f i x ∂μ)| ^ p ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hC_int (ae_of_all _ (fun _ => by positivity))).symm
  have hS : ∫⁻ ω : Ω × Ω, ENNReal.ofReal (|∑ i, (f i ω.1 - f i ω.2)| ^ p) ∂(μ.prod μ) =
      ENNReal.ofReal (∫ ω : Ω × Ω, |symmetrizedFinsetSum f Finset.univ ω| ^ p ∂(μ.prod μ)) := by
    have := ofReal_integral_eq_lintegral_ofReal hsymm_int (ae_of_all _ (fun _ => by positivity))
    rw [this]; rfl
  have h1 : ∫⁻ ω, ENNReal.ofReal (|∑ i, (f i ω - ∫ x, f i x ∂μ)| ^ p) ∂μ ≤
      ∫⁻ ω : Ω × Ω, ENNReal.ofReal (|∑ i, (f i ω.1 - f i ω.2)| ^ p) ∂(μ.prod μ) := by
    rw [hC, hS]
    exact ENNReal.ofReal_le_ofReal hreal
  have hDm : ∀ i, Measurable (fun ω : Ω × Ω => f i ω.1 - f i ω.2) := fun i =>
    ((hmeas i).comp measurable_fst).sub ((hmeas i).comp measurable_snd)
  have h2 := lintegral_abs_sum_rpow_le_of_symm (μ := μ.prod μ)
    (D := fun i (ω : Ω × Ω) => f i ω.1 - f i ω.2) hDm
    (iIndepFun_sub_comp_fst_comp_snd_prod hind hmeas)
    (fun i => identDistrib_sub_comp_fst_comp_snd_prod_neg (hmeas i)) hp0
  have h3 := lintegral_diff_root_le (μ := μ) hmeas hp
  have hK0 : 0 ≤ 2 * Real.exp (-p / 2) * p ^ (p / 2) := by positivity
  calc (∫⁻ ω, ENNReal.ofReal (|∑ i, (f i ω - ∫ x, f i x ∂μ)| ^ p) ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal (2 * Real.exp (-p / 2) * p ^ (p / 2)) *
          ∫⁻ ω : Ω × Ω, ENNReal.ofReal ((∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2)) ∂(μ.prod μ)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (h1.trans h2) (by positivity)
    _ = ENNReal.ofReal (khintchineConst p) *
          (∫⁻ ω : Ω × Ω, ENNReal.ofReal ((∑ i, (f i ω.1 - f i ω.2) ^ 2) ^ (p / 2)) ∂(μ.prod μ)) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.ofReal_rpow_of_nonneg hK0 (by positivity)]
        rfl
    _ ≤ ENNReal.ofReal (khintchineConst p) *
          (2 * (∫⁻ ω, ENNReal.ofReal ((∑ i, f i ω ^ 2) ^ (p / 2)) ∂μ) ^ (1 / p)) := by gcongr
    _ = _ := by ring

end SubdiffusiveProcess.Rosenthal
