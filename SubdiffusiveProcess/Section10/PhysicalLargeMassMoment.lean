import SubdiffusiveProcess.Section10.PhysicalLargeMassDeterministic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Uniform moment of the spatial average. Dependence between cells is unrestricted.
The required input order is exactly 2dQ, chosen before the model threshold. -/
theorem massGlobalConstant_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s Q C : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (K : (Fin d → ℤ) → Ω → ℝ) (hKm : ∀ j, Measurable (K j))
    (hK : ∀ j ω, 0 ≤ K j ω)
    (hm : ∀ j, (∫⁻ ω, ENNReal.ofReal (K j ω ^ ((2 * d : ℕ) * Q)) ∂μ) ≤ ENNReal.ofReal C) :
    Measurable (fun ω => massGlobalConstant s (fun j => K j ω)) ∧
    (∫⁻ ω, ENNReal.ofReal (massGlobalConstant s (fun j => K j ω) ^ Q) ∂μ) ≤
      ENNReal.ofReal ((((15 : ℝ) ^ d + 1) ^ Q * (2 : ℝ) ^ Q) *
        (1 + ((27 : ℝ) ^ d) ^ Q * C)) := by
  classical
  let J := massGlobalGrid d s
  let w : ℝ := s ^ d
  let V : ℝ := (27 : ℝ) ^ d
  let T : ℝ := ((15 : ℝ) ^ d + 1) ^ Q * (2 : ℝ) ^ Q
  let S : Ω → ℝ := fun ω => massSpatialAverage s (fun j => K j ω)
  let R : Ω → ℝ := fun ω => w * ∑ j ∈ J, K j ω ^ ((2 * d : ℕ) * Q)
  have hw : 0 < w := pow_pos hs d
  have hV : 0 < V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : ∀ ω, 0 ≤ S ω := fun ω => mul_nonneg hw.le
    (Finset.sum_nonneg fun j _ => pow_nonneg (hK j ω) _)
  have hR : ∀ ω, 0 ≤ R ω := fun ω => mul_nonneg hw.le
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hK j ω) _)
  have hSm : Measurable S := measurable_const.mul
    (Finset.measurable_sum J fun j _ => (hKm j).pow_const (2 * d))
  have hRm : Measurable R := measurable_const.mul
    (Finset.measurable_sum J fun j _ => (hKm j).pow measurable_const)
  have hglobm : Measurable (fun ω => massGlobalConstant s (fun j => K j ω)) :=
    measurable_const.mul (measurable_const.add hSm)
  refine ⟨hglobm, ?_⟩
  have hcard : w * (J.card : ℝ) ≤ V := massGlobalGrid_weight_card hs hs1
  have havg : ∀ ω, S ω ^ Q ≤ V ^ (Q - 1) * R ω := by
    intro ω
    have h := mass_rpow_sum_bound J hw hcard hQ (fun j => K j ω ^ (2 * d))
      (fun j _ => pow_nonneg (hK j ω) _)
    simpa only [S, R, massSpatialAverage, J, w,
      ← Real.rpow_natCast_mul (hK _ ω)] using h
  have hpoint : ∀ ω, massGlobalConstant s (fun j => K j ω) ^ Q ≤
      T * (1 + V ^ (Q - 1) * R ω) := by
    intro ω
    change (((15 : ℝ) ^ d + 1) * (1 + S ω)) ^ Q ≤ _
    rw [Real.mul_rpow (by positivity) (by linarith [hS ω])]
    calc
      _ ≤ ((15 : ℝ) ^ d + 1) ^ Q * ((2 : ℝ) ^ Q * (1 + S ω ^ Q)) :=
        mul_le_mul_of_nonneg_left (mass_one_add_rpow (hS ω) hQ) (by positivity)
      _ = T * (1 + S ω ^ Q) := by dsimp [T]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [havg ω]) hT
  have hRmoment : (∫⁻ ω, ENNReal.ofReal (R ω) ∂μ) ≤ ENNReal.ofReal (V * C) := by
    have heq : (fun ω => ENNReal.ofReal (R ω)) =
        fun ω => ENNReal.ofReal w * ∑ j ∈ J, ENNReal.ofReal (K j ω ^ ((2 * d : ℕ) * Q)) := by
      funext ω
      dsimp only [R]
      rw [ENNReal.ofReal_mul hw.le, ENNReal.ofReal_sum_of_nonneg]
      exact fun j _ => Real.rpow_nonneg (hK j ω) _
    rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finset_sum J (fun j _ =>
        show Measurable (fun ω => ENNReal.ofReal (K j ω ^ ((2 * d : ℕ) * Q))) from
          ENNReal.measurable_ofReal.comp ((hKm j).pow measurable_const))]
    calc
      _ ≤ ENNReal.ofReal w * ∑ _j ∈ J, ENNReal.ofReal C :=
        mul_le_mul_right (Finset.sum_le_sum fun j _ => hm j) _
      _ = ENNReal.ofReal (w * ((J.card : ℝ) * C)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hw.le]
      _ ≤ ENNReal.ofReal (V * C) := ENNReal.ofReal_le_ofReal (by nlinarith [hcard])
  calc
    (∫⁻ ω, ENNReal.ofReal (massGlobalConstant s (fun j => K j ω) ^ Q) ∂μ)
        ≤ ∫⁻ ω, ENNReal.ofReal (T * (1 + V ^ (Q - 1) * R ω)) ∂μ :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpoint ω)
    _ = ENNReal.ofReal T *
        (1 + ENNReal.ofReal (V ^ (Q - 1)) * ∫⁻ ω, ENNReal.ofReal (R ω) ∂μ) := by
      simp_rw [ENNReal.ofReal_mul hT, ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (Real.rpow_nonneg hV.le _) (hR _)), ENNReal.ofReal_one,
        ENNReal.ofReal_mul (Real.rpow_nonneg hV.le _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp
    _ ≤ ENNReal.ofReal T * (1 + ENNReal.ofReal (V ^ (Q - 1)) * ENNReal.ofReal (V * C)) := by
      gcongr
    _ = ENNReal.ofReal (T * (1 + V ^ Q * C)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hV.le _),
        ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (by positivity),
        ← ENNReal.ofReal_mul hT]
      congr 1
      rw [← mul_assoc, ← Real.rpow_add_one hV.ne']
      congr 2
      ring
    _ = _ := rfl

end SubdiffusiveProcess.Section10
