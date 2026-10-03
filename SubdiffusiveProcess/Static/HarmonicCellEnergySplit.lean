module

public import SubdiffusiveProcess.Static.HarmonicCellBallEstimate
public import SubdiffusiveProcess.Static.HarmonicCellReflection

@[expose] public section

/-! # Literal energy readout for a reflected boundary correction -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The literal weighted lower integral pays only a factor two for a gradient sum. -/
theorem lintegral_energy_add_le {d : ℕ} (W : Set (Vec d))
    (a : Vec d → ℝ) (F G : Vec d → Vec d) (ha : ∀ x, 0 ≤ a x)
    (hF : AEMeasurable (fun x => ENNReal.ofReal (a x * vecNormSq (F x)))
      (volume.restrict W))
    (hG : AEMeasurable (fun x => ENNReal.ofReal (a x * vecNormSq (G x)))
      (volume.restrict W)) :
    ∫⁻ x in W, ENNReal.ofReal (a x * vecNormSq (F x + G x)) ≤
      2 * ((∫⁻ x in W, ENNReal.ofReal (a x * vecNormSq (F x))) +
        ∫⁻ x in W, ENNReal.ofReal (a x * vecNormSq (G x))) := by
  calc
    _ ≤ ∫⁻ x in W, ENNReal.ofReal
        (2 * (a x * vecNormSq (F x) + a x * vecNormSq (G x))) := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left (vecNormSq_add_le (F x) (G x)) (ha x)
      nlinarith only [h]
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add (mul_nonneg (ha _) (vecNormSq_nonneg _))
          (mul_nonneg (ha _) (vecNormSq_nonneg _))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hF _]
      norm_num

/-- A bounded smooth gradient contributes the same `d-1/2` energy growth
on subunit balls as the reflected correction. -/
theorem lintegral_energy_le_of_gradient_bound {d : ℕ} [NeZero d]
    (z : Vec d) {r Lam B : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : Vec d → ℝ) (G : Vec d → Vec d) (hLam : 0 ≤ Lam) (hB : 0 ≤ B)
    (ha : ∀ x ∈ euclideanBall z r, a x ≤ Lam)
    (hG : ∀ x ∈ euclideanBall z r, vecNormSq (G x) ≤ B) :
    ∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecNormSq (G x)) ≤
      ENNReal.ofReal (Lam * B * (volume (smallContrastUnitBall d)).toReal *
        r ^ ((d : ℝ) - 1 / 2)) := by
  have hraw : (∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecNormSq (G x))) ≤
      ENNReal.ofReal (Lam * B) * volume (euclideanBall z r) := by
    calc
      _ ≤ ∫⁻ _x in euclideanBall z r, ENNReal.ofReal (Lam * B) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (isOpen_euclideanBall z r).measurableSet] with x hx
        exact ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_right (ha x hx) (vecNormSq_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (hG x hx) hLam))
      _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ]
  have hvolfin : volume (euclideanBall z r) ≠ ⊤ :=
    Homogenization.Book.Ch01.volume_euclideanBall_ne_top z r
  rw [← ENNReal.ofReal_toReal hvolfin,
    ← ENNReal.ofReal_mul (mul_nonneg hLam hB),
    volume_euclideanBall_toReal_eq_unit_mul_pow z hr] at hraw
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpower : r ^ d ≤ r ^ ((d : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower
    (mul_nonneg (mul_nonneg hLam hB) ENNReal.toReal_nonneg)

end SubdiffusiveProcess.Static
