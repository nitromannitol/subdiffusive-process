module

public import SubdiffusiveProcess.Static.CutoffRescaledPoincare
public import SubdiffusiveProcess.Static.Comparison

@[expose] public section

/-! # Extended-integral readout of the normalized physical energy -/

open MeasureTheory Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The unit-cube energy readout remains valid without an additional
integrability hypothesis on the candidate vector field. -/
theorem cutoffUnitEnergy_le_energy {d : ℕ} (M : GMCModel d) (L m : ℕ)
    (ω : PotentialSample d) (F : Vec d → Vec d) :
    ENNReal.ofReal (cutoffUnitEnergy M L m ω F) ≤
      energy (openCubeSet (originCube d 0))
        (fun x => (ahom M L)⁻¹ * aCutoff M L ω ((3 : ℝ) ^ m • x)) F := by
  let U := openCubeSet (originCube d 0)
  let f : Vec d → ℝ := fun x => aCutoff M L ω ((3 : ℝ) ^ m • x) * vecDot (F x) (F x)
  have hf : ∀ x, 0 ≤ f x := fun x => mul_nonneg (aCutoff_pos M L ω _).le
    (vecNormSq_nonneg (F x))
  have hunit : normalizedCubeMeasure (originCube d 0) = volume.restrict U := by
    simp only [normalizedCubeMeasure, cubeVolume, cubeScaleFactor, originCube,
      zpow_zero, one_pow, inv_one, ENNReal.ofReal_one, one_smul]
    exact Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)
  have hint : ENNReal.ofReal (∫ x in U, f x) ≤ ∫⁻ x in U, ENNReal.ofReal (f x) := by
    calc
      ENNReal.ofReal (∫ x in U, f x) = ‖∫ x in U, f x‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (integral_nonneg hf)]
      _ ≤ ∫⁻ x in U, ‖f x‖ₑ := enorm_integral_le_lintegral_enorm f
      _ = ∫⁻ x in U, ENNReal.ofReal (f x) := lintegral_congr fun x => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf x)]
  have hc : 0 ≤ (ahom M L)⁻¹ := inv_nonneg.mpr (ahom_pos M L).le
  unfold cutoffUnitEnergy
  rw [hunit, ENNReal.ofReal_mul hc]
  refine (mul_le_mul_right hint _).trans (le_of_eq ?_)
  unfold energy
  simp_rw [mul_assoc, ENNReal.ofReal_mul hc]
  exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

end SubdiffusiveProcess.Static
