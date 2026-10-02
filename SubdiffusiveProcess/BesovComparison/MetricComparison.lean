import SubdiffusiveProcess.BesovComparison.DefinitionBridge
import Homogenization.Sobolev.Fractional.AssemblyPieces
import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

/-! Comparing the exact scalar Euclidean and ambient fractional kernels. -/
open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

def scalarEnergy (a p : ℝ) (u : Vec d → ℝ) (t : ℝ) (x y : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|u x - u y| ^ p) / ENNReal.ofReal (t ^ a)

theorem scalarEnergy_measurable (a p : ℝ) (u : Vec d → ℝ) (hu : Measurable u)
    (t : Vec d × Vec d → ℝ) (ht : Measurable t) :
    Measurable (fun z : Vec d × Vec d => scalarEnergy a p u (t z) z.1 z.2) := by
  unfold scalarEnergy
  exact (continuous_abs.measurable.comp ((hu.comp measurable_fst).sub (hu.comp measurable_snd)) |>.pow_const p).ennreal_ofReal.div
    (ht.pow_const a).ennreal_ofReal

theorem scalarEnergy_eq_real (a p : ℝ) (u : Vec d → ℝ) (t : ℝ) (x y : Vec d)
    (ht : 0 < t) :
    scalarEnergy a p u t x y = ENNReal.ofReal (|u x - u y| ^ p / t ^ a) := by
  unfold scalarEnergy
  exact (ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht a)).symm

theorem scalarEnergy_self (a p : ℝ) (hp : 0 < p) (u : Vec d → ℝ) (t : ℝ) (x : Vec d) :
    scalarEnergy a p u t x x = 0 := by
  simp [scalarEnergy, Real.zero_rpow hp.ne']

theorem scalarEnergy_euclidean_le (a p : ℝ) (ha : 0 ≤ a) (u : Vec d → ℝ) (x y : Vec d) :
    scalarEnergy a p u (euclideanDist x y) x y ≤ scalarEnergy a p u (dist x y) x y := by
  unfold scalarEnergy
  apply ENNReal.div_le_div_left
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow dist_nonneg (dist_le_euclideanDist x y) ha)

theorem scalarEnergy_ambient_le [NeZero d] (a p : ℝ) (ha : 0 < a) (hp : 0 < p)
    (u : Vec d → ℝ) (x y : Vec d) :
    scalarEnergy a p u (dist x y) x y ≤
      ENNReal.ofReal ((d : ℝ) ^ a) * scalarEnergy a p u (euclideanDist x y) x y := by
  by_cases hxy : x = y
  · subst y
    simp only [scalarEnergy_self a p hp, mul_zero, le_refl]
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have heuc : 0 < euclideanDist x y := hdist.trans_le (dist_le_euclideanDist x y)
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hden : euclideanDist x y ^ a ≤ (d : ℝ) ^ a * dist x y ^ a := by
    calc
      _ ≤ ((d : ℝ) * dist x y) ^ a :=
        Real.rpow_le_rpow heuc.le (euclideanDist_le_dimension_mul_dist x y) ha.le
      _ = _ := Real.mul_rpow hd.le hdist.le
  rw [scalarEnergy_eq_real a p u _ x y hdist, scalarEnergy_eq_real a p u _ x y heuc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le a)]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_div_assoc, div_le_div_iff₀ (Real.rpow_pos_of_pos hdist a) (Real.rpow_pos_of_pos heuc a)]
  calc
    _ ≤ |u x - u y| ^ p * ((d : ℝ) ^ a * dist x y ^ a) :=
      mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg (abs_nonneg _) p)
    _ = _ := by ring

theorem scalar_gagliardo_power (s p : ℝ) (hp : 0 < p) (hs : 0 < s)
    (u : Vec d → ℝ) (z : Vec d × Vec d) :
    ‖Gagliardo.gagliardoKernel s (ENNReal.ofReal p) u z‖ₑ ^ p =
      scalarEnergy ((d : ℝ) + s * p) p u (dist z.1 z.2) z.1 z.2 := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have ha : 0 < (d : ℝ) + s * p := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos hs hp)
  have hid := Gagliardo.enorm_gagliardoKernel_rpow s hp0 ENNReal.ofReal_ne_top u z
  rw [ENNReal.toReal_ofReal hp.le] at hid
  rw [hid, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  rcases z with ⟨x,y⟩
  by_cases hxy : x = y
  · subst y
    simp [scalarEnergy_self _ p hp, Real.zero_rpow hp.ne']
  have ht := dist_pos.mpr hxy
  rw [scalarEnergy_eq_real _ p u _ x y ht, Real.rpow_neg ht.le,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg dist_nonneg _))]
  congr 1
  simp only [add_comm (s*p), div_eq_mul_inv]
  ring

def ambientWsp (d : ℕ) (m : ℤ) (s p : ℝ) (u : Vec d → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal s * (volume (cube d m))⁻¹ *
    ∫⁻ x in cube d m, ∫⁻ y in cube d m,
      scalarEnergy ((d : ℝ) + s*p) p u (dist x y) x y) ^ p⁻¹

theorem ambientWsp_eq_gagliardo (m : ℤ) (s p : ℝ) (hs : 0 < s) (hp : 0 < p)
    (u : Vec d → ℝ) (hu : Measurable u) :
    ambientWsp d m s p u = ENNReal.ofReal s ^ p⁻¹ *
      Gagliardo.cubeGagliardoESeminorm (originCube d m) s (ENNReal.ofReal p) u := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  rw [Gagliardo.Internal.cubeGagliardoESeminorm_eq_lintegral hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, one_div]
  have hkernel : (fun z : Vec d × Vec d => ‖Gagliardo.gagliardoKernel s (ENNReal.ofReal p) u z‖ₑ ^ p) =
      (fun z => scalarEnergy ((d : ℝ) + s*p) p u (dist z.1 z.2) z.1 z.2) := by
    funext z; exact scalar_gagliardo_power s p hp hs u z
  rw [hkernel, Gagliardo.gagliardoCubeMeasure, normalized_root_measure]
  rw [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    Measure.prod_smul_left, lintegral_smul_measure]
  rw [lintegral_prod _ (scalarEnergy_measurable _ _ u hu _ measurable_dist).aemeasurable]
  unfold ambientWsp
  rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
  rfl

end SubdiffusiveProcess.BesovComparison
