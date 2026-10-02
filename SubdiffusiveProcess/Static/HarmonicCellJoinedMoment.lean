import SubdiffusiveProcess.Static.HarmonicCellEnvelopePrice
import SubdiffusiveProcess.Static.HarmonicCellSignedJoining

/-! # Uniform moments of the literal joined cell envelope -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

theorem measurable_harmonicCellJoinedEnvelope {Omega : Type*} [MeasurableSpace Omega]
    (d k : ℕ) (R D G : Omega → ℝ) (hR : Measurable R) (hD : Measurable D) (hG : Measurable G) :
    Measurable (fun omega => harmonicCellJoinedEnvelope d k (R omega) (D omega) (G omega)) := by
  unfold harmonicCellJoinedEnvelope harmonicCellTransition
  exact hG.add (measurable_const.mul (((hR.add hG).add
    (measurable_const.mul (hD.add measurable_const))).pow_const (d + 6)))

/-- The native signed joining retains a uniform requested moment: its quarter
scale margin compensates the higher moments of both microscopic banks. -/
theorem harmonicCellJoinedEnvelope_norm_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (d k : ℕ) (q : ℝ) (hq : 1 ≤ q)
    (R D G : Omega → ℝ) (hRm : Measurable R) (hDm : Measurable D) (hGm : Measurable G)
    (hR : ∀ omega, 1 ≤ R omega) (hD : ∀ omega, 1 ≤ D omega) (hG : ∀ omega, 1 ≤ G omega)
    {A B C eta : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hcost : eta * ((d + 6 : ℕ) : ℝ) ≤ 1 / 4)
    (hRn : eLpNorm R (ENNReal.ofReal (q * ((d + 6 : ℕ) : ℝ))) mu ≤
      ENNReal.ofReal (A * (3 : ℝ) ^ (eta * (k : ℝ))))
    (hDn : eLpNorm D (ENNReal.ofReal (q * ((d + 6 : ℕ) : ℝ))) mu ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (eta * (k : ℝ))))
    (hGn : eLpNorm G (ENNReal.ofReal (q * ((d + 6 : ℕ) : ℝ))) mu ≤ ENNReal.ofReal B) :
    eLpNorm (fun omega => harmonicCellJoinedEnvelope d k (R omega) (D omega) (G omega))
      (ENNReal.ofReal q) mu ≤
      ENNReal.ofReal (B + harmonicCellJoiningPrice d (harmonicCellContrast d) *
        (A + B + 2 / harmonicCellContrast d * (C + 1)) ^ (d + 6)) := by
  let n := d + 6
  let c := 2 / harmonicCellContrast d
  let U := fun omega => R omega + G omega + c * (D omega + 1)
  let Ctot := A + B + c * (C + 1)
  let P := harmonicCellJoiningPrice d (harmonicCellContrast d)
  have hc : 0 ≤ c := by have h := harmonicCellContrast_pos d; dsimp only [c]; positivity
  have hP : 0 ≤ P := harmonicCellJoiningPrice_nonneg d (harmonicCellContrast_pos d).le
  have hCtot : 0 ≤ Ctot := by dsimp only [Ctot]; positivity
  have hQ : 1 ≤ q * (n : ℝ) := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by dsimp only [n]; omega)
    nlinarith
  have hqQ : q ≤ q * (n : ℝ) := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by dsimp only [n]; omega)
    nlinarith
  have hUm : Measurable U := (hRm.add hGm).add ((hDm.add measurable_const).const_mul c)
  have hU : ∀ omega, 0 ≤ U omega := by
    intro omega
    have hR0 := zero_le_one.trans (hR omega)
    have hG0 := zero_le_one.trans (hG omega)
    have hD0 := zero_le_one.trans (hD omega)
    dsimp only [U]
    positivity
  have hUn := harmonicCell_sum_envelope_norm_le mu R G D hRm hGm hDm hQ hc hA hB hC
    (Real.one_le_rpow (by norm_num) (mul_nonneg heta (Nat.cast_nonneg _))) hRn hGn hDn
  have hcomp := harmonicCell_compensated_power_norm_le mu U hU q (by linarith) n k (by
    dsimp only [n]; omega) hCtot hcost hUn
  have hsecond : eLpNorm (fun omega => P *
      ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) * U omega ^ n)) (ENNReal.ofReal q) mu ≤
      ENNReal.ofReal (P * Ctot ^ n) := by
    calc
      _ = ENNReal.ofReal P * eLpNorm
          (fun omega => (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) * U omega ^ n) (ENNReal.ofReal q) mu := by
        simpa only [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hP]
          using eLpNorm_const_smul P
            (fun omega => (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) * U omega ^ n) (ENNReal.ofReal q) mu
      _ ≤ ENNReal.ofReal P * ENNReal.ofReal (Ctot ^ n) := mul_le_mul_right hcomp _
      _ = _ := (ENNReal.ofReal_mul hP).symm
  have hGq := (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqQ)
    hGm.aestronglyMeasurable).trans hGn
  have hsecondm : Measurable (fun omega => P *
      ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) * U omega ^ n)) :=
    measurable_const.mul (measurable_const.mul (hUm.pow_const n))
  have hsum := (eLpNorm_add_le hGm.aestronglyMeasurable hsecondm.aestronglyMeasurable
    (ENNReal.one_le_ofReal.mpr hq)).trans (add_le_add hGq hsecond)
  have hfun : (fun omega => harmonicCellJoinedEnvelope d k (R omega) (D omega) (G omega)) =
      fun omega => G omega + P * ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) * U omega ^ n) := by
    funext omega
    dsimp only [harmonicCellJoinedEnvelope, P, U, n, c, harmonicCellTransition]
    ring
  rw [hfun]
  refine hsum.trans_eq ?_
  rw [← ENNReal.ofReal_add hB (mul_nonneg hP (pow_nonneg hCtot _))]

end SubdiffusiveProcess.Static
