module

public import SubdiffusiveProcess.Static.HarmonicPairFactors

@[expose] public section

/-! # Product moments for the macroscopic harmonic cell envelope -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- An energy square and a geometric stopping price retain arbitrary moments. -/
theorem harmonic_energy_stopping_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K Z : Ω → ℝ)
    (hK : Measurable K) (hZ : Measurable Z) {q A CK CZ : ℝ}
    (hq : 1 ≤ q) (hA : 0 ≤ A) (hCK : 0 ≤ CK) (hCZ : 0 ≤ CZ)
    (hKN : eLpNorm K (ENNReal.ofReal (4*q)) μ ≤ ENNReal.ofReal CK)
    (hZN : eLpNorm Z (ENNReal.ofReal (2*q)) μ ≤ ENNReal.ofReal CZ) :
    eLpNorm (fun omega => 1+A*(K omega+1)^2*Z omega) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (1+A*(CK+1)^2*CZ) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let F := fun omega => K omega+1
  have hF : Measurable F := hK.add measurable_const
  have hFN : eLpNorm F (ENNReal.ofReal (4*q)) μ ≤ ENNReal.ofReal (CK+1) := by
    have hc : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (4*q)) μ = 1 := by
      rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (by positivity)).ne' (NeZero.ne μ)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
    refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith))).trans ?_
    rw [hc]
    exact (add_le_add hKN le_rfl).trans_eq (by
      rw [ENNReal.ofReal_add hCK (by norm_num), ENNReal.ofReal_one])
  have hsq : eLpNorm (fun omega => (F omega)^2) (ENNReal.ofReal (2*q)) μ ≤
      ENNReal.ofReal ((CK+1)^2) := by
    have hp := pair_eLpNorm_mul_le μ F F (by positivity : 0 < 2*q)
      hF.aestronglyMeasurable hF.aestronglyMeasurable
    rw [show 2*(2*q)=4*q by ring] at hp
    have hp' : eLpNorm (fun omega => (F omega)^2) (ENNReal.ofReal (2*q)) μ ≤
        (ENNReal.ofReal (CK+1))^2 := by
      simpa only [← sq] using! hp.trans (mul_le_mul' hFN hFN)
    exact hp'.trans_eq (ENNReal.ofReal_pow (by positivity) 2).symm
  have hprod := pair_eLpNorm_mul_le μ (fun omega => (F omega)^2) Z hq0
    (hF.pow_const 2).aestronglyMeasurable hZ.aestronglyMeasurable
  have hprodN := hprod.trans (mul_le_mul' hsq hZN)
  have hc : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) μ = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq0).ne' (NeZero.ne μ)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  have hscaled : eLpNorm (fun omega => A*(F omega)^2*Z omega) (ENNReal.ofReal q) μ =
      ENNReal.ofReal A*eLpNorm (fun omega => (F omega)^2*Z omega) (ENNReal.ofReal q) μ := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, Real.enorm_eq_ofReal hA] using!
      eLpNorm_const_smul A (fun omega => (F omega)^2*Z omega) (ENNReal.ofReal q) μ
  refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
  rw [hc, hscaled]
  refine (add_le_add le_rfl (mul_le_mul' le_rfl hprodN)).trans_eq ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by norm_num) (by positivity),
    ENNReal.ofReal_one]

end SubdiffusiveProcess.Static
