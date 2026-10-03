module

public import SubdiffusiveProcess.Static.HarmonicCellMomentArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.MaximalDerivative

@[expose] public section

/-! # Cutoff-uniform moments of the microscopic logarithmic derivative price -/

open MeasureTheory Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A positive microscopic derivative envelope on one translated unit cell. -/
def harmonicMicroscopicDerivativeEnvelope {d : ℕ} (j : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ℝ := 1 + fixedCutoffOscillationEnvelope j z omega

theorem one_le_harmonicMicroscopicDerivativeEnvelope {d : ℕ} (j : ℕ) (z : Vec d)
    (omega : PotentialSample d) : 1 ≤ harmonicMicroscopicDerivativeEnvelope j z omega :=
  le_add_of_nonneg_right (fixedCutoffOscillationEnvelope_nonneg j z omega)

theorem measurable_harmonicMicroscopicDerivativeEnvelope {d : ℕ} (j : ℕ) (z : Vec d) :
    Measurable (harmonicMicroscopicDerivativeEnvelope j z) :=
  measurable_const.add (measurable_fixedCutoffOscillationEnvelope j z)

/-- Derivative moments are uniform in the cutoff and centre. -/
theorem harmonicMicroscopicDerivativeEnvelope_moment_bound {d : ℕ} (q : ℝ) (hq : 1 ≤ q)
    (M : GMCModel d) (hdelta : M.delta ≤ 1) (j : ℕ) (z : Vec d) :
    eLpNorm (harmonicMicroscopicDerivativeEnvelope j z) (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (1 + gammaMomentConst 2 * q ^ (2 : ℝ)⁻¹ * fixedCutoffOscillationConst) := by
  let X := fixedCutoffOscillationEnvelope (d := d) j z
  let A := fixedCutoffOscillationConst * M.delta
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hA : 0 < A := mul_pos fixedCutoffOscillationConst_pos M.shellPrefix.delta_pos
  have hX : Measurable X := measurable_fixedCutoffOscillationEnvelope j z
  have hX0 : ∀ omega, 0 ≤ X omega := fixedCutoffOscillationEnvelope_nonneg j z
  have htail := isBigOWith_gammaTwo_fixedCutoffOscillationEnvelope M j z
  have hi := integrable_rpow_of_isBigOWith_gammaSigma (by norm_num) hA hq hX0 hX.aemeasurable htail
  have hmoment := integral_rpow_le_of_isBigOWith_gammaSigma
    (by norm_num) hA hq hX0 hX.aemeasurable htail
  have hgamma := (gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)).le
  have hn : eLpNorm X (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (gammaMomentConst 2 * q ^ (2 : ℝ)⁻¹ * A) := by
    rw [eLpNorm_nonneg_eq_ofReal_integral_root M.P.toMeasure X hX0 hq0 hi]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((gammaMomentConst 2 * q ^ (2 : ℝ)⁻¹ * A) ^ q) ^ q⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun omega => Real.rpow_nonneg (hX0 omega) q)
          hmoment (inv_nonneg.mpr hq0.le)
      _ = _ := Real.rpow_rpow_inv (by positivity) hq0.ne'
  have hconst : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal q)
      M.P.toMeasure = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq0).ne' (NeZero.ne M.P.toMeasure)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  refine (eLpNorm_add_le (f := fun _ : PotentialSample d => (1 : ℝ)) (g := X)
    (ENNReal.one_le_ofReal.mpr hq)).trans ?_
  rw [hconst]
  refine (add_le_add le_rfl hn).trans ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [A]
  have hosc := fixedCutoffOscillationConst_pos.le
  have hbound := mul_le_mul_of_nonneg_left hdelta
    (mul_nonneg (mul_nonneg hgamma (Real.rpow_nonneg hq0.le (2 : ℝ)⁻¹)) hosc)
  nlinarith only [hbound]

/-- The same interface as the coefficient price, allowing one finite-bank
argument to consume either envelope. -/
theorem exists_harmonicMicroscopicDerivativeEnvelope_geometric_moment_bound
    (d : ℕ) (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 → ∀ j : ℕ, ∀ p : Fin d → ℤ,
        eLpNorm (harmonicMicroscopicDerivativeEnvelope j (physicalShellCoverCenter 0 p))
          (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (eta * (j : ℝ))) := by
  let C := 1 + gammaMomentConst 2 * q ^ (2 : ℝ)⁻¹ * fixedCutoffOscillationConst
  have hC : 0 < C := by
    have hg := gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)
    have ho := fixedCutoffOscillationConst_pos
    dsimp only [C]
    positivity
  refine ⟨1, C, by norm_num, hC, ?_⟩
  intro M hM j p
  refine (harmonicMicroscopicDerivativeEnvelope_moment_bound q hq M hM j _).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hg : 1 ≤ (3 : ℝ) ^ (eta * (j : ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hg hC.le

end SubdiffusiveProcess.Static
