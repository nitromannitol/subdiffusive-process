module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Envelope
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

@[expose] public section

/-! Law-uniform exponential moments for the finite-cutoff logarithmic envelope. -/

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
  Homogenization.IndependentSums
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.Section6

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The shell-gauge scale with its dependence on the law removed. -/
def cutoffShellGaugeScale (d L : ℕ) (k : ℤ) (delta : ℝ) : ℝ :=
  if L = 0 then
    ((3 * Real.log ((shellCoverShifts d k).card : ℝ)) ^ (2 : ℝ)⁻¹) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * delta)
  else
    ((3 * Real.log ((L + 1 : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹) *
      (Finset.univ : Finset (Fin (L + 1))).sup' Finset.univ_nonempty
        (fun j =>
          ((3 * Real.log
            ((shellCoverShifts d (k - (j : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * delta))

theorem cutoffShellGaugeScale_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (k : ℤ) :
    cutoffShellGaugeScale d L k M.delta = aCutoffCubeShellGaugeScale M L k := rfl

/-- An explicit bound depending only on dimension, cutoff, cube scale,
    disorder strength, and moment order. -/
def cutoffEnvelopeExpMomentBound (d L : ℕ) (k : ℤ) (delta q : ℝ) : ℝ :=
  Real.exp (q * (L + 1 : ℝ) * ((Real.log 2 / 2) * delta ^ 2)) *
    (2 * Real.exp (gammaSigmaLargeMgfConst 2 *
      (cutoffShellGaugeScale d L k delta * (q * (L + 1 : ℝ))) ^
        gammaExpConjExponent 2))

theorem cutoffEnvelopeExpMomentBound_pos (d L : ℕ) (k : ℤ) (delta q : ℝ) :
    0 < cutoffEnvelopeExpMomentBound d L k delta q := by
  unfold cutoffEnvelopeExpMomentBound
  exact mul_pos (Real.exp_pos _) (mul_pos (by norm_num) (Real.exp_pos _))

/-- The quantitative version of the qualitative cutoff-envelope integrability
    theorem. Its right hand side has no dependence on the shell law. -/
theorem integral_exp_mul_cutoffEnvelope_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (k : ℤ)
    {q : ℝ} (hq : 0 < q) :
    (∫ omega, Real.exp (q * aCutoffCubeLogEnvelope M L k omega) ∂M.P.toMeasure) ≤
      cutoffEnvelopeExpMomentBound d L k M.delta q := by
  let c : ℝ := q * (L + 1 : ℝ)
  have hc : 0 < c := mul_pos hq (by positivity)
  have hbig : IsBigO M.P.toMeasure (gammaSigma 2)
      (aCutoffCubeShellGauge L k) (aCutoffCubeShellGaugeScale M L k) := by
    simpa only [IsBigO, abs_of_nonneg (aCutoffCubeShellGauge_nonneg L k _)] using
      isBigOWith_gammaTwo_aCutoffCubeShellGauge M L k
  have hmgf := mgf_le_two_mul_exp_of_isBigO_gammaSigma_of_one_lt
    (measurable_aCutoffCubeShellGauge L k).aemeasurable
    (by norm_num : (1 : ℝ) < 2) (aCutoffCubeShellGaugeScale_pos M L k) hc.le hbig
  have heq : (fun omega => Real.exp (q * aCutoffCubeLogEnvelope M L k omega)) =
      fun omega => Real.exp (c * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        Real.exp (c * aCutoffCubeShellGauge L k omega) := by
    funext omega
    rw [← Real.exp_add]
    congr 1
    dsimp only [c, aCutoffCubeLogEnvelope]
    ring
  rw [heq, integral_const_mul]
  have htau := mul_le_mul_of_nonneg_left (tauSq_le_delta_sq M) hc.le
  have hconst := Real.exp_le_exp.mpr htau
  unfold cutoffEnvelopeExpMomentBound
  rw [cutoffShellGaugeScale_eq]
  exact mul_le_mul hconst hmgf (integral_nonneg fun _ => (Real.exp_pos _).le)
    (Real.exp_pos _).le

end SubdiffusiveProcess.Section6
