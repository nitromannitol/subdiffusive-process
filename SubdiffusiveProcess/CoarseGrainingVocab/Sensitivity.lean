import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Scalar coefficient sensitivity
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- The real-valued `L^∞(U)` error in the scalar ratio `a / b - 1`. -/
noncomputable def scalarRatioLInf {d : ℕ} (U : Ch02.Domain d)
    (a b : Vec d → ℝ) : ℝ :=
  (eLpNorm (fun x => a x / b x - 1) ∞
    (volumeMeasureOn (U : Set (Vec d)))).toReal

private theorem scalarRatioLInf_lt_top {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) :
    eLpNorm (fun x => a x / b x - 1) ∞
      (volumeMeasureOn (U : Set (Vec d))) < ∞ := by
  have hbound : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      ‖a x / b x - 1‖ ≤ ha.Lam / hb.lam + 1 := by
    filter_upwards [ha.aeBounds, hb.aeBounds] with x hax hbx
    have hapos : 0 < a x := lt_of_lt_of_le ha.lam_pos hax.1
    have hbpos : 0 < b x := lt_of_lt_of_le hb.lam_pos hbx.1
    have hratio : a x / b x ≤ ha.Lam / hb.lam :=
      div_le_div₀ (ha.lam_pos.le.trans ha.lam_le_Lam) hax.2 hb.lam_pos hbx.1
    rw [Real.norm_eq_abs]
    calc
      |a x / b x - 1| ≤ |a x / b x| + |(1 : ℝ)| := abs_sub _ _
      _ = a x / b x + 1 := by rw [abs_of_pos (div_pos hapos hbpos), abs_one]
      _ ≤ ha.Lam / hb.lam + 1 := by linarith
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_lt_top_of_ae_bound hbound


private theorem integrable_scalar_dirichlet_integrand {d : ℕ}
    {U : Ch02.Domain d} {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (u : H1Function (U : Set (Vec d))) :
    Integrable (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
      (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) := by
  let c : Ch02.CoeffOn U :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U ha.toCoeffOn
  have hcEll :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
      U ha.toCoeffOn
  have hcInt :=
    Homogenization.Internal.Ch02.BookCh02.integrableOn_h1_coefficientEnergyDensity
      hcEll u
  have hcEq :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U ha.toCoeffOn
  have hcInt' : Integrable (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
      (matVecMul (c.toCoeffField x) (u.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) :=
    hcInt.const_mul (1 / 2 : ℝ)
  refine hcInt'.congr ?_
  filter_upwards [hcEq] with x hx
  simp [c, hx]

/-- The ratio error bounds the ratio almost everywhere. -/
theorem abs_scalar_ratio_sub_one_le_scalarRatioLInf_ae {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      |a x / b x - 1| ≤ scalarRatioLInf U a b := by
  have hfinite := scalarRatioLInf_lt_top ha hb
  have hess := enorm_ae_le_eLpNormEssSup (fun x => a x / b x - 1)
    (volumeMeasureOn (U : Set (Vec d)))
  filter_upwards [hess] with x hx
  have hleft : (‖a x / b x - 1‖ₑ : ℝ≥0∞) ≠ ∞ := by simp
  have hright : eLpNormEssSup (fun x => a x / b x - 1)
      (volumeMeasureOn (U : Set (Vec d))) ≠ ∞ := by
    rw [← eLpNorm_exponent_top]
    exact hfinite.ne
  have hreal := (ENNReal.toReal_le_toReal hleft hright).2 hx
  simpa [scalarRatioLInf, eLpNorm_exponent_top, Real.enorm_eq_ofReal_abs] using hreal


/-- The paper's symmetric scalar coefficient-ratio error. -/
noncomputable def scalarSensitivityError {d : ℕ} (U : Ch02.Domain d)
    (a b : Vec d → ℝ) : ℝ :=
  max (scalarRatioLInf U a b) (scalarRatioLInf U b a)

/-- Scalar ratio errors are nonnegative. -/
theorem scalarRatioLInf_nonneg {d : ℕ} (U : Ch02.Domain d)
    (a b : Vec d → ℝ) : 0 ≤ scalarRatioLInf U a b :=
  ENNReal.toReal_nonneg

/-- The symmetric scalar sensitivity error is nonnegative. -/
theorem scalarSensitivityError_nonneg {d : ℕ} (U : Ch02.Domain d)
    (a b : Vec d → ℝ) : 0 ≤ scalarSensitivityError U a b :=
  le_trans (scalarRatioLInf_nonneg U a b) (le_max_left _ _)

/-- Almost-everywhere two-sided coefficient comparison supplied by the paper's
ratio error. -/
theorem scalar_coeff_comparable_ae {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) :
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      (1 - scalarSensitivityError U a b) * b x ≤ a x ∧
      a x ≤ (1 + scalarSensitivityError U a b) * b x ∧
      (1 - scalarSensitivityError U a b) * a x ≤ b x ∧
      b x ≤ (1 + scalarSensitivityError U a b) * a x := by
  have hab := abs_scalar_ratio_sub_one_le_scalarRatioLInf_ae ha hb
  have hba := abs_scalar_ratio_sub_one_le_scalarRatioLInf_ae hb ha
  filter_upwards [ha.aeBounds, hb.aeBounds, hab, hba] with x hax hbx habx hbax
  have hapos : 0 < a x := lt_of_lt_of_le ha.lam_pos hax.1
  have hbpos : 0 < b x := lt_of_lt_of_le hb.lam_pos hbx.1
  have hab_eps : |a x / b x - 1| ≤ scalarSensitivityError U a b :=
    habx.trans (le_max_left _ _)
  have hba_eps : |b x / a x - 1| ≤ scalarSensitivityError U a b :=
    hbax.trans (le_max_right _ _)
  have hab_lo : 1 - scalarSensitivityError U a b ≤ a x / b x := by
    have := neg_abs_le (a x / b x - 1)
    linarith
  have hab_hi : a x / b x ≤ 1 + scalarSensitivityError U a b := by
    have := le_abs_self (a x / b x - 1)
    linarith
  have hba_lo : 1 - scalarSensitivityError U a b ≤ b x / a x := by
    have := neg_abs_le (b x / a x - 1)
    linarith
  have hba_hi : b x / a x ≤ 1 + scalarSensitivityError U a b := by
    have := le_abs_self (b x / a x - 1)
    linarith
  constructor
  · exact (le_div_iff₀ hbpos).mp hab_lo
  constructor
  · exact (div_le_iff₀ hbpos).mp hab_hi
  constructor
  · exact (le_div_iff₀ hapos).mp hba_lo
  · exact (div_le_iff₀ hapos).mp hba_hi


/-- Dirichlet energy comparison for scalar coefficients. -/
theorem symmetricDirichletEnergyValue_le_mul_scalarSensitivityError {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    (u : H1Function (U : Set (Vec d))) :
    Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn u ≤
      (1 + scalarSensitivityError U a b) *
        Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn u := by
  let c : ℝ := 1 + scalarSensitivityError U a b
  let fA : Vec d → ℝ := fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
    (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x))
  let fB : Vec d → ℝ := fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
    (matVecMul (hb.toCoeffOn.toCoeffField x) (u.grad x))
  have hIntA : Integrable fA (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_scalar_dirichlet_integrand ha u
  have hIntB : Integrable fB (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_scalar_dirichlet_integrand hb u
  have hcomp := scalar_coeff_comparable_ae ha hb
  have hpoint : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), fA x ≤ c * fB x := by
    filter_upwards [hcomp] with x hx
    have hnorm : 0 ≤ vecDot (u.grad x) (u.grad x) := by
      simpa [vecNormSq] using vecNormSq_nonneg (u.grad x)
    simp only [fA, fB, ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      matVecMul_scalarMatrix, vecDot_smul_right]
    dsimp only [c]
    calc
      1 / 2 * (a x * vecDot (u.grad x) (u.grad x)) =
          a x * (1 / 2 * vecDot (u.grad x) (u.grad x)) := by ring
      _ ≤ ((1 + scalarSensitivityError U a b) * b x) *
          (1 / 2 * vecDot (u.grad x) (u.grad x)) :=
        mul_le_mul_of_nonneg_right hx.2.1 (mul_nonneg (by norm_num) hnorm)
      _ = (1 + scalarSensitivityError U a b) *
          (1 / 2 * (b x * vecDot (u.grad x) (u.grad x))) := by ring
  have hint : (∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d))) ≤
      ∫ x, c * fB x ∂ volumeMeasureOn (U : Set (Vec d)) :=
    integral_mono_ae hIntA (hIntB.const_mul c) hpoint
  have hvol : 0 ≤ (volume (U : Set (Vec d))).toReal⁻¹ := by positivity
  unfold Ch02.symmetricDirichletEnergyValue Ch02.average
  change (volume (U : Set (Vec d))).toReal⁻¹ *
      (∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d))) ≤
    c * ((volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d)))
  calc
    (volume (U : Set (Vec d))).toReal⁻¹ *
          (∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d)))
        ≤ (volume (U : Set (Vec d))).toReal⁻¹ *
          (∫ x, c * fB x ∂ volumeMeasureOn (U : Set (Vec d))) :=
      mul_le_mul_of_nonneg_left hint hvol
    _ = c * ((volume (U : Set (Vec d))).toReal⁻¹ *
          ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d))) := by
      rw [integral_const_mul]
      ring


/-- The scalar ratio error controls the change of every fixed Dirichlet energy. -/
theorem abs_symmetricDirichletEnergyValue_sub_le {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b)
    (u : H1Function (U : Set (Vec d))) :
    |Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn u -
        Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn u| ≤
      scalarSensitivityError U a b *
        Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn u := by
  let ε := scalarSensitivityError U a b
  let fA : Vec d → ℝ := fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
    (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x))
  let fB : Vec d → ℝ := fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
    (matVecMul (hb.toCoeffOn.toCoeffField x) (u.grad x))
  have hIntA : Integrable fA (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_scalar_dirichlet_integrand ha u
  have hIntB : Integrable fB (volumeMeasureOn (U : Set (Vec d))) :=
    integrable_scalar_dirichlet_integrand hb u
  have hratio := abs_scalar_ratio_sub_one_le_scalarRatioLInf_ae ha hb
  have hpoint : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      |fA x - fB x| ≤ ε * fB x := by
    filter_upwards [ha.aeBounds, hb.aeBounds, hratio] with x hax hbx hx
    have hbpos : 0 < b x := lt_of_lt_of_le hb.lam_pos hbx.1
    have hnorm : 0 ≤ vecDot (u.grad x) (u.grad x) := by
      simpa [vecNormSq] using vecNormSq_nonneg (u.grad x)
    have hεratio : |a x / b x - 1| ≤ ε :=
      hx.trans (le_max_left _ _)
    have hab : a x - b x = (a x / b x - 1) * b x := by
      field_simp [hbpos.ne']
    simp only [fA, fB, ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      matVecMul_scalarMatrix, vecDot_smul_right]
    rw [show 1 / 2 * (a x * vecDot (u.grad x) (u.grad x)) -
        1 / 2 * (b x * vecDot (u.grad x) (u.grad x)) =
        1 / 2 * ((a x - b x) * vecDot (u.grad x) (u.grad x)) by ring]
    rw [hab, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_pos hbpos, abs_of_nonneg hnorm]
    have hfactor : 0 ≤ 1 / 2 * b x * vecDot (u.grad x) (u.grad x) := by
      positivity
    calc
      1 / 2 * (|a x / b x - 1| * b x * vecDot (u.grad x) (u.grad x)) =
          |a x / b x - 1| *
            (1 / 2 * b x * vecDot (u.grad x) (u.grad x)) := by ring
      _ ≤ ε * (1 / 2 * b x * vecDot (u.grad x) (u.grad x)) :=
        mul_le_mul_of_nonneg_right hεratio hfactor
      _ = ε * (1 / 2 * (b x * vecDot (u.grad x) (u.grad x))) := by ring
  have hdiffInt :
      |(∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d))) -
          ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d))| ≤
        ε * ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d)) := by
    calc
      |(∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d))) -
          ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d))| =
          |∫ x, fA x - fB x ∂ volumeMeasureOn (U : Set (Vec d))| := by
        rw [integral_sub hIntA hIntB]
      _ ≤ ∫ x, |fA x - fB x| ∂ volumeMeasureOn (U : Set (Vec d)) := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := volumeMeasureOn (U : Set (Vec d))) (fun x => fA x - fB x)
      _ ≤ ∫ x, ε * fB x ∂ volumeMeasureOn (U : Set (Vec d)) :=
        integral_mono_ae (hIntA.sub hIntB).abs (hIntB.const_mul ε) hpoint
      _ = ε * ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d)) :=
        integral_const_mul ε fB
  have hvol : 0 ≤ (volume (U : Set (Vec d))).toReal⁻¹ := by positivity
  unfold Ch02.symmetricDirichletEnergyValue Ch02.average
  change |(volume (U : Set (Vec d))).toReal⁻¹ *
      (∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d))) -
      (volume (U : Set (Vec d))).toReal⁻¹ *
      (∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d)))| ≤
    ε * ((volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d)))
  rw [← mul_sub, abs_mul, abs_of_nonneg hvol]
  calc
    (volume (U : Set (Vec d))).toReal⁻¹ *
        |(∫ x, fA x ∂ volumeMeasureOn (U : Set (Vec d))) -
          ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d))| ≤
      (volume (U : Set (Vec d))).toReal⁻¹ *
        (ε * ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d))) :=
      mul_le_mul_of_nonneg_left hdiffInt hvol
    _ = ε * ((volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x, fB x ∂ volumeMeasureOn (U : Set (Vec d))) := by ring


/-- The paper's scalar ratio error controls the Dirichlet variational value. -/
theorem abs_symmetricDirichletNu_sub_le {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) (p : Vec d) :
    |Ch02.symmetricDirichletNu U ha.toCoeffOn p -
        Ch02.symmetricDirichletNu U hb.toCoeffOn p| ≤
      scalarSensitivityError U a b *
        Ch02.symmetricDirichletNu U hb.toCoeffOn p := by
  let ε := scalarSensitivityError U a b
  let DA := Ch02.symmetricDirichletNu U ha.toCoeffOn p
  let DB := Ch02.symmetricDirichletNu U hb.toCoeffOn p
  have hTheoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTheoryB := Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  obtain ⟨uA, huA⟩ := hTheoryA.dirichlet_minimizer_exists p
  obtain ⟨uB, huB⟩ := hTheoryB.dirichlet_minimizer_exists p
  have hDA : DA = Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn uA :=
    Homogenization.Internal.Ch02.BookCh02.symmetricDirichletNu_eq_of_minimizer huA
  have hDB : DB = Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn uB :=
    Homogenization.Internal.Ch02.BookCh02.symmetricDirichletNu_eq_of_minimizer huB
  have hε : 0 ≤ ε := scalarSensitivityError_nonneg U a b
  by_cases hle : DA ≤ DB
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hminB := huB.2 uA huA.1
    have hfixed := abs_symmetricDirichletEnergyValue_sub_le hb ha uA
    have hεsymm : scalarSensitivityError U b a = ε := by
      simp only [ε, scalarSensitivityError, max_comm]
    calc
      -(DA - DB) = DB - DA := by ring
      _ ≤ Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn uA -
          Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn uA := by
        rw [hDA, hDB]
        linarith
      _ ≤ |Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn uA -
          Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn uA| := le_abs_self _
      _ ≤ scalarSensitivityError U b a *
          Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn uA := hfixed
      _ = ε * DA := by rw [hεsymm, hDA]
      _ ≤ ε * DB := mul_le_mul_of_nonneg_left hle hε
  · have hle' : DB ≤ DA := le_of_not_ge hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle')]
    have hminA := huA.2 uB huB.1
    have hfixed := abs_symmetricDirichletEnergyValue_sub_le ha hb uB
    calc
      DA - DB ≤ Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn uB -
          Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn uB := by
        rw [hDA, hDB]
        linarith
      _ ≤ |Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn uB -
          Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn uB| := le_abs_self _
      _ ≤ ε * Ch02.symmetricDirichletEnergyValue U hb.toCoeffOn uB := hfixed
      _ = ε * DB := by rw [hDB]


/-- Quadratic-form version of the primal coarse-matrix sensitivity estimate. -/
theorem abs_vecDot_sigmaCoarse_sub_le {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) (p : Vec d) :
    |vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) -
        vecDot p (matVecMul (Ch02.sigmaCoarse U hb.toCoeffOn) p)| ≤
      scalarSensitivityError U a b *
        vecDot p (matVecMul (Ch02.sigmaCoarse U hb.toCoeffOn) p) := by
  have h := abs_symmetricDirichletNu_sub_le ha hb p
  have hTheoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTheoryB := Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  rw [hTheoryA.dirichlet_value_by_sigma, hTheoryB.dirichlet_value_by_sigma] at h
  have htwo := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  calc
    |vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) -
        vecDot p (matVecMul (Ch02.sigmaCoarse U hb.toCoeffOn) p)| =
      2 * |1 / 2 * vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) -
        1 / 2 * vecDot p (matVecMul (Ch02.sigmaCoarse U hb.toCoeffOn) p)| := by
          rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), ← abs_mul]
          congr 1
          ring
    _ ≤ 2 * (scalarSensitivityError U a b *
        (1 / 2 * vecDot p (matVecMul (Ch02.sigmaCoarse U hb.toCoeffOn) p))) := htwo
    _ = scalarSensitivityError U a b *
        vecDot p (matVecMul (Ch02.sigmaCoarse U hb.toCoeffOn) p) := by ring

/-- Primal coarse-matrix sensitivity in the paper's `a(U)` vocabulary, stated
in its square-root-free quadratic-form characterization. -/
theorem abs_vecDot_aMatrix_sub_le {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) (p : Vec d) :
    |vecDot p (matVecMul (aMatrix U ha.toCoeffOn) p) -
        vecDot p (matVecMul (aMatrix U hb.toCoeffOn) p)| ≤
      scalarSensitivityError U a b *
        vecDot p (matVecMul (aMatrix U hb.toCoeffOn) p) := by
  have hTheoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTheoryB := Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  change |vecDot p (matVecMul (Ch02.aCoarse U ha.toCoeffOn) p) -
      vecDot p (matVecMul (Ch02.aCoarse U hb.toCoeffOn) p)| ≤
    scalarSensitivityError U a b *
      vecDot p (matVecMul (Ch02.aCoarse U hb.toCoeffOn) p)
  rw [hTheoryA.derived_matrices.1, hTheoryB.derived_matrices.1]
  exact abs_vecDot_sigmaCoarse_sub_le ha hb p


-- D-013 proof-route provenance: the dual competitor/minimizer decomposition mirrors
-- Algsuperdiff/Section24/Sensitivity/Provider/Path/MuExpansion.lean; the final
-- congruence step uses CoarseGraining's positive-matrix CFC square-root API.


private theorem matrixOperatorNorm_le_of_abs_quadratic_le {d : ℕ}
    {A : Mat d} {r : ℝ} (hr : 0 ≤ r) (hA : A.IsSymm)
    (hquad : ∀ x : Vec d,
      |vecDot x (matVecMul A x)| ≤ r * vecNormSq x) :
    Ch02.matrixOperatorNorm A ≤ r := by
  have hHerm : A.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
  have hAlgHerm (s : ℝ) : Matrix.IsHermitian (algebraMap ℝ (Mat d) s) := by
    have hs : (s • (1 : Mat d)).IsSymm := Matrix.isSymm_one.smul s
    rw [Algebra.algebraMap_eq_smul_one]
    simpa only [Matrix.IsHermitian] using hs
  have hUpper : A ≤ algebraMap ℝ (Mat d) r := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact (hAlgHerm r).sub hHerm
    · intro x
      have hx := hquad x
      have hxle := (abs_le.mp hx).2
      have halg : vecDot x (matVecMul (algebraMap ℝ (Mat d) r) x) =
          r * vecNormSq x := by
        have hm : matVecMul (algebraMap ℝ (Mat d) r) x = r • x := by
          funext i
          simp [Algebra.algebraMap_eq_smul_one, matVecMul, Matrix.one_apply]
        rw [hm, vecDot_smul_right]
        rfl
      change 0 ≤ vecDot x (matVecMul (algebraMap ℝ (Mat d) r - A) x)
      rw [show matVecMul (algebraMap ℝ (Mat d) r - A) x =
          matVecMul (algebraMap ℝ (Mat d) r) x - matVecMul A x by
        exact Matrix.sub_mulVec _ _ _]
      rw [show vecDot x
          (matVecMul (algebraMap ℝ (Mat d) r) x - matVecMul A x) =
          vecDot x (matVecMul (algebraMap ℝ (Mat d) r) x) -
            vecDot x (matVecMul A x) by
        simp [vecDot, mul_sub, Finset.sum_sub_distrib]]
      rw [halg]
      apply sub_nonneg.mpr
      linarith
  have hLower : algebraMap ℝ (Mat d) (-r) ≤ A := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact hHerm.sub (hAlgHerm (-r))
    · intro x
      have hx := hquad x
      have hxle := (abs_le.mp hx).1
      have halg : vecDot x (matVecMul (algebraMap ℝ (Mat d) (-r)) x) =
          -r * vecNormSq x := by
        have hm : matVecMul (algebraMap ℝ (Mat d) (-r)) x = (-r) • x := by
          funext i
          simp [Algebra.algebraMap_eq_smul_one, matVecMul, Matrix.one_apply]
        rw [hm, vecDot_smul_right]
        simp [vecNormSq]
      change 0 ≤ vecDot x (matVecMul (A - algebraMap ℝ (Mat d) (-r)) x)
      rw [show matVecMul (A - algebraMap ℝ (Mat d) (-r)) x =
          matVecMul A x - matVecMul (algebraMap ℝ (Mat d) (-r)) x by
        exact Matrix.sub_mulVec _ _ _]
      rw [show vecDot x
          (matVecMul A x - matVecMul (algebraMap ℝ (Mat d) (-r)) x) =
          vecDot x (matVecMul A x) -
            vecDot x (matVecMul (algebraMap ℝ (Mat d) (-r)) x) by
        simp [vecDot, mul_sub, Finset.sum_sub_distrib]]
      rw [halg]
      apply sub_nonneg.mpr
      linarith
  have hP : (algebraMap ℝ (Mat d) r - A).PosSemidef :=
    (Matrix.le_iff.mp hUpper)
  have hQ : (A - algebraMap ℝ (Mat d) (-r)).PosSemidef :=
    (Matrix.le_iff.mp hLower)
  have hQ' : (A + algebraMap ℝ (Mat d) r).PosSemidef := by
    simpa [map_neg] using hQ
  have hcA : Commute (algebraMap ℝ (Mat d) r) A :=
    Algebra.commutes r A
  have hcomm : Commute (algebraMap ℝ (Mat d) r - A)
      (A + algebraMap ℝ (Mat d) r) :=
    (hcA.add_right (Commute.refl _)).sub_left
      ((Commute.refl A).add_right hcA.symm)
  have hprod : ((algebraMap ℝ (Mat d) r - A) *
      (A + algebraMap ℝ (Mat d) r)).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact (Commute.mul_nonneg hP.nonneg hQ'.nonneg hcomm)
  have hsquare : (algebraMap ℝ (Mat d) (r ^ 2) - A * A).PosSemidef := by
    have heq : algebraMap ℝ (Mat d) (r ^ 2) - A * A =
        (algebraMap ℝ (Mat d) r - A) *
          (A + algebraMap ℝ (Mat d) r) := by
      rw [map_pow, pow_two]
      noncomm_ring [hcA.eq]
    rw [heq]
    exact hprod
  rw [Ch02.matrixOperatorNorm_eq_l2_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ hr ?_
  intro x
  let ξ : Vec d := x.ofLp
  have hsquare' := hsquare.dotProduct_mulVec_nonneg ξ
  have hnormsq : vecNormSq (matVecMul A ξ) ≤ r ^ 2 * vecNormSq ξ := by
    have hAA : vecDot ξ (matVecMul (A * A) ξ) =
        vecNormSq (matVecMul A ξ) := by
      rw [← matVecMul_mul, vecDot_matVecMul_comm_of_isSymm hA]
      rfl
    have halg : vecDot ξ (matVecMul (algebraMap ℝ (Mat d) (r ^ 2)) ξ) =
        r ^ 2 * vecNormSq ξ := by
      have hm : matVecMul (algebraMap ℝ (Mat d) (r ^ 2)) ξ = (r ^ 2) • ξ := by
        funext i
        simp [Algebra.algebraMap_eq_smul_one, matVecMul, Matrix.one_apply]
      rw [hm, vecDot_smul_right]
      rfl
    have hsquare'' : 0 ≤ vecDot ξ
        (matVecMul (algebraMap ℝ (Mat d) (r ^ 2) - A * A) ξ) := by
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hsquare'
    rw [show matVecMul (algebraMap ℝ (Mat d) (r ^ 2) - A * A) ξ =
        matVecMul (algebraMap ℝ (Mat d) (r ^ 2)) ξ -
          matVecMul (A * A) ξ by exact Matrix.sub_mulVec _ _ _] at hsquare''
    rw [show vecDot ξ
          (matVecMul (algebraMap ℝ (Mat d) (r ^ 2)) ξ - matVecMul (A * A) ξ) =
        vecDot ξ (matVecMul (algebraMap ℝ (Mat d) (r ^ 2)) ξ) -
          vecDot ξ (matVecMul (A * A) ξ) by
      simp [vecDot, mul_sub, Finset.sum_sub_distrib]] at hsquare''
    rw [halg, hAA] at hsquare''
    exact sub_nonneg.mp hsquare''
  have hsq : Ch02.vecNorm (matVecMul A ξ) ^ 2 ≤
      (r * Ch02.vecNorm ξ) ^ 2 := by
    simpa [Ch02.vecNorm_sq_eq_vecNormSq, mul_pow] using hnormsq
  have hnorm : Ch02.vecNorm (matVecMul A ξ) ≤ r * Ch02.vecNorm ξ :=
    (sq_le_sq₀ (Ch02.vecNorm_nonneg _)
      (mul_nonneg hr (Ch02.vecNorm_nonneg _))).mp hsq
  simpa [ξ, Matrix.toEuclideanCLM_toLp, matVecMul, Matrix.mulVec,
    Ch02.vecNorm] using hnorm

private theorem normalizedMatrixDeviation_le_of_abs_quadratic_le {d : ℕ}
    {B A : Mat d} {r : ℝ} (hr : 0 ≤ r) (hB : B.PosDef) (hA : A.PosDef)
    (hquad : ∀ x : Vec d,
      |vecDot x (matVecMul A x) - vecDot x (matVecMul B x)| ≤
        r * vecDot x (matVecMul B x)) :
    Ch02.matrixOperatorNorm
        (matrixInvSqrt B * A * matrixInvSqrt B - (1 : Mat d)) ≤ r := by
  let R : Mat d := CFC.sqrt B
  let S : Mat d := R⁻¹
  have hBnonneg : (0 : Mat d) ≤ B := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact hB.posSemidef
  have hRnonneg : (0 : Mat d) ≤ R := by
    exact CFC.sqrt_nonneg B
  have hRpsd : R.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact hRnonneg
  have hRunit : IsUnit R := by
    exact (CFC.isUnit_sqrt_iff B hBnonneg).2 hB.isUnit
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  have hRinvLeft : S * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hRinvRight : R * S = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRsymm : R.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hRpsd.isHermitian
  have hSsymm : S.IsSymm := isSymm_nonsingInv hRsymm
  have hBsq : R * R = B := by
    simpa [R, pow_two] using CFC.sq_sqrt B hBnonneg
  have hSBS : S * B * S = 1 := by
    rw [← hBsq]
    calc
      S * (R * R) * S = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hRinvLeft, hRinvRight, one_mul]
  have hAsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.posSemidef.isHermitian
  have hDsymm : (S * A * S - (1 : Mat d)).IsSymm := by
    rw [Matrix.IsSymm]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hSsymm, hAsymm]
    simp [Matrix.mul_assoc]
  have hqcongA (x : Vec d) :
      vecDot x (matVecMul (S * A * S) x) =
        vecDot (matVecMul S x) (matVecMul A (matVecMul S x)) := by
    rw [← matVecMul_mul, ← matVecMul_mul]
    rw [vecDot_matVecMul_comm_of_isSymm hSsymm]
    exact vecDot_comm _ _
  have hqcongB (x : Vec d) :
      vecDot (matVecMul S x) (matVecMul B (matVecMul S x)) = vecNormSq x := by
    calc
      vecDot (matVecMul S x) (matVecMul B (matVecMul S x)) =
          vecDot x (matVecMul (S * B * S) x) := by
        rw [← matVecMul_mul, ← matVecMul_mul]
        rw [vecDot_matVecMul_comm_of_isSymm hSsymm]
        exact (vecDot_comm _ _).symm
      _ = vecNormSq x := by
        rw [hSBS]
        simp [vecNormSq, vecDot, matVecMul, Matrix.one_apply]
  have hDquad (x : Vec d) :
      |vecDot x (matVecMul (S * A * S - (1 : Mat d)) x)| ≤
        r * vecNormSq x := by
    have h := hquad (matVecMul S x)
    rw [hqcongB] at h
    rw [sub_matVecMul]
    rw [show vecDot x
          (matVecMul (S * A * S) x - matVecMul (1 : Mat d) x) =
        vecDot x (matVecMul (S * A * S) x) -
          vecDot x (matVecMul (1 : Mat d) x) by
      simp [vecDot, mul_sub, Finset.sum_sub_distrib]]
    rw [hqcongA]
    simpa [vecNormSq, vecDot, matVecMul, Matrix.one_apply] using h
  change Ch02.matrixOperatorNorm (S * A * S - (1 : Mat d)) ≤ r
  exact matrixOperatorNorm_le_of_abs_quadratic_le hr hDsymm hDquad
private theorem symmetricNeumannEnergyValue_eq_linear_sub_dirichlet {d : ℕ}
    {U : Ch02.Domain d} {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (q : Vec d) (u : H1Function (U : Set (Vec d))) :
    Ch02.symmetricNeumannEnergyValue U ha.toCoeffOn q u =
      Ch02.average U (fun x => vecDot q (u.grad x)) -
        Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn u := by
  have hlin : MeasureTheory.IntegrableOn (fun x => vecDot q (u.grad x))
      (U : Set (Vec d)) :=
    Homogenization.Internal.Ch02.BookCh02.integrableOn_vecDot_const_h1Grad q u
  have hdir := integrable_scalar_dirichlet_integrand ha u
  unfold Ch02.symmetricNeumannEnergyValue Ch02.symmetricDirichletEnergyValue
    Ch02.average
  exact Homogenization.volumeAverage_sub hlin hdir

private theorem average_vecDot_const_grad_smul {d : ℕ} {U : Ch02.Domain d}
    (q : Vec d) (c : ℝ) (u : H1Function (U : Set (Vec d))) :
    Ch02.average U (fun x => vecDot q ((c • u).grad x)) =
      c * Ch02.average U (fun x => vecDot q (u.grad x)) := by
  have hlin : MeasureTheory.IntegrableOn (fun x => vecDot q (u.grad x))
      (U : Set (Vec d)) :=
    Homogenization.Internal.Ch02.BookCh02.integrableOn_vecDot_const_h1Grad q u
  rw [H1Function.smul_grad]
  have hfun : (fun x => vecDot q ((fun x => c • u.grad x) x)) =
      c • (fun x => vecDot q (u.grad x)) := by
    funext x
    simp [vecDot_smul_right]
  rw [hfun]
  change Homogenization.volumeAverage (U : Set (Vec d))
      (c • (fun x => vecDot q (u.grad x))) =
    c * Homogenization.volumeAverage (U : Set (Vec d))
      (fun x => vecDot q (u.grad x))
  rw [Homogenization.volumeAverage_smul]

private theorem symmetricDirichletEnergyValue_smul {d : ℕ}
    {U : Ch02.Domain d} {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (c : ℝ) (u : H1Function (U : Set (Vec d))) :
    Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn (c • u) =
      c ^ 2 * Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn u := by
  unfold Ch02.symmetricDirichletEnergyValue
  rw [H1Function.smul_grad]
  have hfun :
      (fun x => (1 / 2 : ℝ) * vecDot ((fun x => c • u.grad x) x)
        (matVecMul (ha.toCoeffOn.toCoeffField x) ((fun x => c • u.grad x) x))) =
      c ^ 2 • (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
        (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x))) := by
    funext x
    rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    simp [pow_two]
    ring
  rw [hfun]
  change Homogenization.volumeAverage (U : Set (Vec d))
      (c ^ 2 • (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
        (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x)))) =
    c ^ 2 * Homogenization.volumeAverage (U : Set (Vec d))
      (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
        (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x)))
  rw [Homogenization.volumeAverage_smul]

private theorem symmetricNeumannNu_le_one_add_error_mul {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b) (q : Vec d) :
    Ch02.symmetricNeumannNu U hb.toCoeffOn q ≤
      (1 + scalarSensitivityError U a b) *
        Ch02.symmetricNeumannNu U ha.toCoeffOn q := by
  let ε := scalarSensitivityError U a b
  let c := 1 + ε
  have hε : 0 ≤ ε := scalarSensitivityError_nonneg U a b
  have hc : 0 < c := by dsimp [c]; linarith
  have hTheoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTheoryB := Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  obtain ⟨uA, _huAmean, huA⟩ := hTheoryA.neumann_meanZero_maximizer_exists q
  obtain ⟨uB, _huBmean, huB⟩ := hTheoryB.neumann_meanZero_maximizer_exists q
  have hNA := Homogenization.Internal.Ch02.BookCh02.symmetricNeumannNu_eq_of_maximizer huA
  have hNB := Homogenization.Internal.Ch02.BookCh02.symmetricNeumannNu_eq_of_maximizer huB
  have hfixed := symmetricDirichletEnergyValue_le_mul_scalarSensitivityError ha hb uB
  have hcomp := huA (c⁻¹ • uB)
  rw [symmetricNeumannEnergyValue_eq_linear_sub_dirichlet ha,
    symmetricNeumannEnergyValue_eq_linear_sub_dirichlet ha] at hcomp
  rw [average_vecDot_const_grad_smul,
    symmetricDirichletEnergyValue_smul] at hcomp
  rw [hNA, hNB]
  rw [symmetricNeumannEnergyValue_eq_linear_sub_dirichlet ha,
    symmetricNeumannEnergyValue_eq_linear_sub_dirichlet hb]
  dsimp only [c, ε] at hc ⊢
  have hcne : 1 + scalarSensitivityError U a b ≠ 0 := by linarith
  have hcomp' := mul_le_mul_of_nonneg_left hcomp hc.le
  have hinv : (1 + scalarSensitivityError U a b)⁻¹ *
      (1 + scalarSensitivityError U a b) = 1 := inv_mul_cancel₀ hcne
  have hinv2 : ((1 + scalarSensitivityError U a b)⁻¹) ^ 2 *
      (1 + scalarSensitivityError U a b) =
        (1 + scalarSensitivityError U a b)⁻¹ := by
    field_simp [hcne]
  dsimp only [c, ε] at hcomp'
  field_simp [hcne] at hcomp'
  nlinarith


private theorem matLoewnerLE_sigmaStarInv_one_add_error {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b) :
    MatLoewnerLE (Ch02.sigmaStarInvCoarse U hb.toCoeffOn)
      ((1 + scalarSensitivityError U a b) •
        Ch02.sigmaStarInvCoarse U ha.toCoeffOn) := by
  intro q
  have h := symmetricNeumannNu_le_one_add_error_mul ha hb q
  have hTheoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTheoryB := Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  rw [hTheoryA.neumann_value_by_sigmaStarInv,
    hTheoryB.neumann_value_by_sigmaStarInv] at h
  simp only [smul_matVecMul, vecDot_smul_right]
  nlinarith

private theorem abs_vecDot_aStarMatrix_sub_le {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) (p : Vec d) :
    |vecDot p (matVecMul (aStarMatrix U ha.toCoeffOn) p) -
        vecDot p (matVecMul (aStarMatrix U hb.toCoeffOn) p)| ≤
      scalarSensitivityError U a b *
        vecDot p (matVecMul (aStarMatrix U hb.toCoeffOn) p) := by
  let ε := scalarSensitivityError U a b
  let c := 1 + ε
  let IA := Ch02.sigmaStarInvCoarse U ha.toCoeffOn
  let IB := Ch02.sigmaStarInvCoarse U hb.toCoeffOn
  have hε : 0 ≤ ε := scalarSensitivityError_nonneg U a b
  have hc : 0 < c := by dsimp [c]; linarith
  have hIA : IA.PosDef := Ch02.sigmaStarInvCoarse_posDef U ha.toCoeffOn
  have hIB : IB.PosDef := Ch02.sigmaStarInvCoarse_posDef U hb.toCoeffOn
  have hBA : MatLoewnerLE IB (c • IA) :=
    matLoewnerLE_sigmaStarInv_one_add_error ha hb
  have hAB : MatLoewnerLE IA (c • IB) := by
    have h := matLoewnerLE_sigmaStarInv_one_add_error hb ha
    simpa [IA, IB, c, ε, scalarSensitivityError, max_comm] using h
  have hInvBA : MatLoewnerLE (c • IA)⁻¹ IB⁻¹ :=
    matLoewnerLE_inv_of_posDef hIB (hIA.smul hc) hBA
  have hInvAB : MatLoewnerLE (c • IB)⁻¹ IA⁻¹ :=
    matLoewnerLE_inv_of_posDef hIA (hIB.smul hc) hAB
  letI : Invertible c := invertibleOfNonzero hc.ne'
  have hscaleIA : (c • IA)⁻¹ = c⁻¹ • IA⁻¹ := by
    simpa [invOf_eq_inv] using Matrix.inv_smul IA c
      ((Matrix.isUnit_iff_isUnit_det IA).mp hIA.isUnit)
  have hscaleIB : (c • IB)⁻¹ = c⁻¹ • IB⁻¹ := by
    simpa [invOf_eq_inv] using Matrix.inv_smul IB c
      ((Matrix.isUnit_iff_isUnit_det IB).mp hIB.isUnit)
  have hlowerInv : c⁻¹ * vecDot p (matVecMul IB⁻¹ p) ≤
      vecDot p (matVecMul IA⁻¹ p) := by
    have := hInvAB p
    rw [hscaleIB] at this
    simpa [smul_matVecMul, vecDot_smul_right] using this
  have hupperInv : vecDot p (matVecMul IA⁻¹ p) ≤
      c * vecDot p (matVecMul IB⁻¹ p) := by
    have h := hInvBA p
    rw [hscaleIA] at h
    have hscalar : c⁻¹ * vecDot p (matVecMul IA⁻¹ p) ≤
        vecDot p (matVecMul IB⁻¹ p) := by
      simpa [smul_matVecMul, vecDot_smul_right] using h
    have hmul := mul_le_mul_of_nonneg_left hscalar hc.le
    have hcne : c ≠ 0 := hc.ne'
    field_simp [hcne] at hmul
    exact hmul
  have hIBnn : 0 ≤ vecDot p (matVecMul IB⁻¹ p) := by
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hIB.inv.posSemidef.dotProduct_mulVec_nonneg p
  have hlower : (1 - ε) * vecDot p (matVecMul IB⁻¹ p) ≤
      vecDot p (matVecMul IA⁻¹ p) := by
    have hnum : 1 - ε ≤ c⁻¹ := by
      dsimp [c]
      have hden : 0 < 1 + ε := by linarith
      rw [inv_eq_one_div, le_div_iff₀ hden]
      nlinarith [sq_nonneg ε]
    exact (mul_le_mul_of_nonneg_right hnum hIBnn).trans hlowerInv
  have hTheoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hTheoryB := Ch02.responseSymmetricDirichletNeumannTheory U hb.toCoeffOn hb.isSymmetric
  change |vecDot p (matVecMul (Ch02.aStarCoarse U ha.toCoeffOn) p) -
      vecDot p (matVecMul (Ch02.aStarCoarse U hb.toCoeffOn) p)| ≤
    scalarSensitivityError U a b *
      vecDot p (matVecMul (Ch02.aStarCoarse U hb.toCoeffOn) p)
  rw [hTheoryA.derived_matrices.2.1, hTheoryB.derived_matrices.2.1]
  unfold Ch02.sigmaStarCoarse
  change |vecDot p (matVecMul IA⁻¹ p) - vecDot p (matVecMul IB⁻¹ p)| ≤
    ε * vecDot p (matVecMul IB⁻¹ p)
  rw [abs_le]
  constructor <;> dsimp [c] at hupperInv hlower ⊢ <;> linarith


private theorem aMatrix_posDef {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) :
    (aMatrix U ha.toCoeffOn).PosDef := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hsigma : (Ch02.sigmaCoarse U ha.toCoeffOn).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simpa [Matrix.IsHermitian, Matrix.IsSymm] using
        Ch02.sigmaCoarse_isSymm U ha.toCoeffOn
    · intro p hp
      have hstar := (Ch02.sigmaStarCoarse_posDef U ha.toCoeffOn).dotProduct_mulVec_pos hp
      have hle := hTheory.dirichlet_neumann_bracketing.2.1 p
      have hstar' : 0 < (1 / 2 : ℝ) *
          vecDot p (matVecMul (Ch02.sigmaStarCoarse U ha.toCoeffOn) p) := by
        have : 0 < vecDot p
            (matVecMul (Ch02.sigmaStarCoarse U ha.toCoeffOn) p) := by
          simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstar
        nlinarith
      have := hstar'.trans_le hle
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using (show
        0 < vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) by
          nlinarith)
  change (Ch02.aCoarse U ha.toCoeffOn).PosDef
  rw [hTheory.derived_matrices.1]
  exact hsigma

private theorem aStarMatrix_posDef {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) :
    (aStarMatrix U ha.toCoeffOn).PosDef := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  change (Ch02.aStarCoarse U ha.toCoeffOn).PosDef
  rw [hTheory.derived_matrices.2.1]
  exact Ch02.sigmaStarCoarse_posDef U ha.toCoeffOn

/-- Source-exact scalar sensitivity of both normalized coarse matrices. -/
theorem normalized_aStarMatrix_and_aMatrix_deviation_le {d : ℕ}
    {U : Ch02.Domain d} {a b : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) (hb : ScalarCoeffOnData U b) :
    Ch02.matrixOperatorNorm
        (matrixInvSqrt (aStarMatrix U hb.toCoeffOn) *
          aStarMatrix U ha.toCoeffOn *
          matrixInvSqrt (aStarMatrix U hb.toCoeffOn) - (1 : Mat d)) ≤
      scalarSensitivityError U a b ∧
    Ch02.matrixOperatorNorm
        (matrixInvSqrt (aMatrix U hb.toCoeffOn) *
          aMatrix U ha.toCoeffOn *
          matrixInvSqrt (aMatrix U hb.toCoeffOn) - (1 : Mat d)) ≤
      scalarSensitivityError U a b := by
  constructor
  · exact normalizedMatrixDeviation_le_of_abs_quadratic_le
      (scalarSensitivityError_nonneg U a b) (aStarMatrix_posDef hb)
      (aStarMatrix_posDef ha) (abs_vecDot_aStarMatrix_sub_le ha hb)
  · exact normalizedMatrixDeviation_le_of_abs_quadratic_le
      (scalarSensitivityError_nonneg U a b) (aMatrix_posDef hb)
      (aMatrix_posDef ha) (abs_vecDot_aMatrix_sub_le ha hb)


/-- Scalar reciprocal-error inequality used in the paper's `J` sensitivity proof. -/
theorem mul_inv_sub_one_sq_le (x : ℝ) (hx : 0 < x) :
    x * (x⁻¹ - 1) ^ 2 ≤ 2 * (x - 1) ^ 2 + 2 * (x⁻¹ - 1) ^ 2 := by
  have hxne : x ≠ 0 := hx.ne'
  field_simp [hxne]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 1 / 2)]

-- D-013 proof-route provenance: the following doubled-energy comparison mirrors
-- Algsuperdiff/Section24/Sensitivity/Provider/Path/PointwiseExpansion.lean,
-- Path/Densities.lean, Path/MuExpansion.lean, and Path/Bounds.lean.  The common
-- admissible minimizer is compared pointwise, then the response-gradient term
-- is absorbed by Young's inequality before exact coefficient homogeneity.

private theorem mul_vecDot_le_young {d : ℕ} (r δ : ℝ)
    (hδ : 0 < δ) (x y : Vec d) :
    r * vecDot x y ≤
      δ / 2 * vecNormSq x + r ^ 2 / (2 * δ) * vecNormSq y := by
  have hi (i : Fin d) :
      r * (x i * y i) ≤ δ / 2 * (x i * x i) +
        r ^ 2 / (2 * δ) * (y i * y i) := by
    have hδ2 : 0 < 2 * δ := by positivity
    have heq : δ / 2 * (x i * x i) +
        r ^ 2 / (2 * δ) * (y i * y i) =
        (δ ^ 2 * (x i * x i) + r ^ 2 * (y i * y i)) / (2 * δ) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ hδ2).2
    nlinarith [sq_nonneg (δ * x i - r * y i)]
  rw [vecDot, vecNormSq, vecNormSq]
  calc
    r * ∑ i, x i * y i = ∑ i, r * (x i * y i) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, (δ / 2 * (x i * x i) +
        r ^ 2 / (2 * δ) * (y i * y i)) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = δ / 2 * ∑ i, x i * x i +
        r ^ 2 / (2 * δ) * ∑ i, y i * y i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem scalar_block_energy_change_le {d : ℕ}
    (alpha beta δ : ℝ) (hα : 0 < alpha) (hβ : 0 < beta)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (X : BlockVec d) :
    (1 / 2 : ℝ) *
          (beta * vecNormSq X.1 + beta⁻¹ * vecNormSq X.2) -
        (1 / 2 : ℝ) *
          (alpha * vecNormSq X.1 + alpha⁻¹ * vecNormSq X.2) ≤
      δ * ((1 / 2 : ℝ) * alpha *
        vecNormSq (X.1 + alpha⁻¹ • X.2)) +
      3 / δ *
        ((beta / alpha - 1) ^ 2 + (alpha / beta - 1) ^ 2) *
        ((1 / 2 : ℝ) *
          (alpha * vecNormSq X.1 + alpha⁻¹ * vecNormSq X.2)) := by
  let r := beta / alpha - 1
  let s := alpha / beta - 1
  let z : Vec d := alpha⁻¹ • X.2
  have hαne : alpha ≠ 0 := hα.ne'
  have hβne : beta ≠ 0 := hβ.ne'
  have hzinv : vecNormSq X.2 = alpha ^ 2 * vecNormSq z := by
    simp [z, vecNormSq_smul, hαne]
  have hs : s = -r + (alpha / beta) * r ^ 2 := by
    dsimp [r, s]
    field_simp
    ring
  have hdiff :
      (1 / 2 : ℝ) *
            (beta * vecNormSq X.1 + beta⁻¹ * vecNormSq X.2) -
          (1 / 2 : ℝ) *
            (alpha * vecNormSq X.1 + alpha⁻¹ * vecNormSq X.2) =
        (1 / 2 : ℝ) * alpha *
          (r * (vecNormSq X.1 - vecNormSq z) +
            (alpha / beta) * r ^ 2 * vecNormSq z) := by
    rw [hzinv]
    dsimp [r, z]
    field_simp
    ring
  have hnormdiff : vecNormSq X.1 - vecNormSq z =
      vecDot (X.1 + z) (X.1 - z) := by
    change (∑ i : Fin d, X.1 i * X.1 i) -
        (∑ i : Fin d, z i * z i) = _
    calc
      (∑ i : Fin d, X.1 i * X.1 i) - (∑ i : Fin d, z i * z i) =
          ∑ i : Fin d, (X.1 i * X.1 i - z i * z i) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin d, (X.1 i + z i) * (X.1 i - z i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      _ = vecDot (X.1 + z) (X.1 - z) := by
        rfl
  have hyoung := mul_vecDot_le_young r δ hδ (X.1 + z) (X.1 - z)
  have hminus := vecNormSq_sub_le X.1 z
  have hcross :
      (1 / 2 : ℝ) * alpha * r *
          (vecNormSq X.1 - vecNormSq z) ≤
        δ * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          1 / δ * r ^ 2 *
            ((1 / 2 : ℝ) * alpha *
              (vecNormSq X.1 + vecNormSq z)) := by
    rw [hnormdiff]
    have hhalfalpha : 0 ≤ (1 / 2 : ℝ) * alpha := by positivity
    have hm := mul_le_mul_of_nonneg_left hyoung hhalfalpha
    have hcoef : 0 ≤ r ^ 2 / (2 * δ) * ((1 / 2 : ℝ) * alpha) := by
      exact mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) hhalfalpha
    have hm2 := mul_le_mul_of_nonneg_left hminus hcoef
    have hP : 0 ≤ (1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z) :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) (vecNormSq_nonneg _)
    have hE : 0 ≤ (1 / 2 : ℝ) * alpha *
        (vecNormSq X.1 + vecNormSq z) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hα.le)
        (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))
    calc
      (1 / 2 : ℝ) * alpha * r * vecDot (X.1 + z) (X.1 - z) =
          ((1 / 2 : ℝ) * alpha) * (r * vecDot (X.1 + z) (X.1 - z)) := by ring
      _ ≤ ((1 / 2 : ℝ) * alpha) *
          (δ / 2 * vecNormSq (X.1 + z) +
            r ^ 2 / (2 * δ) * vecNormSq (X.1 - z)) := hm
      _ = δ / 2 * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          (r ^ 2 / (2 * δ) * ((1 / 2 : ℝ) * alpha)) *
            vecNormSq (X.1 - z) := by ring
      _ ≤ δ / 2 * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          (r ^ 2 / (2 * δ) * ((1 / 2 : ℝ) * alpha)) *
            (2 * (vecNormSq X.1 + vecNormSq z)) :=
        by
          simpa [add_comm] using
            add_le_add_right hm2
              (δ / 2 * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)))
      _ = δ / 2 * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          1 / δ * r ^ 2 *
            ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)) := by ring
      _ ≤ δ * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          1 / δ * r ^ 2 *
            ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)) := by
        simpa [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_right (by linarith : δ / 2 ≤ δ) hP)
          (1 / δ * r ^ 2 *
            ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)))
  have hrec := mul_inv_sub_one_sq_le (alpha / beta) (div_pos hα hβ)
  have hinv : (alpha / beta)⁻¹ - 1 = r := by
    dsimp [r]
    field_simp
  rw [hinv] at hrec
  have hznonneg := vecNormSq_nonneg z
  have hcorr :
      (1 / 2 : ℝ) * alpha * ((alpha / beta) * r ^ 2 * vecNormSq z) ≤
        2 * (r ^ 2 + s ^ 2) *
          ((1 / 2 : ℝ) * alpha *
            (vecNormSq X.1 + vecNormSq z)) := by
    have hfactor : 0 ≤ (1 / 2 : ℝ) * alpha * vecNormSq z := by positivity
    have hm := mul_le_mul_of_nonneg_right hrec hfactor
    have hsum : 0 ≤ 2 * (r ^ 2 + s ^ 2) := by positivity
    have hzle : vecNormSq z ≤ vecNormSq X.1 + vecNormSq z := by
      linarith [vecNormSq_nonneg X.1]
    calc
      (1 / 2 : ℝ) * alpha * ((alpha / beta) * r ^ 2 * vecNormSq z) =
          (alpha / beta * r ^ 2) *
            ((1 / 2 : ℝ) * alpha * vecNormSq z) := by ring
      _ ≤ (2 * (alpha / beta - 1) ^ 2 + 2 * r ^ 2) *
            ((1 / 2 : ℝ) * alpha * vecNormSq z) := hm
      _ = 2 * (r ^ 2 + s ^ 2) *
            ((1 / 2 : ℝ) * alpha * vecNormSq z) := by
        dsimp [s]
        ring
      _ ≤ 2 * (r ^ 2 + s ^ 2) *
            ((1 / 2 : ℝ) * alpha *
              (vecNormSq X.1 + vecNormSq z)) := by
        gcongr
  have henergy :
      (1 / 2 : ℝ) *
          (alpha * vecNormSq X.1 + alpha⁻¹ * vecNormSq X.2) =
        (1 / 2 : ℝ) * alpha *
          (vecNormSq X.1 + vecNormSq z) := by
    rw [hzinv]
    dsimp [z]
    field_simp
  rw [hdiff, henergy]
  have hsum_nonneg : 0 ≤ r ^ 2 + s ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hE_nonneg : 0 ≤ (1 / 2 : ℝ) * alpha *
      (vecNormSq X.1 + vecNormSq z) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hα.le)
      (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))
  have hconst : 1 / δ * r ^ 2 + 2 * (r ^ 2 + s ^ 2) ≤
      3 / δ * (r ^ 2 + s ^ 2) := by
    have hδinv : 1 ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]
      simpa using hδone
    have hinvnonneg : 0 ≤ 1 / δ := by positivity
    have hrle : r ^ 2 ≤ r ^ 2 + s ^ 2 := by
      linarith [sq_nonneg s]
    have hfirst := mul_le_mul_of_nonneg_left hrle hinvnonneg
    have hsecond : r ^ 2 + s ^ 2 ≤ 1 / δ * (r ^ 2 + s ^ 2) := by
      simpa using mul_le_mul_of_nonneg_right hδinv hsum_nonneg
    calc
      1 / δ * r ^ 2 + 2 * (r ^ 2 + s ^ 2) ≤
          1 / δ * (r ^ 2 + s ^ 2) +
            2 * (1 / δ * (r ^ 2 + s ^ 2)) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by norm_num))
      _ = 3 / δ * (r ^ 2 + s ^ 2) := by ring
  calc
    (1 / 2 : ℝ) * alpha *
          (r * (vecNormSq X.1 - vecNormSq z) +
            (alpha / beta) * r ^ 2 * vecNormSq z) =
        (1 / 2 : ℝ) * alpha * r *
            (vecNormSq X.1 - vecNormSq z) +
          (1 / 2 : ℝ) * alpha *
            ((alpha / beta) * r ^ 2 * vecNormSq z) := by ring
    _ ≤ δ * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          1 / δ * r ^ 2 *
              ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)) +
          2 * (r ^ 2 + s ^ 2) *
              ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)) :=
      add_le_add hcross hcorr
    _ = δ * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          (1 / δ * r ^ 2 + 2 * (r ^ 2 + s ^ 2)) *
              ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)) := by ring
    _ ≤ δ * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)) +
          3 / δ * (r ^ 2 + s ^ 2) *
              ((1 / 2 : ℝ) * alpha * (vecNormSq X.1 + vecNormSq z)) :=
      by
        simpa [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_right hconst hE_nonneg)
            (δ * ((1 / 2 : ℝ) * alpha * vecNormSq (X.1 + z)))

-- D-013 analogue: Algsuperdiff/Section24/Sensitivity/Provider/Path/Densities.lean.
private theorem memVectorL2_potential_of_mu_admissible {d : ℕ}
    {U : Ch02.Domain d} {P : BlockVec d} {X : Ch02.DoubledField d}
    (hX : Ch02.IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) X.potential := by
  have h1 : MemVectorL2 (U : Set (Vec d)) (fun x => X.potential x - P.1) := hX.1.1
  have h2 : MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => P.1) :=
    memVectorL2_const P.1
  refine MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) (h1.add h2)
  show (X.potential x - P.1) + P.1 = X.potential x
  abel

private theorem memVectorL2_flux_of_mu_admissible {d : ℕ}
    {U : Ch02.Domain d} {P : BlockVec d} {X : Ch02.DoubledField d}
    (hX : Ch02.IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) X.flux := by
  have h1 : MemVectorL2 (U : Set (Vec d)) (fun x => X.flux x - P.2) := hX.2.1
  have h2 : MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => P.2) :=
    memVectorL2_const P.2
  refine MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => ?_) (h1.add h2)
  show (X.flux x - P.2) + P.2 = X.flux x
  abel

private theorem memVectorL2_blockMatrixField_snd_local {d : ℕ}
    {U : Ch02.Domain d} (a : Ch02.CoeffOn U) {X : Ch02.DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => (blockMatVecMul (Ch02.blockMatrixField a x) (X.eval x)).2) := by
  let ap := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hEll :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hae : ap.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hk : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (skewPart (ap.toCoeffField x)) (X.potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hpot
  have hsub : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (skewPart (ap.toCoeffField x)) (X.potential x) - X.flux x) :=
    hk.sub hflux
  have hw : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (ap.toCoeffField x))⁻¹
        (matVecMul (skewPart (ap.toCoeffField x)) (X.potential x) - X.flux x)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hsub
  refine MeasureTheory.MemLp.ae_eq ?_ hw.neg
  filter_upwards [hae] with x hx
  rw [show Ch02.blockMatrixField a x = blockMatrixOfCoeff (a.toCoeffField x) by rfl,
    blockMatVecMul_blockMatrixOfCoeff_snd, ← hx]
  change -matVecMul (symmPart (ap.toCoeffField x))⁻¹
      (matVecMul (skewPart (ap.toCoeffField x)) (X.potential x) - X.flux x) =
    matVecMul (symmPart (ap.toCoeffField x))⁻¹
      (X.flux x - matVecMul (skewPart (ap.toCoeffField x)) (X.potential x))
  rw [show X.flux x - matVecMul (skewPart (ap.toCoeffField x)) (X.potential x) =
      -(matVecMul (skewPart (ap.toCoeffField x)) (X.potential x) - X.flux x) by abel,
    matVecMul_neg]

private theorem memVectorL2_blockMatrixField_fst_local {d : ℕ}
    {U : Ch02.Domain d} (a : Ch02.CoeffOn U) {X : Ch02.DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => (blockMatVecMul (Ch02.blockMatrixField a x) (X.eval x)).1) := by
  let ap := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hEll :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hae : ap.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hsnd := memVectorL2_blockMatrixField_snd_local ap hpot hflux
  have hs : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (ap.toCoeffField x)) (X.potential x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hpot
  have hkim : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (skewPart (ap.toCoeffField x))
        ((blockMatVecMul (Ch02.blockMatrixField ap x) (X.eval x)).2)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hsnd
  refine MeasureTheory.MemLp.ae_eq ?_ (hs.add hkim)
  filter_upwards [hae] with x hx
  change matVecMul (symmPart (ap.toCoeffField x)) (X.potential x) +
      matVecMul (skewPart (ap.toCoeffField x))
        ((blockMatVecMul (Ch02.blockMatrixField ap x) (X.eval x)).2) =
    (blockMatVecMul (Ch02.blockMatrixField a x) (X.eval x)).1
  rw [hx]
  simp only [Ch02.blockMatrixField, hx]
  change matVecMul (symmPart (a.toCoeffField x)) (X.eval x).1 +
      matVecMul (skewPart (a.toCoeffField x))
        ((blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)).2) =
    (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)).1
  rw [blockMatVecMul_blockMatrixOfCoeff_snd,
    blockMatVecMul_blockMatrixOfCoeff_fst]

private theorem integrableOn_blockEnergyDensity_local {d : ℕ}
    {U : Ch02.Domain d} (a : Ch02.CoeffOn U) {X : Ch02.DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    IntegrableOn (fun x => Ch02.blockEnergyDensityAt a (X.eval x) x)
      (U : Set (Vec d)) := by
  have h1 := integrableOn_vecDot_of_memVectorL2 hpot
    (memVectorL2_blockMatrixField_fst_local a hpot hflux)
  have h2 := integrableOn_vecDot_of_memVectorL2 hflux
    (memVectorL2_blockMatrixField_snd_local a hpot hflux)
  exact (h1.add h2).const_mul (1 / 2 : ℝ)

private theorem volumeAverage_mono_ae_local {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : IntegrableOn f U) (hg : IntegrableOn g U)
    (hfg : f ≤ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f ≤ volumeAverage U g := by
  unfold volumeAverage
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

private theorem doubledMu_le_doubledMuValue_local {d : ℕ}
    {U : Ch02.Domain d} (a : Ch02.CoeffOn U) (P : BlockVec d)
    {X : Ch02.DoubledField d} (hX : Ch02.IsDoubledMuAdmissible U P X) :
    Ch02.doubledMu U a P ≤ Ch02.doubledMuValue U a X := by
  obtain ⟨Y, hY⟩ := (Ch02.doubledMuTheory U a).minimizer_exists P
  have hbdd : BddBelow (Ch02.doubledMuValueSet U a P) := by
    refine ⟨Ch02.doubledMuValue U a Y, ?_⟩
    rintro m ⟨Z, hZ, rfl⟩
    exact hY.2 Z hZ
  exact csInf_le hbdd ⟨X, hX, rfl⟩

private theorem scalar_block_energy_density_eq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (X : BlockVec d)
    (x : Vec d) (hax : a x ≠ 0) :
    Ch02.blockEnergyDensityAt ha.toCoeffOn X x =
      (1 / 2 : ℝ) * (a x * vecNormSq X.1 + (a x)⁻¹ * vecNormSq X.2) := by
  have hInv : ((scalarMatrix (d := d) (a x))⁻¹ : Mat d) =
      scalarMatrix (d := d) (a x)⁻¹ := by
    rw [scalarMatrix, nonsing_inv_smul (a x) hax (by simp)]
    simp [scalarMatrix]
  have ht : matTranspose (0 : Mat d) = 0 := by ext i j; simp [matTranspose]
  have hBlock : blockMatrixOfCoeff (scalarMatrix (d := d) (a x)) =
      { upperLeft := scalarMatrix (d := d) (a x)
        upperRight := 0
        lowerLeft := 0
        lowerRight := scalarMatrix (d := d) (a x)⁻¹ } := by
    unfold blockMatrixOfCoeff
    rw [BlockMat.mk.injEq]
    simp [Ch02.symmPart_scalarMatrix, Ch02.skewPart_scalarMatrix, hInv, ht]
  unfold Ch02.blockEnergyDensityAt
  rw [show Ch02.blockMatrixField ha.toCoeffOn x =
      blockMatrixOfCoeff (scalarMatrix (d := d) (a x)) by rfl, hBlock]
  have hz (z : Vec d) : matVecMul (0 : Mat d) z = 0 := by
    funext i
    simp [matVecMul]
  simp [blockVecDot, blockMatVecMul, matVecMul_scalarMatrix, vecNormSq, hz,
    vecDot_smul_right]

private theorem scalar_block_lower_eq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a) (X : BlockVec d)
    (x : Vec d) (hax : a x ≠ 0) :
    (blockMatVecMul (blockCoeffField ha.toCoeffOn.toCoeffField x) X).2 =
      (a x)⁻¹ • X.2 := by
  have hInv : ((scalarMatrix (d := d) (a x))⁻¹ : Mat d) =
      scalarMatrix (d := d) (a x)⁻¹ := by
    rw [scalarMatrix, nonsing_inv_smul (a x) hax (by simp)]
    simp [scalarMatrix]
  have ht : matTranspose (0 : Mat d) = 0 := by ext i j; simp [matTranspose]
  have hBlock : blockMatrixOfCoeff (scalarMatrix (d := d) (a x)) =
      { upperLeft := scalarMatrix (d := d) (a x)
        upperRight := 0
        lowerLeft := 0
        lowerRight := scalarMatrix (d := d) (a x)⁻¹ } := by
    unfold blockMatrixOfCoeff
    rw [BlockMat.mk.injEq]
    simp [Ch02.symmPart_scalarMatrix, Ch02.skewPart_scalarMatrix, hInv, ht]
  rw [show blockCoeffField ha.toCoeffOn.toCoeffField x =
      blockMatrixOfCoeff (scalarMatrix (d := d) (a x)) by rfl, hBlock]
  have hz (z : Vec d) : matVecMul (0 : Mat d) z = 0 := by
    funext i
    simp [matVecMul]
  simp [blockMatVecMul, matVecMul_scalarMatrix, hz]

private theorem volumeAverage_congr_ae_local {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact integral_congr_ae hfg

private theorem doubled_response_density_average_eq {d : ℕ}
    {U : Ch02.Domain d} {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (p q : Vec d) {X : Ch02.DoubledField d}
    (hX : Ch02.IsDoubledMuMinimizer U ha.toCoeffOn (-p, q) X) :
    Ch02.average U (fun x =>
        (1 / 2 : ℝ) * a x *
          vecNormSq (X.potential x + (a x)⁻¹ • X.flux x)) =
      J U ha.toCoeffOn p q := by
  let v := Ch02.canonicalMaximizer (Ch02.responseExistenceTheory U ha.toCoeffOn) p q
  have hextract :=
    Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient
      U ha.toCoeffOn p q hX
  have hgrad :
      (fun x => X.potential x + (a x)⁻¹ • X.flux x) =ᵐ[
        volumeMeasureOn (U : Set (Vec d))] v.toSolution.toH1.grad := by
    filter_upwards [ha.aeBounds, hextract] with x hax hx
    rw [← hx]
    congr 2
    simpa using (scalar_block_lower_eq ha (X.eval x) x
      (lt_of_lt_of_le ha.lam_pos hax.1).ne').symm
  have havg : Ch02.average U (fun x =>
        (1 / 2 : ℝ) * a x *
          vecNormSq (X.potential x + (a x)⁻¹ • X.flux x)) =
      Ch02.average U (fun x =>
        (1 / 2 : ℝ) * a x * vecNormSq (v.toSolution.toH1.grad x)) :=
    volumeAverage_congr_ae_local (hgrad.mono fun x hx => by
      change (1 / 2 : ℝ) * a x *
          vecNormSq (X.potential x + (a x)⁻¹ • X.flux x) =
        (1 / 2 : ℝ) * a x * vecNormSq (v.toSolution.toH1.grad x)
      have hx' : X.potential x + (a x)⁻¹ • X.flux x =
          v.toSolution.toH1.grad x := hx
      rw [hx'])
  rw [havg]
  have henergy := Ch02.responseJ_eq_energy_of_isResponseMaximizer v.isMaximizer
  change Ch02.average U (fun x =>
      (1 / 2 : ℝ) * a x * vecNormSq (v.toSolution.toH1.grad x)) =
    Ch02.responseJ U ha.toCoeffOn p q
  rw [henergy]
  unfold Ch02.variationEnergyValue
  change volumeAverage (U : Set (Vec d)) (fun x =>
      (1 / 2 : ℝ) * a x * vecNormSq (v.toSolution.toH1.grad x)) =
    (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
      (Ch02.variationEnergyIntegrand U ha.toCoeffOn v.toSolution)
  rw [← volumeAverage_smul]
  apply volumeAverage_congr_ae_local
  filter_upwards [ha.aeBounds] with x hax
  simp [Ch02.variationEnergyIntegrand, ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix, vecDot_smul_right,
    vecNormSq]
  ring

private theorem integrable_scalar_dirichlet_integrand_local2 {d : ℕ}
    {U : Ch02.Domain d} {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (u : H1Function (U : Set (Vec d))) :
    Integrable (fun x => (1 / 2 : ℝ) * a x * vecNormSq (u.grad x))
      (volumeMeasureOn (U : Set (Vec d))) := by
  let ap := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U ha.toCoeffOn
  have hEll :=
    Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
      U ha.toCoeffOn
  have hInt :=
    Homogenization.Internal.Ch02.BookCh02.integrableOn_h1_coefficientEnergyDensity
      hEll u
  have hae := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq
    U ha.toCoeffOn
  have hInt' : Integrable (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
      (matVecMul (ap.toCoeffField x) (u.grad x)))
      (volumeMeasureOn (U : Set (Vec d))) := hInt.const_mul (1 / 2 : ℝ)
  refine hInt'.congr ?_
  filter_upwards [hae] with x hx
  rw [hx]
  simp [ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]
  ring

private theorem responseJ_sensitivity_one {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (p q : Vec d) :
    J U hb.toCoeffOn p q ≤ (1 + δ) * J U ha.toCoeffOn p q +
      3 / δ *
        (scalarRatioLInf U b a ^ 2 + scalarRatioLInf U a b ^ 2) *
        (J U ha.toCoeffOn p q + vecDot p q) := by
  obtain ⟨X, hX⟩ := (Ch02.doubledMuTheory U ha.toCoeffOn).minimizer_exists (-p, q)
  have hpot := memVectorL2_potential_of_mu_admissible hX.1
  have hflux := memVectorL2_flux_of_mu_admissible hX.1
  let Ea : Vec d → ℝ := fun x => Ch02.blockEnergyDensityAt ha.toCoeffOn (X.eval x) x
  let Eb : Vec d → ℝ := fun x => Ch02.blockEnergyDensityAt hb.toCoeffOn (X.eval x) x
  let R : Vec d → ℝ := fun x =>
    (1 / 2 : ℝ) * a x * vecNormSq (X.potential x + (a x)⁻¹ • X.flux x)
  let C : ℝ := 3 / δ *
    (scalarRatioLInf U b a ^ 2 + scalarRatioLInf U a b ^ 2)
  have hEa : IntegrableOn Ea (U : Set (Vec d)) :=
    integrableOn_blockEnergyDensity_local ha.toCoeffOn hpot hflux
  have hEb : IntegrableOn Eb (U : Set (Vec d)) :=
    integrableOn_blockEnergyDensity_local hb.toCoeffOn hpot hflux
  let v := Ch02.canonicalMaximizer (Ch02.responseExistenceTheory U ha.toCoeffOn) p q
  have hextract := Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient
    U ha.toCoeffOn p q hX
  have hgrad : (fun x => X.potential x + (a x)⁻¹ • X.flux x) =ᵐ[
      volumeMeasureOn (U : Set (Vec d))] v.toSolution.toH1.grad := by
    filter_upwards [ha.aeBounds, hextract] with x hax hx
    rw [← hx]
    congr 2
    simpa using (scalar_block_lower_eq ha (X.eval x) x
      (lt_of_lt_of_le ha.lam_pos hax.1).ne').symm
  have hR : IntegrableOn R (U : Set (Vec d)) := by
    have hvInt := integrable_scalar_dirichlet_integrand_local2 ha v.toSolution.toH1
    refine hvInt.congr ?_
    filter_upwards [hgrad] with x hx
    dsimp [R]
    have hx' : X.potential x + (a x)⁻¹ • X.flux x =
        v.toSolution.toH1.grad x := hx
    rw [hx']
  have hRhs : IntegrableOn (fun x => δ * R x + C * Ea x)
      (U : Set (Vec d)) := hR.const_mul δ |>.add (hEa.const_mul C)
  have hba := abs_scalar_ratio_sub_one_le_scalarRatioLInf_ae hb ha
  have hab := abs_scalar_ratio_sub_one_le_scalarRatioLInf_ae ha hb
  have hpoint : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)),
      Eb x - Ea x ≤ δ * R x + C * Ea x := by
    filter_upwards [ha.aeBounds, hb.aeBounds, hba, hab] with x hax hbx hbaX habX
    have hapos : 0 < a x := lt_of_lt_of_le ha.lam_pos hax.1
    have hbpos : 0 < b x := lt_of_lt_of_le hb.lam_pos hbx.1
    have hcore := scalar_block_energy_change_le (a x) (b x) δ hapos hbpos hδ hδone
      (X.eval x)
    rw [← scalar_block_energy_density_eq ha (X.eval x) x hapos.ne',
      ← scalar_block_energy_density_eq hb (X.eval x) x hbpos.ne'] at hcore
    have hsquares :
        (b x / a x - 1) ^ 2 + (a x / b x - 1) ^ 2 ≤
          scalarRatioLInf U b a ^ 2 + scalarRatioLInf U a b ^ 2 := by
      have h1 : (b x / a x - 1) ^ 2 ≤ scalarRatioLInf U b a ^ 2 :=
        by
          have hm := mul_self_le_mul_self (abs_nonneg (b x / a x - 1)) hbaX
          simpa [pow_two, abs_mul_self] using hm
      have h2 : (a x / b x - 1) ^ 2 ≤ scalarRatioLInf U a b ^ 2 :=
        by
          have hm := mul_self_le_mul_self (abs_nonneg (a x / b x - 1)) habX
          simpa [pow_two, abs_mul_self] using hm
      linarith
    have hEaNonneg : 0 ≤ Ea x := by
      dsimp [Ea]
      rw [scalar_block_energy_density_eq ha (X.eval x) x hapos.ne']
      have hinv : 0 ≤ (a x)⁻¹ := (inv_pos.mpr hapos).le
      exact mul_nonneg (by norm_num) (add_nonneg
        (mul_nonneg hapos.le (vecNormSq_nonneg _))
        (mul_nonneg hinv (vecNormSq_nonneg _)))
    have hcoeff : 0 ≤ 3 / δ := by positivity
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquares hcoeff) hEaNonneg
    calc
      Eb x - Ea x ≤ δ * R x +
          3 / δ * ((b x / a x - 1) ^ 2 + (a x / b x - 1) ^ 2) * Ea x := by
        simpa [Ea, Eb, R, Ch02.DoubledField.eval] using hcore
      _ ≤ δ * R x + C * Ea x := by
        dsimp [C]
        simpa [add_comm] using add_le_add_right hm (δ * R x)
  have hdiffInt : IntegrableOn (fun x => Eb x - Ea x) (U : Set (Vec d)) := hEb.sub hEa
  have havgdiff' := volumeAverage_mono_ae_local hdiffInt hRhs hpoint
  have havgR := doubled_response_density_average_eq ha p q hX
  have havgSplit :
      volumeAverage (U : Set (Vec d)) (fun x => δ * R x + C * Ea x) =
        δ * J U ha.toCoeffOn p q + C * Ch02.doubledMuValue U ha.toCoeffOn X := by
    calc
      volumeAverage (U : Set (Vec d)) (fun x => δ * R x + C * Ea x) =
          volumeAverage (U : Set (Vec d)) (fun x => δ * R x) +
            volumeAverage (U : Set (Vec d)) (fun x => C * Ea x) := by
        simpa using volumeAverage_add (hR.const_mul δ) (hEa.const_mul C)
      _ = δ * volumeAverage (U : Set (Vec d)) R +
          C * volumeAverage (U : Set (Vec d)) Ea := by
        rw [← volumeAverage_smul, ← volumeAverage_smul]
        rfl
      _ = δ * J U ha.toCoeffOn p q +
          C * Ch02.doubledMuValue U ha.toCoeffOn X := by
        change δ * Ch02.average U R + C * Ch02.doubledMuValue U ha.toCoeffOn X = _
        rw [show Ch02.average U R = J U ha.toCoeffOn p q by simpa [R] using havgR]
  have hvalue : Ch02.doubledMuValue U hb.toCoeffOn X ≤
      Ch02.doubledMuValue U ha.toCoeffOn X +
        δ * J U ha.toCoeffOn p q + C * Ch02.doubledMuValue U ha.toCoeffOn X := by
    have hdiffavg : Ch02.doubledMuValue U hb.toCoeffOn X -
        Ch02.doubledMuValue U ha.toCoeffOn X ≤
          δ * J U ha.toCoeffOn p q + C * Ch02.doubledMuValue U ha.toCoeffOn X := by
      change volumeAverage (U : Set (Vec d)) Eb - volumeAverage (U : Set (Vec d)) Ea ≤ _
      rw [← volumeAverage_sub hEb hEa]
      rw [havgSplit] at havgdiff'
      exact havgdiff'
    linarith
  have hmuB := doubledMu_le_doubledMuValue_local hb.toCoeffOn (-p, q) hX.1
  have hmuA := hX.doubledMuValue_eq_doubledMu
  have hJa := Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot U ha.toCoeffOn p q
  have hJb := Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot U hb.toCoeffOn p q
  dsimp [C] at hvalue ⊢
  rw [hmuA] at hvalue
  have hmuA_as_J : Ch02.doubledMu U ha.toCoeffOn (-p, q) =
      Ch02.responseJ U ha.toCoeffOn p q + vecDot p q := by linarith [hJa]
  rw [hmuA_as_J] at hvalue
  have hmuBbound := hmuB.trans hvalue
  change Ch02.responseJ U hb.toCoeffOn p q ≤
    (1 + δ) * Ch02.responseJ U ha.toCoeffOn p q +
      3 / δ * (scalarRatioLInf U b a ^ 2 + scalarRatioLInf U a b ^ 2) *
        (Ch02.responseJ U ha.toCoeffOn p q + vecDot p q)
  rw [hJb]
  linarith [hmuBbound]

private noncomputable def scalarCoeffOnData_const_mul {d : ℕ}
    {U : Ch02.Domain d} {b : Vec d → ℝ} (hb : ScalarCoeffOnData U b)
    {c : ℝ} (hc : 0 < c) : ScalarCoeffOnData U (fun x => c * b x) where
  lam := c * hb.lam
  Lam := c * hb.Lam
  lam_pos := mul_pos hc hb.lam_pos
  lam_le_Lam := mul_le_mul_of_nonneg_left hb.lam_le_Lam hc.le
  aeStronglyMeasurable := by
    intro i j
    have h := (hb.aeStronglyMeasurable i j).const_smul c
    convert h using 1
    funext x
    by_cases hx : x ∈ (U : Set (Vec d))
    · simp [restrictCoeffField, hx, scalarCoeffField, scalarMatrix, mul_assoc]
    · simp [restrictCoeffField, hx, scalarCoeffField]
  aeBounds := by
    filter_upwards [hb.aeBounds] with x hx
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc.le,
      mul_le_mul_of_nonneg_left hx.2 hc.le⟩

private theorem scalarRatioLInf_div_const_mul {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (hb : ScalarCoeffOnData U b) (lambda : ℝ) :
    scalarRatioLInf U a (fun x => lambda⁻¹ * b x) =
      scalarRatioLInf U (fun x => lambda * a x) b := by
  unfold scalarRatioLInf
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [hb.aeBounds] with x hbx
  have hbpos : 0 < b x := lt_of_lt_of_le hb.lam_pos hbx.1
  field_simp

theorem responseJ_sensitivity {d : ℕ} {U : Ch02.Domain d}
    {a b : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (hb : ScalarCoeffOnData U b) {lambda delta : ℝ}
    (hlambda : 0 < lambda) (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (p q : Vec d) :
    J U hb.toCoeffOn ((Real.sqrt lambda)⁻¹ • p) (Real.sqrt lambda • q) ≤
      (1 + delta) * J U ha.toCoeffOn p q +
        3 / delta *
          (scalarRatioLInf U (fun x => lambda * a x) b ^ 2 +
            scalarRatioLInf U (fun x => lambda⁻¹ * b x) a ^ 2) *
          (J U ha.toCoeffOn p q + vecDot p q) := by
  let hbScaled : ScalarCoeffOnData U (fun x => lambda⁻¹ * b x) :=
    scalarCoeffOnData_const_mul hb (inv_pos.mpr hlambda)
  have hscaled : Ch02.CoeffOn.AEScaled lambda⁻¹ hb.toCoeffOn hbScaled.toCoeffOn := by
    exact Filter.Eventually.of_forall fun x => by
      ext i j
      simp [hbScaled, scalarCoeffOnData_const_mul, ScalarCoeffOnData.toCoeffOn,
        scalarCoeffField, scalarMatrix, mul_assoc]
  have hhom := (Ch02.responseSubadditivityAndScalingTheory U hb.toCoeffOn).responseJ_homogeneous
    (inv_pos.mpr hlambda) hscaled p q
  have hleft : J U hbScaled.toCoeffOn p q =
      J U hb.toCoeffOn ((Real.sqrt lambda)⁻¹ • p) (Real.sqrt lambda • q) := by
    simpa [Real.sqrt_inv] using hhom
  rw [← hleft]
  have hmain := responseJ_sensitivity_one ha hbScaled hdelta hdelta_one p q
  rw [scalarRatioLInf_div_const_mul hb lambda] at hmain
  simpa [hbScaled, add_comm] using hmain


end

end SubdiffusiveProcess.CoarseGrainingVocab
