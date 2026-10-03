module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBoundedScaleThreshold
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeClockComparison
@[expose] public section

/-! Common coefficient normalization preserves the actual weighted equation; bounded cutoffs admit arbitrarily small normalized contrast outside the existing log-Lipschitz failure event. -/

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
private lemma div_mul_cancel_aux {k : ℝ} (hk : k ≠ 0) (mu p q r : ℝ)
    (h : mu * (p / k) + q / k = r / k) : mu * p + q = r := by
  have h2 := congrArg (fun t : ℝ => t * k) h
  field_simp [hk] at h2
  exact h2

private lemma div_split_aux {k : ℝ} (_hk : k ≠ 0) (mu p q r : ℝ) (h : mu * p + q = r) :
    mu * (p / k) + q / k = r / k := by
  calc mu * (p / k) + q / k = (mu * p + q) / k := by ring
    _ = r / k := congrArg (fun t : ℝ => t / k) h

theorem goodCube_massiveWeakSolution_div_common_coefficient
    {d : ℕ} {U : Set (Vec d)} {a rho : Vec d → ℝ} {k : ℝ} (hk : k ≠ 0)
    (mu : ℝ) (u : H1Function U) (f : Vec d → ℝ) :
    IsMassiveWeakSolutionOn (fun x => a x / k) (fun x => rho x / k) mu U u f ↔
      IsMassiveWeakSolutionOn a rho mu U u f := by
  refine ⟨fun H φ => ?_, fun H φ => ?_⟩
  · have hA : ∫ x in U, rho x / k * u.toFun x * φ.toH1Function.toFun x ∂volume
        = (∫ x in U, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume) / k := by
      simp only [div_mul_eq_mul_div]
      rw [integral_div]
    have hB1 : ∫ x in U, vecDot ((a x / k) • u.grad x) (φ.toH1Function.grad x) ∂volume
        = ∫ x in U, (a x / k) * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume := by
      simp only [vecDot_smul_left]
    have hB2 : ∫ x in U, (a x / k) * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume
        = (∫ x in U, a x * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume) / k := by
      simp only [div_mul_eq_mul_div]
      rw [integral_div]
    have hB3 : ∫ x in U, a x * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume
        = ∫ x in U, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
      simp only [vecDot_smul_left]
    have hB := hB1.trans (hB2.trans (congrArg (fun t : ℝ => t / k) hB3))
    have hF : ∫ x in U, rho x / k * f x * φ.toH1Function.toFun x ∂volume
        = (∫ x in U, rho x * f x * φ.toH1Function.toFun x ∂volume) / k := by
      simp only [div_mul_eq_mul_div]
      rw [integral_div]
    have H' : mu * ∫ x in U, rho x / k * u.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in U, vecDot ((a x / k) • u.grad x) (φ.toH1Function.grad x) ∂volume =
        ∫ x in U, rho x / k * f x * φ.toH1Function.toFun x ∂volume := H φ
    rw [hA, hB, hF] at H'
    exact div_mul_cancel_aux hk mu
      (∫ x in U, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume)
      (∫ x in U, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume)
      (∫ x in U, rho x * f x * φ.toH1Function.toFun x ∂volume) H'
  · have hA : ∫ x in U, rho x / k * u.toFun x * φ.toH1Function.toFun x ∂volume
        = (∫ x in U, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume) / k := by
      simp only [div_mul_eq_mul_div]
      rw [integral_div]
    have hB1 : ∫ x in U, vecDot ((a x / k) • u.grad x) (φ.toH1Function.grad x) ∂volume
        = ∫ x in U, (a x / k) * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume := by
      simp only [vecDot_smul_left]
    have hB2 : ∫ x in U, (a x / k) * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume
        = (∫ x in U, a x * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume) / k := by
      simp only [div_mul_eq_mul_div]
      rw [integral_div]
    have hB3 : ∫ x in U, a x * vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume
        = ∫ x in U, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
      simp only [vecDot_smul_left]
    have hB := hB1.trans (hB2.trans (congrArg (fun t : ℝ => t / k) hB3))
    have hF : ∫ x in U, rho x / k * f x * φ.toH1Function.toFun x ∂volume
        = (∫ x in U, rho x * f x * φ.toH1Function.toFun x ∂volume) / k := by
      simp only [div_mul_eq_mul_div]
      rw [integral_div]
    show mu * ∫ x in U, rho x / k * u.toFun x * φ.toH1Function.toFun x ∂volume +
        ∫ x in U, vecDot ((a x / k) • u.grad x) (φ.toH1Function.grad x) ∂volume =
      ∫ x in U, rho x / k * f x * φ.toH1Function.toFun x ∂volume
    rw [hA, hB, hF]
    exact div_split_aux hk mu
      (∫ x in U, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume)
      (∫ x in U, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume)
      (∫ x in U, rho x * f x * φ.toH1Function.toFun x ∂volume) (H φ)

theorem goodCube_ahom_zero_ge_half {d : ℕ} (M : GMCModel d)
    (hdelta : M.delta ≤ 1 / 2) : (1 / 2 : ℝ) ≤ ahom M 0 := by
  have hδnn : 0 ≤ M.delta := le_of_lt M.shellPrefix.delta_pos
  have hlog2nn : (0:ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hlog2half : (0:ℝ) ≤ Real.log 2 / 2 := by linarith
  have hsq : M.delta ^ 2 ≤ 1 / 4 := by
    rw [pow_two]
    have h1 : M.delta * M.delta ≤ (1 / 2) * M.delta :=
      mul_le_mul_of_nonneg_right hdelta hδnn
    have h2 : (1 / 2) * M.delta ≤ (1 / 2) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hdelta (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc M.delta * M.delta ≤ (1 / 2) * M.delta := h1
      _ ≤ (1 / 2) * (1 / 2) := h2
      _ = 1 / 4 := by norm_num
  have hτ4 : tauSq M.P ≤ Real.log 2 / 2 * (1 / 4) :=
    (tauSq_le_delta_sq M).trans (mul_le_mul_of_nonneg_left hsq hlog2half)
  have hprod : Real.log 2 / 2 * (1 / 4) ≤ Real.log 2 := by
    have h6 : Real.log 2 / 2 ≤ Real.log 2 := by linarith
    have h7 := mul_le_mul h6 (by norm_num : (1 / 4 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) hlog2nn
    rwa [mul_one] at h7
  have hτ5 : tauSq M.P ≤ Real.log 2 := le_trans hτ4 hprod
  have h0' : Real.exp (-(tauSq M.P)) ≤ ahom M 0 := by
    have h0 := SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M 0
    simp only [Nat.cast_zero, zero_add, neg_one_mul] at h0
    exact h0
  have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(tauSq M.P)) := by
    have h8 : Real.exp (-Real.log 2) ≤ Real.exp (-(tauSq M.P)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h9 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      norm_num
    linarith
  linarith

theorem exists_goodCube_boundedScale_coefficient_contrast
    (d J : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ M : GMCModel d, M.delta ≤ c → ∀ n : ℕ, n ≤ J →
      ∀ (z : Lattice d) (omega : PotentialSample d),
        omega ∉ coefficientLocalBadEvent M n 1 (goodCubeBad M n) z →
        ∃ k : ℝ, 0 < k ∧ ∀ x ∈ nativeBox n 1 z,
          k ≤ aCutoff M n omega x ∧ aCutoff M n omega x ≤ (1 + eps) * k ∧
            |aCutoff M n omega x / k - 1| ≤ eps := by
  have hlog1pos : 0 < Real.log (1 + eps) := Real.log_pos (by linarith : (1:ℝ) < 1 + eps)
  have he' : 0 < Real.log (1 + eps) / 2 := div_pos hlog1pos (by norm_num : (0:ℝ) < 2)
  obtain ⟨delta0, hd0pos, -, hth⟩ :=
    exists_goodCube_boundedScale_logLipschitz_threshold d J (Real.log (1 + eps) / 2) he'
  refine ⟨min (1 / 2) delta0, lt_min (by norm_num : (0:ℝ) < 1 / 2) hd0pos, min_le_left _ _, ?_⟩
  intro M hM n hn z omega hom
  obtain ⟨lam, hlam, hstep⟩ := exists_parentEllipticity_scale_of_not_goodCubeBad M n z omega hom
  have hT : logLipschitzThreshold M n * (3:ℝ)^n ≤ Real.log (1 + eps) / 2 :=
    hth M (le_trans hM (min_le_right _ _)) n hn
  have hratio : Real.exp (2 * (logLipschitzThreshold M n * (3 : ℝ) ^ n)) ≤ 1 + eps := by
    have h1 : 2 * (logLipschitzThreshold M n * (3:ℝ)^n) ≤ Real.log (1 + eps) := by linarith
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by linarith : (0:ℝ) < 1 + eps)] at h2
  refine ⟨lam, hlam, ?_⟩
  intro x hx
  obtain ⟨hup, hdown⟩ := hstep x hx
  refine ⟨hup, ?_, ?_⟩
  · exact le_trans hdown (mul_le_mul_of_nonneg_right hratio hlam.le)
  · have e1 : (1:ℝ) ≤ aCutoff M n omega x / lam := by
      rw [one_le_div₀ hlam]
      exact hup
    have e2 : aCutoff M n omega x / lam ≤ 1 + eps := by
      rw [div_le_iff₀ hlam]
      exact le_trans hdown (mul_le_mul_of_nonneg_right hratio hlam.le)
    have e3 : (0:ℝ) ≤ aCutoff M n omega x / lam - 1 := by linarith
    rw [abs_of_nonneg e3]
    linarith
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
