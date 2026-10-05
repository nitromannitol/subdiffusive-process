module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RecenteredPathwiseTransfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ConditionalBadEventAssembly

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

def boundedMultiplierFinalConstant (d : ℕ) (c C₀ : ℝ) : ℝ :=
  recenteredTransferConstant d c (boundedMultiplierSealConstant d c C₀)

private theorem predecessorMiddleHalf
    {d m j : ℕ} (hm : 1 ≤ m) (hmj : m < j) {z' : Vec d} {B' : Set (Vec d)}
    (hB' : B' = translatedCube d ((m : ℤ) - j) z') :
    IsMiddleHalfSubcube ((m - 1 : ℕ) : ℤ) z' (j - 1) B' := by
  refine ⟨z', ?_, ?_⟩
  · have he : ((m - 1 : ℕ) : ℤ) - ((j - 1 : ℕ) : ℤ) =
        (m : ℤ) - (j : ℤ) := by omega
    simpa only [he] using hB'
  · intro x hx
    rw [hB', translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm] at hx
    have he : (m : ℤ) - (j : ℤ) ≤ ((m - 1 : ℕ) : ℤ) - 1 := by omega
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) he
    have hp' : (3 : ℝ) ^ ((m : ℤ) - (j : ℤ)) ≤
        (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) / 3 := by
      calc
        _ ≤ (3 : ℝ) ^ (((m - 1 : ℕ) : ℤ) - 1) := hp
        _ = _ := by
          rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
          norm_num
    have hpos : 0 < (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) := by positivity
    simpa only [norm_sub_rev] using hx.le.trans (by nlinarith)

private theorem concentricUnitMiddleHalf {d n : ℕ} (hn : 1 ≤ n) (z : Vec d) :
    IsMiddleHalfSubcube (n : ℤ) z n (translatedCube d 0 z) := by
  refine ⟨z, by simp, ?_⟩
  intro x hx
  rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm] at hx
  have hp : (3 : ℝ) ≤ (3 : ℝ) ^ n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hn
  simpa only [zpow_natCast, norm_sub_rev] using hx.le.trans (by nlinarith)

/-- Complete ambient positive-parent below-scale family. -/
theorem exists_positiveBelowScaleEvents
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {epsilon c C₀ : ℝ} (hepsilon : epsilon ≤ boundedMultiplierEpsilonStar d)
    (hc : 0 < c) (hcHalf : c ≤ 1 / 2) (hC₀ : 1 ≤ C₀)
    (hcell : ∀ M : GMCModel d, M.delta ≤ c →
      ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d,
      ∀ j : ℕ, 0 < j → (j : ℤ) ≤ m →
      ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
        ∃ badTheta : Set (Sample d), MeasurableSet badTheta ∧
          M.P.toMeasure badTheta ≤ ENNReal.ofReal
            ((C₀ - 1) * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
          ∀ omega ∉ badTheta,
            omega ∈ coveringRestrictedGradientGood M L m z →
              BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C₀ c omega) :
    ∀ M : GMCModel d, M.delta ≤ c →
      ∀ L : ℕ, ∀ m : ℤ, 0 < m → ∀ z : Vec d,
      ∀ j : ℕ, 0 < j → m < (j : ℤ) →
      ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
        ∃ badTheta : Set (Sample d), MeasurableSet badTheta ∧
          M.P.toMeasure badTheta ≤ ENNReal.ofReal
            ((boundedMultiplierFinalConstant d c C₀ - 1) *
              Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
          ∀ omega ∉ badTheta,
            omega ∈ coveringRestrictedGradientGood M L m z →
              BoundedMultiplierBelowScalePathwiseEstimate M L m z j B' epsilon
                (boundedMultiplierFinalConstant d c C₀) c omega := by
  intro M hdelta L m hm z j hj hmj B' hB'
  let mn := m.toNat
  have hmn : 0 < mn := Int.pos_iff_toNat_pos.mp hm
  have hmEq : (mn : ℤ) = m := Int.toNat_of_nonneg hm.le
  have hmnj : mn < j := by
    have hz : (mn : ℤ) < (j : ℤ) := by simpa only [hmEq] using hmj
    exact_mod_cast hz
  obtain ⟨z', hB'eq, hB'collar⟩ := hB'
  have hz'mem : z' ∈ B' := by
    rw [hB'eq, translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)
  have hz' := hB'collar z' hz'mem
  have hpred := predecessorMiddleHalf (m := mn) hmn hmnj
    (by simpa only [hmEq] using hB'eq)
  let C₁ := boundedMultiplierSealConstant d c C₀
  let C := boundedMultiplierFinalConstant d c C₀
  have hC₁one : 1 ≤ C₁ := by
    dsimp only [C₁, boundedMultiplierSealConstant]
    have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
    have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
    nlinarith
  have hC₁nonneg : 0 ≤ C₁ := zero_le_one.trans hC₁one
  have hCtail : C₁ ≤ C - 1 := by
    dsimp only [C, boundedMultiplierFinalConstant, recenteredTransferConstant]
    have hrpow : 1 ≤ (3 : ℝ) ^ c := Real.one_le_rpow (by norm_num) hc.le
    have hsqrt := Real.sqrt_nonneg ((3 : ℝ) ^ d)
    nlinarith [mul_le_mul_of_nonneg_left hrpow hC₁nonneg]
  by_cases hm1 : mn = 1
  · subst mn
    have hmone : m = 1 := by omega
    subst m
    obtain ⟨bad, hbadMeas, hbadTail, hlocal⟩ :=
      exists_bad_nonpositive_belowScale hd M L (m := (0 : ℤ)) le_rfl z'
        (j - 1) (by omega) hpred epsilon C₁ c hepsilon hc.le hcHalf
        hC₁one
        (by dsimp only [C₁, boundedMultiplierSealConstant];
            have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
            have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d; nlinarith)
        (by dsimp only [C₁, boundedMultiplierSealConstant];
            have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
            have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d; nlinarith)
    refine ⟨bad, (restrictedCoefficientSigma_le
      (fun x _hx ↦ measurable_aCutoff M L x)) _ hbadMeas, ?_, ?_⟩
    · exact hbadTail.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCtail (Real.exp_pos _).le))
    · intro omega homega _hgood
      simpa only [C, C₁, boundedMultiplierFinalConstant, Nat.cast_one] using!
        boundedMultiplierBelowScalePathwiseEstimate_of_recentered hd M L 1
          le_rfl z z' j (by simpa using hmj)
          (by simpa using hB'eq) (by simpa using hz')
          omega hC₁nonneg (hlocal omega homega)
  · have hnpos : 0 < mn - 1 := by omega
    let n := mn - 1
    have hunit := concentricUnitMiddleHalf (d := d) hnpos z'
    have hscale := hcell M hdelta L (n : ℤ) z' n hnpos le_rfl
      (translatedCube d 0 z') hunit
    have htheta := exists_bad_positiveBelowScale_of_scaleOneEvent hd M L n hnpos
      z' z' (j - 1) (by dsimp only [n]; omega)
      (B' := B') (by
        have he : (n : ℤ) - ((j - 1 : ℕ) : ℤ) = m - (j : ℤ) := by
          dsimp only [n]
          rw [← hmEq]
          omega
        simpa only [he] using hB'eq)
      (by simp; positivity) (epsilon := epsilon) (C₀ := C₀) (c := c)
      hepsilon hc.le hcHalf hC₀
      (by simpa only [n] using hscale)
    have hSigma : restrictedCoefficientSigma (aCutoff M L)
        (translatedCube d (n : ℤ) z') ≤
        (inferInstance : MeasurableSpace (Sample d)) :=
      restrictedCoefficientSigma_le fun x _hx ↦ measurable_aCutoff M L x
    obtain ⟨bad, hbadMeas, hbadTail, hlocal⟩ :=
      exists_union_restrictedGradientBad_of_measurability M L (n : ℤ) z'
        inferInstance hSigma C₁ c hC₁one (hcHalf.trans (by norm_num))
        (BoundedMultiplierBelowScalePathwiseEstimate M L (n : ℤ) z'
          (j - 1) B' epsilon C₁ c) (by simpa only [C₁] using htheta)
    refine ⟨bad, hbadMeas, hbadTail.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCtail (Real.exp_pos _).le)), ?_⟩
    intro omega homega _hgood
    simpa only [hmEq, C, C₁, n, boundedMultiplierFinalConstant] using!
      boundedMultiplierBelowScalePathwiseEstimate_of_recentered hd M L mn hmn
        z z' j hmnj (by simpa only [hmEq] using hB'eq)
        (by simpa only [hmEq] using hz') omega hC₁nonneg (hlocal omega homega)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
