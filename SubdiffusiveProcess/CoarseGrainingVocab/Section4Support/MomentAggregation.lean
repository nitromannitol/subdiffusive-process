module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SphereQuarterNet
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import SubdiffusiveProcess.Analysis.RawLp

@[expose] public section

/-!
# Section 4 support: finite maxima and square-root moments

These are the measure-theoretic aggregation atoms used after the per-cube
response estimates in `l.ellipticity.bound` and
`l.multiscale.response.large.cubes`.

The decomposition mirrors
`Algsuperdiff/Section3/Provider/MultiscaleEstimate/HomogenizationLanes.lean`:
take the sharp cardinality root at each finite spatial grid before summing the
geometrically discounted scale contributions.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The manuscript's `ENNReal` moment carrier uses the v4.26 norm formula
at a positive finite exponent. -/
theorem paperENNRealLpNorm_eq_eLpNorm {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p X = SubdiffusiveProcess.RawLp.eLpNorm X (ENNReal.ofReal p) mu := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  simp only [paperENNRealLpNorm, enorm_eq_self, one_div]

/-- Measurable observables agree with the guarded norm API. -/
theorem paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    (X : Omega → ℝ≥0∞) (hX : AEStronglyMeasurable X mu) :
    paperENNRealLpNorm mu p X = eLpNorm X (ENNReal.ofReal p) mu := by
  rw [paperENNRealLpNorm_eq_eLpNorm mu hp X, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hX]

/-- Lyapunov monotonicity for the manuscript's `ENNReal` moment carrier on a
probability space. -/
theorem paperENNRealLpNorm_le_of_exponent_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) {X : Omega → ℝ≥0∞}
    (hX : Measurable X) :
    paperENNRealLpNorm mu p X ≤ paperENNRealLpNorm mu q X := by
  have hq : 0 < q := hp.trans_le hpq
  rw [paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable mu hp X hX.aestronglyMeasurable,
    paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable mu hq X hX.aestronglyMeasurable]
  exact eLpNorm_le_eLpNorm_of_exponent_le
    (ENNReal.ofReal_le_ofReal hpq)

/-- Holder in the manuscript's nonnegative moment carrier, with equal
conjugate exponents. -/
theorem paperENNRealLpNorm_mul_le_two_mul
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X Y : Omega → ℝ≥0∞}
    (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu) :
    paperENNRealLpNorm mu p (fun omega ↦ X omega * Y omega) ≤
      paperENNRealLpNorm mu (2 * p) X *
        paperENNRealLpNorm mu (2 * p) Y := by
  have hp0 : 0 ≤ p := hp.le
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two (hX.pow_const p) (hY.pow_const p)
  unfold paperENNRealLpNorm
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
  have hbase :
      (∫⁻ omega, X omega ^ p * Y omega ^ p ∂mu) ≤
        (∫⁻ omega, X omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) *
          (∫⁻ omega, Y omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) := by
    convert hholder using 1
    all_goals simp only [← ENNReal.rpow_mul, one_div, mul_comm p]
  calc
    (∫⁻ omega, X omega ^ p * Y omega ^ p ∂mu) ^ p⁻¹ ≤
        ((∫⁻ omega, X omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) *
          (∫⁻ omega, Y omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ)) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hbase (inv_nonneg.mpr hp0)
    _ = (∫⁻ omega, X omega ^ (2 * p) ∂mu) ^ (2 * p)⁻¹ *
          (∫⁻ omega, Y omega ^ (2 * p) ∂mu) ^ (2 * p)⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 2 <;> field_simp

/-- Sharp finite-maximum moment bound.  In contrast to a triangle-inequality
bound, the grid cardinality is paid as `card^(1/p)`. -/
theorem paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Omega → ℝ≥0∞)
    (hX : ∀ i ∈ s, Measurable (X i)) (A : ℝ≥0∞)
    (hA : ∀ i ∈ s, paperENNRealLpNorm mu p (X i) ≤ A) :
    paperENNRealLpNorm mu p (s.sup' hs X) ≤
      (s.card : ℝ≥0∞) ^ p⁻¹ * A := by
  classical
  have hp0 : 0 ≤ p := hp.le
  have hinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  have hpoint : ∀ omega, (s.sup' hs X omega) ^ p ≤
      ∑ i ∈ s, (X i omega) ^ p := by
    intro omega
    simp only [Finset.sup'_apply]
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hs (fun j => X j omega)
    rw [heq]
    exact Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0∞) ≤ (X j omega) ^ p from bot_le)) hi
  have hI : (∫⁻ omega, (s.sup' hs X omega) ^ p ∂mu) ≤
      ∑ i ∈ s, ∫⁻ omega, (X i omega) ^ p ∂mu := by
    calc
      _ ≤ ∫⁻ omega, ∑ i ∈ s, (X i omega) ^ p ∂mu :=
        lintegral_mono hpoint
      _ = _ := by
        rw [lintegral_finset_sum]
        intro i hi
        simpa only [Function.comp_apply] using!
          ENNReal.continuous_rpow_const.measurable.comp (hX i hi)
  have hIi : ∀ i ∈ s, (∫⁻ omega, (X i omega) ^ p ∂mu) ≤ A ^ p := by
    intro i hi
    have h := ENNReal.rpow_le_rpow (hA i hi) hp0
    simpa only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hp.ne', ENNReal.rpow_one] using h
  unfold paperENNRealLpNorm
  calc
    (∫⁻ omega, (s.sup' hs X omega) ^ p ∂mu) ^ p⁻¹ ≤
        (∑ i ∈ s, ∫⁻ omega, (X i omega) ^ p ∂mu) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hI hinv0
    _ ≤ (∑ _i ∈ s, A ^ p) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i hi => hIi i hi) hinv0
    _ = (s.card : ℝ≥0∞) ^ p⁻¹ * A := by
      rw [Finset.sum_const, nsmul_eq_mul,
        ENNReal.mul_rpow_of_nonneg _ _ hinv0, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]

/-- On a probability space, taking the square root of a nonnegative observable
costs at most the square root of its moment at the same exponent. -/
theorem paperENNRealLpNorm_rpow_half_le {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} (hX : Measurable X) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (1 / 2 : ℝ)) ≤
      (paperENNRealLpNorm mu p X) ^ (1 / 2 : ℝ) := by
  have hp2 : 0 < p / 2 := div_pos hp (by norm_num)
  have heq : paperENNRealLpNorm mu p
      (fun omega => X omega ^ (1 / 2 : ℝ)) =
      (paperENNRealLpNorm mu (p / 2) X) ^ (1 / 2 : ℝ) := by
    unfold paperENNRealLpNorm
    simp_rw [← ENNReal.rpow_mul]
    congr 1
    · congr 1
      ring_nf
    · ring_nf
  rw [heq]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  rw [paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable mu hp2 X hX.aestronglyMeasurable,
    paperENNRealLpNorm_eq_eLpNorm_of_aestronglyMeasurable mu hp X hX.aestronglyMeasurable]
  apply eLpNorm_le_eLpNorm_of_exponent_le
  · exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Countable Minkowski inequality for nonnegative measurable observables in
the manuscript's moment convention. -/
theorem paperENNRealLpNorm_tsum_le_tsum {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) {p : ℝ} (hp : 1 ≤ p)
    (X : ℕ → Omega → ℝ≥0∞) (hX : ∀ n, Measurable (X n)) :
    paperENNRealLpNorm mu p (fun omega => ∑' n, X n omega) ≤
      ∑' n, paperENNRealLpNorm mu p (X n) := by
  let B : ℝ≥0∞ := ∑' n, paperENNRealLpNorm mu p (X n)
  by_cases hB : B = ∞
  · rw [show (∑' n, paperENNRealLpNorm mu p (X n)) = ∞ from hB]
    exact le_top
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hp0 : 0 ≤ p := hpPos.le
  have hinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  let S : ℕ → Omega → ℝ≥0∞ := fun n omega => ∑ k ∈ Finset.range n, X k omega
  have hS : ∀ n, Measurable (S n) := by
    intro n
    exact Finset.measurable_sum _ fun k _ => hX k
  have hpow : (fun omega => (∑' n, X n omega) ^ p) =
      fun omega => ⨆ n, (S n omega) ^ p := by
    funext omega
    rw [ENNReal.tsum_eq_iSup_nat]
    simpa only [ENNReal.orderIsoRpow_apply, S] using
      (ENNReal.orderIsoRpow p hpPos).map_iSup
        (fun n => ∑ k ∈ Finset.range n, X k omega)
  have hpartial : ∀ n, paperENNRealLpNorm mu p (S n) ≤ B := by
    intro n
    calc
      paperENNRealLpNorm mu p (S n) ≤
          ∑ k ∈ Finset.range n, paperENNRealLpNorm mu p (X k) :=
        paperENNRealLpNorm_finset_sum_le mu hp (Finset.range n) X
          (fun k _ => hX k)
      _ ≤ ∑' k, paperENNRealLpNorm mu p (X k) :=
        ENNReal.sum_le_tsum (Finset.range n)
      _ = B := rfl
  have hpartialI : ∀ n,
      (∫⁻ omega, (S n omega) ^ p ∂mu) ≤ B ^ p := by
    intro n
    have h := ENNReal.rpow_le_rpow (hpartial n) hp0
    simpa only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hpPos.ne', ENNReal.rpow_one] using h
  unfold paperENNRealLpNorm
  rw [hpow, lintegral_iSup]
  · calc
      (⨆ n, ∫⁻ omega, (S n omega) ^ p ∂mu) ^ p⁻¹ ≤
          (B ^ p) ^ p⁻¹ := by
        apply ENNReal.rpow_le_rpow _ hinv0
        exact iSup_le hpartialI
      _ = B := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hpPos.ne', ENNReal.rpow_one]
      _ = ∑' n, paperENNRealLpNorm mu p (X n) := rfl
  · intro n
    exact ENNReal.continuous_rpow_const.measurable.comp (hS n)
  · intro a b hab omega
    apply ENNReal.rpow_le_rpow _ hp0
    dsimp only [S]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun _ _ _ => bot_le)

end

end SubdiffusiveProcess.CoarseGrainingVocab
