module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Basic.ENNReal.Holder

@[expose] public section

open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Extended-valued finite aggregation, with the supremum at infinity. -/
def finiteAggregation {ι : Type*} (S : Finset ι) (w : ℝ≥0∞) (p : ℝ≥0∞)
    (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  if p = ⊤ then ⨆ i ∈ S, a i
  else (w * ∑ i ∈ S, a i ^ p.toReal) ^ (1 / p.toReal)

/-- Monotonicity of the finite aggregation, including the infinity endpoint. -/
theorem finiteAggregation_mono {ι : Type*} (S : Finset ι) (w : ℝ≥0∞)
    (p : ℝ≥0∞) (_hp : 1 ≤ p) {a b : ι → ℝ≥0∞} (hab : ∀ i ∈ S, a i ≤ b i) :
    finiteAggregation S w p a ≤ finiteAggregation S w p b := by
  unfold finiteAggregation
  split_ifs with hpTop
  · exact iSup₂_mono hab
  · apply ENNReal.rpow_le_rpow
    · exact mul_le_mul_right (Finset.sum_le_sum fun i hi =>
        ENNReal.rpow_le_rpow (hab i hi) ENNReal.toReal_nonneg) w
    · exact one_div_nonneg.mpr ENNReal.toReal_nonneg

/-- Weighted Holder inequality for finite sums, including both endpoints. -/
theorem finiteAggregation_holder {ι : Type*} (S : Finset ι)
    (w : ℝ≥0∞) (hw0 : w ≠ 0) (hwTop : w ≠ ⊤)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (a b : ι → ℝ≥0∞) :
    w * ∑ i ∈ S, a i * b i ≤
      finiteAggregation S w p a * finiteAggregation S w (ENNReal.conjExponent p) b := by
  classical
  by_cases hp1 : p = 1
  · subst p
    simp only [finiteAggregation]
    have hc : ENNReal.conjExponent 1 = ⊤ := by simp [ENNReal.conjExponent]
    rw [hc]
    simp only [ENNReal.one_ne_top, ite_false, ite_true, ENNReal.toReal_one, div_one,
      ENNReal.rpow_one]
    have hs : (∑ i ∈ S, a i * b i) ≤ (∑ i ∈ S, a i) * ⨆ i ∈ S, b i := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hbi : b i ≤ ⨆ k ∈ S, b k :=
        le_iSup_of_le i (le_iSup_of_le hi le_rfl)
      exact mul_le_mul_right hbi (a i)
    exact (mul_le_mul_right hs w).trans_eq (mul_assoc _ _ _).symm
  by_cases hpTop : p = ⊤
  · subst p
    have hc : ENNReal.conjExponent ⊤ = 1 := by simp [ENNReal.conjExponent]
    simp only [finiteAggregation, hc, ENNReal.one_ne_top, ite_false, ite_true,
      ENNReal.toReal_one, div_one, ENNReal.rpow_one]
    have hs : (∑ i ∈ S, a i * b i) ≤ (⨆ i ∈ S, a i) * ∑ i ∈ S, b i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hai : a i ≤ ⨆ k ∈ S, a k :=
        le_iSup_of_le i (le_iSup_of_le hi le_rfl)
      simpa only [mul_comm] using mul_le_mul_right hai (b i)
    exact (mul_le_mul_right hs w).trans_eq (by ac_rfl)
  let q := ENNReal.conjExponent p
  let : ENNReal.HolderConjugate p q := ENNReal.HolderConjugate.conjExponent hp
  have hqTop : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one (p := q) (q := p)).2 hp1
  have hpReal : 1 < p.toReal := by
    have hge := ENNReal.toReal_mono hpTop hp
    have hne : p.toReal ≠ 1 := fun h => hp1 ((ENNReal.toReal_eq_one_iff p).mp h)
    exact lt_of_le_of_ne hge hne.symm
  have hpq : Real.HolderConjugate p.toReal q.toReal :=
    ENNReal.HolderConjugate.toReal hpReal
  change w * ∑ i ∈ S, a i * b i ≤ finiteAggregation S w p a * finiteAggregation S w q b
  simp only [finiteAggregation, hpTop, hqTop, ite_false]
  calc
    w * ∑ i ∈ S, a i * b i ≤ w *
        ((∑ i ∈ S, a i ^ p.toReal) ^ (1 / p.toReal) *
          (∑ i ∈ S, b i ^ q.toReal) ^ (1 / q.toReal)) :=
      mul_le_mul_right (ENNReal.inner_le_Lp_mul_Lq S a b hpq) w
    _ = (w * ∑ i ∈ S, a i ^ p.toReal) ^ (1 / p.toReal) *
          (w * ∑ i ∈ S, b i ^ q.toReal) ^ (1 / q.toReal) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpq.nonneg),
        ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpq.symm.nonneg)]
      rw [mul_mul_mul_comm, ← ENNReal.rpow_add _ _ hw0 hwTop, hpq.one_div_add_one_div, div_one,
        ENNReal.rpow_one]

end SubdiffusiveProcess.Besov
