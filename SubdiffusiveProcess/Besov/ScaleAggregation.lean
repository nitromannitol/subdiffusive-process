module

public import SubdiffusiveProcess.Besov.SpatialAggregation
public import SubdiffusiveProcess.Besov.ThreeIndexNorms

@[expose] public section

open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Homogeneity of the finite aggregation, including its supremum endpoint. -/
theorem finiteAggregation_const_mul {ι : Type*} (S : Finset ι) (w : ℝ≥0∞)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (k : ℝ≥0∞) (_hk0 : k ≠ 0) (_hkTop : k ≠ ⊤)
    (a : ι → ℝ≥0∞) :
    finiteAggregation S w p (fun i => k * a i) = k * finiteAggregation S w p a := by
  unfold finiteAggregation
  split_ifs with hpTop
  · simp only [ENNReal.mul_iSup]
  · have hpPos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one (ENNReal.toReal_mono hpTop hp)
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
    rw [← Finset.mul_sum]
    rw [show w * (k ^ p.toReal * ∑ i ∈ S, a i ^ p.toReal) =
      k ^ p.toReal * (w * ∑ i ∈ S, a i ^ p.toReal) by ac_rfl]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpPos.le),
      ← ENNReal.rpow_mul, mul_one_div_cancel hpPos.ne', ENNReal.rpow_one]

/-- A finite collection of scale entries is bounded by the full scale norm. -/
theorem finiteAggregation_le_scaleAggregation {ι : Type*} (S : Finset ι)
    (s : ℝ) (m : ℤ) (p : ℝ≥0∞) (_hp : 1 ≤ p) (a : ℤ → ℝ≥0∞)
    (f : ι → ℤ) (hf : Set.InjOn f S) (hfBound : ∀ i ∈ S, f i ≤ m) :
    finiteAggregation S (ENNReal.ofReal s) p (fun i => a (f i)) ≤
      scaleAggregation s m p a := by
  classical
  unfold finiteAggregation scaleAggregation
  split_ifs with hpTop
  · apply iSup₂_le
    intro i hi
    exact le_iSup_of_le (f i) (le_iSup_of_le (hfBound i hi) le_rfl)
  · apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr ENNReal.toReal_nonneg)
    apply mul_le_mul_right
    calc
      (∑ i ∈ S, a (f i) ^ p.toReal) =
          ∑ n ∈ S.image f, (if n ≤ m then a n ^ p.toReal else 0) := by
        rw [Finset.sum_image]
        · exact Finset.sum_congr rfl fun i hi => by rw [if_pos (hfBound i hi)]
        · exact hf
      _ ≤ ∑' n : ℤ, (if n ≤ m then a n ^ p.toReal else 0) := ENNReal.sum_le_tsum _

/-- Scale Holder inequality, with exactly the source's factor s⁻¹. -/
theorem scaleAggregation_holder_finset (S : Finset ℤ) (s : ℝ) (hs : 0 < s)
    (m : ℤ) (p : ℝ≥0∞) (hp : 1 ≤ p) (a b : ℤ → ℝ≥0∞)
    (hS : ∀ n ∈ S, n ≤ m) :
    (∑ n ∈ S, a n * b n) ≤ ENNReal.ofReal s⁻¹ *
      (scaleAggregation s m p a * scaleAggregation s m (ENNReal.conjExponent p) b) := by
  have hw0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  letI : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  have hc : 1 ≤ ENNReal.conjExponent p := ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p
  have h := finiteAggregation_holder S (ENNReal.ofReal s) hw0 ENNReal.ofReal_ne_top p hp a b
  have hn := mul_le_mul' (finiteAggregation_le_scaleAggregation S s m p hp a id
      (fun _ _ _ _ heq => heq) hS)
    (finiteAggregation_le_scaleAggregation S s m _ hc b id (fun _ _ _ _ heq => heq) hS)
  have hmul := mul_le_mul_right (h.trans hn) (ENNReal.ofReal s⁻¹)
  simpa only [← mul_assoc, ENNReal.ofReal_inv_of_pos hs,
    ENNReal.inv_mul_cancel hw0 ENNReal.ofReal_ne_top, one_mul] using hmul

/-- Scale pairing also permits different injective reindexings of its two factors. -/
theorem scaleAggregation_holder_reindexed {ι : Type*} (S : Finset ι) (s : ℝ) (hs : 0 < s)
    (m : ℤ) (p : ℝ≥0∞) (hp : 1 ≤ p) (a b : ℤ → ℝ≥0∞)
    (f g : ι → ℤ) (hf : Set.InjOn f S) (hg : Set.InjOn g S)
    (hfBound : ∀ i ∈ S, f i ≤ m) (hgBound : ∀ i ∈ S, g i ≤ m) :
    (∑ i ∈ S, a (f i) * b (g i)) ≤ ENNReal.ofReal s⁻¹ *
      (scaleAggregation s m p a * scaleAggregation s m (ENNReal.conjExponent p) b) := by
  have hw0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  letI : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  have hc : 1 ≤ ENNReal.conjExponent p := ENNReal.HolderConjugate.one_le _ p
  have h := finiteAggregation_holder S (ENNReal.ofReal s) hw0 ENNReal.ofReal_ne_top p hp
    (fun i => a (f i)) (fun i => b (g i))
  have hn := mul_le_mul' (finiteAggregation_le_scaleAggregation S s m p hp a f hf hfBound)
    (finiteAggregation_le_scaleAggregation S s m _ hc b g hg hgBound)
  have hmul := mul_le_mul_right (h.trans hn) (ENNReal.ofReal s⁻¹)
  simpa only [← mul_assoc, ENNReal.ofReal_inv_of_pos hs,
    ENNReal.inv_mul_cancel hw0 ENNReal.ofReal_ne_top, one_mul] using hmul

/-- A singleton with unit weight has its own entry as its norm. -/
theorem finiteAggregation_singleton_one {ι : Type*} [DecidableEq ι]
    (i : ι) (p : ℝ≥0∞) (hp : 1 ≤ p) (a : ι → ℝ≥0∞) :
    finiteAggregation {i} 1 p a = a i := by
  unfold finiteAggregation
  split_ifs with hpTop
  · simp
  · have hpPos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one (ENNReal.toReal_mono hpTop hp)
    simp only [Finset.sum_singleton, one_mul]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hpPos.ne', ENNReal.rpow_one]

/-- A single entry is bounded by s⁻¹ times the scale norm for 0<s≤1. -/
theorem scaleAggregation_entry_le (s : ℝ) (hs : 0 < s) (hsOne : s ≤ 1)
    (m n : ℤ) (hn : n ≤ m) (p : ℝ≥0∞) (hp : 1 ≤ p) (a : ℤ → ℝ≥0∞) :
    a n ≤ ENNReal.ofReal s⁻¹ * scaleAggregation s m p a := by
  have hw0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hK : 1 ≤ ENNReal.ofReal s⁻¹ := by
    rw [ENNReal.one_le_ofReal]
    exact (one_le_inv₀ hs).mpr hsOne
  have hw : 1 ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal s := by
    rw [ENNReal.ofReal_inv_of_pos hs, ENNReal.inv_mul_cancel hw0 ENNReal.ofReal_ne_top]
  calc
    a n = finiteAggregation {n} 1 p a := (finiteAggregation_singleton_one n p hp a).symm
    _ ≤ ENNReal.ofReal s⁻¹ * finiteAggregation {n} (ENNReal.ofReal s) p a :=
      finiteAggregation_weight_le _ p hp _ _ _ hK hw a
    _ ≤ ENNReal.ofReal s⁻¹ * scaleAggregation s m p a := mul_le_mul_right
      (finiteAggregation_le_scaleAggregation {n} s m p hp a id
        (fun _ _ _ _ h => h) (by simpa using hn)) _

/-- Monotonicity of the full scale aggregation. -/
theorem scaleAggregation_mono (s : ℝ) (m : ℤ) (p : ℝ≥0∞)
    {a b : ℤ → ℝ≥0∞} (hab : ∀ n ≤ m, a n ≤ b n) :
    scaleAggregation s m p a ≤ scaleAggregation s m p b := by
  unfold scaleAggregation
  split_ifs
  · exact iSup₂_mono hab
  · apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr ENNReal.toReal_nonneg)
    apply mul_le_mul_right
    apply ENNReal.tsum_le_tsum
    intro n
    split_ifs with hn
    · exact ENNReal.rpow_le_rpow (hab n hn) ENNReal.toReal_nonneg
    · exact le_rfl

/-- Homogeneity of the full scale aggregation. -/
theorem scaleAggregation_const_mul (s : ℝ) (m : ℤ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (k : ℝ≥0∞) (a : ℤ → ℝ≥0∞) :
    scaleAggregation s m p (fun n => k * a n) = k * scaleAggregation s m p a := by
  unfold scaleAggregation
  split_ifs with hpTop
  · simp only [ENNReal.mul_iSup]
  · have hpPos : 0 < p.toReal := lt_of_lt_of_le zero_lt_one (ENNReal.toReal_mono hpTop hp)
    have heq : (fun n => if n ≤ m then (k * a n) ^ p.toReal else 0) =
        (fun n => k ^ p.toReal * (if n ≤ m then a n ^ p.toReal else 0)) := by
      funext n
      split_ifs
      · exact ENNReal.mul_rpow_of_nonneg _ _ hpPos.le
      · simp
    rw [heq, ENNReal.tsum_mul_left]
    rw [show ENNReal.ofReal s * (k ^ p.toReal * ∑' n : ℤ, if n ≤ m then a n ^ p.toReal else 0) =
      k ^ p.toReal * (ENNReal.ofReal s * ∑' n : ℤ, if n ≤ m then a n ^ p.toReal else 0) by ac_rfl]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hpPos.le),
      ← ENNReal.rpow_mul, mul_one_div_cancel hpPos.ne', ENNReal.rpow_one]

end SubdiffusiveProcess.Besov
