import SubdiffusiveProcess.Besov.FiniteAggregation
import SubdiffusiveProcess.Besov.ThreeIndexNorms
import Mathlib.Data.Set.Card
import Mathlib.Order.CompleteLattice.Finset

open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Convert the source's finitely supported sum into the finite aggregation. -/
theorem averageLr_eq_finiteAggregation {ι : Type*} (S : Set ι) (hS : S.Finite)
    (p : ℝ≥0∞) (a : ι → ℝ≥0∞) :
    averageLr S p a = finiteAggregation hS.toFinset (S.ncard : ℝ≥0∞)⁻¹ p a := by
  classical
  unfold averageLr finiteAggregation
  split_ifs
  · simp only [Set.Finite.mem_toFinset]
  · rw [finsum_mem_eq_finite_toFinset_sum _ hS]

/-- Congruence only requires equality on the averaging family. -/
theorem finiteAggregation_congr {ι : Type*} (S : Finset ι) (w p : ℝ≥0∞)
    (a b : ι → ℝ≥0∞) (hab : ∀ i ∈ S, a i = b i) :
    finiteAggregation S w p a = finiteAggregation S w p b := by
  unfold finiteAggregation
  split_ifs
  · exact iSup_congr fun i => iSup_congr fun hi => hab i hi
  · rw [Finset.sum_congr rfl fun i hi => congrArg (fun x : ℝ≥0∞ => x ^ p.toReal) (hab i hi)]

/-- Reindex a finite aggregation along an injection. -/
theorem finiteAggregation_image {ι κ : Type*} [DecidableEq κ] (S : Finset ι)
    (f : ι → κ) (hf : Set.InjOn f S) (w p : ℝ≥0∞) (a : κ → ℝ≥0∞) :
    finiteAggregation (S.image f) w p a = finiteAggregation S w p (fun i => a (f i)) := by
  unfold finiteAggregation
  split_ifs
  · exact Finset.iSup_finset_image
  · rw [Finset.sum_image (f := fun i => a i ^ p.toReal) hf]

/-- A larger averaging weight costs at most its ratio, uniformly in p≥1. -/
theorem finiteAggregation_weight_le {ι : Type*} (S : Finset ι)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (w v K : ℝ≥0∞) (hK : 1 ≤ K)
    (hwv : w ≤ K * v) (a : ι → ℝ≥0∞) :
    finiteAggregation S w p a ≤ K * finiteAggregation S v p a := by
  unfold finiteAggregation
  split_ifs with hpTop
  · exact le_mul_of_one_le_left' hK
  · have hpReal : 1 ≤ p.toReal := ENNReal.toReal_mono hpTop hp
    have he : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr ENNReal.toReal_nonneg
    have heOne : 1 / p.toReal ≤ 1 := (div_le_one (by linarith : 0 < p.toReal)).mpr hpReal
    calc
      (w * ∑ i ∈ S, a i ^ p.toReal) ^ (1 / p.toReal) ≤
          (K * (v * ∑ i ∈ S, a i ^ p.toReal)) ^ (1 / p.toReal) := by
        apply ENNReal.rpow_le_rpow _ he
        simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_right hwv (∑ i ∈ S, a i ^ p.toReal)
      _ = K ^ (1 / p.toReal) *
          (v * ∑ i ∈ S, a i ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ he
      _ ≤ K * (v * ∑ i ∈ S, a i ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr
        simpa only [ENNReal.rpow_one] using
          ENNReal.rpow_le_rpow_of_exponent_le hK heOne

/-- Injection into a larger spatial averaging family costs only a cardinality ratio. -/
theorem finiteAggregation_sampling {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (hS : S.Nonempty) (f : ι → κ) (hf : Set.InjOn f S)
    (hfT : ∀ i ∈ S, f i ∈ T) (K : ℕ) (hK : 1 ≤ K)
    (hcard : T.card ≤ K * S.card) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (a : κ → ℝ≥0∞) :
    finiteAggregation S (S.card : ℝ≥0∞)⁻¹ p (fun i => a (f i)) ≤
      (K : ℝ≥0∞) * finiteAggregation T (T.card : ℝ≥0∞)⁻¹ p a := by
  classical
  have hT : T.Nonempty := by obtain ⟨i, hi⟩ := hS; exact ⟨f i, hfT i hi⟩
  have hSc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hTc : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
  have hKr : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hcardr : (T.card : ℝ) ≤ (K : ℝ) * (S.card : ℝ) := by exact_mod_cast hcard
  have hweightReal : (S.card : ℝ)⁻¹ ≤ (K : ℝ) * (T.card : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hSc hTc]
    simpa only [one_mul] using hcardr
  have hweight : (S.card : ℝ≥0∞)⁻¹ ≤ (K : ℝ≥0∞) * (T.card : ℝ≥0∞)⁻¹ := by
    simpa only [ENNReal.ofReal_inv_of_pos hSc, ENNReal.ofReal_inv_of_pos hTc,
      ENNReal.ofReal_mul (by linarith : 0 ≤ (K : ℝ)), ENNReal.ofReal_natCast] using
        ENNReal.ofReal_le_ofReal hweightReal
  have hK' : 1 ≤ (K : ℝ≥0∞) := by exact_mod_cast hK
  have hsub : S.image f ⊆ T := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact hfT i hi
  have hnorm : finiteAggregation S (T.card : ℝ≥0∞)⁻¹ p (fun i => a (f i)) ≤
      finiteAggregation T (T.card : ℝ≥0∞)⁻¹ p a := by
    unfold finiteAggregation
    split_ifs with hpTop
    · apply iSup₂_le
      intro i hi
      exact le_iSup_of_le (f i) (le_iSup_of_le (hfT i hi) le_rfl)
    · apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr ENNReal.toReal_nonneg)
      apply mul_le_mul_right
      change (∑ i ∈ S, (a (f i)) ^ p.toReal) ≤ ∑ i ∈ T, a i ^ p.toReal
      calc
        (∑ i ∈ S, (a (f i)) ^ p.toReal) = ∑ i ∈ S.image f, a i ^ p.toReal :=
          (Finset.sum_image (f := fun i => a i ^ p.toReal) hf).symm
        _ ≤ ∑ i ∈ T, a i ^ p.toReal := Finset.sum_le_sum_of_subset hsub
  exact (finiteAggregation_weight_le S p hp _ _ _ hK' hweight _).trans
    (mul_le_mul_right hnorm _)

end SubdiffusiveProcess.Besov
