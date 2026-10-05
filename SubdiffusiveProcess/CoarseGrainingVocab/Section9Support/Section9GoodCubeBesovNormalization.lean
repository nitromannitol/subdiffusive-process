module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMassCore
public import Mathlib.Analysis.MeanInequalitiesPow
@[expose] public section

/-!
# Normalizing the good-cube negative Besov test

A lower bound on the cube average pays the inverse normalization. The
depth-zero term pays for subtracting the mean; the paper scale factor
is retained on both sides of the comparison.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
/-- Multiplication by a constant is linear for the normalized cube average. -/
private theorem cubeAverage_const_mul {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ)
    (_hf : MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R)) (c : ℝ) :
    cubeAverage R (fun x => c * f x) = c * cubeAverage R f := by
  calc cubeAverage R (fun x => c * f x)
      = ∫ x, c * f x ∂(Homogenization.normalizedCubeMeasure R) :=
        cubeAverage_eq_integral_normalizedCubeMeasure R _
    _ = c * ∫ x, f x ∂(Homogenization.normalizedCubeMeasure R) :=
        MeasureTheory.integral_const_mul c f
    _ = c * cubeAverage R f := by rw [cubeAverage_eq_integral_normalizedCubeMeasure]

/-- Subtracting a constant is linear for the normalized cube average. -/
private theorem cubeAverage_sub_const {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ)
    (hf : MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R)) (e : ℝ) :
    cubeAverage R (fun x => f x - e) = cubeAverage R f - e := by
  have hreal : (Homogenization.normalizedCubeMeasure R).real Set.univ = 1 := by
    rw [MeasureTheory.Measure.real_def, Homogenization.normalizedCubeMeasure_apply_univ]
    norm_num
  calc cubeAverage R (fun x => f x - e)
      = ∫ x, f x - e ∂(Homogenization.normalizedCubeMeasure R) :=
        cubeAverage_eq_integral_normalizedCubeMeasure R _
    _ = ∫ x, f x ∂(Homogenization.normalizedCubeMeasure R)
          - ∫ x, e ∂(Homogenization.normalizedCubeMeasure R) :=
        MeasureTheory.integral_sub hf (MeasureTheory.integrable_const e)
    _ = cubeAverage R f - e := by
        rw [MeasureTheory.integral_const e, hreal,
          cubeAverage_eq_integral_normalizedCubeMeasure]
        norm_num

/-- Integrability transfers from `f - 1` to `f`. -/
private theorem integrable_of_sub_one {d : ℕ} (R : TriadicCube d) {f : Vec d → ℝ}
    (h : MeasureTheory.Integrable (fun x => f x - 1)
      (Homogenization.normalizedCubeMeasure R)) :
    MeasureTheory.Integrable f (Homogenization.normalizedCubeMeasure R) := by
  refine (h.add (MeasureTheory.integrable_const (1 : ℝ))).congr ?_
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

/-- The depth-zero exact-circ block average is the `p`-th power of the absolute
normalized cube average. -/
theorem exactCircDepthAverage_depth_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) :
    exactCircDepthAverage Q p f hf 0 = (ENNReal.ofReal |cubeAverage Q f|) ^ p := by
  simp only [exactCircDepthAverage, exactCircBlockMean_eq_cubeAverage]
  simp only [descendantsAtDepth_zero, Finset.card_singleton, Nat.cast_one, inv_one, one_mul]
  rw [Finset.sum_attach {Q} (fun R : TriadicCube d => (ENNReal.ofReal |cubeAverage R f|) ^ p), Finset.sum_singleton]

/-- Two-term `ℓ^p` bound for a single normalized block mean. -/
private theorem blockPower_le {d : ℕ} (Q R : TriadicCube d) (p : ℝ) (hp1 : 1 ≤ p)
    (f g : Vec d → ℝ) (A : ℝ) (hA : 0 < A)
    (hmean : cubeAverage R g = (cubeAverage R f - cubeAverage Q f) / A) :
    (ENNReal.ofReal |cubeAverage R g|) ^ p ≤
      (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p *
        ((ENNReal.ofReal |cubeAverage R f|) ^ p + (ENNReal.ofReal |cubeAverage Q f|) ^ p)) := by
  have habs : |cubeAverage R g| = |cubeAverage R f - cubeAverage Q f| / A := by
    rw [hmean, abs_div, abs_of_pos hA]
  have hmul : |cubeAverage R g| * A = |cubeAverage R f - cubeAverage Q f| := by
    rw [habs]
    field_simp
  have hwa : ENNReal.ofReal |cubeAverage R g| * ENNReal.ofReal A
      = ENNReal.ofReal |cubeAverage R f - cubeAverage Q f| := by
    rw [← ENNReal.ofReal_mul (abs_nonneg (cubeAverage R g)), hmul]
  have hane : ENNReal.ofReal A ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hA
  have hw : ENNReal.ofReal |cubeAverage R g|
      = ENNReal.ofReal |cubeAverage R f - cubeAverage Q f| * (ENNReal.ofReal A)⁻¹ := by
    have h1 : ENNReal.ofReal |cubeAverage R g| * ENNReal.ofReal A * (ENNReal.ofReal A)⁻¹
        = ENNReal.ofReal |cubeAverage R f - cubeAverage Q f| * (ENNReal.ofReal A)⁻¹ := by
      rw [hwa]
    rw [mul_assoc, ENNReal.mul_inv_cancel hane ENNReal.ofReal_ne_top, mul_one] at h1
    exact h1
  have hXle : ENNReal.ofReal |cubeAverage R f - cubeAverage Q f| ≤
      ENNReal.ofReal |cubeAverage R f| + ENNReal.ofReal |cubeAverage Q f| := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
  calc (ENNReal.ofReal |cubeAverage R g|) ^ p
      = (ENNReal.ofReal |cubeAverage R f - cubeAverage Q f|) ^ p *
          ((ENNReal.ofReal A)⁻¹) ^ p := by
        rw [hw, ENNReal.mul_rpow_of_nonneg _ _ (by linarith only [hp1] : (0 : ℝ) ≤ p)]
    _ ≤ (ENNReal.ofReal |cubeAverage R f| + ENNReal.ofReal |cubeAverage Q f|) ^ p *
          ((ENNReal.ofReal A)⁻¹) ^ p :=
          mul_le_mul' (ENNReal.rpow_le_rpow hXle (by linarith only [hp1] : (0 : ℝ) ≤ p))
            (le_refl _)
    _ ≤ ((2 : ℝ≥0∞) ^ (p - 1) *
            ((ENNReal.ofReal |cubeAverage R f|) ^ p +
              (ENNReal.ofReal |cubeAverage Q f|) ^ p)) *
          ((ENNReal.ofReal A)⁻¹) ^ p :=
          mul_le_mul'
            (ENNReal.rpow_add_le_mul_rpow_add_rpow (ENNReal.ofReal |cubeAverage R f|)
              (ENNReal.ofReal |cubeAverage Q f|) hp1) (le_refl _)
    _ = (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p *
            ((ENNReal.ofReal |cubeAverage R f|) ^ p +
              (ENNReal.ofReal |cubeAverage Q f|) ^ p)) := by
        ring

/-- The normalized depth average of the normalized field is controlled by the
unnormalized one, with the explicit two-term cost. -/
private theorem depthAverage_le {d : ℕ} (Q : TriadicCube d) (p : ℝ) (hp1 : 1 ≤ p)
    (f g : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (hg : ExactCircIntegrable Q g)
    (A : ℝ) (hA : 0 < A)
    (hmean : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      cubeAverage R g = (cubeAverage R f - cubeAverage Q f) / A)
    (j : ℕ) :
    exactCircDepthAverage Q p g hg j ≤
      (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p) *
        (exactCircDepthAverage Q p f hf j + (ENNReal.ofReal |cubeAverage Q f|) ^ p) := by
  have hcardne : (descendantsAtDepth Q j).card ≠ 0 :=
    (descendantsAtDepth_nonempty Q j).card_pos.ne'
  have hnn1 : ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      ((descendantsAtDepth Q j).card : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hcardne) (by simp)
  have hnn2 : ∀ X : ℝ≥0∞, ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (((descendantsAtDepth Q j).card : ℝ≥0∞) * X) = X := by
    intro X
    rw [← mul_assoc, hnn1, one_mul]
  have e1 : ∀ R : {x : TriadicCube d // x ∈ descendantsAtDepth Q j},
      (ENNReal.ofReal |exactCircBlockMean R.1 g (hg.block j R.1 R.2)|) ^ p ≤
        (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p *
          ((ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)|) ^ p
            + (ENNReal.ofReal |cubeAverage Q f|) ^ p)) := by
    intro R
    rw [exactCircBlockMean_eq_cubeAverage R.1 g (hg.block j R.1 R.2),
      exactCircBlockMean_eq_cubeAverage R.1 f (hf.block j R.1 R.2)]
    exact blockPower_le Q R.1 p hp1 f g A hA (hmean j R.1 R.2)
  unfold exactCircDepthAverage
  dsimp only
  calc ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (descendantsAtDepth Q j).attach.sum (fun R =>
            (ENNReal.ofReal |exactCircBlockMean R.1 g (hg.block j R.1 R.2)|) ^ p) ≤
          ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (descendantsAtDepth Q j).attach.sum (fun R =>
              (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p *
                ((ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)|) ^ p
                  + (ENNReal.ofReal |cubeAverage Q f|) ^ p))) := by
        exact mul_le_mul' (le_refl _)
          (Finset.sum_le_sum (fun R _ => e1 R))
      _ = (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p) *
            (((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                (descendantsAtDepth Q j).attach.sum (fun R =>
                  (ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)|) ^ p)
              + (ENNReal.ofReal |cubeAverage Q f|) ^ p) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_attach, nsmul_eq_mul]
        have hstep : ∀ X : ℝ≥0∞, ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            ((2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p * X))
          = (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p) *
            (((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ * X) := by
          intro X
          ring
        rw [hstep, mul_add ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ _ _, hnn2]


/-- The weighted depth term of the normalized field is controlled by the unnormalized
depth term plus the depth-zero moment, with the explicit two-term cost. -/
theorem depthTerm_le {d : ℕ} (Q : TriadicCube d) (p : ℝ) (hp0 : 0 < p) (hp1 : 1 ≤ p)
    (f g : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (hg : ExactCircIntegrable Q g)
    (A : ℝ) (hA : 0 < A)
    (hmean : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      cubeAverage R g = (cubeAverage R f - cubeAverage Q f) / A)
    (j : ℕ) :
    (exactCircDepthTerm Q (1 / 8) p g hg j) ^ p ≤
      (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p) *
        ((exactCircDepthTerm Q (1 / 8) p f hf j) ^ p +
          (ENNReal.ofReal |cubeAverage Q f|) ^ p *
            (exactCircDepthWeight Q (1 / 8) j) ^ p) := by
  rw [exactCircDepthTerm_rpow Q hp0 g hg j]
  calc (exactCircDepthWeight Q (1 / 8) j) ^ p * exactCircDepthAverage Q p g hg j ≤
          (exactCircDepthWeight Q (1 / 8) j) ^ p *
            ((2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p) *
              (exactCircDepthAverage Q p f hf j + (ENNReal.ofReal |cubeAverage Q f|) ^ p)) := by
        exact mul_le_mul' (le_refl _)
          (depthAverage_le Q p hp1 f g hf hg A hA hmean j)
      _ = (2 : ℝ≥0∞) ^ (p - 1) * (((ENNReal.ofReal A)⁻¹) ^ p) *
            ((exactCircDepthTerm Q (1 / 8) p f hf j) ^ p +
              (ENNReal.ofReal |cubeAverage Q f|) ^ p *
                (exactCircDepthWeight Q (1 / 8) j) ^ p) := by
        rw [exactCircDepthTerm_rpow Q hp0 f hf j]
        ring


/-- The exact-circ depth weights form a geometric series dominated by twice the
depth-zero weight. -/
theorem depthWeight_series_le {d : ℕ} (Q : TriadicCube d) (hd : 2 ≤ d) :
    ∑' j : ℕ, (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ)) ≤
      2 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := by
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hratio : (3 : ℝ≥0∞) ^ (-((1 / 8 : ℝ) * (4 * (d : ℝ)))) ≤ (2 : ℝ≥0∞)⁻¹ := by
    calc _ ≤ (3 : ℝ≥0∞) ^ (-1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hdreal])
      _ ≤ (2 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.rpow_neg_one]
          exact ENNReal.inv_le_inv' (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  have hterm (j : ℕ) : (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ)) =
      (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) *
        ((3 : ℝ≥0∞) ^ (-((1 / 8 : ℝ) * (4 * (d : ℝ))))) ^ j := by
    simp only [exactCircDepthWeight, exactCircSourceDepth, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    rw [← ENNReal.rpow_add _ _ (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
    congr 1
    push_cast
    ring
  calc (∑' j : ℕ, (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ)))
      ≤ ∑' j : ℕ, (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) *
        ((2 : ℝ≥0∞)⁻¹) ^ j := by
          apply ENNReal.tsum_le_tsum
          intro j
          rw [hterm]
          exact mul_le_mul' le_rfl (pow_le_pow_left' hratio j)
    _ = 2 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, mul_comm]

theorem goodCube_normalized_negativeBesov_le
    {d : ℕ} (hd : 2 ≤ d) (Q : TriadicCube d) (a : Vec d → ℝ)
    (_ha : Continuous a) (havg : (1 / 2 : ℝ) ≤ cubeAverage Q a)
    (hf : ExactCircIntegrable Q (fun x => a x - 1))
    (hb : ExactCircIntegrable Q (fun x => a x / cubeAverage Q a - 1)) :
    paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
        (fun x => a x / cubeAverage Q a - 1) hb ≤
      8 * paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
        (fun x => a x - 1) hf := by
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp0 : 0 < 4 * (d : ℝ) := by linarith
  have hp1 : 1 ≤ 4 * (d : ℝ) := by linarith
  have hApos : 0 < cubeAverage Q a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) havg
  have hQ0 : Q ∈ descendantsAtDepth Q 0 := by
    rw [descendantsAtDepth_zero Q]
    exact Finset.mem_singleton_self Q
  have haQ : MeasureTheory.Integrable a (Homogenization.normalizedCubeMeasure Q) :=
    integrable_of_sub_one Q (hf.block 0 Q hQ0)
  have hmQ : cubeAverage Q (fun x => a x - 1) = cubeAverage Q a - 1 :=
    cubeAverage_sub_const Q a haQ 1
  have hmean : ∀ (j : ℕ) (R : TriadicCube d), R ∈ descendantsAtDepth Q j →
      cubeAverage R (fun x => a x / cubeAverage Q a - 1)
        = (cubeAverage R (fun x => a x - 1) - cubeAverage Q (fun x => a x - 1)) /
          cubeAverage Q a := by
    intro j R hR
    have hRa : MeasureTheory.Integrable a (Homogenization.normalizedCubeMeasure R) :=
      integrable_of_sub_one R (hf.block j R hR)
    have hRa' : MeasureTheory.Integrable (fun x : Vec d => (1 / cubeAverage Q a) * a x)
        (Homogenization.normalizedCubeMeasure R) :=
      hRa.const_mul (1 / cubeAverage Q a)
    have hfun : (fun x : Vec d => a x / cubeAverage Q a - 1)
        = fun x => (1 / cubeAverage Q a) * a x - 1 := by
      funext x
      field_simp
    have h1 : cubeAverage R (fun x => a x / cubeAverage Q a - 1)
        = (1 / cubeAverage Q a) * cubeAverage R a - 1 := by
      rw [hfun, cubeAverage_sub_const R _ hRa' 1,
        cubeAverage_const_mul R a hRa (1 / cubeAverage Q a)]
    have h2 : cubeAverage R (fun x => a x - 1) = cubeAverage R a - 1 :=
      cubeAverage_sub_const R a hRa 1
    rw [h1, h2, hmQ]
    field_simp
    ring
  have hterm := depthTerm_le Q (4 * (d : ℝ)) hp0 hp1 (fun x => a x - 1)
    (fun x => a x / cubeAverage Q a - 1) hf hb (cubeAverage Q a) hApos hmean
  have hweight := depthWeight_series_le Q hd
  have hzero := exactCircDepthAverage_depth_zero Q (4 * (d : ℝ)) (fun x => a x - 1) hf
  set Sf : ℝ≥0∞ := ∑' j : ℕ, (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ))
    (fun x => a x - 1) hf j) ^ (4 * (d : ℝ)) with hSf
  set Sg : ℝ≥0∞ := ∑' j : ℕ, (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ))
    (fun x => a x / cubeAverage Q a - 1) hb j) ^ (4 * (d : ℝ)) with hSg
  have hB : (∑' j : ℕ, (ENNReal.ofReal |cubeAverage Q (fun x => a x - 1)|) ^ (4 * (d : ℝ)) *
        (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ))) ≤
      2 * (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf 0)
        ^ (4 * (d : ℝ)) := by
    calc ∑' j : ℕ, (ENNReal.ofReal |cubeAverage Q (fun x => a x - 1)|) ^ (4 * (d : ℝ)) *
              (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ)) ≤
            (ENNReal.ofReal |cubeAverage Q (fun x => a x - 1)|) ^ (4 * (d : ℝ)) *
              (2 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ))) := by
          rw [ENNReal.tsum_mul_left]
          exact mul_le_mul' (le_refl _) hweight
        _ = 2 * ((exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) *
              (ENNReal.ofReal |cubeAverage Q (fun x => a x - 1)|) ^ (4 * (d : ℝ))) := by
          ring
        _ = 2 * (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf 0)
              ^ (4 * (d : ℝ)) := by
          rw [exactCircDepthTerm_rpow Q hp0 (fun x => a x - 1) hf 0, hzero]
  have hsum : Sg ≤ (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
        (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) *
        (Sf + 2 * (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf 0)
          ^ (4 * (d : ℝ))) := by
    calc Sg ≤ ∑' j : ℕ, (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
                (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) *
                ((exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf j)
                  ^ (4 * (d : ℝ)) +
                  (ENNReal.ofReal |cubeAverage Q (fun x => a x - 1)|) ^ (4 * (d : ℝ)) *
                    (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ))) := by
          exact ENNReal.tsum_le_tsum (fun j => hterm j)
        _ = (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
                (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) *
                (Sf + ∑' j : ℕ, (ENNReal.ofReal |cubeAverage Q (fun x => a x - 1)|)
                  ^ (4 * (d : ℝ)) * (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ))) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ← hSf]
        _ ≤ (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
                (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) *
                (Sf + 2 * (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf 0)
                  ^ (4 * (d : ℝ))) := by
          exact mul_le_mul' (le_refl _) (add_le_add (le_refl _) hB)
  have hTle : (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf 0)
      ^ (4 * (d : ℝ)) ≤ Sf :=
    by simpa only [Sf] using! ENNReal.le_tsum (f := fun j =>
      exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf j ^ (4 * (d : ℝ))) 0
  have hKle : (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) * (((ENNReal.ofReal (cubeAverage Q a))⁻¹)
        ^ (4 * (d : ℝ))) ≤ (2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1) := by
    have hAinv : ((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))
        ≤ (2 : ℝ≥0∞) ^ (4 * (d : ℝ)) := by
      apply ENNReal.rpow_le_rpow _ hp0.le
      calc (ENNReal.ofReal (cubeAverage Q a))⁻¹ ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ :=
          ENNReal.inv_le_inv' (ENNReal.ofReal_le_ofReal havg)
        _ = 2 := by
          rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          norm_num
    calc (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) * (((ENNReal.ofReal (cubeAverage Q a))⁻¹)
          ^ (4 * (d : ℝ))) ≤
        (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) * (2 : ℝ≥0∞) ^ (4 * (d : ℝ)) :=
          mul_le_mul' (le_refl _) hAinv
      _ = (2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1) := by
          rw [← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
          congr 1
          ring
  have h2big : (3 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) + 1) := by
    have h6 : (2 : ℝ≥0∞) ^ (1 : ℝ) ≤ (2 : ℝ≥0∞) ^ (4 * (d : ℝ)) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hp1
    have h7 : (2 : ℝ≥0∞) ^ (1 : ℝ) = 2 := ENNReal.rpow_one _
    calc (3 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) + (2 : ℝ≥0∞) := by norm_num
      _ = (2 : ℝ≥0∞) ^ (1 : ℝ) + (2 : ℝ≥0∞) ^ (1 : ℝ) := by simp only [h7]
      _ ≤ (2 : ℝ≥0∞) ^ (4 * (d : ℝ)) + (2 : ℝ≥0∞) ^ (4 * (d : ℝ)) := add_le_add h6 h6
      _ = (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) + 1) := by
          have h8 : (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) + 1)
              = (2 : ℝ≥0∞) ^ (4 * (d : ℝ)) * (2 : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
              (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          rw [h8, ENNReal.rpow_one]
          ring
  have h3le : (3 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1))
      ≤ (8 : ℝ≥0∞) ^ (4 * (d : ℝ)) := by
    calc (3 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1)) ≤
        (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) + 1) * ((2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1)) :=
          mul_le_mul' h2big (le_refl _)
      _ = (2 : ℝ≥0∞) ^ (((4 * (d : ℝ)) + 1) + (2 * (4 * (d : ℝ)) - 1)) := by
          rw [← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      _ = (8 : ℝ≥0∞) ^ (4 * (d : ℝ)) := by
          have h9 : (8 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 3 := by norm_num
          rw [h9, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1
          ring
  have hsum3 : Sg ≤ (8 : ℝ≥0∞) ^ (4 * (d : ℝ)) * Sf := by
    calc Sg ≤ (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
            (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) *
            (Sf + 2 * (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) (fun x => a x - 1) hf 0)
              ^ (4 * (d : ℝ))) := hsum
      _ ≤ (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
              (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) * (Sf + 2 * Sf) :=
            mul_le_mul' (le_refl _)
              (add_le_add (le_refl _) (mul_le_mul' (le_refl (2 : ℝ≥0∞)) hTle))
      _ = (2 : ℝ≥0∞) ^ ((4 * (d : ℝ)) - 1) *
              (((ENNReal.ofReal (cubeAverage Q a))⁻¹) ^ (4 * (d : ℝ))) * (3 * Sf) := by
            ring
      _ ≤ (2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1) * (3 * Sf) :=
            mul_le_mul' hKle (le_refl _)
      _ = (3 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (2 * (4 * (d : ℝ)) - 1)) * Sf := by
            ring
      _ ≤ (8 : ℝ≥0∞) ^ (4 * (d : ℝ)) * Sf := mul_le_mul' h3le (le_refl _)
  unfold paperNegativeBesovCircDiagonal
  rw [← hSf, ← hSg]
  calc (ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ * Sg ^ (4 * (d : ℝ))⁻¹ ≤
      (ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ *
        (((8 : ℝ≥0∞) ^ (4 * (d : ℝ)) * Sf) ^ (4 * (d : ℝ))⁻¹) :=
        mul_le_mul' (le_refl _) (ENNReal.rpow_le_rpow hsum3 (inv_nonneg.mpr hp0.le))
    _ = (ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ *
          (((8 : ℝ≥0∞) ^ (4 * (d : ℝ))) ^ (4 * (d : ℝ))⁻¹ * Sf ^ (4 * (d : ℝ))⁻¹) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0.le)]
    _ = (ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ *
          ((8 : ℝ≥0∞) * Sf ^ (4 * (d : ℝ))⁻¹) := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
    _ = (8 : ℝ≥0∞) * ((ENNReal.ofReal (1 / 8 : ℝ)) ^ (4 * (d : ℝ))⁻¹ *
          Sf ^ (4 * (d : ℝ))⁻¹) := by ring
    _ = 8 * paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
          (fun x => a x - 1) hf := rfl


end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
