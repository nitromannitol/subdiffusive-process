module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovScaleSum
public import Homogenization.Besov.Negative.ExactFiniteBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevScalars
@[expose] public section

set_option autoImplicit false

/-! A single descendant moment extracted from the exact negative Besov mass bound. -/
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
theorem weightedSobolev_depth_single {d : ℕ} (Q : TriadicCube d)
    (s p : ℝ) (hp : 0 < p) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ) :
    ENNReal.ofReal s * (exactCircDepthTerm Q s p f hf j) ^ p ≤
      (paperNegativeBesovCircDiagonal Q s p f hf) ^ p := by
  calc ENNReal.ofReal s * (exactCircDepthTerm Q s p f hf j) ^ p
      ≤ ENNReal.ofReal s * ∑' k, (exactCircDepthTerm Q s p f hf k) ^ p :=
        mul_le_mul_right (ENNReal.le_tsum (f := fun k => (exactCircDepthTerm Q s p f hf k) ^ p) j) _
    _ = (paperNegativeBesovCircDiagonal Q s p f hf) ^ p :=
        (paperNegativeBesovCircDiagonal_rpow Q hp f hf).symm

theorem weightedSobolev_block_single {d : ℕ} (Q : TriadicCube d)
    (p : ℝ) (f : Vec d → ℝ) (hf : ExactCircIntegrable Q f) (j : ℕ)
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
    ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal |exactCircBlockMean R f (hf.block j R hR)|) ^ p ≤
      exactCircDepthAverage Q p f hf j := by
  have hs : (ENNReal.ofReal |cubeAverage R f|)^p ≤
      ∑ S ∈ descendantsAtDepth Q j, (ENNReal.ofReal |cubeAverage S f|)^p :=
    Finset.single_le_sum (f := fun S : TriadicCube d =>
      (ENNReal.ofReal |cubeAverage S f|) ^ p) (fun _ _ => zero_le) hR
  simp only [exactCircDepthAverage, exactCircBlockMean_eq_cubeAverage]
  rw [Finset.sum_attach (descendantsAtDepth Q j)
    (fun S : TriadicCube d => (ENNReal.ofReal |cubeAverage S f|) ^ p)]
  exact mul_le_mul_right hs _

theorem weightedSobolev_mass_weight (d : ℕ) (m : ℤ) (j : ℕ) :
    (ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ)))) ^ (4 * (d : ℝ)) *
      (ENNReal.ofReal (1 / 8 : ℝ) *
        (exactCircDepthWeight (originCube d m) (1 / 8) j) ^ (4 * (d : ℝ)) *
        ((descendantsAtDepth (originCube d m) j).card : ℝ≥0∞)⁻¹) =
      ENNReal.ofReal ((1 / 8 : ℝ) * (3 : ℝ) ^
        (-(3 / 8 : ℝ) * (j : ℝ) * (4 * (d : ℝ)))) := by
  have hthree (a : ℝ) : ENNReal.ofReal ((3 : ℝ) ^ a) = (3 : ℝ≥0∞) ^ a := by
    symm
    simpa using! (ENNReal.ofReal_rpow_of_pos (p := a) (by norm_num : (0 : ℝ) < 3))
  unfold exactCircDepthWeight exactCircSourceDepth
  simp only [originCube, Int.cast_sub, Int.cast_natCast, descendantsAtDepth_card,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
  simp only [hthree, ← ENNReal.rpow_natCast, ← ENNReal.rpow_neg, ← ENNReal.rpow_mul]
  calc
    _ = ENNReal.ofReal (1 / 8 : ℝ) *
        (((3 : ℝ≥0∞) ^ (-(1 / 8 : ℝ) * (m : ℝ) * (4 * (d : ℝ))) *
          (3 : ℝ≥0∞) ^ (((m : ℝ) - (j : ℝ)) * (1 / 8) * (4 * (d : ℝ)))) *
          (3 : ℝ≥0∞) ^ (-((d : ℝ) * (j : ℝ)))) := by
      ring_nf
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ (by norm_num : (3 : ℝ≥0∞) ≠ 0)
        (by norm_num : (3 : ℝ≥0∞) ≠ ⊤),
        ← ENNReal.rpow_add _ _ (by norm_num : (3 : ℝ≥0∞) ≠ 0)
        (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
      congr 2
      ring

theorem weightedSobolev_cell_moment {d : ℕ} (hd : 2 ≤ d) (m : ℤ)
    (f : Vec d → ℝ) (hf : ExactCircIntegrable (originCube d m) f)
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal (originCube d m) (1 / 8) (4 * (d : ℝ)) f hf ≤
        ENNReal.ofReal M)
    (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    (1 / 8 : ℝ) * (3 : ℝ) ^ (-(3 / 8 : ℝ) * (j : ℝ) * (4 * (d : ℝ))) *
      |cubeAverage R f| ^ (4 * (d : ℝ)) ≤ M ^ (4 * (d : ℝ)) := by
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : 0 < 4 * (d : ℝ) := by linarith
  let Q := originCube d m
  let p : ℝ := 4 * (d : ℝ)
  have hdepth := weightedSobolev_depth_single Q (1 / 8) p hp f hf j
  rw [exactCircDepthTerm_rpow Q hp f hf j] at hdepth
  have hblock := weightedSobolev_block_single Q p f hf j R hR
  have hlower : ENNReal.ofReal (1 / 8 : ℝ) *
      (exactCircDepthWeight Q (1 / 8) j) ^ p *
      ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (ENNReal.ofReal |exactCircBlockMean R f (hf.block j R hR)|) ^ p ≤
      (paperNegativeBesovCircDiagonal Q (1 / 8) p f hf) ^ p := by
    calc
      _ ≤ ENNReal.ofReal (1 / 8 : ℝ) *
          ((exactCircDepthWeight Q (1 / 8) j) ^ p *
            exactCircDepthAverage Q p f hf j) := by
        simpa only [mul_assoc] using! mul_le_mul_right hblock
          (ENNReal.ofReal (1 / 8 : ℝ) * (exactCircDepthWeight Q (1 / 8) j) ^ p)
      _ ≤ _ := hdepth
  have hmoment := (mul_le_mul_right hlower
    ((ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ)))) ^ p)).trans
    (weightedSobolev_scaled_moment hp.le hmass)
  have hw := weightedSobolev_mass_weight d m j
  change (ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (m : ℝ)))) ^ p *
      (ENNReal.ofReal (1 / 8 : ℝ) * (exactCircDepthWeight Q (1 / 8) j) ^ p *
        ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹) = _ at hw
  rw [← mul_assoc, hw, exactCircBlockMean_eq_cubeAverage,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hM hp.le] at hmoment
  exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hM p)).mp hmoment

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
