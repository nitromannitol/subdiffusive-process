import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBesovNormalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasure
/-!
# A local coefficient ratio supplies the normalized negative Besov test

A field bounded in absolute value by one on a cube has scaled paper
`(1/8, 4*d)` negative Besov norm at most one. If `c ≤ b ≤ 2*c`, its actual
cube average lies in the same interval and `|b / average - 1| ≤ 1`.
Neither conclusion uses an ensemble average or a bound outside the cube.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private theorem uniform_depthWeight_series_le {d : ℕ} (Q : TriadicCube d) (hd : 2 ≤ d) :
    ∑' j : ℕ, (exactCircDepthWeight Q (1 / 8) j) ^ (4 * (d : ℝ)) ≤
      2 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.depthWeight_series_le (d := d) (Q := Q) (hd := hd)


/-- A local absolute bound pays the scaled paper negative Besov test. -/
theorem goodCube_negativeBesov_le_one_of_abs_le
    {d : ℕ} (hd : 2 ≤ d) (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : ExactCircIntegrable Q f)
    (hbound : ∀ x ∈ openCubeSet Q, |f x| ≤ 1) :
    ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (Q.scale : ℝ))) *
      paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) f hf ≤ 1 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : 0 < 4 * (d : ℝ) := by linarith
  have hmean (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
      |exactCircBlockMean R f (hf.block j R hR)| ≤ 1 := by
    have hb : ∀ᵐ x ∂normalizedCubeMeasure R, ‖f x‖ ≤ 1 := by
      apply Section8Support.weightedSobolev_normalized_ae R
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      simpa only [Real.norm_eq_abs] using
        hbound x (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)
    simpa only [exactCircBlockMean, Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const hb
  have havg (j : ℕ) : exactCircDepthAverage Q (4 * (d : ℝ)) f hf j ≤ 1 := by
    have hcard : (descendantsAtDepth Q j).card ≠ 0 :=
      (descendantsAtDepth_nonempty Q j).card_pos.ne'
    unfold exactCircDepthAverage
    dsimp only
    calc ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (descendantsAtDepth Q j).attach.sum (fun R =>
            (ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)|) ^
              (4 * (d : ℝ)))
        ≤ ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (descendantsAtDepth Q j).attach.sum (fun _ => (1 : ℝ≥0∞)) := by
          apply mul_le_mul' le_rfl
          apply Finset.sum_le_sum
          intro R _
          have hm : ENNReal.ofReal |exactCircBlockMean R.1 f (hf.block j R.1 R.2)| ≤ 1 := by
            simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hmean j R.1 R.2)
          simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hm hp.le
      _ = 1 := by
        simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one]
        exact ENNReal.inv_mul_cancel (by exact_mod_cast hcard) (by simp)
  have hsum : (∑' j : ℕ, (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) f hf j) ^
      (4 * (d : ℝ))) ≤
      2 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := by
    refine (ENNReal.tsum_le_tsum (fun j => ?_)).trans (uniform_depthWeight_series_le Q hd)
    rw [exactCircDepthTerm_rpow Q hp f hf j]
    simpa only [mul_one] using mul_le_mul' (le_refl ((exactCircDepthWeight Q (1 / 8) j) ^
      (4 * (d : ℝ)))) (havg j)
  have hpow : (paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) f hf) ^
      (4 * (d : ℝ)) ≤ (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := by
    rw [paperNegativeBesovCircDiagonal_rpow Q hp f hf]
    calc ENNReal.ofReal (1 / 8 : ℝ) *
          (∑' j : ℕ, (exactCircDepthTerm Q (1 / 8) (4 * (d : ℝ)) f hf j) ^
            (4 * (d : ℝ)))
        ≤ ENNReal.ofReal (1 / 8 : ℝ) *
            (2 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ))) :=
          mul_le_mul' le_rfl hsum
      _ = (ENNReal.ofReal (1 / 8 : ℝ) * 2) *
            (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := by ring
      _ ≤ 1 * (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) :=
          mul_le_mul' (by
            calc ENNReal.ofReal (1 / 8 : ℝ) * 2
                = ENNReal.ofReal (1 / 8 : ℝ) * ENNReal.ofReal (2 : ℝ) := by norm_num
              _ = ENNReal.ofReal ((1 / 8 : ℝ) * 2) :=
                (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)).symm
              _ ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal (by norm_num)
              _ = 1 := ENNReal.ofReal_one) le_rfl
      _ = (exactCircDepthWeight Q (1 / 8) 0) ^ (4 * (d : ℝ)) := one_mul _
  have hnorm : paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) f hf ≤
      exactCircDepthWeight Q (1 / 8) 0 := (ENNReal.rpow_le_rpow_iff hp).mp hpow
  have hcancel : ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (Q.scale : ℝ))) *
      exactCircDepthWeight Q (1 / 8) 0 = 1 := by
    have hthree : ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (Q.scale : ℝ))) =
        (3 : ℝ≥0∞) ^ (-(1 / 8 : ℝ) * (Q.scale : ℝ)) := by
      simpa only [ENNReal.ofReal_ofNat] using
        (ENNReal.ofReal_rpow_of_pos (p := -(1 / 8 : ℝ) * (Q.scale : ℝ))
          (by norm_num : (0 : ℝ) < 3)).symm
    rw [hthree]
    simp only [exactCircDepthWeight, exactCircSourceDepth, Nat.cast_zero, sub_zero]
    rw [← ENNReal.rpow_add _ _ (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
    convert (ENNReal.rpow_zero : (3 : ℝ≥0∞) ^ (0 : ℝ) = 1) using 1
    congr 1
    ring
  exact (mul_le_mul' le_rfl hnorm).trans_eq hcancel

/-- Pointwise factor-two bounds control the actual average and its normalized
paper Besov test on the same cube. -/
theorem goodCube_normalized_besov_of_ratio
    {d : ℕ} (hd : 2 ≤ d) (Q : TriadicCube d) (b : Vec d → ℝ)
    (hb : Continuous b) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ openCubeSet Q, c ≤ b x ∧ b x ≤ 2 * c) :
    c ≤ cubeAverage Q b ∧ cubeAverage Q b ≤ 2 * c ∧
      ∀ hf : ExactCircIntegrable Q (fun x => b x / cubeAverage Q b - 1),
        ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (Q.scale : ℝ))) *
          paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ))
            (fun x => b x / cubeAverage Q b - 1) hf ≤ 1 := by
  have hI : Integrable b (normalizedCubeMeasure Q) :=
    (exactCircIntegrable_of_continuous Q hb).block 0 Q (by simp [descendantsAtDepth_zero])
  have hAE : ∀ᵐ x ∂normalizedCubeMeasure Q, c ≤ b x ∧ b x ≤ 2 * c := by
    apply Section8Support.weightedSobolev_normalized_ae Q
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact hbound x hx
  have hlo : c ≤ cubeAverage Q b := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    simpa using integral_mono_ae (integrable_const c) hI (hAE.mono fun _ hx => hx.1)
  have hhi : cubeAverage Q b ≤ 2 * c := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    simpa using integral_mono_ae hI (integrable_const (2 * c)) (hAE.mono fun _ hx => hx.2)
  refine ⟨hlo, hhi, ?_⟩
  intro hf
  apply goodCube_negativeBesov_le_one_of_abs_le hd Q _ hf
  intro x hx
  have ha : 0 < cubeAverage Q b := hc.trans_le hlo
  have hnn : 0 ≤ b x / cubeAverage Q b :=
    div_nonneg (hc.le.trans (hbound x hx).1) ha.le
  have hu : b x / cubeAverage Q b ≤ 2 := (div_le_iff₀ ha).2
    ((hbound x hx).2.trans (mul_le_mul_of_nonneg_left hlo (by norm_num)))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
