import MarkovProcess.DenseTime.TwoPointMarginals
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationDrift

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec contDiff_vecNormSq
open MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent MeasureTheory
open scoped ENNReal NNReal
theorem edist_rpow_four_le_vecNormSq {d : ℕ} (x y : Vec d) :
    edist x y ^ (4 : ℝ) ≤ ENNReal.ofReal ((vecNormSq (y-x))^2) := by
  rw [edist_comm x y, edist_dist, dist_eq_norm]
  have key : ENNReal.ofReal ‖y-x‖ ^ (4 : ℝ) = ENNReal.ofReal (‖y - x‖ ^ 4) := by
    norm_num only [ENNReal.rpow_ofNat]; exact (ENNReal.ofReal_pow (norm_nonneg (y-x)) 4).symm
  rw [key]
  apply ENNReal.ofReal_le_ofReal
  have h : ‖y - x‖ ^ 2 ≤ vecNormSq (y - x) := by
    have := one_add_norm_sq_le_vecNormSq (y - x)
    linarith
  nlinarith [mul_self_le_mul_self (sq_nonneg ‖y-x‖) h]

theorem min_one_sub_min_one_le {s t : NNReal} (hst : s ≤ t) :
    min t 1-min s 1 ≤ t-s := by
  by_cases hs : s ≤ 1
  · rw [min_eq_left hs, tsub_le_iff_right, tsub_add_cancel_of_le hst]
    exact min_le_left t 1
  · have hs : 1 ≤ s := le_of_not_ge hs
    have ht : 1 ≤ t := le_trans hs hst
    rw [min_eq_right ht, min_eq_right hs, tsub_self]
    exact zero_le _

theorem ofReal_quadratic_square_translate_le {d : ℕ} (x y : Vec d) :
    ENNReal.ofReal ((1+vecNormSq y)^2) ≤
      8*(ENNReal.ofReal ((1+vecNormSq x)^2)+ENNReal.ofReal ((vecNormSq (y-x))^2)) := by
  have h := ENNReal.ofReal_le_ofReal (quadratic_square_translate_le x y)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤8),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_ofNat] using h

theorem measurable_ofReal_centeredQuartic {d : ℕ} (x : Vec d) :
    Measurable (fun y : Vec d ↦ ENNReal.ofReal ((vecNormSq (y-x))^2)) := by
  have hq : Measurable (fun y : Vec d => vecNormSq (y - x)) :=
    (contDiff_vecNormSq (d := d) (n := ⊤)).continuous.measurable.comp
      (measurable_id.sub measurable_const)
  exact (hq.pow_const 2).ennreal_ofReal

theorem measurable_ofReal_quadraticSquare {d : ℕ} :
    Measurable (fun y : Vec d ↦ ENNReal.ofReal ((1+vecNormSq y)^2)) := by
  have hq : Measurable (fun y : Vec d ↦ vecNormSq y) :=
    (contDiff_vecNormSq (d := d) (n := ⊤)).continuous.measurable
  exact ((measurable_const.add hq).pow_const 2).ennreal_ofReal

theorem cast_clipped_time (n : ℕ) (s : DenseTime) :
    DenseTime.castOrderEmbedding ((n : NNRat)+min s 1) =
      (n : NNReal)+min (DenseTime.castOrderEmbedding s) 1 := by
  simp only [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply,
    NNRat.cast_add, NNRat.cast_natCast, NNRat.cast_min, NNRat.cast_one]

theorem clipped_increment_bounds (n s t : NNReal) (hst : s ≤ t) :
    n+min s 1 ≤ n+min t 1 ∧
    (n+min t 1)-(n+min s 1) ≤ 1 ∧
    (n+min t 1)-(n+min s 1) ≤ t-s ∧ n+min s 1 ≤ n+1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · gcongr
  · rw [add_tsub_add_eq_tsub_left]
    exact (tsub_le_self).trans (min_le_right _ _)
  · rw [add_tsub_add_eq_tsub_left]
    exact min_one_sub_min_one_le hst
  · simpa only [add_comm] using add_le_add_left (min_le_right s 1) n

theorem ofReal_fourth_profile {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E) (a : ℝ) (t : NNReal) :
    ENNReal.ofReal (K*a^2*(t:ℝ)^2*E) =
      (Real.toNNReal K : ENNReal)*(t : ENNReal)^2*(Real.toNNReal E : ENNReal)*ENNReal.ofReal (a^2) := by
  have _ := hE
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hK, ENNReal.ofReal_pow t.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  change (Real.toNNReal K : ENNReal) * ENNReal.ofReal (a^2) * (t : ENNReal)^2 *
    (Real.toNNReal E : ENNReal) =
    (Real.toNNReal K : ENNReal) * (t : ENNReal)^2 * (Real.toNNReal E : ENNReal) *
    ENNReal.ofReal (a^2)
  ac_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
