module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationDrift

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec contDiff_vecNormSq
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent MeasureTheory MarkovProcess
open scoped ENNReal NNReal
theorem ofReal_exp_add_time (C : ℝ) (s t : NNReal) :
    ENNReal.ofReal (Real.exp (C*(s+t:NNReal))) =
      ENNReal.ofReal (Real.exp (C*(s:ℝ)))*ENNReal.ofReal (Real.exp (C*(t:ℝ))) := by
  rw [NNReal.coe_add, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem one_le_ofReal_exp_time {C : ℝ} (hC : 0 ≤ C) (t : NNReal) :
    1 ≤ ENNReal.ofReal (Real.exp (C*(t:ℝ))) := by
  rw [←ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.2 (mul_nonneg hC t.coe_nonneg))

theorem ofReal_quadratic_quotient {d : ℕ} (C T R : ℝ) (x : Vec d) :
    ENNReal.ofReal (Real.exp (C*T))*ENNReal.ofReal (1+vecNormSq x)/ENNReal.ofReal (1+R^2) =
      ENNReal.ofReal (Real.exp (C*T)*(1+vecNormSq x)/(1+R^2)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_mul (by positivity)]

theorem measurable_ofReal_quadratic {d : ℕ} :
    Measurable (fun x : Vec d ↦ ENNReal.ofReal (1+vecNormSq x)) :=
  Measurable.ennreal_ofReal
    (measurable_const.add (contDiff_vecNormSq (d := d) (n := ⊤)).continuous.measurable)

theorem measurableSet_countable_hit {alpha iota : Type*} [MeasurableSpace alpha] [Countable iota]
    (V : alpha → ENNReal) (hV : Measurable V) (H : ENNReal) :
    MeasurableSet {path : iota → alpha | ∃ i, H ≤ V (path i)} := by
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_le measurable_const (hV.comp (measurable_pi_apply i))

theorem measurableSet_dense_hit {alpha : Type*} [MeasurableSpace alpha]
    (V : alpha → ENNReal) (hV : Measurable V) (H : ENNReal) (T : NNReal) :
    MeasurableSet {omega : DenseTime → alpha | ∃ q, DenseTime.castOrderEmbedding q ≤ T ∧ H ≤ V (omega q)} := by
  simp only [Set.setOf_exists, Set.setOf_and]
  exact MeasurableSet.iUnion fun q =>
    (MeasurableSet.const _).inter
      (measurableSet_le measurable_const (hV.comp (measurable_pi_apply q)))

theorem monotone_toNNReal_exp_mul {C : ℝ} (hC : 0 ≤ C) :
    Monotone (fun t : NNReal ↦ Real.toNNReal (Real.exp (C*(t:ℝ)))) := by
  intro s t hst
  apply Real.toNNReal_mono
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hst hC

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
