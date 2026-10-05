module

public import SubdiffusiveProcess.Meyers.Defs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.BallPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2

@[expose] public section

/-! The mean-zero Poincaré inequality on a sup-ball (cube) in unnormalised `eLpNorm` form, for
`H1Function`s, with the explicit dependence `≤ K_d · r · ‖∇u‖₂` on the radius. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

variable {d : ℕ}

theorem gradNorm_eq_euclideanNorm {U : Set (Vec d)} (u : H1Function U) :
    (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) = fun x => euclideanNorm (u.grad x) := by
  funext x
  simp [euclideanNorm, vecNormSq, vecDot, sq]

theorem memLp_two_gradNorm {U : Set (Vec d)} (u : H1Function U) :
    MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) 2 (volume.restrict U) := by
  rw [gradNorm_eq_euclideanNorm]
  have hgrad : MemLp (fun x => HilbertVec.ofVec (u.grad x)) 2 (volume.restrict U) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [Function.comp_apply, PiLp.toLp_apply] using u.gradMemL2 i
  simpa only [euclideanNorm_eq_norm_ofVec] using hgrad.norm

theorem eLpNorm_sub_average_le [NeZero d] (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (Metric.ball x0 r)) :
    (eLpNorm (fun y => u.toFun y - volumeAverage (Metric.ball x0 r) u.toFun) 2
        (volume.restrict (Metric.ball x0 r))).toReal ≤
      (unitMeanZeroPoincareConst d * (2 * r) * (d : ℝ)) *
        (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) 2
          (volume.restrict (Metric.ball x0 r))).toReal := by
  have hvol_lt : volume (Metric.ball x0 r) < ⊤ := measure_ball_lt_top
  have : IsFiniteMeasure (volume.restrict (Metric.ball x0 r)) := ⟨by simpa [Measure.restrict_apply_univ] using hvol_lt⟩
  have hVpos : 0 < (volume (Metric.ball x0 r)).toReal := by
    apply ENNReal.toReal_pos
    · exact (Metric.measure_ball_pos volume x0 hr).ne'
    · exact hvol_lt.ne
  have hf : MemLp (fun y => u.toFun y - volumeAverage (Metric.ball x0 r) u.toFun) 2 (volume.restrict (Metric.ball x0 r)) :=
    u.memL2.sub (memLp_const _)
  have hG : MemLp (fun x => euclideanNorm (u.grad x)) 2 (volume.restrict (Metric.ball x0 r)) := by
    rw [← gradNorm_eq_euclideanNorm]; exact memLp_two_gradNorm u
  have hP := SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.normalizedL2On_metricBall_sub_average_le_vectorGradient
    x0 hr u
  unfold SubdiffusiveProcess.CoarseGrainingVocab.vectorNormalizedL2On at hP
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div hf,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div hG] at hP
  rw [gradNorm_eq_euclideanNorm]
  have hs : 0 < Real.sqrt ((volume (Metric.ball x0 r)).toReal) := Real.sqrt_pos.mpr hVpos
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hs] at hP
  exact hP

end SubdiffusiveProcess.Meyers
