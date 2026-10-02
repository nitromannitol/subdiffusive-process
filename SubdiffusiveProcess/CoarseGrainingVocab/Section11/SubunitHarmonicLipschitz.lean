import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzScaling
import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzConstant
import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzGeometry

/-!
# Harmonic Lipschitz bounds from scaled logarithmic coefficient control

On balls of radius `side * interiorContrastFraction d H`, relative coefficient
oscillations decay geometrically. The exact harmonic-comparison estimate gives
uniform gradient averages and hence the Lipschitz endpoint of the Campanato
estimate. Caccioppoli, Lebesgue normalization and finite convex chaining give
the cube estimate, with an explicit `C(d) * exp (C(d) * H)` constant.

The cube side is any positive real number.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open Homogenization hiding cubeSet
open MeasureTheory Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section

/-- The local Lipschitz estimate for the given continuous weakly harmonic function. -/
theorem harmonic_lipschitz_on_local_ball {d : ℕ} [NeZero d]
 {a h : Vec d → ℝ} {H : ℝ} {U : Cube d} (hU : 0 < U.2)
 (hctrl : LogCoefficientControlOn a H U) (hh : WeakHarmonic a (cubeSet U) h)
 (hmem : MemLp h 2 (volume.restrict (cubeSet U)))
 {x z w : Vec d} (hx : x ∈ SubdiffusiveProcess.Section9.centeredAxisCube U.1 (U.2/2))
 (hz : z ∈ euclideanBall x (U.2 * interiorContrastFraction d H / 2 / 2))
 (hw : w ∈ euclideanBall x (U.2 * interiorContrastFraction d H / 2 / 2)) :
 |h z-h w| ≤ interiorLipschitzPrice d H * (euclideanNorm (z-w)/U.2) *
 normalizedL2On (cubeSet U) (fun y => h y-averageOn (cubeSet U) h) := by
  let R : ℝ := U.2 * interiorContrastFraction d H
  let L : ℝ := Real.sqrt d * (Real.sqrt H / U.2)
  have hf : 0 < interiorContrastFraction d H := interiorContrastFraction_pos d H
  have hR : 0 < R := mul_pos hU hf
  have hL : 0 ≤ L := by
    show 0 ≤ Real.sqrt d * (Real.sqrt H / U.2)
    positivity
  have hRsmall : R ≤ U.2/8 := by
    have hs := mul_le_mul_of_nonneg_left (interiorContrastFraction_le d H) hU.le
    have h8 : U.2 * (1/8:ℝ) = U.2/8 := by ring
    show U.2 * interiorContrastFraction d H ≤ U.2/8
    linarith
  have hclosed := closedBall_subset_cubeSet_of_mem_middleHalf hU hRsmall hx
  have hballQ : euclideanBall x R ⊆ cubeSet U :=
    (euclideanBall_subset_metricBall hR).trans
      (Metric.ball_subset_closedBall.trans hclosed)
  have hball2Q : euclideanBall x R ⊆ SubdiffusiveProcess.Section9.centeredAxisCube U.1 (2*U.2) :=
    hballQ.trans (cubeSet_subset_double hU.le)
  have hWopen : IsOpen (euclideanBall x R) := isOpen_euclideanBall x R
  have hWbdd : Bornology.IsBounded (euclideanBall x R) :=
    Metric.isBounded_ball.subset (euclideanBall_subset_metricBall hR)
  have hWclos : closure (euclideanBall x R) ⊆ cubeSet U :=
    (closure_mono (euclideanBall_subset_metricBall hR)).trans
      (Metric.closure_ball_subset_closedBall.trans hclosed)
  obtain ⟨u, huAE, huTest⟩ := hh.2 (euclideanBall x R) hWopen hWbdd.isCompact_closure hWclos
  have hu : IsWeaklyHarmonicOn a (euclideanBall x R) u := by
    intro phi
    simpa only [vecDot_smul_left] using huTest phi
  have ha : ContinuousOn a (euclideanBall x R) :=
    (contDiffOn_of_logCoefficientControlOn hctrl).continuousOn.mono hball2Q
  have hpos : ∀ y ∈ euclideanBall x R, 0 < a y := fun y hy => hctrl.1 y (hball2Q hy)
  have hlog : ∀ y ∈ euclideanBall x R, ∀ v ∈ euclideanBall x R,
      |Real.log (a v)-Real.log (a y)| ≤ L*‖v-y‖ := by
    intro y hy v hv
    exact abs_log_sub_le_of_logCoefficientControlOn hU hctrl (hball2Q hy) (hball2Q hv)
  have hLs : L*R ≤ smallContrastThreshold d (1/2:ℝ)/8 := log_lipschitz_radius_guard hU
  obtain ⟨g, hgcont, hgae, hholder⟩ :=
    exists_lipschitz_representative_of_log_lipschitz_caccioppoli hR hL hLs ha hpos hlog hu
      (averageOn (cubeSet U) h)
  have hsmall : euclideanBall x (R/2/2) ⊆ euclideanBall x R :=
    euclideanBall_subset_euclideanBall (by linarith) (by linarith)
  have hgh : g =ᵐ[volume.restrict (euclideanBall x (R/2/2))] h :=
    hgae.trans (huAE.filter_mono (ae_mono (Measure.restrict_mono hsmall le_rfl)))
  have hEq : Set.EqOn g h (euclideanBall x (R/2/2)) :=
    Measure.eqOn_open_of_ae_eq hgh (isOpen_euclideanBall x (R/2/2)) hgcont
      (hh.1.mono (hsmall.trans hballQ))
  have hloc := hholder z hz w hw
  rw [hEq hz, hEq hw, Real.rpow_one] at hloc
  have hnormEq : normalizedL2On (euclideanBall x R)
      (fun y => u.toFun y-averageOn (cubeSet U) h) =
      normalizedL2On (euclideanBall x R) (fun y => h y-averageOn (cubeSet U) h) := by
    apply Section9Support.WeightedLocalHarmonic.normalizedL2On_congr_ae
    filter_upwards [huAE] with y hy
    rw [hy]
  have hnorm := normalizedL2On_ball_le_cube hU hf (show R=U.2*interiorContrastFraction d H from rfl)
    hballQ hmem
  rw [← hnormEq] at hnorm
  have hpriceEq := halfBallCaccioppoliDataPrice_mul_halfRadius_eq_normalizedL2On (x := x) hR u.toFun
    (averageOn (cubeSet U) h)
  have hprice := lipschitz_price_from_caccioppoli hU hf (unitLipschitzPrice_nonneg d)
    (boundedMultiplierCaccioppoliEndpointConst_nonneg d) (euclideanNorm_nonneg (z-w)) hpriceEq hnorm
  exact hloc.trans hprice

/-- The harmonic Lipschitz display under scaled logarithmic coefficient control,
valid on the middle quarter of every cube of positive side. -/
theorem harmonic_lipschitz_of_logCoefficientControlOn (d : ℕ) (hd : 2 ≤ d)
 {a h : Vec d → ℝ} {H : ℝ} {U : Cube d} (hU : 0 < U.2)
 (hctrl : LogCoefficientControlOn a H U) (hh : WeakHarmonic a (cubeSet U) h)
 (hL2 : MemLp h 2 (volume.restrict (cubeSet U))) :
 ∀ z ∈ middleQuarter U, ∀ w ∈ middleQuarter U,
 |h z-h w| ≤ harmonicLipschitzConstant d * Real.exp (harmonicLipschitzConstant d * H) *
 (euclideanNorm (z-w)/U.2) * normalizedL2On (cubeSet U) (fun y => h y-averageOn (cubeSet U) h) := by
  letI : NeZero d := ⟨by omega⟩
  let R : ℝ := U.2 * interiorContrastFraction d H / 2 / 2
  let K : ℝ := interiorLipschitzPrice d H / U.2 *
    normalizedL2On (cubeSet U) (fun y => h y-averageOn (cubeSet U) h)
  have hR : 0 < R := by
    have hpos := interiorContrastFraction_pos d H
    dsimp only [R]
    positivity
  have hconv : Convex ℝ (middleQuarter U) := convex_axisCube _ _
  have hlocal : ∀ x ∈ middleQuarter U, ∀ y ∈ middleQuarter U,
      euclideanNorm (x-y) < R → |h x-h y| ≤ K*euclideanNorm (x-y) := by
    intro x hx y hy hxy
    have hxhalf : x ∈ SubdiffusiveProcess.Section9.centeredAxisCube U.1 (U.2/2) := by
      apply Section9Support.mem_centeredAxisCube.mpr
      intro i
      have hi := Section9Support.mem_centeredAxisCube.mp hx i
      linarith
    have hxx : x ∈ euclideanBall x R := Section6Schauder.mem_euclideanBall_self hR
    have hyx : y ∈ euclideanBall x R := by
      apply mem_euclideanBall_of_euclideanNorm_lt hR
      change euclideanDist y x < R
      rw [euclideanDist_comm]
      exact hxy
    have hl := harmonic_lipschitz_on_local_ball hU hctrl hh hL2 hxhalf hxx hyx
    convert hl using 1
    dsimp only [K]
    ring
  intro z hz w hw
  have hg := abs_sub_le_of_uniform_local hconv hR hlocal hz hw
  have hp := interiorLipschitzPrice_le (d := d) (one_le_of_logCoefficientControlOn hctrl)
  calc |h z-h w| ≤ interiorLipschitzPrice d H * (euclideanNorm (z-w)/U.2) *
      normalizedL2On (cubeSet U) (fun y => h y-averageOn (cubeSet U) h) := by
        convert hg using 1
        dsimp only [K]
        ring
    _ ≤ harmonicLipschitzConstant d * Real.exp (harmonicLipschitzConstant d * H) *
      (euclideanNorm (z-w)/U.2) * normalizedL2On (cubeSet U) (fun y => h y-averageOn (cubeSet U) h) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (div_nonneg (euclideanNorm_nonneg _) hU.le))
        (Real.sqrt_nonneg _)
end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
