import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalSubunitArbitraryRadius
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveCaccioppoliReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.OscillationSubsetReadout

/-!
# Deep-target readout at nonpositive parent scales
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- In the deep branch, the target oscillation is controlled directly by the
ambient oscillation, with the explicit square-root target/radius decay. -/
theorem exists_middleHalfSubcube_nonpositiveDeepOscillation
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    {m : ℤ} (hm : m ≤ 0) (z : Vec d) (j : ℕ)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube m z j B')
    (omega : PotentialSample d)
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    (hthetaPos : ∀ y ∈ translatedCube d m z, 0 < theta y)
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    (hfirst : 1 / 2 * (3 : ℝ) ^ (m - j) ≤
      (boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m) /
        (12 * (d : ℝ))) :
    ∃ n : ℕ,
      oscillationOn B' (euclideanBallAverageRepresentative h.toFun) ≤
        smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
          oscillationOn {y : Vec d | ‖y - z‖ ≤
            3 * (3 : ℝ) ^ m / 8}
            (euclideanBallAverageRepresentative h.toFun) *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ∧
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ≤
        Real.sqrt
          (36 * (d : ℝ) * (1 / 2 * (3 : ℝ) ^ (m - j)) /
            (boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m)) := by
  let R := boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m
  let r := 1 / 2 * (3 : ℝ) ^ (m - j)
  have hR : 0 < R := mul_pos
    (boundedMultiplierNonpositiveRadiusFloor_pos d) (by positivity)
  have hr : 0 < r := by dsimp only [r]; positivity
  obtain ⟨n, hfit, hdecay⟩ :=
    exists_subunitContractionDepth hR hr (by simpa only [R, r] using hfirst)
  obtain ⟨z', hB'eq, hcollar, htarget⟩ :=
    exists_middleHalfSubcube_center_and_subset_ball hB'
  obtain ⟨p, hp, hz'cell, hballCell, hcontract⟩ :=
    exists_coverCell_localSubunitContraction_caccioppoli_of_radius
      hd M L m z omega hcollar hR
      (by simpa only [R] using
        boundedMultiplierNonpositiveRadius_mul_le_mesh (d := d) hm)
      (by simpa only [R] using
        boundedMultiplierNonpositiveRadius_mul_le_ambient (d := d) (m := m))
      (by
        have hlower :=
          boundedMultiplierNonpositiveRadiusFloor_mul_zpow_le_localRadius
            (d := d) M L (m := m) hm z (omega := omega) hgood
        simpa only [R] using hlower)
      hthetaCont hb hthetaClose hharm
      (euclideanBallAverageRepresentative h.toFun z') n
  let radius := (R / 2) / (2 * (d : ℝ)) *
    (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))
  have htargetSub : B' ⊆ Metric.ball z' radius := by
    apply htarget
    simpa only [R, r, radius] using hfit
  let s : Vec d → ℝ := fun y ↦ aCutoff M L omega y * theta y
  have hsCont : ContinuousOn s (translatedCube d m z) :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hsPos : ∀ y ∈ translatedCube d m z, 0 < s y := by
    intro y hy
    exact mul_pos (aCutoff_pos M L omega y) (hthetaPos y hy)
  have hcubeOpen : IsOpen (translatedCube d m z) := by
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  have hrep := continuousOn_and_ae_eq_euclideanBallAverageRepresentative
    hd hcubeOpen hsCont hsPos hharm
  have hd0 : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpowPos : 0 < (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpowLt : (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact neg_lt_zero.mpr (by positivity)
  have hradiusR : radius < R / (2 * (d : ℝ)) := by
    dsimp only [radius]
    have hden : 0 < 2 * (d : ℝ) := mul_pos (by norm_num) hd0
    have hhalf : (R / 2) / (2 * (d : ℝ)) < R / (2 * (d : ℝ)) :=
      div_lt_div_of_pos_right (by linarith) hden
    exact (mul_lt_of_lt_one_right (by positivity) hpowLt).trans hhalf
  have hclosed : Metric.closedBall z' radius ⊆ translatedCube d m z := by
    have hclosedMetric : Metric.closedBall z' radius ⊆
        Metric.ball z' (R / (2 * (d : ℝ))) :=
      Metric.closedBall_subset_ball hradiusR
    have hmetric : Metric.ball z' (R / (2 * (d : ℝ))) ⊆
        euclideanBall z' ((d : ℝ) * (R / (2 * (d : ℝ)))) :=
      metricBall_subset_euclideanBall_dimension z' _
    have heq : (d : ℝ) * (R / (2 * (d : ℝ))) = R / 2 := by
      field_simp [hd0.ne']
    have heuc : euclideanBall z' ((d : ℝ) * (R / (2 * (d : ℝ)))) ⊆
        euclideanBall z' R := by
      rw [heq]
      exact euclideanBall_subset_euclideanBall (by positivity) (by linarith)
    exact hclosedMetric.trans (hmetric.trans (heuc.trans
      (hballCell.trans Set.inter_subset_left)))
  have hB'ne : B'.Nonempty := by
    refine ⟨z', ?_⟩
    rw [hB'eq, translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)
  have htargetOsc := oscillationOn_le_of_subset_metricBall hB'ne htargetSub
    (hrep.1.mono hclosed) hcontract
  have hprice :=
    halfBallCaccioppoliDataPrice_nonpositive_le_ambientOscillation
      hm hcollar hrep.1 hrep.2
  have hC0 : 0 ≤ smallContrastSchauderConstant d :=
    smallContrastSchauderConstant_nonneg d
  have hpow0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprice hC0) hpow0
  refine ⟨n, htargetOsc.trans ?_, ?_⟩
  · simpa only [R, mul_assoc] using hscaled
  · simpa only [R, r] using hdecay

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
