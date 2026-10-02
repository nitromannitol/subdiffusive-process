import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveL2Endpoint
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

/-!
# Theta ladder: scale-zero point endpoint

This is the scale-one/small-contrast last step of the finite Campanato
telescope.  Unlike the nonpositive-parent specialization, the radius is kept
explicit; the positive-parent gradient event later supplies its deterministic
lower bound.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- Dimension/parent-scale price of the positive-parent scale-zero endpoint. -/
def positiveScaleZeroPointPrice (d m : ℕ) : ℝ :=
  let R := boundedMultiplierRadiusFloor d / (Real.sqrt (m : ℝ) + 1)
  smallContrastSchauderConstant d *
      boundedMultiplierCaccioppoliEndpointConst d *
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹) +
    Real.sqrt (((volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d)⁻¹)

theorem positiveScaleZeroPointPrice_nonneg (d m : ℕ) :
    0 ≤ positiveScaleZeroPointPrice d m := by
  unfold positiveScaleZeroPointPrice
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (smallContrastSchauderConstant_nonneg d)
        (boundedMultiplierCaccioppoliEndpointConst_nonneg d))
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- Point-to-scale-zero mean control at any admissible deterministic radius.
The two displayed square-root volume ratios are the only radius price. -/
theorem point_sub_scaleZeroMean_le_caccioppoli
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (omega : PotentialSample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {R : ℝ} (hR : 0 < R) (hRhalf : R ≤ 1 / 2)
    (hRmesh : R ≤ (6 : ℝ)⁻¹)
    (hRambient : R ≤ (3 : ℝ) ^ m / 4)
    (hRadaptive : R ≤ boundedMultiplierLocalRadius M L m z omega)
    (hunitParent : translatedCube d 0 x ⊆ translatedCube d m z)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) h) :
    |euclideanBallAverageRepresentative h.toFun x -
        averageOn (translatedCube d 0 x) h.toFun| ≤
      (smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
          Real.sqrt ((volume (translatedCube d 0 x)).toReal /
            (volume (euclideanBall x R)).toReal) +
        Real.sqrt ((volume (translatedCube d 0 x)).toReal /
          (volume (euclideanBall x (R / 4))).toReal)) *
        normalizedL2On (translatedCube d 0 x)
          (fun y ↦ h.toFun y - averageOn (translatedCube d 0 x) h.toFun) := by
  let Q := translatedCube d 0 x
  let P := euclideanBall x (R / 4)
  let A := averageOn Q h.toFun
  let g : Vec d → ℝ := fun y ↦ h.toFun y - A
  have hballQ : euclideanBall x R ⊆ Q := by
    intro y hy
    dsimp only [Q]
    rw [translatedCube_eq_metricBall]
    simpa using Metric.ball_subset_ball hRhalf
      (euclideanBall_subset_metricBall hR hy)
  have hPQ : P ⊆ Q := by
    dsimp only [P]
    exact (euclideanBall_subset_euclideanBall (by positivity) (by linarith)).trans
      hballQ
  have hQpos : 0 < (volume Q).toReal := by
    dsimp only [Q]
    exact volume_translatedCube_toReal_pos 0 x
  have hQtop : volume Q ≠ ⊤ := by
    dsimp only [Q]
    exact volume_translatedCube_ne_top 0 x
  have hBallPos : 0 < (volume (euclideanBall x R)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hR))
  have hPpos : 0 < (volume P).toReal := by
    dsimp only [P]
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x
        (by positivity : 0 < R / 4)))
  have hmemQ : MemLp h.toFun 2 (volume.restrict Q) :=
    h.memL2.mono_measure (Measure.restrict_mono hunitParent le_rfl)
  letI : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hQtop⟩
  have hfQ : IntegrableOn h.toFun Q := hmemQ.integrable one_le_two
  have hf2Q : IntegrableOn (fun y ↦ h.toFun y ^ 2) Q := hmemQ.integrable_sq
  have hg2Q : IntegrableOn (fun y ↦ g y ^ 2) Q := by
    have hlinear : IntegrableOn (fun y ↦ 2 * A * h.toFun y) Q :=
      hfQ.const_mul (2 * A)
    have hconst : IntegrableOn (fun _ : Vec d ↦ A ^ 2) Q :=
      integrableOn_const hQtop
    have hid : (fun y ↦ g y ^ 2) =
        fun y ↦ h.toFun y ^ 2 - 2 * A * h.toFun y + A ^ 2 := by
      funext y
      dsimp only [g]
      ring
    rw [hid]
    exact (hf2Q.sub hlinear).add hconst
  have hnormBall := Section6Iteration.normalizedL2On_le_of_subset
    hballQ hQpos hBallPos hg2Q
  have hpoint := localSubunit_point_sub_ballAverage_le_caccioppoli_of_radius
    hd M L m z omega hcollar hR hRmesh hRambient hRadaptive
      hthetaCont hb hthetaClose hharm A
  have hprice := halfBallCaccioppoliDataPrice_mul_halfRadius_eq_normalizedL2On
    (d := d) (x := x) hR h.toFun A
  have hpoint' :
      |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| ≤
        smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
          Real.sqrt ((volume Q).toReal /
            (volume (euclideanBall x R)).toReal) * normalizedL2On Q g := by
    have hscaled := mul_le_mul_of_nonneg_left hnormBall
      (mul_nonneg (smallContrastSchauderConstant_nonneg d)
        (boundedMultiplierCaccioppoliEndpointConst_nonneg d))
    calc
      |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| ≤
          smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d x R h.toFun A * (R / 2) := by
        have hquarter : (R / 2) / 2 = R / 4 := by ring
        simpa only [P, hquarter] using hpoint
      _ = smallContrastSchauderConstant d *
          (boundedMultiplierCaccioppoliEndpointConst d *
            normalizedL2On (euclideanBall x R) g) := by
        rw [← hprice]
        ring
      _ ≤ smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
          (Real.sqrt ((volume Q).toReal /
            (volume (euclideanBall x R)).toReal) * normalizedL2On Q g) := by
        simpa only [mul_assoc] using hscaled
      _ = _ := by ring
  have hmean := abs_averageOn_subset_sub_averageOn_le
    (isOpen_euclideanBall x (R / 4)).measurableSet hPQ hQtop hQpos hPpos
    hfQ hf2Q
  have htri := abs_sub_le (euclideanBallAverageRepresentative h.toFun x)
    (averageOn P h.toFun) (averageOn Q h.toFun)
  calc
    |euclideanBallAverageRepresentative h.toFun x - averageOn Q h.toFun| ≤
        |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| +
          |averageOn P h.toFun - averageOn Q h.toFun| := htri
    _ ≤ (smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
          Real.sqrt ((volume Q).toReal /
            (volume (euclideanBall x R)).toReal) +
        Real.sqrt ((volume Q).toReal / (volume P).toReal)) *
          normalizedL2On Q g := by
      calc
        _ ≤ (smallContrastSchauderConstant d *
              boundedMultiplierCaccioppoliEndpointConst d *
              Real.sqrt ((volume Q).toReal /
                (volume (euclideanBall x R)).toReal)) *
              normalizedL2On Q g +
            Real.sqrt ((volume Q).toReal / (volume P).toReal) *
              normalizedL2On Q g := add_le_add hpoint' hmean
        _ = _ := by ring
    _ = _ := by rfl

/-- Positive-parent specialization.  The deterministic radius loses only the
printed `sqrt m + 1` factor and is supplied by the parent restricted-gradient
good event. -/
theorem positiveParent_point_sub_scaleZeroMean_le
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L m : ℕ) (hm : 0 < m)
    (z : Vec d) (omega : PotentialSample d)
    (hgood : omega ∈ coveringRestrictedGradientGood M L (m : ℤ) z)
    {x : Vec d} (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d (m : ℤ) z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d (m : ℤ) z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d (m : ℤ) z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d (m : ℤ) z) h) :
    let R := boundedMultiplierRadiusFloor d / (Real.sqrt (m : ℝ) + 1)
    |euclideanBallAverageRepresentative h.toFun x -
        averageOn (translatedCube d 0 x) h.toFun| ≤
      (smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
          Real.sqrt ((volume (translatedCube d 0 x)).toReal /
            (volume (euclideanBall x R)).toReal) +
        Real.sqrt ((volume (translatedCube d 0 x)).toReal /
          (volume (euclideanBall x (R / 4))).toReal)) *
        normalizedL2On (translatedCube d 0 x)
          (fun y ↦ h.toFun y - averageOn (translatedCube d 0 x) h.toFun) := by
  dsimp only
  let R := boundedMultiplierRadiusFloor d / (Real.sqrt (m : ℝ) + 1)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hden : 1 ≤ Real.sqrt (m : ℝ) + 1 := by
    linarith [Real.sqrt_nonneg (m : ℝ)]
  have hdenPos : 0 < Real.sqrt (m : ℝ) + 1 := zero_lt_one.trans_le hden
  have hR : 0 < R := div_pos (boundedMultiplierRadiusFloor_pos d) hdenPos
  have hfloorMesh : boundedMultiplierRadiusFloor d ≤ (6 : ℝ)⁻¹ :=
    min_le_left _ _
  have hRmesh : R ≤ (6 : ℝ)⁻¹ := by
    rw [div_le_iff₀ hdenPos]
    have hmesh0 : 0 ≤ (6 : ℝ)⁻¹ := by positivity
    exact hfloorMesh.trans (by nlinarith)
  have hRhalf : R ≤ 1 / 2 := hRmesh.trans (by norm_num)
  have hparentScale : (3 / 4 : ℝ) ≤ (3 : ℝ) ^ m / 4 := by
    have hpow : (3 : ℝ) ≤ (3 : ℝ) ^ m := by
      have hpowMono := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm
      simpa only [pow_one] using hpowMono
    linarith
  have hRambient : R ≤ (3 : ℝ) ^ m / 4 :=
    hRmesh.trans ((by norm_num : (6 : ℝ)⁻¹ ≤ 3 / 4).trans hparentScale)
  have hRadaptive : R ≤ boundedMultiplierLocalRadius M L (m : ℤ) z omega := by
    simpa only [R] using
      boundedMultiplierRadiusFloor_div_sqrt_add_one_le_localRadius
        M L (by exact_mod_cast hm) z hgood
  have hunitParent : translatedCube d 0 x ⊆ translatedCube d (m : ℤ) z := by
    rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
    apply Metric.ball_subset_ball'
    rw [dist_eq_norm]
    have hpow : (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ m := zpow_natCast _ _
    rw [hpow]
    have hpowLower : (3 : ℝ) ≤ (3 : ℝ) ^ m := by
      have hmono := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm
      simpa only [pow_one] using hmono
    norm_num
    nlinarith
  simpa only [R] using point_sub_scaleZeroMean_le_caccioppoli
    hd M L (m : ℤ) z omega hcollar hR hRhalf hRmesh hRambient hRadaptive
      hunitParent hthetaCont hb hthetaClose hharm

/-- The previous endpoint with its radius dependence collected in the
dimension/parent-scale function `positiveScaleZeroPointPrice`. -/
theorem positiveParent_point_sub_scaleZeroMean_le_price
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L m : ℕ) (hm : 0 < m)
    (z : Vec d) (omega : PotentialSample d)
    (hgood : omega ∈ coveringRestrictedGradientGood M L (m : ℤ) z)
    {x : Vec d} (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d (m : ℤ) z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d (m : ℤ) z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d (m : ℤ) z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d (m : ℤ) z) h) :
    |euclideanBallAverageRepresentative h.toFun x -
        averageOn (translatedCube d 0 x) h.toFun| ≤
      positiveScaleZeroPointPrice d m *
        normalizedL2On (translatedCube d 0 x)
          (fun y ↦ h.toFun y - averageOn (translatedCube d 0 x) h.toFun) := by
  have hraw := positiveParent_point_sub_scaleZeroMean_le
    hd M L m hm z omega hgood hcollar hthetaCont hb hthetaClose hharm
  let R := boundedMultiplierRadiusFloor d / (Real.sqrt (m : ℝ) + 1)
  have hR : 0 < R := div_pos (boundedMultiplierRadiusFloor_pos d)
    (by linarith [Real.sqrt_nonneg (m : ℝ)])
  have hQ : (volume (translatedCube d 0 x)).toReal = 1 := by
    rw [volume_translatedCube_toReal]
    norm_num
  have hBall : (volume (euclideanBall x R)).toReal =
      (volume (smallContrastUnitBall d)).toReal * R ^ d :=
    volume_euclideanBall_toReal_eq_unit_mul_pow x hR
  have hQuarter : (volume (euclideanBall x (R / 4))).toReal =
      (volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d :=
    volume_euclideanBall_toReal_eq_unit_mul_pow x (by positivity)
  dsimp only at hraw
  rw [hQ, hBall, hQuarter, one_div] at hraw
  simpa only [positiveScaleZeroPointPrice, R, one_div] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
