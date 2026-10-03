module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveL2Endpoint
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitRadiusAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

@[expose] public section

/-!
# Scale-zero pointwise readout

This file supplies the deterministic endpoint used at the bottom of the
positive-scale Campanato telescope.  The adaptive small-contrast ball is
compared with the unit cube centred at the same physical point.  Its only
price is the explicit inverse square-root volume factor of the adaptive
radius.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- Dimension and radius dependent price in the scale-zero pointwise
readout. -/
def boundedMultiplierScaleZeroL2Price (d : ℕ) (R : ℝ) : ℝ :=
  smallContrastSchauderConstant d *
      boundedMultiplierCaccioppoliEndpointConst d *
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹) +
    Real.sqrt (((volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d)⁻¹)

theorem boundedMultiplierScaleZeroL2Price_nonneg (d : ℕ) (R : ℝ) :
    0 ≤ boundedMultiplierScaleZeroL2Price d R := by
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (smallContrastSchauderConstant_nonneg d)
        (boundedMultiplierCaccioppoliEndpointConst_nonneg d))
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- Enlarging the adaptive radius can only decrease its inverse-volume
price. -/
theorem boundedMultiplierScaleZeroL2Price_antitone
    {d : ℕ} [NeZero d] {R₀ R : ℝ}
    (hR₀ : 0 < R₀) (hR : 0 < R) (hR₀R : R₀ ≤ R) :
  boundedMultiplierScaleZeroL2Price d R ≤
      boundedMultiplierScaleZeroL2Price d R₀ := by
  have hunit : 0 < (volume (smallContrastUnitBall d)).toReal := by
    unfold smallContrastUnitBall
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num : (0 : ℝ) < 1)))
  have hpow : R₀ ^ d ≤ R ^ d := pow_le_pow_left₀ hR₀.le hR₀R d
  have hden :
      (volume (smallContrastUnitBall d)).toReal * R₀ ^ d ≤
        (volume (smallContrastUnitBall d)).toReal * R ^ d :=
    mul_le_mul_of_nonneg_left hpow hunit.le
  have hden₀ : 0 < (volume (smallContrastUnitBall d)).toReal * R₀ ^ d :=
    mul_pos hunit (pow_pos hR₀ d)
  have hdenR : 0 < (volume (smallContrastUnitBall d)).toReal * R ^ d :=
    mul_pos hunit (pow_pos hR d)
  have hinv :
      ((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹ ≤
        ((volume (smallContrastUnitBall d)).toReal * R₀ ^ d)⁻¹ :=
    (inv_le_inv₀ hdenR hden₀).2 hden
  have hroot := Real.sqrt_le_sqrt hinv
  have hquarter : R₀ / 4 ≤ R / 4 := div_le_div_of_nonneg_right hR₀R (by norm_num)
  have hpowQuarter : (R₀ / 4) ^ d ≤ (R / 4) ^ d :=
    pow_le_pow_left₀ (by positivity) hquarter d
  have hdenQuarter :
      (volume (smallContrastUnitBall d)).toReal * (R₀ / 4) ^ d ≤
        (volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d :=
    mul_le_mul_of_nonneg_left hpowQuarter hunit.le
  have hdenQuarter₀ :
      0 < (volume (smallContrastUnitBall d)).toReal * (R₀ / 4) ^ d :=
    mul_pos hunit (pow_pos (by positivity) d)
  have hdenQuarterR :
      0 < (volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d :=
    mul_pos hunit (pow_pos (by positivity) d)
  have hinvQuarter :
      ((volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d)⁻¹ ≤
        ((volume (smallContrastUnitBall d)).toReal * (R₀ / 4) ^ d)⁻¹ :=
    (inv_le_inv₀ hdenQuarterR hdenQuarter₀).2 hdenQuarter
  have hrootQuarter := Real.sqrt_le_sqrt hinvQuarter
  unfold boundedMultiplierScaleZeroL2Price
  exact add_le_add
    (mul_le_mul_of_nonneg_left hroot
      (mul_nonneg (smallContrastSchauderConstant_nonneg d)
        (boundedMultiplierCaccioppoliEndpointConst_nonneg d)))
    hrootQuarter

/-- On the restricted gradient-good event, the scale-zero price is bounded
by its explicit square-root-parent-growth radius floor. -/
theorem boundedMultiplierScaleZeroL2Price_le_of_restrictedGradientGood
    {d : ℕ} [NeZero d] (M : GMCModel d) (L : ℕ) {m : ℕ} (hm : 0 < m)
    (z : Vec d) {omega : PotentialSample d}
    (hgood : omega ∈ coveringRestrictedGradientGood M L (m : ℤ) z) :
    boundedMultiplierScaleZeroL2Price d
        (boundedMultiplierLocalRadius M L (m : ℤ) z omega) ≤
      boundedMultiplierScaleZeroL2Price d
        (boundedMultiplierRadiusFloor d / (Real.sqrt (m : ℝ) + 1)) := by
  have hden : 0 < Real.sqrt (m : ℝ) + 1 := by
    linarith [Real.sqrt_nonneg (m : ℝ)]
  have hfloor : 0 < boundedMultiplierRadiusFloor d :=
    boundedMultiplierRadiusFloor_pos d
  apply boundedMultiplierScaleZeroL2Price_antitone
    (div_pos hfloor hden)
    (boundedMultiplierLocalRadius_pos M L (m : ℤ) z omega)
  simpa only [Int.cast_natCast] using
    boundedMultiplierRadiusFloor_div_sqrt_add_one_le_localRadius
      M L (m := (m : ℤ)) (by exact_mod_cast hm) z hgood

private theorem translatedUnitCube_subset_parent
    {m : ℕ} (hm : 0 < m) {z x : Vec d}
    (hx : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4) :
    translatedCube d 0 x ⊆ translatedCube d (m : ℤ) z := by
  rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
  apply Metric.ball_subset_ball'
  rw [dist_eq_norm, zpow_natCast]
  have hpow : 3 ≤ (3 : ℝ) ^ m := by
    calc
      (3 : ℝ) = 3 ^ (1 : ℕ) := by norm_num
      _ ≤ 3 ^ m := pow_le_pow_right₀ (a := (3 : ℝ)) (m := 1) (n := m)
        (by norm_num) (by omega)
  norm_num
  nlinarith

private theorem euclideanBall_subset_translatedUnitCube
    {x : Vec d} {R : ℝ} (hR : 0 < R) (hRmesh : R ≤ (6 : ℝ)⁻¹) :
    euclideanBall x R ⊆ translatedCube d 0 x := by
  rw [translatedCube_eq_metricBall]
  exact (euclideanBall_subset_metricBall hR).trans
    (Metric.ball_subset_ball (by norm_num at hRmesh ⊢; linarith))

private theorem scaleZero_outer_volumeRatio [NeZero d]
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    (volume (translatedCube d 0 x)).toReal /
        (volume (euclideanBall x R)).toReal =
      ((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹ := by
  rw [volume_translatedCube_toReal,
    volume_euclideanBall_toReal_eq_unit_mul_pow x hR]
  norm_num

private theorem scaleZero_inner_volumeRatio [NeZero d]
    (x : Vec d) {R : ℝ} (hR : 0 < R) :
    (volume (translatedCube d 0 x)).toReal /
        (volume (euclideanBall x (R / 4))).toReal =
      ((volume (smallContrastUnitBall d)).toReal * (R / 4) ^ d)⁻¹ := by
  rw [volume_translatedCube_toReal,
    volume_euclideanBall_toReal_eq_unit_mul_pow x (by positivity : 0 < R / 4)]
  norm_num

/-- At every collared point of a positive-scale parent, the canonical
representative differs from its own centred unit-cube average by the
adaptive-radius price times the centred normalized `L²` oscillation on that
unit cube. -/
theorem scaleZero_point_sub_centeredAverage_le_normalizedL2
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    {m : ℕ} (hm : 0 < m) (z : Vec d)
    (omega : PotentialSample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d (m : ℤ) z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d (m : ℤ) z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d (m : ℤ) z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d (m : ℤ) z) h) :
    let R := boundedMultiplierLocalRadius M L (m : ℤ) z omega
    |euclideanBallAverageRepresentative h.toFun x -
        averageOn (translatedCube d 0 x) h.toFun| ≤
      boundedMultiplierScaleZeroL2Price d R *
        normalizedL2On (translatedCube d 0 x)
          (fun y ↦ h.toFun y - averageOn (translatedCube d 0 x) h.toFun) := by
  dsimp only
  let Q := translatedCube d 0 x
  let A := averageOn Q h.toFun
  let R := boundedMultiplierLocalRadius M L (m : ℤ) z omega
  let P := euclideanBall x (R / 4)
  let g : Vec d → ℝ := fun y ↦ h.toFun y - A
  have hR : 0 < R := by
    simpa only [R] using boundedMultiplierLocalRadius_pos M L (m : ℤ) z omega
  have hRmesh : R ≤ (6 : ℝ)⁻¹ := by
    simpa only [R] using
      boundedMultiplierLocalRadius_le_mesh M L (m : ℤ) z omega
  have hQB : Q ⊆ translatedCube d (m : ℤ) z := by
    simpa only [Q] using translatedUnitCube_subset_parent hm hcollar
  have hballQ : euclideanBall x R ⊆ Q := by
    simpa only [Q] using euclideanBall_subset_translatedUnitCube hR hRmesh
  have hPQ : P ⊆ Q := by
    exact (euclideanBall_subset_euclideanBall (by positivity)
      (by linarith [hR])).trans hballQ
  have hQpos : 0 < (volume Q).toReal := by
    dsimp only [Q]
    exact volume_translatedCube_toReal_pos 0 x
  have hQtop : volume Q ≠ ⊤ := by
    apply ne_of_lt
    dsimp only [Q]
    rw [translatedCube, cube,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq]
    exact volume_openCubeSet_lt_top (originCube d 0)
  have hRballPos : 0 < (volume (euclideanBall x R)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hR))
  have hPpos : 0 < (volume P).toReal := by
    dsimp only [P]
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x
        (by positivity : 0 < R / 4)))
  letI : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr hQtop⟩
  have hmemQ : MemLp h.toFun 2 (volume.restrict Q) :=
    h.memL2.mono_measure (Measure.restrict_mono hQB le_rfl)
  have hfQ : IntegrableOn h.toFun Q := hmemQ.integrable one_le_two
  have hf2Q : IntegrableOn (fun y ↦ h.toFun y ^ 2) Q := hmemQ.integrable_sq
  have hconstQ : MemLp (fun _ : Vec d ↦ A) 2 (volume.restrict Q) :=
    memLp_const A
  have hg2Q : IntegrableOn (fun y ↦ g y ^ 2) Q :=
    (hmemQ.sub hconstQ).integrable_sq
  have hnormBall := normalizedL2On_le_of_subset
    hballQ hQpos hRballPos hg2Q
  have houterRatio : Real.sqrt ((volume Q).toReal /
        (volume (euclideanBall x R)).toReal) =
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹) := by
    rw [scaleZero_outer_volumeRatio x hR]
  rw [houterRatio] at hnormBall
  have hpoint := localSubunit_point_sub_ballAverage_le_caccioppoli_of_radius
    hd M L (m : ℤ) z omega hcollar hR hRmesh
    (by simpa only [R] using
      boundedMultiplierLocalRadius_le_ambient M L (m : ℤ) z omega)
    (by rfl : R ≤ boundedMultiplierLocalRadius M L (m : ℤ) z omega)
    hthetaCont hb hthetaClose hharm A
  have hprice := halfBallCaccioppoliDataPrice_mul_halfRadius_eq_normalizedL2On
    (d := d) (x := x) hR h.toFun A
  have hpoint' :
      |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| ≤
        smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹) *
              normalizedL2On Q g := by
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
          boundedMultiplierCaccioppoliEndpointConst d *
            normalizedL2On (euclideanBall x R) g := by
        change smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d x R h.toFun A * (R / 2) =
          smallContrastSchauderConstant d *
            boundedMultiplierCaccioppoliEndpointConst d *
              normalizedL2On (euclideanBall x R) (fun y ↦ h.toFun y - A)
        calc
          _ = smallContrastSchauderConstant d *
              (halfBallCaccioppoliDataPrice d x R h.toFun A * (R / 2)) := by ring
          _ = smallContrastSchauderConstant d *
              (boundedMultiplierCaccioppoliEndpointConst d *
                normalizedL2On (euclideanBall x R)
                  (fun y ↦ h.toFun y - A)) := by rw [hprice]
          _ = _ := by ring
      _ ≤ smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            (Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹) *
              normalizedL2On Q g) := by
        exact hscaled
      _ = smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹) *
              normalizedL2On Q g := by ring
  have hmean := abs_averageOn_subset_sub_averageOn_le
    (isOpen_euclideanBall x (R / 4)).measurableSet hPQ
    hQtop hQpos hPpos hfQ hf2Q
  have hinnerRatio : Real.sqrt ((volume Q).toReal / (volume P).toReal) =
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
        (R / 4) ^ d)⁻¹) := by
    dsimp only [P]
    rw [scaleZero_inner_volumeRatio x hR]
  rw [hinnerRatio] at hmean
  have htri := abs_sub_le (euclideanBallAverageRepresentative h.toFun x)
    (averageOn P h.toFun) (averageOn Q h.toFun)
  calc
    |euclideanBallAverageRepresentative h.toFun x - averageOn Q h.toFun| ≤
        |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| +
          |averageOn P h.toFun - averageOn Q h.toFun| := htri
    _ ≤ boundedMultiplierScaleZeroL2Price d R * normalizedL2On Q g := by
      calc
        _ ≤ (smallContrastSchauderConstant d *
              boundedMultiplierCaccioppoliEndpointConst d *
                Real.sqrt (((volume (smallContrastUnitBall d)).toReal * R ^ d)⁻¹)) *
              normalizedL2On Q g +
            Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
              (R / 4) ^ d)⁻¹) * normalizedL2On Q g :=
          add_le_add hpoint' hmean
        _ = _ := by
          unfold boundedMultiplierScaleZeroL2Price
          ring
    _ = boundedMultiplierScaleZeroL2Price d R *
        normalizedL2On (translatedCube d 0 x)
          (fun y ↦ h.toFun y -
            averageOn (translatedCube d 0 x) h.toFun) := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
