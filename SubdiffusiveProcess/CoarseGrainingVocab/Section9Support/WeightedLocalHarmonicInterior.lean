module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicScaledContrast
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveL2Endpoint
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastLocalRegularity

@[expose] public section

/-!
# The interior display of `l.weighted.local.harmonic` v4

`e.weighted.local.harmonic.interior` asks, for `B' ⊆` the middle half of `B`,

    sup_{B'} |h - (h)_B| ≤ C ‖h - (h)_B‖_{L̲²(B)}

for every `a`-harmonic `h` on `B`, with `C` bound *before* the geometry.  v4
supplies the two hypotheses that make this true: the inner cube in the middle
half, and the scale-invariant `FamilyLogCoefficientControl a H Qfam`.

This module proves the display at a single cube, from `LogCoefficientControlOn`
alone. The route is to localize
to a radius on which the coefficient contrast is dimensional, apply the
small-contrast interior theory there, and pay a covering price that depends only
on `d` and `H`:

* `abs_log_sub_le_of_logCoefficientControlOn` — the scaled control makes `log a`
  Lipschitz on the double cube with constant `√d·√H/size`;
* `abs_inv_mul_sub_one_le_of_logCoefficientControlOn` — hence the contrast on a
  ball of radius `size · interiorContrastFraction d H` is below the Schauder
  threshold, *uniformly in the scale*;
* `abs_sub_averageOn_le_interiorHarmonicConstant` — the display itself.

No De Giorgi–Nash–Moser is used: the small-contrast Schauder estimate
(`SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.canonicalRepresentative_sub_ballAverage_le_of_smallContrast`)
together with the ball Caccioppoli price is what closes it, and both are
quantitative in the contrast rather than in `sup a / inf a` globally.
-/

set_option autoImplicit false
open Homogenization hiding cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab (normalizedL2On averageOn)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support (mem_centeredAxisCube)
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic

variable {d : ℕ}

/-! ## The coefficient layer -/

/-- The scaled control makes `log a` Lipschitz on the double cube with constant
`√d · √H / size`.  Nothing here is a bound on `sup a / inf a`. -/
theorem abs_log_sub_le_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ}
    {B : Cube d} (hB : 0 < B.2) (hctrl : LogCoefficientControlOn a H B)
    {x y : Vec d} (hx : x ∈ centeredAxisCube B.1 (2 * B.2))
    (hy : y ∈ centeredAxisCube B.1 (2 * B.2)) :
    |Real.log (a y) - Real.log (a x)| ≤
      Real.sqrt d * (Real.sqrt H / B.2) * ‖y - x‖ := by
  obtain ⟨_hpos, G, K, _hG, hK, hdiff, hgrad, _hholder, hscale⟩ := hctrl
  have hconv : Convex ℝ (centeredAxisCube B.1 (2 * B.2)) := convex_axisCube _ _
  have hbd : ∀ z ∈ centeredAxisCube B.1 (2 * B.2),
      ‖fderiv ℝ (fun w => Real.log (a w)) z‖ ≤ Real.sqrt d * G := by
    intro z hz
    refine (norm_fderiv_le_sqrt_card_mul_euclideanNorm (fun w => Real.log (a w)) z).trans ?_
    exact mul_le_mul_of_nonneg_left (hgrad z hz) (Real.sqrt_nonneg _)
  have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := fun w => Real.log (a w)) (fun z hz => hdiff z hz) hbd hx hy
  have hGB : G ≤ Real.sqrt H / B.2 := by
    have hsq : (B.2 * G) ^ 2 ≤ H := by
      nlinarith [mul_nonneg (sq_nonneg B.2) hK]
    have h1 : B.2 * G ≤ Real.sqrt H := by
      calc B.2 * G = Real.sqrt ((B.2 * G) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt H := Real.sqrt_le_sqrt hsq
    rw [le_div_iff₀ hB]
    linarith
  refine (Real.norm_eq_abs _ ▸ hmean).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hGB (Real.sqrt_nonneg _)) (norm_nonneg _)

/-- At radius `r` with `√d·√H·r/size ≤ delta/2 ≤ 1`, the coefficient normalized at
the centre of the ball has contrast at most `delta` on it. -/
theorem abs_inv_mul_sub_one_le_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ}
    {B : Cube d} (hB : 0 < B.2) (hctrl : LogCoefficientControlOn a H B)
    {x : Vec d} {r delta : ℝ} (hr : 0 < r)
    (hx : x ∈ centeredAxisCube B.1 (2 * B.2))
    (hball : euclideanBall x r ⊆ centeredAxisCube B.1 (2 * B.2))
    (hsmall : Real.sqrt d * (Real.sqrt H / B.2) * r ≤ delta / 2)
    (hdelta : delta ≤ 2) :
    ∀ y ∈ euclideanBall x r, |(a x)⁻¹ * a y - 1| ≤ delta := by
  intro y hy
  have hyc := hball hy
  have hlog := abs_log_sub_le_of_logCoefficientControlOn hB hctrl hx hyc
  have hdist : ‖y - x‖ < r := by
    have := euclideanBall_subset_metricBall hr hy
    rwa [mem_ball_iff_norm] at this
  have hkey : |Real.log (a y) - Real.log (a x)| ≤ delta / 2 := by
    refine hlog.trans (le_trans ?_ hsmall)
    exact mul_le_mul_of_nonneg_left hdist.le (by positivity)
  have hax : 0 < a x := hctrl.1 x hx
  have hay : 0 < a y := hctrl.1 y hyc
  have heq : (a x)⁻¹ * a y = Real.exp (Real.log (a y) - Real.log (a x)) := by
    rw [Real.exp_sub, Real.exp_log hay, Real.exp_log hax]
    field_simp
  rw [heq]
  have h1 : |Real.log (a y) - Real.log (a x)| ≤ 1 := by linarith
  have h2 := Real.abs_exp_sub_one_le h1
  linarith

/-! ## The localization radius and the interior constant -/

theorem smallContrastThreshold_half_pos (d : ℕ) :
    0 < smallContrastThreshold d (1 / 2 : ℝ) := by
  have h : (0 : ℝ) < (2 : ℝ) ^ (-(3 + (d : ℝ) / 2)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold smallContrastThreshold
  nlinarith

theorem smallContrastThreshold_half_le_sixteenth (d : ℕ) :
    smallContrastThreshold d (1 / 2 : ℝ) ≤ 1 / 16 := by
  have h := smallContrastThreshold_le_eighth_gap d (by norm_num : (1 / 2 : ℝ) ≤ 1)
  linarith

/-- The fraction of the side length at which `LogCoefficientControlOn a H B` forces
the coefficient contrast below the small-contrast Schauder threshold.

Because the hypothesis bounds `size² |∇log a|²` rather than `|∇log a|²`, this
fraction depends only on `d` and `H` — never on the scale.  That is what makes the
constant of the interior display uniform over the family. -/
def interiorContrastFraction (d : ℕ) (H : ℝ) : ℝ :=
  smallContrastThreshold d (1 / 2 : ℝ) / (8 * (1 + Real.sqrt d * Real.sqrt H))

theorem interiorContrastFraction_pos (d : ℕ) (H : ℝ) :
    0 < interiorContrastFraction d H := by
  have hs : 0 ≤ Real.sqrt d * Real.sqrt H :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact div_pos (smallContrastThreshold_half_pos d) (by linarith)

theorem interiorContrastFraction_le (d : ℕ) (H : ℝ) :
    interiorContrastFraction d H ≤ 1 / 128 := by
  have hs : 0 ≤ Real.sqrt d * Real.sqrt H :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hden : (0 : ℝ) < 8 * (1 + Real.sqrt d * Real.sqrt H) := by linarith
  have hnum := smallContrastThreshold_half_le_sixteenth d
  rw [interiorContrastFraction, div_le_iff₀ hden]
  nlinarith

/-- The constant of the interior estimate for the weighted local harmonic function, depending only on `d` and
on the scaled coefficient bound `H`.

The first summand is the small-contrast Schauder price times the ball Caccioppoli
price times the cost of passing from the localization ball to the whole cube; the
second is the cost of replacing the average over the localization ball by the
average over the cube. -/
def interiorHarmonicConstant (d : ℕ) (H : ℝ) : ℝ :=
  smallContrastSchauderConstant d * boundedMultiplierCaccioppoliEndpointConst d *
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
        interiorContrastFraction d H ^ d)⁻¹) +
    Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
      (interiorContrastFraction d H / 4) ^ d)⁻¹)

theorem interiorHarmonicConstant_nonneg (d : ℕ) (H : ℝ) :
    0 ≤ interiorHarmonicConstant d H :=
  add_nonneg
    (mul_nonneg
      (mul_nonneg (smallContrastSchauderConstant_nonneg d)
        (boundedMultiplierCaccioppoliEndpointConst_nonneg d))
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem volume_smallContrastUnitBall_toReal_pos (d : ℕ) [NeZero d] :
    0 < (volume (smallContrastUnitBall d)).toReal := by
  have hball := Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
    (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
  simpa only [smallContrastUnitBall] using
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hball)

/-! ## Volume bookkeeping -/

theorem volume_cubeSet_toReal {B : Cube d} (hB : 0 ≤ B.2) :
    (volume (cubeSet B)).toReal = B.2 ^ d :=
  SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal B.1 hB

theorem volume_cubeSet_ne_top {B : Cube d} : volume (cubeSet B) ≠ ⊤ :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.volume_axisCube_ne_top
    (fun i => B.1 i - B.2 / 2) B.2

theorem interior_volumeRatio [NeZero d] {B : Cube d} (hB : 0 < B.2)
    (x : Vec d) {s r : ℝ} (hs : 0 < s) (hr : r = B.2 * s) :
    (volume (cubeSet B)).toReal / (volume (euclideanBall x r)).toReal =
      ((volume (smallContrastUnitBall d)).toReal * s ^ d)⁻¹ := by
  have hrpos : 0 < r := by rw [hr]; positivity
  have hunit : 0 < (volume (smallContrastUnitBall d)).toReal :=
    volume_smallContrastUnitBall_toReal_pos d
  have hBd : (0 : ℝ) < B.2 ^ d := by positivity
  have hsd : (0 : ℝ) < s ^ d := by positivity
  rw [volume_cubeSet_toReal hB.le,
    volume_euclideanBall_toReal_eq_unit_mul_pow x hrpos, hr, mul_pow]
  field_simp

/-! ## Almost-everywhere congruence of the normalized quantities -/

theorem volumeAverage_congr_ae {W : Set (Vec d)} {f₁ f₂ : Vec d → ℝ}
    (hfg : f₁ =ᵐ[volume.restrict W] f₂) :
    volumeAverage W f₁ = volumeAverage W f₂ := by
  unfold volumeAverage
  rw [integral_congr_ae hfg]

theorem averageOn_congr_ae {W : Set (Vec d)} {f₁ f₂ : Vec d → ℝ}
    (hfg : f₁ =ᵐ[volume.restrict W] f₂) : averageOn W f₁ = averageOn W f₂ :=
  volumeAverage_congr_ae hfg

theorem normalizedL2On_congr_ae {W : Set (Vec d)} {f₁ f₂ : Vec d → ℝ}
    (hfg : f₁ =ᵐ[volume.restrict W] f₂) :
    normalizedL2On W f₁ = normalizedL2On W f₂ := by
  unfold normalizedL2On
  refine congrArg Real.sqrt (volumeAverage_congr_ae (hfg.mono (fun y hy => ?_)))
  show f₁ y ^ 2 = f₂ y ^ 2
  rw [hy]

/-! ## The interior display at one cube -/



theorem abs_sub_averageOn_le_interiorHarmonicConstant [NeZero d] (hd : 2 ≤ d)
    {a : Vec d → ℝ} {H : ℝ} {B : Cube d} (hB : 0 < B.2)
    (hctrl : LogCoefficientControlOn a H B)
    {h : Vec d → ℝ} (hharm : WeakHarmonic a (cubeSet B) h)
    (hmem : MemLp h 2 (volume.restrict (cubeSet B)))
    {x : Vec d} (hx : x ∈ centeredAxisCube B.1 (B.2 / 2)) :
    |h x - averageOn (cubeSet B) h| ≤
      interiorHarmonicConstant d H *
        normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
  have hfrpos : 0 < interiorContrastFraction d H := interiorContrastFraction_pos d H
  have hfrle : interiorContrastFraction d H ≤ 1 / 128 := interiorContrastFraction_le d H
  obtain ⟨R, hRfrac⟩ : ∃ R : ℝ, R = B.2 * interiorContrastFraction d H := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRfrac]; positivity
  have hRsmall : R ≤ B.2 / 128 := by rw [hRfrac]; nlinarith
  obtain ⟨delta, hdthr⟩ : ∃ delta : ℝ, delta = smallContrastThreshold d (1 / 2 : ℝ) :=
    ⟨_, rfl⟩
  have hdpos : 0 < delta := by rw [hdthr]; exact smallContrastThreshold_half_pos d
  have hd16 : delta ≤ 1 / 16 := by
    rw [hdthr]; exact smallContrastThreshold_half_le_sixteenth d
  -- geometry of the localization ball
  have h2B : cubeSet B ⊆ centeredAxisCube B.1 (2 * B.2) := cubeSet_subset_double hB.le
  have hclosed : Metric.closedBall x R ⊆ cubeSet B := by
    intro y hy
    have hyx : ‖y - x‖ ≤ R := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
    show y ∈ centeredAxisCube B.1 B.2
    refine mem_centeredAxisCube.mpr fun i => ?_
    have h1 : |y i - x i| ≤ R := by
      have hcoord := norm_le_pi_norm (y - x) i
      simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
      exact hcoord.trans hyx
    have h2 : |x i - B.1 i| < B.2 / 2 / 2 := mem_centeredAxisCube.mp hx i
    have h3 : |y i - B.1 i| ≤ |y i - x i| + |x i - B.1 i| := abs_sub_le _ _ _
    linarith
  have hballQ : euclideanBall x R ⊆ cubeSet B :=
    (euclideanBall_subset_metricBall hR).trans
      (Metric.ball_subset_closedBall.trans hclosed)
  have hball2B : euclideanBall x R ⊆ centeredAxisCube B.1 (2 * B.2) := hballQ.trans h2B
  have hxball : x ∈ euclideanBall x R := by
    show vecNormSq (x - x) < R ^ 2
    have hz : vecNormSq (x - x) = (0 : ℝ) := by simp [vecNormSq, vecDot]
    rw [hz]; positivity
  have hx2B : x ∈ centeredAxisCube B.1 (2 * B.2) := hball2B hxball
  -- small contrast on the localization ball
  have hclose : ∀ y ∈ euclideanBall x R, |(a x)⁻¹ * a y - 1| ≤ delta := by
    refine abs_inv_mul_sub_one_le_of_logCoefficientControlOn hB hctrl hR hx2B hball2B ?_
      (by linarith)
    have hs : 0 ≤ Real.sqrt d * Real.sqrt H :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hden : (0 : ℝ) < 8 * (1 + Real.sqrt d * Real.sqrt H) := by linarith
    have heq : Real.sqrt d * (Real.sqrt H / B.2) * R
        = Real.sqrt d * Real.sqrt H * delta / (8 * (1 + Real.sqrt d * Real.sqrt H)) := by
      rw [hRfrac, interiorContrastFraction, hdthr]
      field_simp
    rw [heq, div_le_iff₀ hden]
    nlinarith
  -- the harmonic representative on the localization ball
  have hWopen : IsOpen (euclideanBall x R) := isOpen_euclideanBall x R
  have hWbdd : Bornology.IsBounded (euclideanBall x R) :=
    Metric.isBounded_ball.subset (euclideanBall_subset_metricBall hR)
  have hWclos : closure (euclideanBall x R) ⊆ cubeSet B := by
    refine (closure_mono (euclideanBall_subset_metricBall hR)).trans ?_
    exact Metric.closure_ball_subset_closedBall.trans hclosed
  obtain ⟨u, hu_ae, hu_test⟩ :=
    hharm.2 (euclideanBall x R) hWopen hWbdd.isCompact_closure hWclos
  have hu_wh : IsWeaklyHarmonicOn a (euclideanBall x R) u := by
    intro phi
    simpa only [vecDot_smul_left] using hu_test phi
  have hacont : ContinuousOn a (euclideanBall x R) :=
    (contDiffOn_of_logCoefficientControlOn hctrl).continuousOn.mono hball2B
  have hRhalf : (0 : ℝ) < R / 2 := by positivity
  have hballHalf : euclideanBall x (R / 2) ⊆ euclideanBall x R :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith)
  have hdata : smallContrastDataSize d (1 / 2 : ℝ)
      (ballToUnitH1 x hRhalf
        (u.restrict (isOpen_euclideanBall x (R / 2)) hballHalf)) (fun _ => 0) ≤
      halfBallCaccioppoliDataPrice d x R u.toFun (averageOn (cubeSet B) h) :=
    smallContrastDataSize_halfBall_le_caccioppoli hWopen hacont hu_wh hR
      (subset_refl _) hd16 hclose (averageOn (cubeSet B) h)
  have hlocal : |euclideanBallAverageRepresentative u.toFun x -
        averageOn (euclideanBall x (R / 2 / 2)) u.toFun| ≤
      smallContrastSchauderConstant d * smallContrastDataSize d (1 / 2 : ℝ)
          (ballToUnitH1 x hRhalf
            (u.restrict (isOpen_euclideanBall x (R / 2)) hballHalf)) (fun _ => 0) *
        (R / 2) ^ (1 - (1 / 2 : ℝ)) * (R / 2 / 2) ^ (1 / 2 : ℝ) :=
    canonicalRepresentative_sub_ballAverage_le_of_smallContrast hWopen hacont hu_wh
      hRhalf hballHalf (a x) delta (1 / 2 : ℝ) hd (by constructor <;> norm_num)
      hdpos.le (le_of_eq hdthr) (by linarith)
      (fun y hy => hclose y (hballHalf hy))
  -- measure-theoretic bookkeeping on the cube
  have hQpos : 0 < (volume (cubeSet B)).toReal := by
    rw [volume_cubeSet_toReal hB.le]; positivity
  have hQtop : volume (cubeSet B) ≠ ⊤ := volume_cubeSet_ne_top
  let : IsFiniteMeasure (volume.restrict (cubeSet B)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hQtop⟩
  have hfQ : IntegrableOn h (cubeSet B) := hmem.integrable one_le_two
  have hf2Q : IntegrableOn (fun y => h y ^ 2) (cubeSet B) := hmem.integrable_sq
  have hg2Q : IntegrableOn
      (fun y => (h y - averageOn (cubeSet B) h) ^ 2) (cubeSet B) := by
    have hlinear : IntegrableOn
        (fun y => 2 * averageOn (cubeSet B) h * h y) (cubeSet B) := hfQ.const_mul _
    have hconst : IntegrableOn
        (fun _ : Vec d => averageOn (cubeSet B) h ^ 2) (cubeSet B) :=
      integrableOn_const hQtop
    have heq : (fun y => (h y - averageOn (cubeSet B) h) ^ 2)
        = fun y => h y ^ 2 - 2 * averageOn (cubeSet B) h * h y
            + averageOn (cubeSet B) h ^ 2 := by
      funext y; ring
    rw [heq]
    exact (hf2Q.sub hlinear).add hconst
  have hballRpos : 0 < (volume (euclideanBall x R)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hR))
  have hquarter : (0 : ℝ) < R / 2 / 2 := by positivity
  have hballPpos : 0 < (volume (euclideanBall x (R / 2 / 2))).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hquarter))
  have hPball : euclideanBall x (R / 2 / 2) ⊆ euclideanBall x R :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith)
  have hPQ : euclideanBall x (R / 2 / 2) ⊆ cubeSet B := hPball.trans hballQ
  -- the radius factor of the Schauder readout
  have hpow : (R / 2) ^ (1 - (1 / 2 : ℝ)) * (R / 2 / 2) ^ (1 / 2 : ℝ) ≤ R / 2 := by
    have hmono : (R / 2 / 2) ^ (1 / 2 : ℝ) ≤ (R / 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hexp : (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [hexp]
    calc (R / 2) ^ (1 / 2 : ℝ) * (R / 2 / 2) ^ (1 / 2 : ℝ)
        ≤ (R / 2) ^ (1 / 2 : ℝ) * (R / 2) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hRhalf.le _)
      _ = R / 2 := by rw [← Real.rpow_add hRhalf]; norm_num
  have hC0 := smallContrastSchauderConstant_nonneg d
  have hend0 := boundedMultiplierCaccioppoliEndpointConst_nonneg d
  have hprice0 : (0 : ℝ) ≤
      halfBallCaccioppoliDataPrice d x R u.toFun (averageOn (cubeSet B) h) :=
    Real.sqrt_nonneg _
  have hstep1 : |euclideanBallAverageRepresentative u.toFun x -
        averageOn (euclideanBall x (R / 2 / 2)) u.toFun| ≤
      smallContrastSchauderConstant d *
        halfBallCaccioppoliDataPrice d x R u.toFun (averageOn (cubeSet B) h) * (R / 2) := by
    refine hlocal.trans ?_
    calc smallContrastSchauderConstant d * smallContrastDataSize d (1 / 2 : ℝ)
            (ballToUnitH1 x hRhalf
              (u.restrict (isOpen_euclideanBall x (R / 2)) hballHalf)) (fun _ => 0) *
            (R / 2) ^ (1 - (1 / 2 : ℝ)) * (R / 2 / 2) ^ (1 / 2 : ℝ)
        = (smallContrastSchauderConstant d * smallContrastDataSize d (1 / 2 : ℝ)
            (ballToUnitH1 x hRhalf
              (u.restrict (isOpen_euclideanBall x (R / 2)) hballHalf)) (fun _ => 0)) *
            ((R / 2) ^ (1 - (1 / 2 : ℝ)) * (R / 2 / 2) ^ (1 / 2 : ℝ)) := by ring
      _ ≤ (smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d x R u.toFun (averageOn (cubeSet B) h)) *
            ((R / 2) ^ (1 - (1 / 2 : ℝ)) * (R / 2 / 2) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdata hC0)
            (mul_nonneg (Real.rpow_nonneg hRhalf.le _) (Real.rpow_nonneg hquarter.le _))
      _ ≤ smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d x R u.toFun (averageOn (cubeSet B) h) * (R / 2) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0 hprice0)
  -- transfers between the `H¹` representative and `h`
  have hpriceEq := halfBallCaccioppoliDataPrice_mul_halfRadius_eq_normalizedL2On
    (d := d) (x := x) hR u.toFun (averageOn (cubeSet B) h)
  have hnormEq : normalizedL2On (euclideanBall x R)
        (fun y => u.toFun y - averageOn (cubeSet B) h)
      = normalizedL2On (euclideanBall x R)
        (fun y => h y - averageOn (cubeSet B) h) := by
    refine normalizedL2On_congr_ae (hu_ae.mono (fun y hy => ?_))
    show u.toFun y - averageOn (cubeSet B) h = h y - averageOn (cubeSet B) h
    rw [hy]
  have haveEq : averageOn (euclideanBall x (R / 2 / 2)) u.toFun
      = averageOn (euclideanBall x (R / 2 / 2)) h :=
    averageOn_congr_ae (hu_ae.filter_mono (ae_mono (Measure.restrict_mono hPball le_rfl)))
  have hrepr : euclideanBallAverageRepresentative u.toFun x = h x :=
    euclideanBallAverageRepresentative_eq_local hWopen (subset_refl _)
      (hu_ae.mono (fun y hy => hy.symm)) (hharm.1.mono hballQ) hxball
  -- the two covering prices
  have hratioR : Real.sqrt ((volume (cubeSet B)).toReal /
        (volume (euclideanBall x R)).toReal)
      = Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
          interiorContrastFraction d H ^ d)⁻¹) := by
    rw [interior_volumeRatio (s := interiorContrastFraction d H) hB x hfrpos hRfrac]
  have hratioP : Real.sqrt ((volume (cubeSet B)).toReal /
        (volume (euclideanBall x (R / 2 / 2))).toReal)
      = Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
          (interiorContrastFraction d H / 4) ^ d)⁻¹) := by
    rw [interior_volumeRatio (s := interiorContrastFraction d H / 4) hB x
      (div_pos hfrpos (by norm_num)) (by rw [hRfrac]; ring)]
  have hnormBall : normalizedL2On (euclideanBall x R)
        (fun y => h y - averageOn (cubeSet B) h) ≤
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
          interiorContrastFraction d H ^ d)⁻¹) *
        normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
    rw [← hratioR]
    exact normalizedL2On_le_of_subset hballQ hQpos hballRpos hg2Q
  have hmean : |averageOn (euclideanBall x (R / 2 / 2)) h - averageOn (cubeSet B) h| ≤
      Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
          (interiorContrastFraction d H / 4) ^ d)⁻¹) *
        normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
    rw [← hratioP]
    exact abs_averageOn_subset_sub_averageOn_le
      (isOpen_euclideanBall x (R / 2 / 2)).measurableSet hPQ hQtop hQpos hballPpos hfQ hf2Q
  -- assembly
  have hfirst : |h x - averageOn (euclideanBall x (R / 2 / 2)) h| ≤
      smallContrastSchauderConstant d * boundedMultiplierCaccioppoliEndpointConst d *
        Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
          interiorContrastFraction d H ^ d)⁻¹) *
        normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
    rw [← hrepr, ← haveEq]
    refine hstep1.trans ?_
    rw [mul_assoc, hpriceEq, hnormEq]
    calc smallContrastSchauderConstant d *
          (boundedMultiplierCaccioppoliEndpointConst d *
            normalizedL2On (euclideanBall x R)
              (fun y => h y - averageOn (cubeSet B) h))
        ≤ smallContrastSchauderConstant d *
          (boundedMultiplierCaccioppoliEndpointConst d *
            (Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
              interiorContrastFraction d H ^ d)⁻¹) *
              normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnormBall hend0) hC0
      _ = _ := by ring
  calc |h x - averageOn (cubeSet B) h|
      ≤ |h x - averageOn (euclideanBall x (R / 2 / 2)) h| +
        |averageOn (euclideanBall x (R / 2 / 2)) h - averageOn (cubeSet B) h| :=
        abs_sub_le _ _ _
    _ ≤ smallContrastSchauderConstant d * boundedMultiplierCaccioppoliEndpointConst d *
          Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
            interiorContrastFraction d H ^ d)⁻¹) *
          normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) +
        Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
            (interiorContrastFraction d H / 4) ^ d)⁻¹) *
          normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) :=
        add_le_add hfirst hmean
    _ = interiorHarmonicConstant d H *
          normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
        rw [interiorHarmonicConstant]; ring






theorem localHarmonic_interiorDisplay [NeZero d] (hd : 2 ≤ d)
    {a : Vec d → ℝ} {H : ℝ} {Qfam : Set (Cube d)}
    (hside : ∀ Q ∈ Qfam, 0 < Q.2)
    (hH : FamilyLogCoefficientControl a H Qfam) :
    ∀ B' ∈ Qfam, ∀ B ∈ Qfam,
      cubeSet B' ⊆ centeredAxisCube B.1 (B.2 / 2) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (cubeSet B) h →
        MemLp h 2 (volume.restrict (cubeSet B)) →
        ∀ x ∈ cubeSet B', |h x - averageOn (cubeSet B) h| ≤
          interiorHarmonicConstant d H *
            normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
  intro B' _hB' B hB hhalf h hharm hmem x hxB'
  exact abs_sub_averageOn_le_interiorHarmonicConstant hd (hside B hB) (hH B hB)
    hharm hmem (hhalf hxB')

/-- The same clause under the anchor's own geometric hypothesis. -/
theorem localHarmonic_interiorDisplay_of_isLocalCubeGeometry [NeZero d] (hd : 2 ≤ d)
    {a : Vec d → ℝ} {H : ℝ} {grid : Finset (Vec d)} {j1 j2 : ℕ} {U : Cube d}
    {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (hgeom : IsLocalCubeGeometry grid j1 j2 U Pfam Qfam Afam)
    (hH : FamilyLogCoefficientControl a H Qfam) :
    ∀ B' ∈ Qfam, ∀ B ∈ Qfam,
      cubeSet B' ⊆ centeredAxisCube B.1 (B.2 / 2) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (cubeSet B) h →
        MemLp h 2 (volume.restrict (cubeSet B)) →
        ∀ x ∈ cubeSet B', |h x - averageOn (cubeSet B) h| ≤
          interiorHarmonicConstant d H *
            normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) :=
  localHarmonic_interiorDisplay hd hgeom.side_pos hH



theorem localHarmonic_interiorDisplay_one_add [NeZero d] (hd : 2 ≤ d)
    {a : Vec d → ℝ} {H : ℝ} {Qfam : Set (Cube d)}
    (hside : ∀ Q ∈ Qfam, 0 < Q.2)
    (hH : FamilyLogCoefficientControl a H Qfam) :
    ∀ B' ∈ Qfam, ∀ B ∈ Qfam,
      cubeSet B' ⊆ centeredAxisCube B.1 (B.2 / 2) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (cubeSet B) h →
        MemLp h 2 (volume.restrict (cubeSet B)) →
        ∀ x ∈ cubeSet B', |h x - averageOn (cubeSet B) h| ≤
          (1 + interiorHarmonicConstant d H) *
            normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h) := by
  intro B' hB' B hB hhalf h hharm hmem x hxB'
  refine (localHarmonic_interiorDisplay hd hside hH B' hB' B hB hhalf h hharm hmem
    x hxB').trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (normalizedL2On_nonneg _ _)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
