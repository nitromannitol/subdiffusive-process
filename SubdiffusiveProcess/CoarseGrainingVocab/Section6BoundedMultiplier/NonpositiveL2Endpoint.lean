module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.CaccioppoliEndpointPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalSubunitArbitraryRadius
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveRadius
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubcubeAveraging

@[expose] public section

/-!
# Direct normalized-`L2` readout at nonpositive scales

This module records the scale-invariant normalized-`L2` version of the
local Caccioppoli price and applies it at the deterministic nonpositive-scale
localization radius.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- The explicit half-ball Caccioppoli price is exactly the normalized
outer-ball `L2` oscillation times its dimension-only endpoint constant. -/
theorem halfBallCaccioppoliDataPrice_mul_halfRadius_eq_normalizedL2On
    [NeZero d] {x : Vec d} {R : ℝ} (hR : 0 < R)
    (f : Vec d → ℝ) (c : ℝ) :
    halfBallCaccioppoliDataPrice d x R f c * (R / 2) =
      boundedMultiplierCaccioppoliEndpointConst d *
        normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) := by
  let V := (volume (euclideanBall x R)).toReal
  have hV : V = (volume (smallContrastUnitBall d)).toReal * R ^ d := by
    dsimp only [V]
    exact volume_euclideanBall_toReal_eq_unit_mul_pow x hR
  have hVpos : 0 < V := by
    dsimp only [V]
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hR))
  have hnormsq : normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) ^ 2 =
      V⁻¹ * ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume := by
    simp only [normalizedL2On_sq, volumeAverage, V]
  have hintEq : (∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume) =
      V * normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) ^ 2 := by
    have hVne : V ≠ 0 := hVpos.ne'
    rw [hnormsq]
    field_simp
  have hnorm0 : 0 ≤ normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) :=
    normalizedL2On_nonneg _ _
  have hhalf : 0 ≤ R / 2 := by positivity
  have hfactor0 : 0 ≤ ((R / 2) ^ d)⁻¹ *
      ((16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
        ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume) := by
    positivity
  change Real.sqrt (((R / 2) ^ d)⁻¹ *
      ((16 * (d : ℝ) *
        (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
        ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume)) * (R / 2) = _
  have hsqrtHalf : Real.sqrt ((R / 2) ^ 2) = R / 2 := Real.sqrt_sq hhalf
  calc
    Real.sqrt (((R / 2) ^ d)⁻¹ *
        ((16 * (d : ℝ) *
          (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
          ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume)) * (R / 2) =
        Real.sqrt (((R / 2) ^ d)⁻¹ *
          ((16 * (d : ℝ) *
            (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
            ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume)) *
          Real.sqrt ((R / 2) ^ 2) := by rw [hsqrtHalf]
    _ = Real.sqrt ((((R / 2) ^ d)⁻¹ *
          ((16 * (d : ℝ) *
            (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
            ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume)) *
          (R / 2) ^ 2) := by rw [Real.sqrt_mul hfactor0]
    _ = boundedMultiplierCaccioppoliEndpointConst d *
        normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) := by
      rw [hintEq, hV]
      have hRne : R ≠ 0 := hR.ne'
      have hendpoint0 : 0 ≤ (2 : ℝ) ^ d *
          (16 * (d : ℝ) * quantitativeBallCutoffGradientConst d ^ 2) *
            (volume (smallContrastUnitBall d)).toReal := by positivity
      rw [show R - R / 2 = R / 2 by ring]
      have halgebra :
          ((R / 2) ^ d)⁻¹ *
              ((16 * (d : ℝ) *
                (quantitativeBallCutoffGradientConst d / (R / 2)) ^ 2) *
                ((volume (smallContrastUnitBall d)).toReal * R ^ d *
                  normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) ^ 2)) *
                (R / 2) ^ 2 =
            ((2 : ℝ) ^ d *
              (16 * (d : ℝ) * quantitativeBallCutoffGradientConst d ^ 2) *
                (volume (smallContrastUnitBall d)).toReal) *
              normalizedL2On (euclideanBall x R) (fun y ↦ f y - c) ^ 2 := by
        rw [div_pow]
        field_simp [hRne]
      rw [halgebra, Real.sqrt_mul hendpoint0, Real.sqrt_sq hnorm0]
      rfl

private theorem translatedCube_isOpen_l2 {d : ℕ} (m : ℤ) (z : Vec d) :
    IsOpen (translatedCube d m z) := by
  have hset : translatedCube d m z =
      (fun x : Vec d ↦ x - z) ⁻¹' openCubeSet (originCube d m) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change u ∈ openCubeSet (originCube d m) at hu
      simpa using hu
    · intro hx
      refine ⟨x - z, ?_, ?_⟩
      · simpa [cube] using hx
      · ext i
        simp
  rw [hset]
  exact (isOpen_openCubeSet (originCube d m)).preimage
    (continuous_id.sub continuous_const)

/-- Direct point-to-short-ball estimate at any deterministic radius below the
adaptive radius.  The Schauder datum has already been replaced by the
contrast-two Caccioppoli price. -/
theorem localSubunit_point_sub_ballAverage_le_caccioppoli_of_radius
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : PotentialSample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {R : ℝ} (hR : 0 < R)
    (hRmesh : R ≤ (6 : ℝ)⁻¹)
    (hRambient : R ≤ (3 : ℝ) ^ m / 4)
    (hRadaptive : R ≤ boundedMultiplierLocalRadius M L m z omega)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    (c : ℝ) :
    let rho := R / 2
    |euclideanBallAverageRepresentative h.toFun x -
        averageOn (euclideanBall x (rho / 2)) h.toFun| ≤
      smallContrastSchauderConstant d *
        halfBallCaccioppoliDataPrice d x R h.toFun c * rho := by
  dsimp only
  let rho := R / 2
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  obtain ⟨p, hp, hxcell, hballCell⟩ :=
    exists_coverCell_euclideanBall_subset hcollar hR hRmesh hRambient
  have hballB : euclideanBall x R ⊆ translatedCube d m z :=
    hballCell.trans Set.inter_subset_left
  have hballRho : euclideanBall x rho ⊆ translatedCube d m z :=
    (euclideanBall_subset_euclideanBall hrho.le (by
      dsimp only [rho]
      linarith)).trans hballB
  let G := coveringLogLipschitzModulus M L m z omega
  let epsilon := boundedMultiplierEpsilonStar d
  let delta := Real.exp epsilon * (1 + epsilon) - 1
  let s : Vec d → ℝ := fun y ↦ aCutoff M L omega y * theta y
  let kappa := aCutoff M L omega x * b
  have hlog : ∀ y ∈ euclideanBall x R,
      |Real.log (aCutoff M L omega y) - Real.log (aCutoff M L omega x)| ≤
        R * G := by
    intro y hy
    have hpair := abs_log_aCutoff_sub_le_coveringLogLipschitzModulus_mul_norm
      M L m z omega p hp (hballCell hy) hxcell
    have hdist : ‖y - x‖ < R := euclideanBall_subset_metricBall hR hy
    exact hpair.trans (by
      simpa [G, mul_comm] using mul_le_mul_of_nonneg_left hdist.le
        (coveringLogLipschitzModulus_nonneg M L m z omega))
  have hscale : R * G ≤ epsilon := by
    have hG : 0 ≤ G := coveringLogLipschitzModulus_nonneg M L m z omega
    exact (mul_le_mul_of_nonneg_right hRadaptive hG).trans (by
      simpa only [G, epsilon] using
        boundedMultiplierLocalRadius_mul_modulus_le M L m z omega)
  have hnormalized : ∀ y ∈ euclideanBall x R,
      |aCutoff M L omega y * theta y /
          (aCutoff M L omega x * b) - 1| ≤ delta := by
    simpa only [delta, epsilon, one_mul] using
      abs_normalized_cutoff_multiplier_sub_one_le (c := 1)
        (fun y _hy ↦ aCutoff_pos M L omega y)
        (aCutoff_pos M L omega x) hb
        (mul_nonneg hR.le
          (coveringLogLipschitzModulus_nonneg M L m z omega))
        (by simpa only [one_mul] using hscale) hlog
        (fun y hy ↦ hthetaClose y (hballB hy))
  have hclose : ∀ y ∈ euclideanBall x R,
      |kappa⁻¹ * s y - 1| ≤ delta := by
    intro y hy
    have hh := hnormalized y hy
    convert hh using 1
    dsimp only [kappa, s]
    field_simp [(aCutoff_pos M L omega x).ne', hb.ne']
  have hdelta16 : delta ≤ 1 / 16 := by
    calc
      delta ≤ smallContrastThreshold d (1 / 2) := by
        simpa only [delta, epsilon] using
          boundedMultiplier_combinedContrast_le_threshold d
      _ ≤ (1 - (1 / 2 : ℝ)) / 8 :=
        smallContrastThreshold_le_eighth_gap d (by norm_num)
      _ = 1 / 16 := by norm_num
  have hsCont : ContinuousOn s (translatedCube d m z) :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  let uBall := h.restrict (isOpen_euclideanBall x rho) hballRho
  have hdata :
      smallContrastDataSize d (1 / 2)
          (ballToUnitH1 x hrho uBall) (fun _ ↦ 0) ≤
        halfBallCaccioppoliDataPrice d x R h.toFun c := by
    have hraw := smallContrastDataSize_halfBall_le_caccioppoli
      (translatedCube_isOpen_l2 m z) hsCont hharm hR hballB
      hdelta16 hclose c
    simpa only [rho, uBall] using hraw
  have hlocal := canonicalRepresentative_sub_ballAverage_le_of_smallContrast
    (translatedCube_isOpen_l2 m z) hsCont hharm hrho hballRho
    kappa delta (1 / 2) hd (by constructor <;> norm_num)
    (boundedMultiplier_combinedContrast_nonneg d)
    (boundedMultiplier_combinedContrast_le_threshold d)
    (boundedMultiplier_combinedContrast_lt_one d)
    (fun y hy ↦ hclose y
      ((euclideanBall_subset_euclideanBall hrho.le (by
        dsimp only [rho]
        linarith)) hy))
  have hpow : rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) ≤ rho := by
    have hmono : (rho / 2) ^ (1 / 2 : ℝ) ≤ rho ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hexponent : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [hexponent]
    calc
      rho ^ (1 / 2 : ℝ) * (rho / 2) ^ (1 / 2 : ℝ) ≤
          rho ^ (1 / 2 : ℝ) * rho ^ (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hmono
          (Real.rpow_nonneg hrho.le (1 / 2 : ℝ))
      _ = rho := by
        rw [← Real.rpow_add hrho]
        norm_num
  have hC0 := smallContrastSchauderConstant_nonneg d
  have hprice0 : 0 ≤ halfBallCaccioppoliDataPrice d x R h.toFun c :=
    Real.sqrt_nonneg _
  calc
    |euclideanBallAverageRepresentative h.toFun x -
        averageOn (euclideanBall x (rho / 2)) h.toFun| ≤
        (smallContrastSchauderConstant d *
          smallContrastDataSize d (1 / 2)
            (ballToUnitH1 x hrho uBall) (fun _ ↦ 0)) *
          rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) := by
      simpa only [rho, s, kappa, delta, uBall] using hlocal
    _ ≤ (smallContrastSchauderConstant d *
          halfBallCaccioppoliDataPrice d x R h.toFun c) *
        (rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ)) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdata hC0)
          (mul_nonneg (Real.rpow_nonneg hrho.le _)
            (Real.rpow_nonneg (div_nonneg hrho.le (by norm_num)) _))
    _ ≤ smallContrastSchauderConstant d *
          halfBallCaccioppoliDataPrice d x R h.toFun c * rho := by
      exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hC0 hprice0)

def boundedMultiplierNonpositiveOuterL2Const (d : ℕ) : ℝ :=
  Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
    boundedMultiplierNonpositiveRadiusFloor d ^ d)⁻¹)

def boundedMultiplierNonpositiveInnerMeanConst (d : ℕ) : ℝ :=
  Real.sqrt (((volume (smallContrastUnitBall d)).toReal *
    (boundedMultiplierNonpositiveRadiusFloor d / 4) ^ d)⁻¹)

def boundedMultiplierNonpositiveL2Const (d : ℕ) : ℝ :=
  smallContrastSchauderConstant d *
      boundedMultiplierCaccioppoliEndpointConst d *
        boundedMultiplierNonpositiveOuterL2Const d +
    boundedMultiplierNonpositiveInnerMeanConst d

theorem boundedMultiplierNonpositiveL2Const_nonneg (d : ℕ) :
    0 ≤ boundedMultiplierNonpositiveL2Const d := by
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (smallContrastSchauderConstant_nonneg d)
        (boundedMultiplierCaccioppoliEndpointConst_nonneg d))
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

private theorem volume_translatedCube_toReal_l2 (m : ℤ) (z : Vec d) :
    (volume (translatedCube d m z)).toReal = ((3 : ℝ) ^ m) ^ d := by
  rw [translatedCube, cube,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet,
    volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
  simp only [originCube]

private theorem nonpositive_outer_volumeRatio
    [NeZero d] (m : ℤ) (z x : Vec d) :
    (volume (translatedCube d m z)).toReal /
        (volume (euclideanBall x
          (boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m))).toReal =
      ((volume (smallContrastUnitBall d)).toReal *
        boundedMultiplierNonpositiveRadiusFloor d ^ d)⁻¹ := by
  have hA : 0 < (3 : ℝ) ^ m := by positivity
  have hfloor : 0 < boundedMultiplierNonpositiveRadiusFloor d :=
    boundedMultiplierNonpositiveRadiusFloor_pos d
  have hunit : 0 < (volume (smallContrastUnitBall d)).toReal := by
    have hball := Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
      (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
    simpa only [smallContrastUnitBall] using
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hball)
  rw [volume_translatedCube_toReal_l2,
    volume_euclideanBall_toReal_eq_unit_mul_pow x (mul_pos hfloor hA), mul_pow]
  field_simp [hA.ne', hfloor.ne', hunit.ne']

private theorem nonpositive_inner_volumeRatio
    [NeZero d] (m : ℤ) (z x : Vec d) :
    (volume (translatedCube d m z)).toReal /
        (volume (euclideanBall x
          ((boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m) / 4))).toReal =
      ((volume (smallContrastUnitBall d)).toReal *
        (boundedMultiplierNonpositiveRadiusFloor d / 4) ^ d)⁻¹ := by
  have hA : 0 < (3 : ℝ) ^ m := by positivity
  have hfloor : 0 < boundedMultiplierNonpositiveRadiusFloor d :=
    boundedMultiplierNonpositiveRadiusFloor_pos d
  have hunit : 0 < (volume (smallContrastUnitBall d)).toReal := by
    have hball := Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
      (0 : Vec d) (by norm_num : (0 : ℝ) < 1)
    simpa only [smallContrastUnitBall] using
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hball)
  rw [volume_translatedCube_toReal_l2,
    volume_euclideanBall_toReal_eq_unit_mul_pow x (by positivity), div_pow,
    mul_pow]
  field_simp [hA.ne', hfloor.ne', hunit.ne']
  rw [div_pow]
  field_simp [hfloor.ne']

/-- Direct normalized-`L2` endpoint at every collared point of a
nonpositive-scale parent cube. -/
theorem nonpositive_point_sub_parentAverage_le_normalizedL2
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    {m : ℤ} (hm : m ≤ 0) (z : Vec d)
    (omega : PotentialSample d)
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z)
    {x : Vec d} (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
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
        averageOn (translatedCube d m z) h.toFun| ≤
      boundedMultiplierNonpositiveL2Const d *
        normalizedL2On (translatedCube d m z)
          (fun y ↦ h.toFun y - averageOn (translatedCube d m z) h.toFun) := by
  let B := translatedCube d m z
  let A := averageOn B h.toFun
  let R := boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m
  let P := euclideanBall x (R / 4)
  let g : Vec d → ℝ := fun y ↦ h.toFun y - A
  have hR : 0 < R := by
    dsimp only [R]
    exact mul_pos (boundedMultiplierNonpositiveRadiusFloor_pos d) (by positivity)
  obtain ⟨_p, _hp, _hxcell, hballCell⟩ := exists_coverCell_euclideanBall_subset
    hcollar hR
    (by simpa only [R] using
      (boundedMultiplierNonpositiveRadius_mul_le_mesh (d := d) hm))
    (by simpa only [R] using
      (boundedMultiplierNonpositiveRadius_mul_le_ambient (d := d) (m := m)))
  have hballB : euclideanBall x R ⊆ B :=
    hballCell.trans Set.inter_subset_left
  have hPB : P ⊆ B :=
    (euclideanBall_subset_euclideanBall (by positivity) (by
      linarith)).trans hballB
  have hBvol : (volume B).toReal = ((3 : ℝ) ^ m) ^ d := by
    simpa only [B] using volume_translatedCube_toReal_l2 (d := d) m z
  have hBpos : 0 < (volume B).toReal := by rw [hBvol]; positivity
  have hBtop : volume B ≠ ⊤ := by
    apply ne_of_lt
    dsimp only [B]
    rw [translatedCube, cube,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq]
    exact volume_openCubeSet_lt_top (originCube d m)
  have hRballPos : 0 < (volume (euclideanBall x R)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x hR))
  have hPpos : 0 < (volume P).toReal := by
    dsimp only [P]
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero x
        (by positivity : 0 < R / 4)))
  letI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      lt_top_iff_ne_top.mpr hBtop⟩
  have hmemB : MemLp h.toFun 2 (volume.restrict B) := by
    simpa only [B] using h.memL2
  have hfB : IntegrableOn h.toFun B := hmemB.integrable one_le_two
  have hf2B : IntegrableOn (fun y ↦ h.toFun y ^ 2) B := hmemB.integrable_sq
  have hg2B : IntegrableOn (fun y ↦ g y ^ 2) B := by
    have hlinear : IntegrableOn (fun y ↦ 2 * A * h.toFun y) B :=
      hfB.const_mul (2 * A)
    have hconst : IntegrableOn (fun _ : Vec d ↦ A ^ 2) B :=
      integrableOn_const hBtop
    have heq : (fun y ↦ g y ^ 2) =
        fun y ↦ h.toFun y ^ 2 - 2 * A * h.toFun y + A ^ 2 := by
      funext y
      dsimp only [g]
      ring
    rw [heq]
    exact (hf2B.sub hlinear).add hconst
  have hnormBall := normalizedL2On_le_of_subset hballB hBpos hRballPos hg2B
  have houterRatio : Real.sqrt ((volume B).toReal /
        (volume (euclideanBall x R)).toReal) =
      boundedMultiplierNonpositiveOuterL2Const d := by
    rw [nonpositive_outer_volumeRatio (d := d) m z x]
    rfl
  rw [houterRatio] at hnormBall
  have hpoint := localSubunit_point_sub_ballAverage_le_caccioppoli_of_radius
    hd M L m z omega hcollar hR
    (by simpa only [R] using
      (boundedMultiplierNonpositiveRadius_mul_le_mesh (d := d) hm))
    (by simpa only [R] using
      (boundedMultiplierNonpositiveRadius_mul_le_ambient (d := d) (m := m)))
    (by simpa only [R] using
      (boundedMultiplierNonpositiveRadiusFloor_mul_zpow_le_localRadius
        (d := d) M L (m := m) hm z (omega := omega) hgood))
    hthetaCont hb hthetaClose hharm A
  have hprice := halfBallCaccioppoliDataPrice_mul_halfRadius_eq_normalizedL2On
    (d := d) (x := x) hR h.toFun A
  have hpoint' :
      |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| ≤
        smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            boundedMultiplierNonpositiveOuterL2Const d *
              normalizedL2On B g := by
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
        simp only [mul_assoc]
      _ ≤ smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            (boundedMultiplierNonpositiveOuterL2Const d *
              normalizedL2On B g) := by
        simpa only [mul_assoc] using hscaled
      _ = smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            boundedMultiplierNonpositiveOuterL2Const d *
              normalizedL2On B g := by ring
  have hmean := abs_averageOn_subset_sub_averageOn_le
    (isOpen_euclideanBall x (R / 4)).measurableSet hPB hBtop hBpos hPpos hfB hf2B
  have hinnerRatio : Real.sqrt ((volume B).toReal / (volume P).toReal) =
      boundedMultiplierNonpositiveInnerMeanConst d := by
    dsimp only [P]
    rw [nonpositive_inner_volumeRatio (d := d) m z x]
    rfl
  rw [hinnerRatio] at hmean
  have htri := abs_sub_le (euclideanBallAverageRepresentative h.toFun x)
    (averageOn P h.toFun) (averageOn B h.toFun)
  calc
    |euclideanBallAverageRepresentative h.toFun x - averageOn B h.toFun| ≤
        |euclideanBallAverageRepresentative h.toFun x - averageOn P h.toFun| +
          |averageOn P h.toFun - averageOn B h.toFun| := htri
    _ ≤ (smallContrastSchauderConstant d *
          boundedMultiplierCaccioppoliEndpointConst d *
            boundedMultiplierNonpositiveOuterL2Const d +
          boundedMultiplierNonpositiveInnerMeanConst d) *
        normalizedL2On B g := by
      calc
        _ ≤ (smallContrastSchauderConstant d *
              boundedMultiplierCaccioppoliEndpointConst d *
                boundedMultiplierNonpositiveOuterL2Const d) *
              normalizedL2On B g +
            boundedMultiplierNonpositiveInnerMeanConst d *
              normalizedL2On B g := add_le_add hpoint' hmean
        _ = _ := by ring
    _ = boundedMultiplierNonpositiveL2Const d * normalizedL2On B g := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
