module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.BallCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalSmallContrast

@[expose] public section

/-!
# Caccioppoli control of the rescaled small-contrast datum

The coefficient used for Caccioppoli is the normalized small-contrast
coefficient divided once more by `1-delta`.  For `delta ≤ 1/16` it lies
between one and two, while the homogeneous equation is unchanged.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

private theorem translatedCube_isOpen' {d : ℕ} (m : ℤ) (z : Vec d) :
    IsOpen (translatedCube d m z) := by
  have hset : translatedCube d m z =
      (fun x : Vec d ↦ x - z) ⁻¹' openCubeSet (originCube d m) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change u ∈ openCubeSet (originCube d m) at hu
      simpa using! hu
    · intro hx
      refine ⟨x - z, ?_, ?_⟩
      · simpa [cube] using! hx
      · ext i
        simp
  rw [hset]
  exact (isOpen_openCubeSet (originCube d m)).preimage
    (continuous_id.sub continuous_const)

/-- Explicit upper bound for the rescaled half-ball gradient datum. -/
def halfBallCaccioppoliDataPrice (d : ℕ) (x : Vec d) (R : ℝ)
    (f : Vec d → ℝ) (c : ℝ) : ℝ :=
  Real.sqrt ((((R / 2) ^ d)⁻¹) *
    ((16 * (d : ℝ) *
      (quantitativeBallCutoffGradientConst d / (R - R / 2)) ^ 2) *
      ∫ y in euclideanBall x R, (f y - c) ^ 2 ∂volume))

/-- The rescaled gradient datum on the half-radius ball is controlled by the
outer-ball centered `L²` energy. -/
theorem smallContrastDataSize_halfBall_le_caccioppoli [NeZero d]
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) {u : H1Function W}
    (hu : IsWeaklyHarmonicOn s W u)
    {x : Vec d} {R : ℝ} (hR : 0 < R)
    (hball : euclideanBall x R ⊆ W)
    {kappa delta : ℝ} (hdelta16 : delta ≤ 1 / 16)
    (hclose : ∀ y ∈ euclideanBall x R,
      |kappa⁻¹ * s y - 1| ≤ delta)
    (c : ℝ) :
    smallContrastDataSize d (1 / 2)
        (ballToUnitH1 x (by positivity : 0 < R / 2)
          (u.restrict (isOpen_euclideanBall x (R / 2))
            ((euclideanBall_subset_euclideanBall (by positivity)
              (by linarith [hR])).trans hball))) (fun _ ↦ 0) ≤
      halfBallCaccioppoliDataPrice d x R u.toFun c := by
  let rho := R / 2
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoR : rho < R := by dsimp [rho]; linarith
  have hinner : euclideanBall x rho ⊆ W :=
    (euclideanBall_subset_euclideanBall hrho.le hrhoR).trans hball
  let uOuter := u.restrict (isOpen_euclideanBall x R) hball
  let uInner := u.restrict (isOpen_euclideanBall x rho) hinner
  let aNorm : Vec d → ℝ := fun y ↦
    (1 - delta)⁻¹ * (kappa⁻¹ * s y)
  have hden : 0 < 1 - delta := by linarith
  have haBounds : ∀ y ∈ euclideanBall x R,
      1 ≤ aNorm y ∧ aNorm y ≤ 2 := by
    intro y hy
    have habs := abs_le.mp (hclose y hy)
    have hlo : 1 - delta ≤ kappa⁻¹ * s y := by linarith
    have hhi : kappa⁻¹ * s y ≤ 1 + delta := by linarith
    constructor
    · rw [show aNorm y = (kappa⁻¹ * s y) / (1 - delta) by
          simp [aNorm, div_eq_inv_mul, mul_comm]]
      exact (le_div_iff₀ hden).2 (by simpa using! hlo)
    · rw [show aNorm y = (kappa⁻¹ * s y) / (1 - delta) by
          simp [aNorm, div_eq_inv_mul, mul_comm]]
      rw [div_le_iff₀ hden]
      linarith
  have haMeas : AEStronglyMeasurable aNorm
      (volumeMeasureOn (euclideanBall x R)) :=
    ((hs.mono hball).aestronglyMeasurable
      (isOpen_euclideanBall x R).measurableSet).const_mul kappa⁻¹
      |>.const_mul (1 - delta)⁻¹
  have huOuter : IsWeaklyHarmonicOn s (euclideanBall x R) uOuter :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      hW (isOpen_euclideanBall x R) hball hu
  have huNorm : IsWeaklyHarmonicOn aNorm (euclideanBall x R) uOuter := by
    have h1 := IsWeaklyHarmonicOn.const_inv_mul kappa huOuter
    have h2 := IsWeaklyHarmonicOn.const_inv_mul (1 - delta) h1
    simpa only [aNorm, mul_assoc] using! h2
  have hboundsAE : ∀ᵐ y ∂(volumeMeasureOn (euclideanBall x R)),
      1 ≤ aNorm y ∧ aNorm y ≤ 2 := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall x R).measurableSet] with y hy
    exact haBounds y hy
  have hcacc := scalarCaccioppoli_innerBall_le_explicit
    hrho hrhoR haMeas hboundsAE uOuter huNorm c
  have hdata := smallContrastDataSize_ballToUnit_zero
    (alpha := (1 / 2 : ℝ)) hrho uInner
  rw [hdata]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (rho ^ d)⁻¹)
  simpa only [rho, uOuter, uInner] using! hcacc

/-- Actual cutoff-times-multiplier local package: the point-to-cell estimate
and the Caccioppoli bound on its sole Schauder datum hold for the same selected
cover cell. -/
theorem exists_coverCell_localSmallContrast_cellAverage_caccioppoli
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ} (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y)
      (translatedCube d m z) h) :
    let R := boundedMultiplierLocalRadius M L m z omega
    let rho := R / 2
    ∃ p ∈ shellCoverShifts d m,
      x ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall x R ⊆ boundedMultiplierCoverCell d m z p ∧
      ∃ hBall : H1Function (euclideanBall x rho),
        hBall.toFun = h.toFun ∧ hBall.grad = h.grad ∧
        |euclideanBallAverageRepresentative h.toFun x -
            averageOn (boundedMultiplierCoverCell d m z p) h.toFun| ≤
          (smallContrastSchauderConstant d *
            smallContrastDataSize d (1 / 2)
              (ballToUnitH1 x
                (boundedMultiplierLocalRadius_half_pos M L m z omega)
                hBall) (fun _ ↦ 0)) *
              rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) +
            Real.sqrt
              ((volume (boundedMultiplierCoverCell d m z p)).toReal /
                (volume (euclideanBall x (rho / 2))).toReal) *
              normalizedL2On (boundedMultiplierCoverCell d m z p)
                (fun y ↦ h.toFun y -
                  averageOn (boundedMultiplierCoverCell d m z p) h.toFun) ∧
        smallContrastDataSize d (1 / 2)
            (ballToUnitH1 x
              (boundedMultiplierLocalRadius_half_pos M L m z omega)
              hBall) (fun _ ↦ 0) ≤
          halfBallCaccioppoliDataPrice d x R h.toFun
            (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) := by
  dsimp only
  let R := boundedMultiplierLocalRadius M L m z omega
  let rho := R / 2
  obtain ⟨p, hp, hxcell, hballCell, hBall, hBallFun, hBallGrad, hpoint⟩ :=
    exists_coverCell_localSmallContrast_cellAverage hd M L m z omega
      hcollar hthetaCont hb hthetaClose hharm
  have hR : 0 < R := boundedMultiplierLocalRadius_pos M L m z omega
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hballB : euclideanBall x R ⊆ translatedCube d m z :=
    hballCell.trans Set.inter_subset_left
  let G := coveringLogLipschitzModulus M L m z omega
  let epsilon := boundedMultiplierEpsilonStar d
  let delta := Real.exp epsilon * (1 + epsilon) - 1
  let s : Vec d → ℝ := fun y ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y
  let kappa := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * b
  have hlog : ∀ y ∈ euclideanBall x R,
      |Real.log (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y) -
        Real.log (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)| ≤ R * G := by
    intro y hy
    have hpair := abs_log_aCutoff_sub_le_coveringLogLipschitzModulus_mul_norm
      M L m z omega p hp (hballCell hy) hxcell
    have hdist : ‖y - x‖ < R := euclideanBall_subset_metricBall hR hy
    exact hpair.trans (by
      simpa [G, mul_comm] using! mul_le_mul_of_nonneg_left hdist.le
        (coveringLogLipschitzModulus_nonneg M L m z omega))
  have hscale : R * G ≤ 1 * epsilon := by
    simpa only [R, G, epsilon, one_mul] using!
      boundedMultiplierLocalRadius_mul_modulus_le M L m z omega
  have hnormalized : ∀ y ∈ euclideanBall x R,
      |SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y /
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * b) - 1| ≤ delta := by
    simpa only [delta, epsilon, one_mul] using!
      abs_normalized_cutoff_multiplier_sub_one_le (c := 1)
        (fun y _hy ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega y)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x) hb
        (mul_nonneg hR.le
          (coveringLogLipschitzModulus_nonneg M L m z omega))
        hscale hlog (fun y hy ↦ hthetaClose y (hballB hy))
  have hclose : ∀ y ∈ euclideanBall x R,
      |kappa⁻¹ * s y - 1| ≤ delta := by
    intro y hy
    have hh := hnormalized y hy
    convert hh using 1
    dsimp [kappa, s]
    field_simp [(SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).ne', hb.ne']
  have hdelta16 : delta ≤ 1 / 16 := by
    calc
      delta ≤ smallContrastThreshold d (1 / 2) := by
        simpa only [delta, epsilon] using!
          boundedMultiplier_combinedContrast_le_threshold d
      _ ≤ (1 - (1 / 2 : ℝ)) / 8 :=
        smallContrastThreshold_le_eighth_gap d (by norm_num)
      _ = 1 / 16 := by norm_num
  have hsCont : ContinuousOn s (translatedCube d m z) :=
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).continuousOn.mul
      hthetaCont
  have hcacc := smallContrastDataSize_halfBall_le_caccioppoli
    (translatedCube_isOpen' m z) hsCont hharm hR hballB hdelta16 hclose
    (averageOn (boundedMultiplierCoverCell d m z p) h.toFun)
  let uInner := h.restrict (isOpen_euclideanBall x rho)
    ((euclideanBall_subset_euclideanBall hrho.le (by dsimp [rho]; linarith)).trans
      hballB)
  have hdataBall := smallContrastDataSize_ballToUnit_zero
    (alpha := (1 / 2 : ℝ)) hrho hBall
  have hdataInner := smallContrastDataSize_ballToUnit_zero
    (alpha := (1 / 2 : ℝ)) hrho uInner
  have hdataEq : smallContrastDataSize d (1 / 2)
      (ballToUnitH1 x hrho hBall) (fun _ ↦ 0) =
      smallContrastDataSize d (1 / 2)
        (ballToUnitH1 x hrho uInner) (fun _ ↦ 0) := by
    rw [hdataBall, hdataInner]
    congr 2
    apply integral_congr_ae
    filter_upwards with y
    rw [hBallGrad]
    rfl
  refine ⟨p, hp, hxcell, hballCell, hBall, hBallFun, hBallGrad, hpoint, ?_⟩
  rw [hdataEq]
  simpa only [R, rho, s, kappa, delta, uInner] using! hcacc

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
