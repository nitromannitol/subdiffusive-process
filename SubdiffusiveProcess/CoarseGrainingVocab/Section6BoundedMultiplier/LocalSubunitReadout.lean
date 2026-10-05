module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalCaccioppoliReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitContraction

@[expose] public section

/-!
# Local triadic readout below scale one

This module inserts the random-radius cutoff normalization and the proved
Caccioppoli datum price into the concentric small-contrast contraction.  It is
the deterministic local leg of the `j > m` branch.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

private theorem translatedCube_isOpen_local {d : ℕ} (m : ℤ) (z : Vec d) :
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

/-- On the restricted gradient-good event, the random localization radius is
bounded below by the same formula with the deterministic event threshold in
place of the random Lipschitz modulus. -/
theorem deterministicRadiusLower_le_boundedMultiplierLocalRadius
    {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    {omega : Sample d}
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z) :
    min (6 : ℝ)⁻¹
        (min ((3 : ℝ) ^ m / 4)
          (boundedMultiplierEpsilonStar d /
            (1 + boundedMultiplierCoverOscillationThreshold M m / 2))) ≤
      boundedMultiplierLocalRadius M L m z omega := by
  have hG0 := coveringLogLipschitzModulus_nonneg M L m z omega
  have hG : coveringLogLipschitzModulus M L m z omega ≤
      boundedMultiplierCoverOscillationThreshold M m / 2 := by
    simpa only [coveringRestrictedGradientGood, Set.mem_ofPred_eq] using hgood
  have hthreshold0 : 0 ≤ boundedMultiplierCoverOscillationThreshold M m / 2 :=
    hG0.trans hG
  have hdenG : 0 < 1 + coveringLogLipschitzModulus M L m z omega := by
    linarith
  have hdenThreshold :
      0 < 1 + boundedMultiplierCoverOscillationThreshold M m / 2 := by
    linarith
  have hfrac : boundedMultiplierEpsilonStar d /
        (1 + boundedMultiplierCoverOscillationThreshold M m / 2) ≤
      boundedMultiplierEpsilonStar d /
        (1 + coveringLogLipschitzModulus M L m z omega) := by
    rw [div_le_div_iff₀ hdenThreshold hdenG]
    exact mul_le_mul_of_nonneg_left (by linarith)
      (boundedMultiplierEpsilonStar_pos d).le
  exact min_le_min le_rfl (min_le_min le_rfl hfrac)

/-- At every collared point, the canonical representative contracts on
triadic sub-balls of the random small-contrast ball.  The Schauder datum has
already been replaced by the explicit contrast-two Caccioppoli price. -/
theorem exists_coverCell_localSubunitContraction_caccioppoli
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : Sample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    (n : ℕ) :
    let R := boundedMultiplierLocalRadius M L m z omega
    let rho := R / 2
    ∃ p ∈ shellCoverShifts d m,
      x ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall x R ⊆ boundedMultiplierCoverCell d m z p ∧
      oscillationOn
          (Metric.ball x
            (rho / (2 * (d : ℝ)) *
              (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))))
          (euclideanBallAverageRepresentative h.toFun) ≤
        smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d x R h.toFun
              (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) *
          rho * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
  dsimp only
  let R := boundedMultiplierLocalRadius M L m z omega
  let rho := R / 2
  have hR : 0 < R := boundedMultiplierLocalRadius_pos M L m z omega
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  obtain ⟨p, hp, hxcell, hballCell⟩ :=
    exists_coverCell_euclideanBall_subset hcollar hR
      (boundedMultiplierLocalRadius_le_mesh M L m z omega)
      (boundedMultiplierLocalRadius_le_ambient M L m z omega)
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
      |Real.log (aCutoff M L omega y) -
        Real.log (aCutoff M L omega x)| ≤ R * G := by
    intro y hy
    have hpair := abs_log_aCutoff_sub_le_coveringLogLipschitzModulus_mul_norm
      M L m z omega p hp (hballCell hy) hxcell
    have hdist : ‖y - x‖ < R := euclideanBall_subset_metricBall hR hy
    exact hpair.trans (by
      simpa [G, mul_comm] using mul_le_mul_of_nonneg_left hdist.le
        (coveringLogLipschitzModulus_nonneg M L m z omega))
  have hscale : R * G ≤ 1 * epsilon := by
    simpa only [R, G, epsilon, one_mul] using
      boundedMultiplierLocalRadius_mul_modulus_le M L m z omega
  have hnormalized : ∀ y ∈ euclideanBall x R,
      |aCutoff M L omega y * theta y /
          (aCutoff M L omega x * b) - 1| ≤ delta := by
    simpa only [delta, epsilon, one_mul] using
      abs_normalized_cutoff_multiplier_sub_one_le (c := 1)
        (fun y _hy ↦ aCutoff_pos M L omega y)
        (aCutoff_pos M L omega x) hb
        (mul_nonneg hR.le
          (coveringLogLipschitzModulus_nonneg M L m z omega))
        hscale hlog (fun y hy ↦ hthetaClose y (hballB hy))
  have hclose : ∀ y ∈ euclideanBall x R,
      |kappa⁻¹ * s y - 1| ≤ delta := by
    intro y hy
    have h := hnormalized y hy
    convert h using 1
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
        halfBallCaccioppoliDataPrice d x R h.toFun
          (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) := by
    have hraw := smallContrastDataSize_halfBall_le_caccioppoli
      (translatedCube_isOpen_local m z) hsCont hharm hR hballB
      hdelta16 hclose
      (averageOn (boundedMultiplierCoverCell d m z p) h.toFun)
    simpa only [rho, uBall] using hraw
  have hcontract :=
    canonicalRepresentative_subunit_contraction_of_smallContrast
      (translatedCube_isOpen_local m z) hsCont hharm hrho hballRho
      kappa delta (1 / 2) hd (by constructor <;> norm_num)
      (boundedMultiplier_combinedContrast_nonneg d)
      (boundedMultiplier_combinedContrast_le_threshold d)
      (boundedMultiplier_combinedContrast_lt_one d)
      (fun y hy ↦ hclose y
        ((euclideanBall_subset_euclideanBall hrho.le (by
          dsimp only [rho]
          linarith)) hy)) n
  have hC0 : 0 ≤ smallContrastSchauderConstant d :=
    smallContrastSchauderConstant_nonneg d
  have hpow0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hprice :
      smallContrastSchauderConstant d *
            smallContrastDataSize d (1 / 2)
              (ballToUnitH1 x hrho uBall) (fun _ ↦ 0) *
          rho * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) ≤
        smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d x R h.toFun
              (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) *
          rho * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdata hC0) hrho.le) hpow0
  refine ⟨p, hp, hxcell, hballCell, ?_⟩
  have hcontract' :
      oscillationOn
          (Metric.ball x
            (rho / (2 * (d : ℝ)) *
              (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))))
          (euclideanBallAverageRepresentative h.toFun) ≤
        smallContrastSchauderConstant d *
            smallContrastDataSize d (1 / 2)
              (ballToUnitH1 x hrho uBall) (fun _ ↦ 0) *
          rho * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
    simpa only [R, rho, s, kappa, delta, uBall] using hcontract
  exact hcontract'.trans hprice

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
