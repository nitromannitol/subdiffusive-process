module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalSubunitReadout

@[expose] public section

/-!
# Arbitrary-radius local small-contrast contraction

The adaptive radius is convenient above scale one.  At nonpositive parent
scales we instead use a smaller deterministic radius.  This module records
the common analytic argument at any positive radius below the adaptive one.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

private theorem translatedCube_isOpen_arbitrary {d : ℕ} (m : ℤ) (z : Vec d) :
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

/-- At any positive radius below the adaptive localization radius, the
canonical representative contracts on concentric triadic sub-balls.  The
Caccioppoli datum may be centered at an arbitrary scalar `c`. -/
theorem exists_coverCell_localSubunitContraction_caccioppoli_of_radius
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : Sample d) {x : Vec d}
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
    (c : ℝ) (n : ℕ) :
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
            halfBallCaccioppoliDataPrice d x R h.toFun c *
          rho * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
  dsimp only
  let rho := R / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
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
    have hG : 0 ≤ G := coveringLogLipschitzModulus_nonneg M L m z omega
    calc
      R * G ≤ boundedMultiplierLocalRadius M L m z omega * G :=
        mul_le_mul_of_nonneg_right hRadaptive hG
      _ ≤ epsilon := by
        simpa only [G, epsilon] using
          boundedMultiplierLocalRadius_mul_modulus_le M L m z omega
      _ = 1 * epsilon := by ring
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
        halfBallCaccioppoliDataPrice d x R h.toFun c := by
    have hraw := smallContrastDataSize_halfBall_le_caccioppoli
      (translatedCube_isOpen_arbitrary m z) hsCont hharm hR hballB
      hdelta16 hclose c
    simpa only [rho, uBall] using hraw
  have hcontract :=
    canonicalRepresentative_subunit_contraction_of_smallContrast
      (translatedCube_isOpen_arbitrary m z) hsCont hharm hrho hballRho
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
            halfBallCaccioppoliDataPrice d x R h.toFun c *
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
    simpa only [rho, s, kappa, delta, uBall] using hcontract
  exact hcontract'.trans hprice

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
