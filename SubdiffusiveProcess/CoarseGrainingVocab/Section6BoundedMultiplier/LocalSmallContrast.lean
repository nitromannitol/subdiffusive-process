module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalBallGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RestrictedGradientEnvelope
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastLocalRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastNormalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastParameter
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubcubeAveraging

@[expose] public section

/-!
# Random-radius small-contrast localization

The radius is a measurable function of the restricted-coefficient gradient
envelope.  Its deterministic collars place the whole ball in one cover cell;
its final factor makes the logarithmic coefficient oscillation small.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

private theorem translatedCube_isOpen {d : ℕ} (m : ℤ) (z : Vec d) :
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

/-- The local radius selected from the restricted measurable gradient
envelope. -/
def boundedMultiplierLocalRadius {d : ℕ} (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (omega : Sample d) : ℝ :=
  min (6 : ℝ)⁻¹
    (min ((3 : ℝ) ^ m / 4)
      (boundedMultiplierEpsilonStar d /
        (1 + coveringLogLipschitzModulus M L m z omega)))

theorem boundedMultiplierLocalRadius_pos {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    0 < boundedMultiplierLocalRadius M L m z omega := by
  apply lt_min (by norm_num)
  apply lt_min (by positivity)
  exact div_pos (boundedMultiplierEpsilonStar_pos d)
    (by linarith [coveringLogLipschitzModulus_nonneg M L m z omega])

theorem boundedMultiplierLocalRadius_le_mesh {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    boundedMultiplierLocalRadius M L m z omega ≤ (6 : ℝ)⁻¹ :=
  min_le_left _ _

theorem boundedMultiplierLocalRadius_half_pos {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    0 < boundedMultiplierLocalRadius M L m z omega / 2 := by
  exact div_pos (boundedMultiplierLocalRadius_pos M L m z omega) (by norm_num)

theorem boundedMultiplierLocalRadius_le_ambient {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    boundedMultiplierLocalRadius M L m z omega ≤ (3 : ℝ) ^ m / 4 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem boundedMultiplierLocalRadius_mul_modulus_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    boundedMultiplierLocalRadius M L m z omega *
        coveringLogLipschitzModulus M L m z omega ≤
      boundedMultiplierEpsilonStar d := by
  let G := coveringLogLipschitzModulus M L m z omega
  let epsilon := boundedMultiplierEpsilonStar d
  have hG : 0 ≤ G := coveringLogLipschitzModulus_nonneg M L m z omega
  have hden : 0 < 1 + G := by linarith
  have hr : boundedMultiplierLocalRadius M L m z omega ≤
      epsilon / (1 + G) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmul := mul_le_mul_of_nonneg_right hr hG
  have heps : 0 ≤ epsilon := (boundedMultiplierEpsilonStar_pos d).le
  calc
    boundedMultiplierLocalRadius M L m z omega * G ≤
        epsilon / (1 + G) * G := hmul
    _ ≤ epsilon := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith

/-- The local point-to-ball-average estimate obtained from the normalized
small-contrast Schauder theorem.  Caccioppoli is applied in the next wrapper
to bound the displayed rescaled gradient datum. -/
theorem exists_coverCell_localSmallContrast_ballAverage {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : Sample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ} (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y) (translatedCube d m z) h) :
    let R := boundedMultiplierLocalRadius M L m z omega
    let rho := R / 2
    ∃ p ∈ shellCoverShifts d m,
      x ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall x R ⊆ boundedMultiplierCoverCell d m z p ∧
      ∃ hBall : H1Function (euclideanBall x rho),
        hBall.toFun = h.toFun ∧ hBall.grad = h.grad ∧
        |euclideanBallAverageRepresentative h.toFun x -
            averageOn (euclideanBall x (rho / 2)) h.toFun| ≤
          (smallContrastSchauderConstant d *
            smallContrastDataSize d (1 / 2)
              (ballToUnitH1 x
                (boundedMultiplierLocalRadius_half_pos M L m z omega)
                hBall) (fun _ ↦ 0)) *
            rho ^ (1 - (1 / 2 : ℝ)) * (rho / 2) ^ (1 / 2 : ℝ) := by
  let R := boundedMultiplierLocalRadius M L m z omega
  let rho := R / 2
  let delta := Real.exp (boundedMultiplierEpsilonStar d) *
    (1 + boundedMultiplierEpsilonStar d) - 1
  have hR := boundedMultiplierLocalRadius_pos M L m z omega
  have hrho : 0 < rho := by dsimp [rho, R]; positivity
  obtain ⟨p, hp, hxcell, hballCell⟩ :=
    exists_coverCell_euclideanBall_subset hcollar hR
      (boundedMultiplierLocalRadius_le_mesh M L m z omega)
      (boundedMultiplierLocalRadius_le_ambient M L m z omega)
  have hballR : euclideanBall x rho ⊆ euclideanBall x R :=
    euclideanBall_subset_euclideanBall hrho.le (by dsimp [rho]; linarith)
  have hballB : euclideanBall x rho ⊆ translatedCube d m z :=
    hballR.trans (hballCell.trans Set.inter_subset_left)
  have hlog : ∀ y ∈ euclideanBall x rho,
      |Real.log (aCutoff M L omega y) - Real.log (aCutoff M L omega x)| ≤
        rho * coveringLogLipschitzModulus M L m z omega := by
    intro y hy
    have hpair := abs_log_aCutoff_sub_le_coveringLogLipschitzModulus_mul_norm
      M L m z omega p hp (hballCell (hballR hy)) hxcell
    have hdist : ‖y - x‖ < rho := euclideanBall_subset_metricBall hrho hy
    exact hpair.trans (by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hdist.le
        (coveringLogLipschitzModulus_nonneg M L m z omega))
  have hnormalized : ∀ y ∈ euclideanBall x rho,
      |aCutoff M L omega y * theta y /
          (aCutoff M L omega x * b) - 1| ≤ delta := by
    have hscale : rho * coveringLogLipschitzModulus M L m z omega ≤
        1 * boundedMultiplierEpsilonStar d := by
      have hG := coveringLogLipschitzModulus_nonneg M L m z omega
      have hhalf : rho * coveringLogLipschitzModulus M L m z omega ≤
          R * coveringLogLipschitzModulus M L m z omega := by
        apply mul_le_mul_of_nonneg_right _ hG
        dsimp [rho]
        linarith [hR]
      exact hhalf.trans (by simpa only [one_mul, R] using
        boundedMultiplierLocalRadius_mul_modulus_le M L m z omega)
    simpa only [one_mul] using abs_normalized_cutoff_multiplier_sub_one_le
      (c := 1)
      (fun y _hy ↦ aCutoff_pos M L omega y) (aCutoff_pos M L omega x) hb
      (mul_nonneg hrho.le
        (coveringLogLipschitzModulus_nonneg M L m z omega))
      hscale
      hlog (fun y hy ↦ hthetaClose y (hballB hy))
  have hclose : ∀ y ∈ euclideanBall x rho,
      |(aCutoff M L omega x * b)⁻¹ *
          (aCutoff M L omega y * theta y) - 1| ≤ delta := by
    intro y hy
    have h := hnormalized y hy
    convert h using 1
    field_simp [(aCutoff_pos M L omega x).ne', hb.ne']
  have hcont : ContinuousOn (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hlocal := canonicalRepresentative_sub_ballAverage_le_of_smallContrast
    (translatedCube_isOpen m z) hcont hharm hrho hballB
    (aCutoff M L omega x * b) delta (1 / 2) hd
    (by constructor <;> norm_num)
    (boundedMultiplier_combinedContrast_nonneg d)
    (boundedMultiplier_combinedContrast_le_threshold d)
    (boundedMultiplier_combinedContrast_lt_one d) hclose
  let hBall := h.restrict (isOpen_euclideanBall x rho) hballB
  refine ⟨p, hp, hxcell, hballCell, hBall, rfl, rfl, ?_⟩
  simpa only [R, rho, delta, hBall] using hlocal

/-- The same local Schauder readout after the pure averaging comparison from
the short ball to its selected cover cell.  This remains a local analytic
readout; the outer consumer now takes target-local oscillation directly. -/
theorem exists_coverCell_localSmallContrast_cellAverage {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : Sample d) {x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {theta : Vec d → ℝ} (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y) (translatedCube d m z) h) :
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
                  averageOn (boundedMultiplierCoverCell d m z p) h.toFun) := by
  dsimp only
  let R := boundedMultiplierLocalRadius M L m z omega
  let rho := R / 2
  obtain ⟨p, hp, hxcell, hballCell, hBall, hBallFun, hBallGrad, hpoint⟩ :=
    exists_coverCell_localSmallContrast_ballAverage hd M L m z omega
      hcollar hthetaCont hb hthetaClose hharm
  let Q := boundedMultiplierCoverCell d m z p
  let P := euclideanBall x (rho / 2)
  have hR : 0 < R := boundedMultiplierLocalRadius_pos M L m z omega
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hPsubR : P ⊆ euclideanBall x R := by
    exact euclideanBall_subset_euclideanBall (by positivity)
      (by dsimp [P, rho]; linarith)
  have hPQ : P ⊆ Q := hPsubR.trans hballCell
  have hPmeas : MeasurableSet P := (isOpen_euclideanBall x (rho / 2)).measurableSet
  have hPpos : 0 < (volume P).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        x (by positivity : 0 < rho / 2)))
  have hQtop : volume Q ≠ ⊤ := by
    apply ne_of_lt
    refine (measure_mono (Set.inter_subset_right : Q ⊆
      translatedCube d 0 (z + physicalShellCoverCenter 0 p))).trans_lt ?_
    have htranslate : translatedCube d 0 (z + physicalShellCoverCenter 0 p) =
        translateSet (z + physicalShellCoverCenter 0 p)
          (openCubeSet (originCube d 0)) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        apply mem_translateSet_iff_sub_mem.2
        simpa [cube] using hu
      · intro hy
        have hy' := mem_translateSet_iff_sub_mem.mp hy
        refine ⟨y - (z + physicalShellCoverCenter 0 p), ?_, ?_⟩
        · simpa [cube] using hy'
        · ext i
          simp
    rw [htranslate]
    rw [volume_translateSet_eq]
    exact volume_openCubeSet_lt_top (originCube d 0)
  have hQpos : 0 < (volume Q).toReal := by
    have hle : volume P ≤ volume Q := measure_mono hPQ
    have hPtop := Homogenization.Book.Ch01.volume_euclideanBall_ne_top x (rho / 2)
    exact hPpos.trans_le (ENNReal.toReal_mono hQtop hle)
  have hQB : Q ⊆ translatedCube d m z := Set.inter_subset_left
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hQtop⟩
  have hmemQ : MemLp h.toFun 2 (volume.restrict Q) :=
    h.memL2.mono_measure (Measure.restrict_mono hQB le_rfl)
  have hfQ : IntegrableOn h.toFun Q := hmemQ.integrable one_le_two
  have hf2Q : IntegrableOn (fun y ↦ h.toFun y ^ 2) Q := hmemQ.integrable_sq
  have hmeanBall := abs_averageOn_subset_sub_averageOn_le hPmeas hPQ
    hQtop hQpos hPpos hfQ hf2Q
  refine ⟨p, hp, hxcell, hballCell, hBall, hBallFun, hBallGrad, ?_⟩
  have htri := abs_sub_le (euclideanBallAverageRepresentative h.toFun x)
    (averageOn P h.toFun) (averageOn Q h.toFun)
  exact htri.trans (add_le_add (by simpa only [P] using hpoint)
    (by simpa only [P, Q] using hmeanBall))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
