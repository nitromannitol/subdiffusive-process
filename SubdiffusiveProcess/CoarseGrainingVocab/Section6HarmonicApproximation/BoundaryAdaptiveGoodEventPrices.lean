module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventInverseRatio

@[expose] public section

/-!
# Good-event density prices for the adaptive boundary estimate

The shared `gap^(-8)` active-cell estimate no longer carries separate datum
and forcing density hypotheses.  The datum is bounded by the comparison-field
energy; the centered forcing is priced by the pointwise shell-ratio consequence
of the good event.

PROVENANCE: this is the density substitution immediately after the adaptive
radius selection in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryOuterCaccioppoli.lean`.
The GMC coefficient price uses the exponential shell-ratio carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Every consecutive canonical radius gap lies in `(0,1]`, so its negative
eighth power is at least one. -/
theorem one_le_coarseCaccioppoliRadiusSequence_gap_rpow_neg_eight (j : ℕ) :
    1 ≤ Real.rpow
      (coarseCaccioppoliRadiusSequence (j + 1) -
        coarseCaccioppoliRadiusSequence j) (-8 : ℝ) := by
  have hlt := coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have hinner := (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have houter := (coarseCaccioppoliRadiusSequence_mem_Icc (j + 1)).2
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
  · linarith
  · linarith
  · norm_num

omit [NeZero d] in
/-- The comparison datum satisfies the complete radius-sequence price with
its parent coefficient energy as the radius-independent budget. -/
theorem boundaryDatumDensity_sequence_le_parentEnergy_gapPower
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (center : Vec d)
    (h : H1Function (openCubeSet Q)) (j : ℕ) :
    let rhoInner := coarseCaccioppoliRadiusSequence j
    let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveDatumDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
      cubeAverage Q (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) h.grad) *
        Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  dsimp only
  have hlt := coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have hinner : 0 < coarseCaccioppoliRadiusSequence j :=
    lt_of_lt_of_le (by norm_num) (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have hbuffer := coarseCaccioppoliBufferedCutoffRadius_between hlt
  have hbase :=
    volumeAverage_boundaryCoerciveDatumDensity_localCanonicalFun_le_energy
      M L omega Q Q center hinner hbuffer.1 h
  have henergy0 : 0 ≤ cubeAverage Q (coefficientEnergyDensity
      (publicCoeffField Q (aCutoffFamily M L omega)) h.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) h.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hgap := one_le_coarseCaccioppoliRadiusSequence_gap_rpow_neg_eight j
  exact hbase.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap henergy0)

omit [NeZero d] in
/-- The centered force satisfies the complete radius-sequence price on a good
event.  The only coefficient factor is the explicit shell-ratio envelope. -/
theorem boundaryCenteredForceDensity_sequence_le_goodEvent_gapPower
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s t : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (Q : TriadicCube d) (center : Vec d)
    (hQ : openCubeSet Q ⊆ cube d (m : ℤ))
    (g : Vec d → Vec d) (hg : ForceBesovRegularity Q t g) (j : ℕ) :
    let rhoInner := coarseCaccioppoliRadiusSequence j
    let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
    let Ag :=
      (tailCoefficientCubeAverage M L m omega)⁻¹ *
        (1 + Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope s m *
          Section6Localization.subunitDeviation M m omega) *
        (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
          (cubeFluctuationVec Q g)) ≤
      Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  dsimp only
  have hlt := coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have hinner : 0 < coarseCaccioppoliRadiusSequence j :=
    lt_of_lt_of_le (by norm_num) (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have hbuffer := coarseCaccioppoliBufferedCutoffRadius_between hlt
  have hbase :=
    volumeAverage_boundaryCoerciveForceDensity_cubeFluctuation_le_goodEvent
      M hmL hsLower hsUpper omega hgood Q Q center hinner hbuffer.1 hQ g hg
  have hleft0 : 0 ≤ volumeAverage (openCubeSet Q)
      (boundaryCoerciveForceDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center
          (coarseCaccioppoliRadiusSequence j)
          (coarseCaccioppoliBufferedCutoffRadius
            (coarseCaccioppoliRadiusSequence j)
            (coarseCaccioppoliRadiusSequence (j + 1))))
        (cubeFluctuationVec Q g)) := by
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet Q)
    intro x _
    exact boundaryCoerciveForceDensity_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
  have hAg0 : 0 ≤
      (tailCoefficientCubeAverage M L m omega)⁻¹ *
        (1 + Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope s m *
          Section6Localization.subunitDeviation M m omega) *
        (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2 :=
    hleft0.trans hbase
  have hgap := one_le_coarseCaccioppoliRadiusSequence_gap_rpow_neg_eight j
  exact hbase.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap hAg0)

omit [NeZero d] in
/-- Translated-event companion of
`boundaryCenteredForceDensity_sequence_le_goodEvent_gapPower`. -/
theorem boundaryCenteredForceDensity_sequence_le_goodEventAt_gapPower
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s t : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hgood : omega ∈ goodEvent M none m z 1 s)
    (Q : TriadicCube d) (center : Vec d)
    (hQ : openCubeSet Q ⊆ translatedCube d (m : ℤ) z)
    (g : Vec d → Vec d) (hg : ForceBesovRegularity Q t g) (j : ℕ) :
    let rhoInner := coarseCaccioppoliRadiusSequence j
    let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
    let Ag :=
      (tailAverage M L m omega (translatedCube d (m : ℤ) z))⁻¹ *
        (1 + Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope s m *
          Section6Localization.subunitDeviation M m
            (translatePotentialSample z omega)) *
        (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
          (cubeFluctuationVec Q g)) ≤
      Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
  dsimp only
  have hlt := coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have hinner : 0 < coarseCaccioppoliRadiusSequence j :=
    lt_of_lt_of_le (by norm_num) (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have hbuffer := coarseCaccioppoliBufferedCutoffRadius_between hlt
  have hbase :=
    volumeAverage_boundaryCoerciveForceDensity_cubeFluctuation_le_goodEventAt
      M hmL hsLower hsUpper omega z hgood Q Q center hinner hbuffer.1 hQ g hg
  have hleft0 : 0 ≤ volumeAverage (openCubeSet Q)
      (boundaryCoerciveForceDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun Q center
          (coarseCaccioppoliRadiusSequence j)
          (coarseCaccioppoliBufferedCutoffRadius
            (coarseCaccioppoliRadiusSequence j)
            (coarseCaccioppoliRadiusSequence (j + 1))))
        (cubeFluctuationVec Q g)) := by
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet Q)
    intro x _
    exact boundaryCoerciveForceDensity_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
  have hAg0 : 0 ≤
      (tailAverage M L m omega (translatedCube d (m : ℤ) z))⁻¹ *
        (1 + Section6Localization.subunitCollapseConstant d *
          Section6Localization.subunitEnvelope s m *
          Section6Localization.subunitDeviation M m
            (translatePotentialSample z omega)) *
        (Fintype.card (Fin d) : ℝ) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q t g ^ 2 :=
    hleft0.trans hbase
  have hgap := one_le_coarseCaccioppoliRadiusSequence_gap_rpow_neg_eight j
  exact hbase.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgap hAg0)

/-- Good-event specialization of the adaptive boundary-radius theorem.  Both
formerly carried density hypotheses are discharged: the datum by its parent
energy and the centered force by the shell-ratio estimate. -/
theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_goodEvent_centered
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ}
        {sEnergy sGood K : ℝ}
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (Q : TriadicCube d) (center : Vec d) (g : Vec d → Vec d)
        (u h : H1Function (openCubeSet Q)),
        m ≤ L → omega ∈ goodEvent M none m 0 1 sGood →
        64 * M.delta ^ 2 ≤ sGood → sGood ≤ 1 / 2 →
        openCubeSet Q ⊆ cube d (m : ℤ) →
        IsForcedEquation Q (aCutoffFamily M L omega) u
          (fun x ↦ -(cubeFluctuationVec Q g x)) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale center (Q.scale - 1))
          (fun y ↦ u.toFun y - h.toFun y) →
        0 < sEnergy → sEnergy ≤ 1 / 4 → 0 < K →
        (tailCoefficientCubeAverage M L m omega)⁻¹ *
            Ch02.LambdaSq Q (sEnergy / 6) (.finite 2)
              (aCutoffFamily M L omega) ≤ K →
        tailCoefficientCubeAverage M L m omega *
            (Ch02.lambdaSq Q (sEnergy / 6) (.finite 2)
              (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (sEnergy / 3) g →
        ForceBesovRegularity Q (sEnergy / 3)
          (fun x ↦ -(cubeFluctuationVec Q g x)) →
        let sigma := tailCoefficientCubeAverage M L m omega
        let BE := cubeAverage Q (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) h.grad)
        let Ag := sigma⁻¹ *
          (1 + Section6Localization.subunitCollapseConstant d *
            Section6Localization.subunitEnvelope sGood m *
            Section6Localization.subunitDeviation M m omega) *
          (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (sEnergy / 3) g ^ 2
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
            (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.grad x)) ≤
          ((5 / 2 : ℝ) * BE +
              boundaryCommonGapPowerBudget Q sEnergy sigma K C BE
                (fun y ↦ u.toFun y - h.toFun y)
                (fun x ↦ -(cubeFluctuationVec Q g x)) +
              (5 / 2 : ℝ) * Ag) *
            coarseCaccioppoliRadiusIterationConst 8 := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget_of_projectedTrace d
  refine ⟨C, hC, ?_⟩
  intro M L m sEnergy sGood K omega Q center g u h hmL hgood
    hsGoodLower hsGoodUpper hQ heq htrace hsEnergy hsEnergy4 hK
    hupper hlower hg hcentered
  let sigma := tailCoefficientCubeAverage M L m omega
  let BE := cubeAverage Q (coefficientEnergyDensity
    (publicCoeffField Q (aCutoffFamily M L omega)) h.grad)
  let Ag := sigma⁻¹ *
    (1 + Section6Localization.subunitCollapseConstant d *
      Section6Localization.subunitEnvelope sGood m *
      Section6Localization.subunitDeviation M m omega) *
    (Fintype.card (Fin d) : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (sEnergy / 3) g ^ 2
  have hsigma : 0 < sigma := tailCoefficientCubeAverage_pos M L m omega
  have hBE : 0 ≤ BE :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) h.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hAg : 0 ≤ Ag := by
    dsimp [Ag, sigma]
    have hdev := subunitDeviation_nonneg M m omega
    have hB : 0 ≤ 1 + Section6Localization.subunitCollapseConstant d *
        Section6Localization.subunitEnvelope sGood m *
        Section6Localization.subunitDeviation M m omega :=
      add_nonneg zero_le_one
        (mul_nonneg
          (mul_nonneg (Section6Localization.subunitCollapseConstant_pos d).le
            (Section6Localization.subunitEnvelope_pos sGood m).le)
          hdev)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hsigma.le) hB) (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
        BE * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
    intro j
    simpa only [BE] using
      boundaryDatumDensity_sequence_le_parentEnergy_gapPower
        M L omega Q center h j
  have hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
            (cubeFluctuationVec Q g)) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
    intro j
    simpa only [Ag, sigma] using
      boundaryCenteredForceDensity_sequence_le_goodEvent_gapPower
        M hmL hsGoodLower hsGoodUpper omega hgood Q center hQ g hg j
  simpa only [sigma, BE, Ag] using
    hbase M L omega u h center heq htrace hsEnergy hsEnergy4 hsigma hK
      hBE hAg hupper hlower hcentered hdatum hforce



theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_goodEventAt_centered
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ}
        {sEnergy sGood K : ℝ}
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
        (Q : TriadicCube d) (center : Vec d) (g : Vec d → Vec d)
        (u h : H1Function (openCubeSet Q)),
        m ≤ L → omega ∈ goodEvent M none m z 1 sGood →
        64 * M.delta ^ 2 ≤ sGood → sGood ≤ 1 / 2 →
        openCubeSet Q ⊆ translatedCube d (m : ℤ) z →
        IsForcedEquation Q (aCutoffFamily M L omega) u
          (fun x ↦ -(cubeFluctuationVec Q g x)) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale center (Q.scale - 1))
          (fun y ↦ u.toFun y - h.toFun y) →
        0 < sEnergy → sEnergy ≤ 1 / 4 → 0 < K →
        let sigma := tailAverage M L m omega (translatedCube d (m : ℤ) z)
        sigma⁻¹ * Ch02.LambdaSq Q (sEnergy / 6) (.finite 2)
              (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (sEnergy / 6) (.finite 2)
              (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (sEnergy / 3) g →
        ForceBesovRegularity Q (sEnergy / 3)
          (fun x ↦ -(cubeFluctuationVec Q g x)) →
        let BE := cubeAverage Q (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) h.grad)
        let Ag := sigma⁻¹ *
          (1 + Section6Localization.subunitCollapseConstant d *
            Section6Localization.subunitEnvelope sGood m *
            Section6Localization.subunitDeviation M m
              (translatePotentialSample z omega)) *
          (Fintype.card (Fin d) : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q (sEnergy / 3) g ^ 2
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
            (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.grad x)) ≤
          ((5 / 2 : ℝ) * BE +
              boundaryCommonGapPowerBudget Q sEnergy sigma K C BE
                (fun y ↦ u.toFun y - h.toFun y)
                (fun x ↦ -(cubeFluctuationVec Q g x)) +
              (5 / 2 : ℝ) * Ag) *
            coarseCaccioppoliRadiusIterationConst 8 := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget_of_projectedTrace d
  refine ⟨C, hC, ?_⟩
  intro M L m sEnergy sGood K omega z Q center g u h hmL hgood
    hsGoodLower hsGoodUpper hQ heq htrace hsEnergy hsEnergy4 hK
  dsimp only
  intro hupper hlower hg hcentered
  let sigma := tailAverage M L m omega (translatedCube d (m : ℤ) z)
  let BE := cubeAverage Q (coefficientEnergyDensity
    (publicCoeffField Q (aCutoffFamily M L omega)) h.grad)
  let Ag := sigma⁻¹ *
    (1 + Section6Localization.subunitCollapseConstant d *
      Section6Localization.subunitEnvelope sGood m *
      Section6Localization.subunitDeviation M m
        (translatePotentialSample z omega)) *
    (Fintype.card (Fin d) : ℝ) *
    scaleNormalizedPositiveBesovVectorSeminormTwo Q (sEnergy / 3) g ^ 2
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L m (translatePotentialSample z omega)
  have hBE : 0 ≤ BE :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) h.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hAg : 0 ≤ Ag := by
    dsimp [Ag, sigma]
    have hdev := subunitDeviation_nonneg M m (translatePotentialSample z omega)
    have hB : 0 ≤ 1 + Section6Localization.subunitCollapseConstant d *
        Section6Localization.subunitEnvelope sGood m *
        Section6Localization.subunitDeviation M m
          (translatePotentialSample z omega) :=
      add_nonneg zero_le_one
        (mul_nonneg
          (mul_nonneg (Section6Localization.subunitCollapseConstant_pos d).le
            (Section6Localization.subunitEnvelope_pos sGood m).le)
          hdev)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hsigma.le) hB) (Nat.cast_nonneg _))
      (sq_nonneg _)
  have hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
        BE * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
    intro j
    simpa only [BE] using
      boundaryDatumDensity_sequence_le_parentEnergy_gapPower
        M L omega Q center h j
  have hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
            (cubeFluctuationVec Q g)) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ) := by
    intro j
    simpa only [Ag, sigma] using
      boundaryCenteredForceDensity_sequence_le_goodEventAt_gapPower
        M hmL hsGoodLower hsGoodUpper omega z hgood Q center hQ g hg j
  simpa only [sigma, BE, Ag] using
    hbase M L omega u h center heq htrace hsEnergy hsEnergy4 hsigma hK
      hBE hAg hupper hlower hcentered hdatum hforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
