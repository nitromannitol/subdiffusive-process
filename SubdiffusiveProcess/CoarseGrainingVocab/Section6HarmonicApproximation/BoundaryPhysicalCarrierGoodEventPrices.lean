import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierRadiusEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryGoodEventInverseRatio
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveForcedEquation

/-!
# Good-event prices for the physical-carrier radius endpoint

The datum part of the finite-height budget has already been externalized.
This module supplies the remaining parent datum and centered-force interfaces
on the translated good event, while retaining explicit prices for the two
affine comparison fields.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

private theorem memLp_hilbertify_of_forceBesovRegularity_physical
    {d : ℕ} {Q : TriadicCube d} {t : ℝ} {F : Vec d → Vec d}
    (hF : ForceBesovRegularity Q t F) :
    MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  let T : Vec d →L[ℝ] HilbertVec d :=
    ((HilbertVec.continuousLinearEquivVec d).symm).toContinuousLinearMap
  simpa [hilbertifyVecField] using T.comp_memLp' hF.memLp

/-- Good-event specialization with the two affine energies exposed as
radius-independent hypotheses. -/
theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_goodEventAt_physicalCarrier
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ}
        {sEnergy sGood K Av Aell : ℝ}
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
        (Q : TriadicCube d) (center : Vec d) (g : Vec d → Vec d)
        (u h v ell : H1Function (openCubeSet Q)),
        m ≤ L → omega ∈ goodEvent M none m z 1 sGood →
        64 * M.delta ^ 2 ≤ sGood → sGood ≤ 1 / 2 →
        openCubeSet Q ⊆ translatedCube d (m : ℤ) z →
        IsForcedEquation Q (aCutoffFamily M L omega) u
          (fun x ↦ -(cubeFluctuationVec Q g x)) →
        IsForcedEquation Q (aCutoffFamily M L omega) v (fun _ ↦ 0) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale center (Q.scale - 1))
          (fun y ↦ u.toFun y - h.toFun y) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (Set.univ : Set (Vec d)) (fun y ↦ v.toFun y - ell.toFun y) →
        localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v ≤ Av →
        localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) ell ≤ Aell →
        0 ≤ Av → 0 ≤ Aell →
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
          ((79 / 8 : ℝ) * Av + (57 / 8 : ℝ) * BE +
            4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE + 13 * Aell +
            3 * Ag +
            4 * boundaryCommonGapPowerBudget Q sEnergy sigma K C 0
              (u - h).toFun (fun x ↦ -(cubeFluctuationVec Q g x))) *
            boundaryThreeQuarterRadiusIterationConst := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_physicalCarrier d
  refine ⟨C, hC, ?_⟩
  intro M L m sEnergy sGood K Av Aell omega z Q center g u h v ell hmL
    hgood hsGoodLower hsGoodUpper hQ heqU heqV htraceU htraceV hEv hEell
    hAv hAell hs hs4 hK
  dsimp only
  let sigma := tailAverage M L m omega (translatedCube d (m : ℤ) z)
  intro hupper hlower hg hcentered
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
    have henv : 0 ≤ 1 + Section6Localization.subunitCollapseConstant d *
        Section6Localization.subunitEnvelope sGood m *
        Section6Localization.subunitDeviation M m
          (translatePotentialSample z omega) :=
      add_nonneg zero_le_one (mul_nonneg
        (mul_nonneg
          (Section6Localization.subunitCollapseConstant_pos d).le
          (Section6Localization.subunitEnvelope_pos sGood m).le) hdev)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr hsigma.le) henv)
        (Nat.cast_nonneg _)) (sq_nonneg _)
  have hweakU := isDivFormWeakSolutionOn_of_isForcedEquation_aCutoff
    M L omega Q u (cubeFluctuationVec Q g) heqU
  have hweakV : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v
      (fun _ ↦ 0) := by
    have hz := isDivFormWeakSolutionOn_of_isForcedEquation_aCutoff
      M L omega Q v (fun _ ↦ (0 : Vec d)) (by simpa using heqV)
    simpa using hz
  have hgOpen : MemVectorL2 (openCubeSet Q) (cubeFluctuationVec Q g) := by
    have hc := forceBesovRegularity_cubeFluctuationVec hg
    have hmem := memVectorL2_cubeSet_of_forceBesovRegularity hc
    rw [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at hmem
    exact hmem
  have htrace : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube Q center 1)
      (fun y ↦ u.toFun y - h.toFun y) := by
    simpa only [coarseCaccioppoliLocalOpenCube_one_eq_openCubeAtScale] using htraceU
  have huLp : MemLp (u - h).toFun (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa only [H1Function.sub_toFun] using
      u.memL2_normalizedCubeMeasure.sub h.memL2_normalizedCubeMeasure
  have hgLp : MemLp (fun x ↦
      HilbertVec.ofVec (-(cubeFluctuationVec Q g x))) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_hilbertify_of_forceBesovRegularity_physical hcentered
  have hEh : ∀ k : ℕ,
      let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
      descendantsAverage Q (k + 1) Eh ≤ BE := by
    intro k
    dsimp only [BE]
    exact (descendantsAverage_comparisonEnergy_eq_parent Q
      (aCutoffFamily M L omega) h (k + 1)).le
  have hBEfull : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega).coeffOn Q) h ≤ BE := by
    rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
      (Set.Subset.rfl) h, volumeAverage_openCubeSet_eq_cubeAverage]
  have hforce : ∀ j : ℕ,
      let rhoI := coarseCaccioppoliRadiusSequence j
      let rhoO := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun Q center rhoI
              (coarseCaccioppoliBufferedCutoffRadius rhoI rhoO))
            (cubeFluctuationVec Q g)) ≤ Ag := by
    intro j
    have hlt := coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
    have hinner : 0 < coarseCaccioppoliRadiusSequence j :=
      lt_of_lt_of_le (by norm_num) (coarseCaccioppoliRadiusSequence_mem_Icc j).1
    simpa only [Ag, sigma] using
      volumeAverage_boundaryCoerciveForceDensity_cubeFluctuation_le_goodEventAt
        M hmL hsGoodLower hsGoodUpper omega z hgood Q Q center hinner
          (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 hQ g hg
  have hraw := hbase M L omega u h v ell center hweakU hweakV hgOpen htrace
    htraceV hs hs4 hsigma hK hBE hAg hupper hlower hcentered huLp hgLp hEh
      hBEfull hforce
  dsimp only [sigma, BE, Ag] at hraw ⊢
  have hR : 0 ≤ boundaryThreeQuarterRadiusIterationConst :=
    boundaryThreeQuarterRadiusIterationConst_nonneg
  have hEvR := mul_le_mul_of_nonneg_right hEv hR
  have hEellR := mul_le_mul_of_nonneg_right hEell hR
  nlinarith only [hraw, hEvR, hEellR]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
