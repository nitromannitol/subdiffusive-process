import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryThreeQuarterRadiusIteration

/-!
# Radius endpoint for the combined signed boundary estimate

The localized signed finite-height row is iterated on the canonical boundary
radii.  All four manuscript budgets remain outside the affine correction;
only the common low-frequency carrier receives the inverse-gap weight.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- The complete signed boundary radius endpoint. -/
theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_combinedSigned
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ag : ℝ} {g : Vec d → Vec d}
        (u r v hRes : H1Function (openCubeSet Q)) (center : Vec d),
        (∀ x, u.grad x = r.grad x + v.grad x) →
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) r g →
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v
            (fun _ ↦ 0) →
        MemVectorL2 (openCubeSet Q) g →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun x ↦ r.toFun x - hRes.toFun x) →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K → 0 ≤ BE → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g x) →
        MemLp (r - hRes).toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad);
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) hRes ≤ BE →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤ Ag) →
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ) (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
          (4 * localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) v +
            (29 / 8 : ℝ) * BE + (5 / 2 : ℝ) * Ag +
            4 * boundaryCommonGapPowerBudget Q s sigma K C BE
              (r - hRes).toFun (fun x ↦ -g x)) *
            boundaryThreeQuarterRadiusIterationConst := by
  obtain ⟨C, hC, hlocal⟩ := exists_boundaryCrossScale_combinedSignedLocalizedStep d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE Ag g u r v hRes center hgrad hweakR hweakV
    hg hzero hs hs4 hsigma hK hBE hAg hupper hlower hreg hresL2 hgL2 hEh
    hBEfull hforce
  let energy : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let Ev := localizedCoeffEnergyValue (openCubeSet Q)
    ((aCutoffFamily M L omega).coeffOn Q) v
  let common := boundaryCommonGapPowerBudget Q s sigma K C BE
    (r - hRes).toFun (fun x ↦ -g x)
  let A := 4 * Ev + (29 / 8 : ℝ) * BE + (5 / 2 : ℝ) * Ag + 4 * common
  have hEv : 0 ≤ Ev := by
    dsimp only [Ev]
    exact localizedCoeffEnergyValue_openCubeSet_nonneg Q
      (aCutoffFamily M L omega) v
  have hcommon : 0 ≤ common := by
    dsimp only [common]
    exact boundaryCommonGapPowerBudget_nonneg Q (r - hRes).toFun
      (fun x ↦ -g x) hs hsigma hK hC hBE hreg
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have henergy0 : ∀ x ∈ openCubeSet Q, 0 ≤ energy x := by
    intro x _
    exact mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have henergyInt : IntegrableOn energy (openCubeSet Q) := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have hbounded : CoarseCaccioppoliRadiusBoundedAbove
      (fun rho ↦ boundaryCrossScaleEnergyProfile Q Q center rho energy) :=
    boundaryCrossScaleEnergyProfile_boundedAbove henergy0 henergyInt
  have hrec : ∀ j : ℕ,
      boundaryCrossScaleEnergyProfile Q Q center
          (coarseCaccioppoliRadiusSequence j) energy ≤
        (3 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center
            (coarseCaccioppoliRadiusSequence (j + 1)) energy +
          A * Real.rpow
            (coarseCaccioppoliRadiusSequence (j + 1) -
              coarseCaccioppoliRadiusSequence j) (-8 : ℝ) := by
    intro j
    have hj := hlocal M L omega u r v hRes center hgrad hweakR hweakV hg hzero
      (coarseCaccioppoliRadiusSequence_mem_Icc j).1
      (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j))
      (coarseCaccioppoliRadiusSequence_lt_one (j + 1))
      hs hs4 hsigma hK hBE hupper hlower hreg hresL2 hgL2 hEh (hforce j)
    have hj' := boundaryCrossScale_physical_threeQuarter_of_combinedSignedStep
      M L omega Q Q center u r v hRes hgrad hBEfull hj
    let gap := coarseCaccioppoliRadiusSequence (j + 1) -
      coarseCaccioppoliRadiusSequence j
    have hgap : 0 < gap := by
      dsimp only [gap]
      exact sub_pos.mpr
        (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j))
    have hgapOne : gap ≤ 1 := by
      have hleft := (coarseCaccioppoliRadiusSequence_mem_Icc j).1
      have hright := (coarseCaccioppoliRadiusSequence_mem_Icc (j + 1)).2
      dsimp only [gap]
      linarith
    have hweight : 1 ≤ Real.rpow gap (-8 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hgap hgapOne (by norm_num)
    have hbase0 : 0 ≤ 4 * Ev + (29 / 8 : ℝ) * BE + (5 / 2 : ℝ) * Ag := by
      positivity
    have hbaseWeight := le_mul_of_one_le_right hbase0 hweight
    dsimp only [energy, Ev, common, A, gap] at hj' hbaseWeight ⊢
    nlinarith only [hj', hbaseWeight]
  simpa only [energy, Ev, common, A] using
    boundary_threeQuarter_radius_iteration hA hbounded hrec

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
