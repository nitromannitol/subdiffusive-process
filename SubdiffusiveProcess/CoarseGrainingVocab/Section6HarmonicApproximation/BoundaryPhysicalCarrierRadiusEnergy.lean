module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierLocalizedStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryThreeQuarterRadiusIteration

@[expose] public section

/-!
# Radius endpoint for the physical-carrier boundary estimate

The explicit three-quarter row is iterated on the canonical radii.  The
canonical lift and affine energy remain radius-independent, while only the
physical low-frequency carrier receives the inverse-gap price.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section



theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_physicalCarrier
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ag : ℝ} {g : Vec d → Vec d}
        (u h v ell : H1Function (openCubeSet Q)) (center : Vec d),
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g →
        IsDivFormWeakSolutionOn
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) v
            (fun _ ↦ 0) →
        MemVectorL2 (openCubeSet Q) g →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun x ↦ u.toFun x - h.toFun x) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (Set.univ : Set (Vec d)) (fun x ↦ v.toFun x - ell.toFun x) →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K → 0 ≤ BE → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g x) →
        MemLp (u - h).toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad);
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) h ≤ BE →
        (∀ j : ℕ,
          let rhoI := coarseCaccioppoliRadiusSequence j
          let rhoO := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoI
                  (coarseCaccioppoliBufferedCutoffRadius rhoI rhoO)) g) ≤ Ag) →
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ) (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
          ((79 / 8 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) v +
            (57 / 8 : ℝ) * BE +
            4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
            13 * localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) ell +
            3 * Ag +
            4 * boundaryCommonGapPowerBudget Q s sigma K C 0
              (u - h).toFun (fun x ↦ -g x)) *
            boundaryThreeQuarterRadiusIterationConst := by
  obtain ⟨C, hC, hlocal⟩ := exists_boundaryCrossScale_physicalCarrierLocalizedStep d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE Ag g u h v ell center hweakU hweakV hg
    hphysical haffine hs hs4 hsigma hK hBE hAg hupper hlower hreg
    hphysicalL2 hgL2 hEh hBEfull hforce
  let energy : Vec d → ℝ := fun x ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  let Ev := localizedCoeffEnergyValue (openCubeSet Q)
    ((aCutoffFamily M L omega).coeffOn Q) v
  let Eell := localizedCoeffEnergyValue (openCubeSet Q)
    ((aCutoffFamily M L omega).coeffOn Q) ell
  let common := boundaryCommonGapPowerBudget Q s sigma K C 0
    (u - h).toFun (fun x ↦ -g x)
  let A := (79 / 8 : ℝ) * Ev + (57 / 8 : ℝ) * BE +
    4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE + 13 * Eell +
      3 * Ag + 4 * common
  have hEv : 0 ≤ Ev := by
    dsimp only [Ev]
    exact localizedCoeffEnergyValue_openCubeSet_nonneg Q
      (aCutoffFamily M L omega) v
  have hEell : 0 ≤ Eell := by
    dsimp only [Eell]
    exact localizedCoeffEnergyValue_openCubeSet_nonneg Q
      (aCutoffFamily M L omega) ell
  have hcommon : 0 ≤ common := by
    dsimp only [common]
    exact boundaryCommonGapPowerBudget_nonneg Q (u - h).toFun
      (fun x ↦ -g x) hs hsigma hK hC (by norm_num) hreg
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
    have hj := hlocal M L omega u h v ell center hweakU hweakV hg hphysical
      haffine (coarseCaccioppoliRadiusSequence_mem_Icc j).1
      (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j))
      (coarseCaccioppoliRadiusSequence_lt_one (j + 1))
      hs hs4 hsigma hK hBE hAg hupper hlower hreg hphysicalL2 hgL2 hEh
      hBEfull (hforce j)
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
    have hbase0 : 0 ≤ (79 / 8 : ℝ) * Ev + (57 / 8 : ℝ) * BE +
        4 * (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
          13 * Eell + 3 * Ag := by positivity
    have hbaseWeight := le_mul_of_one_le_right hbase0 hweight
    dsimp only [energy, Ev, Eell, common, A, gap] at hj hbaseWeight ⊢
    nlinarith only [hj, hbaseWeight]
  simpa only [energy, Ev, Eell, common, A] using
    boundary_threeQuarter_radius_iteration hA hbounded hrec

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
