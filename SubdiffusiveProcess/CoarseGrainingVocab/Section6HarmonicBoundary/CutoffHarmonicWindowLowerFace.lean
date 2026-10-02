/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowSummationLowerFace
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicPhysicalFaceTile
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicLeaves




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicRadius
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The boundary-tile estimate with the vanishing half oriented below the
tile centre.  This is the sign-reversed companion of
`exists_boundaryTileResidualMeanCap_half`. -/
theorem exists_windowSummation_boundaryTileResidualMeanCap_lower
    (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        let T := originCube d k
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        ∀ (w : H1Function (openCubeSet T)) (j0 : Fin d),
          (∀ x ∈ windowSummationCubeLowerHalf T j0,
            w.toFun x = 0) →
          IntegrableOn w.toFun (openCubeSet T) →
          IntegrableOn (fun x ↦ w.toFun x ^ 2) (openCubeSet T) →
          MemLp (fun x ↦ w.toFun x - cubeAverage T w.toFun) 2
            (volume.restrict (openCubeSet T)) →
          cubeAverage T w.toFun ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * cubeScaleFactor T ^ 2 *
              cubeAverage T
                (coefficientEnergyDensity (publicCoeffField T A) w.grad) := by
  obtain ⟨Ctile, hC, hcap⟩ := exists_boundaryTileResidualMeanCap d
  refine ⟨2 * Ctile, by positivity, ?_⟩
  intro M s hs L n k omega y z hcontain hgood
  dsimp only
  intro w j0 hwzero hwint hwint2 hwmem
  have hraw := hcap M s hs L n k omega y z hcontain hgood w
    (windowSummationCubeLowerHalf (originCube d k) j0)
    (1 / 2 : ℝ)
    (measurableSet_windowSummationCubeLowerHalf _ _)
    (windowSummationCubeLowerHalf_subset_openCubeSet _ _)
    (by norm_num)
    (half_mul_volume_openCubeSet_le_volume_windowSummationCubeLowerHalf _ _)
    hwzero hwint hwint2 hwmem
  convert hraw using 1
  all_goals ring

/-- The physical boundary-tile estimate when the domain lies above the met
face. -/
theorem exists_windowSummation_physicalBoundaryTileResidualMeanCap_lower
    (d : ℕ) [NeZero d] :
    ∃ Ctile : ℝ, 0 < Ctile ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (k : ℤ) omega y z,
        translateSet (y - z) (cubeSet (originCube d k)) ⊆
          cubeSet (originCube d ((n : ℤ) + 2)) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
        ∀ (V : Set (Vec d)), MeasurableSet V → ∀ (rho : H10Function V) (j0 : Fin d),
          (∀ x : Vec d, x j0 < 0 → x + y ∉ V) →
          let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
          volumeAverage (translateSet y (openCubeSet (originCube d k)))
              (zeroExtend V rho.toH1Function.toFun) ^ 2 ≤
            Ctile *
                (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - k).toNat : ℕ) : ℝ)) *
                sigma⁻¹ * ((3 : ℝ) ^ k) ^ 2 *
              volumeAverage (translateSet y (openCubeSet (originCube d k)))
                (fun p => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
                  vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)) := by
  obtain ⟨Ctile, hC, hcap⟩ :=
    exists_windowSummation_boundaryTileResidualMeanCap_lower d
  refine ⟨Ctile, hC, ?_⟩
  intro M s hs L n k omega y z hcontain hgood V hV rho j0 houtside
  dsimp only
  set T : TriadicCube d := originCube d k with hT
  set A := aCutoffFamily M L (translatePotentialSample y omega) with hA
  obtain ⟨w, hwfun, hwgrad, hwzero, hwint, hwint2, hwmem⟩ :=
    exists_windowSummation_metFaceTile_zeroExtendedH1_lower
      hV rho y k j0 houtside
  have hraw := hcap M s hs L n k omega y z hcontain hgood w j0
    hwzero hwint hwint2 hwmem
  have hmean : cubeAverage T w.toFun =
      volumeAverage (translateSet y (openCubeSet T))
        (zeroExtend V rho.toH1Function.toFun) := by
    rw [← cubeAverage_comp_addRight_eq_volumeAverage_translateSet T y
      (zeroExtend V rho.toH1Function.toFun)]
    exact congrArg (cubeAverage T) (funext hwfun)
  have hden : cubeAverage T
      (coefficientEnergyDensity (publicCoeffField T A) w.grad) =
      volumeAverage (translateSet y (openCubeSet T))
        (fun p => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)) := by
    rw [← cubeAverage_comp_addRight_eq_volumeAverage_translateSet T y,
      ← volumeAverage_openCubeSet_eq_cubeAverage,
      ← volumeAverage_openCubeSet_eq_cubeAverage]
    refine volumeAverage_eq_of_ae_eq ?_
    filter_upwards [publicCoeffField_ae_eq_openCubeSet T A] with x hx
    simp only [coefficientEnergyDensity, hwgrad x, hx]
    simp [hA, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_right, vecNormSq,
      Section6Covariance.aCutoff_translatePotentialSample]
  rw [hmean, hden] at hraw
  simpa only [hT, cubeScaleFactor_originCube] using hraw

omit [NeZero d] in

/-- The physical tile-family estimate at a lower face of the ambient domain. -/
theorem windowSummation_sq_averageOn_le_lowerFaceTileFamily_of_boundaryTileResidualMeanCap
    (d : ℕ) [NeZero d] :
    ∃ Cface : ℝ, 0 < Cface ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L n : ℕ, ∀ (kappa : ℤ) omega z,
      ∀ (j0 : Fin d) (aface : ℝ) (bcorner : Vec d) (Mt : ℕ),
        0 < Fintype.card (FaceIndex d j0 Mt) →
        (∀ k : FaceIndex d j0 Mt,
          translateSet
              (axisCubeCenter
                (faceTileCorner j0 aface bcorner ((3 : ℝ) ^ kappa) k)
                ((3 : ℝ) ^ kappa) - z)
              (cubeSet (originCube d kappa)) ⊆
            cubeSet (originCube d ((n : ℤ) + 2))) →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (s / 8) →
      ∀ (V : Set (Vec d)), MeasurableSet V → ∀ rho : H10Function V,
        (∀ p : Vec d, p j0 < aface → p ∉ V) →
      ∀ P : Set (Vec d),
        faceInnerSlab j0 aface bcorner ((3 : ℝ) ^ kappa) Mt ⊆ P →
        volume P ≠ ⊤ → 0 < (volume P).toReal →
        let f := zeroExtend V rho.toH1Function.toFun
        let W := faceDoubledSlab j0 aface bcorner ((3 : ℝ) ^ kappa) Mt
        let energy := fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (zeroExtendGrad V rho.toH1Function.grad p)
        IntegrableOn f P → IntegrableOn (fun x ↦ f x ^ 2) P →
        IntegrableOn f W → IntegrableOn energy W →
        let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
        averageOn P f ^ 2 ≤
          Cface * (3 : ℝ) ^
              (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
              sigma⁻¹ * ((3 : ℝ) ^ kappa) ^ 2 * averageOn W energy +
            2 * ((volume P).toReal /
                (volume (faceInnerSlab j0 aface bcorner
                  ((3 : ℝ) ^ kappa) Mt)).toReal) *
              normalizedL2On P (fun x ↦ f x - averageOn P f) ^ 2 := by
  obtain ⟨Ctile, hC, hcap⟩ :=
    exists_windowSummation_physicalBoundaryTileResidualMeanCap_lower d
  refine ⟨2 * (4 : ℝ) ^ d * Ctile, by positivity, ?_⟩
  intro M s hs L n kappa omega z j0 aface bcorner Mt hcard hanchor hgood
    V hV rho hVbelow P hsubP hPtop hPpos
  dsimp only
  intro hfP hf2P hfW heW
  set Lside : ℝ := (3 : ℝ) ^ kappa with hLside
  have hL : 0 < Lside := by
    rw [hLside]
    exact zpow_pos (by norm_num) _
  set f : Vec d → ℝ := zeroExtend V rho.toH1Function.toFun with hf
  set energy : Vec d → ℝ := fun p ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
      vecNormSq (zeroExtendGrad V rho.toH1Function.grad p) with henergy
  set sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
    with hsig
  have hsigma : 0 < sigma := by
    rw [hsig]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    convert h using 1
  set Kt : ℝ := Ctile *
      (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
      sigma⁻¹ * Lside ^ 2 with hKt
  have hKtnonneg : 0 ≤ Kt := by
    rw [hKt]
    have h3 : (0 : ℝ) < (3 : ℝ) ^
      (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hinv : (0 : ℝ) < sigma⁻¹ := inv_pos.mpr hsigma
    positivity
  have hfzero : ∀ x : Vec d, x j0 < aface → f x = 0 := by
    intro x hx
    exact zeroExtend_of_notMem _ (hVbelow x hx)
  have henonneg : ∀ x, 0 ≤ energy x := fun x ↦
    mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have htilecap : ∀ k : FaceIndex d j0 Mt,
      averageOn (axisCube (faceTileCorner j0 aface bcorner Lside k) Lside) f ^ 2 ≤
        Kt * averageOn
          (axisCube (faceTileCorner j0 aface bcorner Lside k) Lside) energy := by
    intro k
    set y : Vec d :=
      axisCubeCenter (faceTileCorner j0 aface bcorner Lside k) Lside with hy
    have hynormal : y j0 = aface := by
      rw [hy, axisCubeCenter_apply, faceTileCorner_normal]
      ring
    have houtside : ∀ x : Vec d, x j0 < 0 → x + y ∉ V := by
      intro x hx
      refine hVbelow (x + y) ?_
      have : (x + y) j0 = x j0 + aface := by
        simp only [Pi.add_apply, hynormal]
      rw [this]
      linarith
    have hraw := hcap M s hs L n kappa omega y z (hanchor k) hgood V hV rho
      j0 houtside
    dsimp only at hraw
    have hset : axisCube (faceTileCorner j0 aface bcorner Lside k) Lside =
        translateSet y (openCubeSet (originCube d kappa)) := by
      rw [hy, hLside]
      exact axisCube_eq_translateSet_openCubeSet_originCube _ kappa
    rw [averageOn, averageOn, hset, hf, henergy, hKt, hLside]
    exact hraw
  have hmain := windowSummation_sq_averageOn_le_lowerFaceTileFamily_of_tileMeanCap
    j0 aface bcorner hL hcard (P := P) (f := f) (e := energy) (Kt := Kt)
    hKtnonneg hsubP hPtop hPpos hfzero hfW hfP hf2P heW henonneg htilecap
  refine hmain.trans ?_
  have hEnonneg :
      0 ≤ averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy := by
    rw [averageOn, volumeAverage]
    refine mul_nonneg (by positivity) (setIntegral_nonneg ?_ fun x _ ↦ henonneg x)
    exact MeasurableSet.iUnion fun k ↦ measurableSet_axisCube _ _
  have hrewrite :
      2 * (4 : ℝ) ^ d *
        (Kt * averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy) =
      (2 * (4 : ℝ) ^ d * Ctile) *
        (3 : ℝ) ^ (s / 4 * ((((n : ℤ) + 2 - kappa).toNat : ℕ) : ℝ)) *
        sigma⁻¹ * Lside ^ 2 *
        averageOn (faceDoubledSlab j0 aface bcorner Lside Mt) energy := by
    rw [hKt]
    ring
  rw [hrewrite]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
