import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorParentPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorPrefactorPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedDatumPrice




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- One non-boundary depth-two cell, with every analytic input expressed on
the manuscript window `U`. -/
theorem exists_interiorCellEnergy_le_windowPrices (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
      ∀ (z x q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
        openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
        omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        let k : ℤ := (n : ℤ) - 2
        let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
        let Q := originCube d k
        let U := truncatedCube d (m : ℤ) (n : ℤ) x
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d ((n : ℤ) + 2) z)
        normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
            (fun y => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y *
              vecNormSq (u.grad y)) ≤
          (81 : ℝ) ^ d *
            ((4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) *
              (B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
                  ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  normalizedL2On U
                    (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
                Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                  (B * sigma⁻¹) *
                  (caccioppoliExactDatumConstant d *
                    cubeBesovScaleWeight (-sOrder.1) Q *
                    (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                      (Real.sqrt ((volume U).toReal /
                          (volume (translatedCube d k c)).toReal) *
                        (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2)) := by
  obtain ⟨C, hC, hinterior⟩ := exists_projectedInteriorCellEnergy_readout d
  obtain ⟨_E, B, _hE, hB, hcaps⟩ :=
    exists_localBoundaryEllipticityCaps_nextWindow d
  refine ⟨C, B, hC, hB, ?_⟩
  intro M sOrder hs L m n hmL hnm z x q omega hz hx hq hpatchPhysical hgood u h g
    hdir hg hh
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  let U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma : ℝ := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  have hkm : k ≤ (m : ℤ) := by dsimp [k]; omega
  have hnL : n + 2 ≤ L := by omega
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hpatch : openCubeAtScale (q - c) (k - 1) ⊆ openCubeSet Q := by
    have hbase := openCubeAtScale_wellPlaced_pullback_subset_originCube
      (d := d) (m := (m : ℤ)) (k := k) (q := q) hkm
      (by simpa only [k, sub_sub, sub_self, sub_zero] using hpatchPhysical)
    simpa only [c, Q] using hbase
  have hPsub : translatedCube d k c ⊆ U := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hq) hkm
  have hcU : c ∈ U := hPsub (by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa using Section6ExcessDecay.zero_mem_cube d k)
  have hUsub : U ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro y hy
    exact hy.2
  have hUpos : 0 < (volume U).toReal := by
    exact Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hPpos : 0 < (volume (translatedCube d k c)).toReal := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ⊤ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) (n : ℤ) x).ne
  have hPpair := ENNReal.toReal_ne_zero.mp hPpos.ne'
  have hPpair' : volume (translateSet c (openCubeSet Q)) ≠ 0 ∧
      volume (translateSet c (openCubeSet Q)) ≠ ⊤ := by
    rw [volume_translateSet_eq]
    constructor
    · intro hzero
      have hz := congrArg ENNReal.toReal hzero
      rw [volume_openCubeSet_toReal] at hz
      exact (cubeVolume_pos Q).ne' hz
    · exact (volume_openCubeSet_lt_top Q).ne
  have hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ⊤ := by
    have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
      change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ)))
        sOrder.1 g ≠ ⊤
      rw [fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm]
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hg.2.eSeminorm_lt_top.ne
    exact memFractionalOn_truncatedCube_of_domain hxDomain (by omega) hfrac
  obtain ⟨g0, u0, hg0, hgLocal, hu0, _heq, _hgReg, hcell⟩ :=
    hinterior M L omega m k q sOrder u h g (averageOn U u.toFun)
      hdir hg hh hs.2 hkm (by exact hq.2) hpatch
  have hparent := normalizedL2SqOnSet_projected_le_window u u0
    (averageOn U u.toFun) hu0 hPsub hUsub hUpos hPpos
  have hsource := projectedForceSeminorm_le_window Q c U sOrder g g0
    (by simpa [Q, c] using hgLocal)
    hg0 (by
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet] at hPsub
      exact hPsub)
    hPpair'.1 hPpair'.2 hU0 hUtop hgUfin
  have hvolP : volume (translateSet c (openCubeSet Q)) =
      volume (translatedCube d k c) := by
    congr 1
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hvolP] at hsource
  have hcap := hcaps M sOrder.1 hs L m n hnL z x c omega hx hcU hgood
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hhalf := interiorHalfEllipticityCaps_of_sixth Q A hs0 hsigma
    hcap.2.2.2.1 hcap.2.2.1
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := A) hC hs0 hs.2 hhalf.2.2
  have hlam : Ch02.lambdaS Q (sOrder.1 / 2) A ≤ B * sigma := hhalf.2.1
  have hlamInv : Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
      B * sigma⁻¹ := by
    calc
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) =
          (Ch02.lambdaS Q (sOrder.1 / 2) A)⁻¹ :=
        Real.rpow_neg_one _
      _ ≤ B * sigma⁻¹ := hhalf.1
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
              ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) *
            (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-sOrder.1) Q *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                  (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 := by
    have hscale : 0 ≤ Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hparent0 : 0 ≤ normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u0.toFun y - averageOn U u.toFun) :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) _ (measurableSet_openCubeSet Q)
    have hcoef : Ch02.lambdaS Q (sOrder.1 / 2) A *
        Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) ≤
        B * sigma * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam hscale
    have hfirst := mul_le_mul hcoef hparent hparent0
      (mul_nonneg (mul_nonneg hB.le hsigma.le) hscale)
    have hsource0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
        (fun x => -g0 x) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (by simpa using _hgReg)
    have hsecondSq := pow_le_pow_left₀ hsource0 hsource 2
    let Sg : ℝ := caccioppoliExactDatumConstant d *
      cubeBesovScaleWeight (-sOrder.1) Q *
        (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translatedCube d k c)).toReal) *
            (fractionalSeminormOn U sOrder.1 g).toReal))
    have hcoefSecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) :=
      mul_le_mul_of_nonneg_left hlamInv
        (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
    have hcoefSecond0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        (B * sigma⁻¹) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hs0] : 0 ≤ sOrder.1 / 2) _)
        (mul_nonneg hB.le (inv_nonneg.mpr hsigma.le))
    have hsecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
            (fun x => -g0 x) ^ 2 ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * sigma⁻¹) * Sg ^ 2 := by
      exact mul_le_mul hcoefSecond (by simpa only [Sg] using hsecondSq)
        (sq_nonneg _) hcoefSecond0
    exact add_le_add (by simpa [mul_assoc] using hfirst)
      (by simpa only [Sg] using hsecond)
  have hrawInner0 : 0 ≤
      Ch02.lambdaS Q (sOrder.1 / 2) A *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2) A) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2) A := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs0]) (by norm_num)
    have hparent0 := normalizedL2SqOnSet_nonneg (openCubeSet Q)
      (fun y => u0.toFun y - averageOn U u.toFun) (measurableSet_openCubeSet Q)
    exact add_nonneg
      (mul_nonneg (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _)) hparent0)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith only [hs0]) _)
          (Real.rpow_nonneg hlam0 _)) (sq_nonneg _))
  have hprefBound0 : 0 ≤
      (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) := by positivity
  have hmul := mul_le_mul hpref hinner hrawInner0 hprefBound0
  have hstep := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  have hfinal := hcell.trans (by
    simpa only [Q, A, c] using hstep)
  simpa only [Q, A, c, U, sigma] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
