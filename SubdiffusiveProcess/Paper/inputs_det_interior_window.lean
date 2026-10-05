module

public import SubdiffusiveProcess.Paper.inputs_det_local_ellipticity
public import SubdiffusiveProcess.Paper.inputs_det_scalar_translation
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.WindowGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow
public import SubdiffusiveProcess.Paper.inputs_det_projected_cell

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper


theorem inputs_det_interior_window (d : ℕ) [NeZero d] (_hd : 2 ≤ d) :
    (∀ Cerr : ℝ, 0 < Cerr → ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ (s : ℝ) (_hs : 0 < s) (_hsle : s ≤ (1 / 4 : ℝ))
        (m n : ℕ), n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
        (a0 : ℝ), 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal Cerr →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ y ∈ truncatedCube d m ((n : ℤ) - 1) x,
        openCubeAtScale y ((n : ℤ) - 3) ⊆ cube d m →
      let k : ℤ := (n : ℤ) - 2;
      let c := Section6ExcessDecay.wellPlacedCentre y (m : ℤ) k;
      let Q := originCube d k;
      let U := truncatedCube d m n x;
      normalizedSetAverage (truncatedCube d m (k - 2) y)
          (fun q => a q * vecNormSq (u.grad q)) ≤
        (81 : ℝ) ^ d *
          ((4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) *
            (B * a0 * Real.rpow (3 : ℝ) (-2 * (Q.scale : ℝ)) *
                ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
                normalizedL2On U (fun q => u.toFun q - averageOn U u.toFun) ^ 2 +
              Real.rpow (s / 2) (-11 : ℝ) * (B * a0⁻¹) *
                (caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s) Q *
                  (Real.rpow s (-(1 / 2 : ℝ)) *
                    (Real.sqrt ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
                      (fractionalSeminormOn U s g).toReal))) ^ 2))) := by
  intro Cerr hCerr
  obtain ⟨C, hC, hprojected⟩ := inputs_det_projected_cell d
  obtain ⟨E, B, hE, hB, hcaps⟩ :=
    inputs_det_local_ellipticity d Cerr hCerr
  refine ⟨C, B, hC, hB, ?_⟩
  intro s hs hsle m n hnm z hz x hx a data a0 ha0 herr hboundary u g hweak hreg
    y hy hpatch
  let k : ℤ := (n : ℤ) - 2
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre y (m : ℤ) k
  let Q : Homogenization.TriadicCube d := originCube d k
  let U : Set (Vec d) := truncatedCube d m n x
  have hkm : k ≤ (m : ℤ) := by
    dsimp [k]
    omega
  have hxDomain : x ∈ cube d m :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 3) z hx
  have hPsub : translatedCube d k c ⊆ U := by
    exact translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
      (by simpa [k, U] using hy) hkm
  have hcU : c ∈ U := hPsub (by
    rw [Section6ExcessDecay.mem_translatedCube_iff]
    simpa [c, k] using Section6ExcessDecay.zero_mem_cube d k)
  have hUsub : U ⊆ openCubeSet (originCube d (m : ℤ)) := by
    intro q hq
    exact hq.2
  have hUpos : 0 < (volume U).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hPpos : 0 < (volume (translatedCube d k c)).toReal := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hU0 : volume U ≠ 0 := (ENNReal.toReal_ne_zero.mp hUpos.ne').1
  have hUtop : volume U ≠ ⊤ :=
    (Section6ExcessDecay.volume_truncatedCube_lt_top d (m : ℤ) n x).ne
  have hnmInt : (n : ℤ) + 5 ≤ (m : ℤ) := by exact_mod_cast hnm
  have hPpair : volume (translateSet c (openCubeSet Q)) ≠ 0 ∧
      volume (translateSet c (openCubeSet Q)) ≠ ⊤ := by
    rw [volume_translateSet_eq]
    constructor
    · intro hzero
      have hz := congrArg ENNReal.toReal hzero
      rw [volume_openCubeSet_toReal] at hz
      exact (cubeVolume_pos Q).ne' hz
    · exact (volume_openCubeSet_lt_top Q).ne
  obtain ⟨sOrder, hsOrder, hg⟩ := hreg
  have hfrac : MemFractionalOn (cube d (m : ℤ)) sOrder.1 g := by
    change fractionalSeminormOn (openCubeSet (originCube d (m : ℤ)))
      sOrder.1 g ≠ ⊤
    rw [fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable _ _ _ hg.2.aestronglyMeasurable]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hg.2.eSeminorm_lt_top.ne
  have hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ⊤ := by
    have hfin := memFractionalOn_truncatedCube_of_domain hxDomain
      (by omega : (n : ℤ) - 1 ≤ (m : ℤ)) hfrac
    simpa [U, MemFractionalOn] using! hfin
  have hqCube : y ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ)
      ((n : ℤ) - 1) x hy
  have hpatchLocal :
      openCubeAtScale (y - c) (k - 1) ⊆ openCubeSet Q := by
    have hbase := openCubeAtScale_wellPlaced_pullback_subset_originCube
      (d := d) (m := (m : ℤ)) (k := k) (q := y) hkm
      (by simpa only [k, sub_sub, sub_self, sub_zero] using! hpatch)
    simpa only [c, Q] using hbase
  obtain ⟨dataC0⟩ := inputs_det_scalar_translation d
    (fun q => a (q + z)) data (c - z)
  have hdataCfun : (fun q => (fun p => a (p + z)) (q + (c - z))) =
      fun q => a (q + c) := by
    funext q
    exact congrArg a (by abel_nf)
  let dataC : ScalarTriadicCoeffData (fun q => a (q + c)) :=
    hdataCfun ▸ dataC0
  have hcap := hcaps s hs hsle m n z x c hx hcU a data dataC a0 ha0 herr
  rcases hcap with ⟨_herrLocal, _hLambdaSq, hlambdaSqInv, hLambdaUpper,
    _hlambdaSInvThird, _hlambdaSThird, _hThetaThird⟩
  obtain ⟨g0, u0, hg0, hgLocal, hu0, hforced, hreg0, hcell⟩ :=
    hprojected a m k y sOrder u g (averageOn U u.toFun) hweak hg
      (by rw [hsOrder]; exact hsle) hkm hqCube hpatchLocal dataC
  have hparent := normalizedL2SqOnSet_projected_le_window u u0
    (averageOn U u.toFun) hu0 hPsub hUsub hUpos hPpos
  have hsource := projectedForceSeminorm_le_window Q c U sOrder g g0
    hgLocal hg0 (by
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet] at hPsub
      exact hPsub) hPpair.1 hPpair.2 hU0 hUtop hgUfin
  have hvolP : volume (translateSet c (openCubeSet Q)) =
      volume (translatedCube d k c) := by
    congr 1
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  rw [hvolP] at hsource
  have hsOrderPos : 0 < sOrder.1 := by rw [hsOrder]; exact hs
  have hsOrderLe : sOrder.1 ≤ 1 / 4 := by rw [hsOrder]; exact hsle
  have hlambdaSqInv' : a0 *
      (Ch02.lambdaSq Q (sOrder.1 / 6) (.finite 2)
        dataC.toTriadicCoeffFamily)⁻¹ ≤ B := by
    simpa [Q, hsOrder] using hlambdaSqInv
  have hhalf' := interiorHalfEllipticityCaps_of_sixth Q
    dataC.toTriadicCoeffFamily hsOrderPos ha0 hLambdaUpper hlambdaSqInv'
  have hpref := caccioppoliWithRHSPrefactor_interiorHalf_le
    (Q := Q) (A := dataC.toTriadicCoeffFamily) hC hsOrderPos hsOrderLe hhalf'.2.2
  have hlam : Ch02.lambdaS Q (sOrder.1 / 2) dataC.toTriadicCoeffFamily ≤ B * a0 :=
    hhalf'.2.1
  have hlamInv : Real.rpow
      (Ch02.lambdaS Q (sOrder.1 / 2) dataC.toTriadicCoeffFamily) (-1 : ℝ) ≤
        B * a0⁻¹ := by
    calc
      Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2)
          dataC.toTriadicCoeffFamily) (-1 : ℝ) =
          (Ch02.lambdaS Q (sOrder.1 / 2)
            dataC.toTriadicCoeffFamily)⁻¹ := Real.rpow_neg_one _
      _ ≤ B * a0⁻¹ := hhalf'.1
  have hinner :
      Ch02.lambdaS Q (sOrder.1 / 2) dataC.toTriadicCoeffFamily *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2)
              dataC.toTriadicCoeffFamily) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 ≤
        B * a0 * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
              ((volume U).toReal / (volume (translatedCube d k c)).toReal) *
              normalizedL2On U
                (fun y => u.toFun y - averageOn U u.toFun) ^ 2 +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * a0⁻¹) *
            (caccioppoliExactDatumConstant d *
              cubeBesovScaleWeight (-sOrder.1) Q *
              (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt ((volume U).toReal /
                    (volume (translatedCube d k c)).toReal) *
                (fractionalSeminormOn U sOrder.1 g).toReal))) ^ 2 := by
    have hscale : 0 ≤ Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hparent0 : 0 ≤ normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u0.toFun y - averageOn U u.toFun) :=
      normalizedL2SqOnSet_nonneg (openCubeSet Q) _ (measurableSet_openCubeSet Q)
    have hcoef : Ch02.lambdaS Q (sOrder.1 / 2) dataC.toTriadicCoeffFamily *
        Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) ≤
        B * a0 * Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hlam hscale
    have hfirst := mul_le_mul hcoef hparent hparent0
      (mul_nonneg (mul_nonneg hB.le ha0.le) hscale)
    have hsource0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
        Q sOrder.1 (fun x => -g0 x) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        hreg0
    have hsecondSq := pow_le_pow_left₀ hsource0 hsource 2
    let Sg : ℝ := caccioppoliExactDatumConstant d *
      cubeBesovScaleWeight (-sOrder.1) Q *
        (Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translatedCube d k c)).toReal) *
            (fractionalSeminormOn U sOrder.1 g).toReal))
    have hcoefSecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2)
          dataC.toTriadicCoeffFamily) (-1 : ℝ) ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * a0⁻¹) :=
      mul_le_mul_of_nonneg_left hlamInv
        (Real.rpow_nonneg (by linarith only [hsOrderPos] : 0 ≤ sOrder.1 / 2) _)
    have hcoefSecond0 : 0 ≤ Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
        (B * a0⁻¹) :=
      mul_nonneg (Real.rpow_nonneg
        (by linarith only [hsOrderPos] : 0 ≤ sOrder.1 / 2) _)
        (mul_nonneg hB.le (inv_nonneg.mpr ha0.le))
    have hsecond : Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
          Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2)
            dataC.toTriadicCoeffFamily) (-1 : ℝ) *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
            (fun x => -g0 x) ^ 2 ≤
        Real.rpow (sOrder.1 / 2) (-11 : ℝ) * (B * a0⁻¹) * Sg ^ 2 :=
      mul_le_mul hcoefSecond (by simpa only [Sg] using hsecondSq)
        (sq_nonneg _) hcoefSecond0
    exact add_le_add (by simpa [mul_assoc] using hfirst)
      (by simpa only [Sg] using hsecond)
  have hrawInner0 : 0 ≤
      Ch02.lambdaS Q (sOrder.1 / 2) dataC.toTriadicCoeffFamily *
            Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) *
            normalizedL2SqOnSet (openCubeSet Q)
              (fun y => u0.toFun y - averageOn U u.toFun) +
          Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
            Real.rpow (Ch02.lambdaS Q (sOrder.1 / 2)
              dataC.toTriadicCoeffFamily) (-1 : ℝ) *
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sOrder.1
              (fun x => -g0 x) ^ 2 := by
    have hlam0 : 0 ≤ Ch02.lambdaS Q (sOrder.1 / 2)
        dataC.toTriadicCoeffFamily := by
      rw [Ch02.lambdaS]
      exact Ch02.lambdaSq_finite_nonneg Q dataC.toTriadicCoeffFamily
        (by linarith only [hsOrderPos] : 0 < sOrder.1 / 2) (by norm_num)
    have hparent0 := normalizedL2SqOnSet_nonneg (openCubeSet Q)
      (fun y => u0.toFun y - averageOn U u.toFun) (measurableSet_openCubeSet Q)
    exact add_nonneg
      (mul_nonneg (mul_nonneg hlam0 (Real.rpow_nonneg (by norm_num) _)) hparent0)
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by linarith only [hsOrderPos]) _)
          (Real.rpow_nonneg hlam0 _)) (sq_nonneg _))
  have hprefBound0 : 0 ≤
      (4 * max 1 C) ^ (8 : ℕ) * 8 * (B ^ 2) ^ (3 : ℕ) := by positivity
  have hmul := mul_le_mul hpref hinner hrawInner0 hprefBound0
  have hstep := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 81 ^ d)
  have hfinal := hcell.trans (by simpa only [Q] using hstep)
  simpa only [Q, U, c, hsOrder] using hfinal

end SubdiffusiveProcess.Paper

