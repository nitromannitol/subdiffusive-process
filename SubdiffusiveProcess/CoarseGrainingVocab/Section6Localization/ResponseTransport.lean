module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.NormalizerSwap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularResummation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity

@[expose] public section

/-!
# Section 6 localization: cutoff-change response transport

This module is the first bounded layer of Step 2 in
`p.good.scale.mathcal.E` (paper label `l.J.sensitivity`).  It changes a local
response probe from a global cutoff `L` and arbitrary positive normalizer `b`
to cutoff `n` and normalizer `ahom_n`.  The constants are the printed constants
obtained from `l.J.sensitivity` at `delta = 1`.

The proof-role split is as in the manuscript: carrier transport is kept
apart from the later shell-ratio and annular-supremum estimates.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The two squared coefficient-ratio errors produced by `l.J.sensitivity`
when cutoff `L` with normalizer `b` is compared to cutoff `n` with normalizer
`ahom_n`. -/
def cutoffRatioError (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (U : Ch02.Domain d) (b : ℝ) : ℝ :=
  scalarRatioLInf U
      (fun x => (b / ahom M n) * _root_.SubdiffusiveProcess.Model.aCutoff M n omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) ^ 2 +
    scalarRatioLInf U
      (fun x => (ahom M n / b) * _root_.SubdiffusiveProcess.Model.aCutoff M L omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) ^ 2

/-- The cutoff-change transport at the manuscript constants `2` and `3`.

This is the direct specialization of `responseJ_sensitivity` with
`lambda = b / ahom_n`, `delta = 1`, and the unit scalar probe. -/
theorem paperScalarProbe_cutoff_le_local_add_ratioError
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) {b : ℝ} (hb : 0 < b)
    (e : Vec d) (he : vecNormSq e = 1) :
    paperScalarProbe Q (aCutoffFamily M L omega) b e ≤
      2 * paperScalarProbe Q (aCutoffFamily M n omega) (ahom M n) e +
        3 * cutoffRatioError M n L omega (Ch02.cubeDomain Q) b *
          (paperScalarProbe Q (aCutoffFamily M n omega) (ahom M n) e + 1) := by
  let U := Ch02.cubeDomain Q
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M n omega
  let c := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let ha : ScalarCoeffOnData U a := aCutoffCoeffOnData M n omega U
  let hc : ScalarCoeffOnData U c := aCutoffCoeffOnData M L omega U
  have han : 0 < ahom M n := ahom_pos M n
  let lambda : ℝ := b / ahom M n
  have hlambda : 0 < lambda := div_pos hb han
  let p : Vec d := (Real.sqrt (ahom M n))⁻¹ • e
  let q : Vec d := Real.sqrt (ahom M n) • e
  have hmain := responseJ_sensitivity ha hc hlambda (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 1) p q
  dsimp [lambda, p, q, a, c, U, ha, hc] at hmain
  have hsqrta : 0 < Real.sqrt (ahom M n) := Real.sqrt_pos.2 han
  have hsqrtmul : Real.sqrt (b / ahom M n) * Real.sqrt (ahom M n) =
      Real.sqrt b := by
    rw [Real.sqrt_div hb.le]
    field_simp
  have hp : (Real.sqrt (b / ahom M n))⁻¹ •
        (Real.sqrt (ahom M n))⁻¹ • e = (Real.sqrt b)⁻¹ • e := by
    rw [smul_smul]
    congr 1
    calc
      (Real.sqrt (b / ahom M n))⁻¹ * (Real.sqrt (ahom M n))⁻¹ =
          (Real.sqrt (b / ahom M n) * Real.sqrt (ahom M n))⁻¹ := by
            rw [mul_inv_rev]
            ring
      _ = (Real.sqrt b)⁻¹ := by rw [hsqrtmul]
  have hq : Real.sqrt (b / ahom M n) • Real.sqrt (ahom M n) • e =
      Real.sqrt b • e := by
    rw [smul_smul, hsqrtmul]
  have hdot : vecDot ((Real.sqrt (ahom M n))⁻¹ • e)
      (Real.sqrt (ahom M n) • e) = 1 := by
    rw [vecDot_smul_left, vecDot_smul_right]
    change (Real.sqrt (ahom M n))⁻¹ *
      (Real.sqrt (ahom M n) * vecNormSq e) = 1
    rw [he]
    field_simp
  have hinv : (b / ahom M n)⁻¹ = ahom M n / b := by
    field_simp
  rw [hp, hq, hdot, hinv] at hmain
  norm_num at hmain
  simpa [paperScalarProbe, cutoffRatioError, aCutoffFamily, aCutoffTriadicData,
    aCutoffCoeffOnData, ScalarCoeffOnData.toCoeffOn, Ch02.cubeDomain_coe] using! hmain

/-- The same transport written on the frozen translated-cube response carrier. -/
theorem paperScalarProbe_translatedCutoff_le_section6Response_add_ratioError
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    {b : ℝ} (hb : 0 < b) (e : Vec d) (he : vecNormSq e = 1) :
    paperScalarProbe (originCube d (n : ℤ))
        (aCutoffFamily M L (translatePotentialSample z omega)) b e ≤
      2 * section6Response M n n omega z e +
        3 * cutoffRatioError M n L (translatePotentialSample z omega)
            (Ch02.cubeDomain (originCube d (n : ℤ))) b *
          (section6Response M n n omega z e + 1) := by
  simpa only [section6Response] using
    paperScalarProbe_cutoff_le_local_add_ratioError M n L
      (translatePotentialSample z omega) (originCube d (n : ℤ)) hb e he

/-- The transport with the literal global tail-average normalizer carried by
the annular probes in `p.good.scale.mathcal.E`. -/
theorem paperScalarProbe_translatedCutoff_tailAverage_le_section6Response
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (e : Vec d) (he : vecNormSq e = 1) :
    paperScalarProbe (originCube d (n : ℤ))
        (aCutoffFamily M L (translatePotentialSample z omega))
        (tailCoefficientCubeAverage M L m omega) e ≤
      2 * section6Response M n n omega z e +
        3 * cutoffRatioError M n L (translatePotentialSample z omega)
            (Ch02.cubeDomain (originCube d (n : ℤ)))
            (tailCoefficientCubeAverage M L m omega) *
          (section6Response M n n omega z e + 1) := by
  exact paperScalarProbe_translatedCutoff_le_section6Response_add_ratioError
    M n L omega z (tailCoefficientCubeAverage_pos M L m omega) e he

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
