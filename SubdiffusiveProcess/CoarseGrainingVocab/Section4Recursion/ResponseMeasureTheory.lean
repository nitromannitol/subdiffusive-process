import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ExpectedJ
import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionLaw
import Homogenization.Book.Ch04.Theorems.WidetildeTheta

/-!
# Measure-theoretic response interfaces for the Section 4 recursion

This module supplies the measurable coarse-ellipticity event, restricted and
unrestricted response integrability, translation stationarity, and entrywise
second moments needed by the combine and homogenization steps.

PROVENANCE: the measurable-event organization follows
`Algsuperdiff/Section3/Provider/Homogenization/CombineBadEvent.lean`, while the
response and stationarity seams follow `CombineExpectation.lean` and
`InitialJLBoundIntegrability.lean`.  The GMC carrier uses measurable versions
under the actual cutoff pushforward law because Chapter 4 intentionally only
exports law-relative a.e.-measurability of its totalized ellipticity
observables.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem neZero_of_gmcModel {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩

private theorem aemeasurable_cutoffUpperEllipticityLiteral {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    AEMeasurable (fun omega : Sample d =>
      Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega)) M.P.toMeasure := by
  have h := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.aemeasurable_LambdaSqCoeffField_finite_one
      (originCube d (m : ℤ)) (by norm_num : (0 : ℝ) < 1 / 4)
  simpa [aCutoffRestrictionLaw_eq_map, Function.comp_def] using
    h.comp_aemeasurable (measurable_aCutoffRegCoeffField M L).aemeasurable

private theorem aemeasurable_cutoffLowerEllipticityLiteral {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    AEMeasurable (fun omega : Sample d =>
      Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
        (aCutoffRegCoeffField M L omega)) M.P.toMeasure := by
  have h := (aCutoffRestrictionLaw_lawCarrier M L)
    |>.aemeasurable_lambdaSqCoeffField_finite_one
      (originCube d (m : ℤ)) (by norm_num : (0 : ℝ) < 1 / 4)
  simpa [aCutoffRestrictionLaw_eq_map, Function.comp_def] using
    h.comp_aemeasurable (measurable_aCutoffRegCoeffField M L).aemeasurable

/-- A measurable version of the upper `s = 1/4`, `q = 1` coarse-ellipticity
observable for the finite GMC cutoff. -/
noncomputable def cutoffUpperEllipticityMeasurable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) : Sample d → ℝ := by
  letI : NeZero d := neZero_of_gmcModel M
  let X : Sample d → ℝ := fun omega =>
    Ch04.LambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
      (aCutoffRegCoeffField M L omega)
  exact AEMeasurable.mk X (aemeasurable_cutoffUpperEllipticityLiteral M L m)

/-- A measurable version of the lower `s = 1/4`, `q = 1` coarse-ellipticity
observable for the finite GMC cutoff. -/
noncomputable def cutoffLowerEllipticityMeasurable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) : Sample d → ℝ := by
  letI : NeZero d := neZero_of_gmcModel M
  let X : Sample d → ℝ := fun omega =>
    Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 4) (.finite 1)
      (aCutoffRegCoeffField M L omega)
  exact AEMeasurable.mk X (aemeasurable_cutoffLowerEllipticityLiteral M L m)

theorem measurable_cutoffUpperEllipticityMeasurable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    Measurable (cutoffUpperEllipticityMeasurable M L m) := by
  letI : NeZero d := neZero_of_gmcModel M
  exact (aemeasurable_cutoffUpperEllipticityLiteral M L m).measurable_mk

theorem measurable_cutoffLowerEllipticityMeasurable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    Measurable (cutoffLowerEllipticityMeasurable M L m) := by
  letI : NeZero d := neZero_of_gmcModel M
  exact (aemeasurable_cutoffLowerEllipticityLiteral M L m).measurable_mk

theorem cutoffUpperEllipticityMeasurable_ae_eq {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    cutoffUpperEllipticityMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega => Ch04.LambdaSqCoeffField
        (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) := by
  letI : NeZero d := neZero_of_gmcModel M
  exact (aemeasurable_cutoffUpperEllipticityLiteral M L m).ae_eq_mk.symm

theorem cutoffLowerEllipticityMeasurable_ae_eq {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    cutoffLowerEllipticityMeasurable M L m =ᵐ[M.P.toMeasure]
      fun omega => Ch04.lambdaSqCoeffField
        (originCube d (m : ℤ)) (1 / 4) (.finite 1)
          (aCutoffRegCoeffField M L omega) := by
  letI : NeZero d := neZero_of_gmcModel M
  exact (aemeasurable_cutoffLowerEllipticityLiteral M L m).ae_eq_mk.symm

/-- The measurable representative of the printed coarse-ellipticity good
event `e.goodevent.combine`. -/
def coarseEllipticityGoodEvent {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) : Set (Sample d) :=
  {omega |
    ahom M L / 2 ≤ cutoffLowerEllipticityMeasurable M L m omega ∧
      cutoffLowerEllipticityMeasurable M L m omega ≤
        cutoffUpperEllipticityMeasurable M L m omega ∧
      cutoffUpperEllipticityMeasurable M L m omega ≤ 2 * ahom M L}

theorem measurableSet_coarseEllipticityGoodEvent {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) :
    MeasurableSet (coarseEllipticityGoodEvent M L m) := by
  exact (measurableSet_le measurable_const
      (measurable_cutoffLowerEllipticityMeasurable M L m)).inter
    ((measurableSet_le (measurable_cutoffLowerEllipticityMeasurable M L m)
      (measurable_cutoffUpperEllipticityMeasurable M L m)).inter
    (measurableSet_le (measurable_cutoffUpperEllipticityMeasurable M L m)
      measurable_const))

theorem measurable_restricted_coarseEllipticityGoodEvent_responseJ {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (p q : Vec d) :
    Measurable ((coarseEllipticityGoodEvent M L m).indicator fun omega =>
      J (Ch02.cubeDomain (originCube d (m : ℤ)))
        (aCutoffCoeffOnData M L omega
          (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn p q) := by
  letI : NeZero d := neZero_of_gmcModel M
  exact (measurable_cutoff_responseJ M L
      (Ch02.cubeDomain (originCube d (m : ℤ))) p q).indicator
        (measurableSet_coarseEllipticityGoodEvent M L m)

private theorem integrable_matrix_quadratic {d : ℕ} {mu : Measure (Sample d)}
    {A : Sample d → Mat d} (hA : Integrable A mu) (p : Vec d) :
    Integrable (fun omega => vecDot p (matVecMul (A omega) p)) mu := by
  simp only [vecDot, matVecMul]
  apply integrable_finset_sum Finset.univ
  intro i hi
  apply Integrable.const_mul
  apply integrable_finset_sum Finset.univ
  intro j hj
  exact (((hA.eval i).eval j).mul_const (p j))

private theorem integrable_aCutoff_apply_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (x : Vec d) :
    Integrable (fun omega : Sample d =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2) M.P.toMeasure := by
  have hratio := (integral_abs_cutoffRatioMinusOne_rpow_root_le_raw
    M L (-1) x 2 (by norm_num) (by omega) (by omega)).1
  have hmajorant := hratio.const_mul 2 |>.add (integrable_const 2)
  have hmeas : Measurable (fun omega : Sample d =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2) :=
    ((measurable_cutoff_uncurry M L).comp
      (measurable_id.prodMk measurable_const)).pow_const 2
  apply hmajorant.mono' hmeas.aestronglyMeasurable
  filter_upwards with omega
  have heq : cutoffRatioMinusOne M L (-1) omega x =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1 := by
    simp [cutoffRatioMinusOne, aCutoffAtInt]
  simp only [Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x))]
  change SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2 ≤
    2 * |cutoffRatioMinusOne M L (-1) omega x| ^ 2 + 2
  rw [heq]
  have hs := sq_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 2)
  rw [Real.rpow_two, sq_abs]
  nlinarith

private theorem integral_aCutoff_apply_sq_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (x : Vec d) :
    ∫ omega : Sample d, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2
        ∂M.P.toMeasure =
      ∫ omega : Sample d, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 ^ 2
        ∂M.P.toMeasure := by
  calc
    _ = ∫ omega : Sample d,
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
          (translatePotentialSequence x omega) 0 ^ 2 ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [aCutoff_translatePotentialSequence M L x omega 0, zero_add]
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence x)
        (potentialSequenceLaw_stationary M x)
        (fun omega : Sample d =>
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 ^ 2)
        (integrable_aCutoff_apply_sq M L 0).1

private theorem integrable_aCutoff_sq_prod_volumeMeasureOn {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable
      (fun z : Sample d × Vec d =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2 ^ 2)
      (M.P.toMeasure.prod (volumeMeasureOn (U : Set (Vec d)))) := by
  have hJoint : AEStronglyMeasurable
      (fun z : Sample d × Vec d =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2 ^ 2)
      (M.P.toMeasure.prod (volumeMeasureOn (U : Set (Vec d)))) :=
    (measurable_cutoff_uncurry M L).pow_const 2 |>.aestronglyMeasurable
  apply (integrable_prod_iff' hJoint).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x => integrable_aCutoff_apply_sq M L x
  · have hEq :
        (fun x : Vec d => ∫ omega : Sample d,
          ‖SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2‖ ∂M.P.toMeasure) =
          fun _ => ∫ omega : Sample d,
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0 ^ 2 ∂M.P.toMeasure := by
      funext x
      rw [show (fun omega : Sample d =>
          ‖SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2‖) =
          fun omega => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2 by
        funext omega
        exact Real.norm_of_nonneg (sq_nonneg _)]
      exact integral_aCutoff_apply_sq_eq_zero M L x
    rw [hEq]
    exact integrable_const _

private theorem square_average_le_average_square {d : ℕ}
    (U : Ch02.Domain d) {f : Vec d → ℝ} (hf : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_sq : Integrable (fun x => f x ^ 2)
      (volumeMeasureOn (U : Set (Vec d)))) :
    Ch02.average U f ^ 2 ≤ Ch02.average U (fun x => f x ^ 2) := by
  let nu := volumeMeasureOn (U : Set (Vec d))
  let v := (volume (U : Set (Vec d))).toReal
  have hv : 0 < v := Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hf_mem : MemLp f (ENNReal.ofReal 2) nu := by
    simpa using (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf_sq
  have hone_mem : MemLp (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal 2) nu :=
    memLp_const _
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := nu) hholder
    (f := f) (g := fun _ : Vec d => (1 : ℝ))
    (Filter.Eventually.of_forall hf_nonneg)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hf_mem hone_mem
  have hI_nonneg : 0 ≤ ∫ x, f x ∂nu := integral_nonneg hf_nonneg
  have hI2_nonneg : 0 ≤ ∫ x, f x ^ 2 ∂nu := integral_nonneg fun _ => sq_nonneg _
  have hbound : ∫ x, f x ∂nu ≤
      Real.sqrt (∫ x, f x ^ 2 ∂nu) * Real.sqrt v := by
    simpa [one_mul, Real.sqrt_eq_rpow, nu, v, volumeMeasureOn,
      Measure.restrict_apply_univ, measureReal_def] using hH
  have hsq : (∫ x, f x ∂nu) ^ 2 ≤
      (∫ x, f x ^ 2 ∂nu) * v := by
    have := (sq_le_sq₀ hI_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))).2 hbound
    simpa [mul_pow, Real.sq_sqrt hI2_nonneg, Real.sq_sqrt hv.le] using this
  unfold Ch02.average
  change (v⁻¹ * ∫ x, f x ∂nu) ^ 2 ≤
    v⁻¹ * ∫ x, f x ^ 2 ∂nu
  rw [mul_pow]
  calc
    v⁻¹ ^ 2 * (∫ x, f x ∂nu) ^ 2 =
        v⁻¹ * (∫ x, f x ∂nu) ^ 2 * v⁻¹ := by ring
    _ ≤
        v⁻¹ * ((∫ x, f x ^ 2 ∂nu) * v) * v⁻¹ := by
      gcongr
    _ = v⁻¹ * ∫ x, f x ^ 2 ∂nu := by field_simp

private theorem integrable_aCutoff_square_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun omega : Sample d =>
      Ch02.average U (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ^ 2))
      M.P.toMeasure := by
  have hIntegral := (integrable_aCutoff_sq_prod_volumeMeasureOn M L U).integral_prod_left
  have hScaled := hIntegral.const_mul
    (volume (U : Set (Vec d))).toReal⁻¹
  simpa [Ch02.average, volumeMeasureOn] using hScaled

private theorem integrable_aCutoff_average_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun omega : Sample d =>
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) ^ 2)
      M.P.toMeasure := by
  apply (integrable_aCutoff_square_average M L U).mono'
  · exact (integrable_aCutoff_average M L U).1.pow 2
  · filter_upwards with omega
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact square_average_le_average_square U
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).measurable
      (fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
      ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).pow 2
        |>.continuousOn.integrableOn_compact
          U.isBoundedDomain.isBounded.isCompact_closure
        |>.mono_set subset_closure)

theorem aux_dedup_d134_abs_randomAMatrix_entry_le_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) (i j : Fin d) :
    |randomAMatrix M L U omega i j| ≤
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by
  let hdata := aCutoffCoeffOnData M L omega U
  let aomega := hdata.toCoeffOn
  let c := Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U aomega hdata.isSymmetric
  have hDerived := hTheory.derived_matrices
  have hApsd : (aMatrix U aomega).PosSemidef := by
    change (Ch02.aCoarse U aomega).PosSemidef
    rw [hDerived.1, ← hDerived.2.2]
    exact Ch02.bCoarse_posSemidef U aomega
  have hAverageMat :
      Ch02.averageMat U aomega.toCoeffField = c • (1 : Mat d) := by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp [Ch02.averageMat, Ch02.average, aomega, hdata, c,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField, scalarMatrix]
    · simp [Ch02.averageMat, Ch02.average, aomega, hdata, c,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField, scalarMatrix, hrs]
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
  have hBpsd : (Ch02.averageMat U aomega.toCoeffField).PosSemidef := by
    rw [hAverageMat]
    exact Matrix.PosSemidef.one.smul hc_nonneg
  have hAB : MatLoewnerLE (aMatrix U aomega)
      (Ch02.averageMat U aomega.toCoeffField) := by
    change MatLoewnerLE (Ch02.aCoarse U aomega)
      (Ch02.averageMat U aomega.toCoeffField)
    simpa [aMatrix, hDerived.1] using hTheory.dirichlet_neumann_bracketing.2.2
  have hNorm := Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    hApsd hBpsd hAB
  have hd_ne : d ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  letI : NeZero d := ⟨hd_ne⟩
  calc
    |randomAMatrix M L U omega i j| = |aMatrix U aomega i j| := rfl
    _ ≤ Ch02.matrixOperatorNorm (aMatrix U aomega) :=
      Ch02.abs_entry_le_matrixOperatorNorm _ _ _
    _ ≤ Ch02.matrixOperatorNorm (Ch02.averageMat U aomega.toCoeffField) := hNorm
    _ = c := by
      rw [hAverageMat]
      exact Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hc_nonneg

private theorem abs_randomAMatrix_entry_le_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) (i j : Fin d) :
    |randomAMatrix M L U omega i j| ≤
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d134_abs_randomAMatrix_entry_le_average (d := d) (M := M) (L := L) (U := U) (omega := omega) (i := i) (j := j)

/-- Every entry of a finite-cutoff primal coarse matrix is square-integrable. -/
theorem integrable_randomAMatrix_entry_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (i j : Fin d) :
    Integrable (fun omega : Sample d => randomAMatrix M L U omega i j ^ 2)
      M.P.toMeasure := by
  apply (integrable_aCutoff_average_sq M L U).mono'
  · exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_randomAMatrix M L U))).pow_const 2).aestronglyMeasurable
  · filter_upwards with omega
    have hsq : randomAMatrix M L U omega i j ^ 2 ≤
        Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) ^ 2 := by
      have havg : 0 ≤ Ch02.average U
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) :=
        mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
          (integral_nonneg fun x =>
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
      apply (sq_le_sq).2
      rw [abs_of_nonneg havg]
      exact abs_randomAMatrix_entry_le_average M L U omega i j
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq

private theorem integrable_aCutoff_inv_apply_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (x : Vec d) :
    Integrable (fun omega : Sample d =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2) M.P.toMeasure := by
  have hratio := (integral_abs_inverseCutoffRatioMinusOne_rpow_root_le_raw
    M L (-1) x 2 (by norm_num) (by omega) (by omega)).1
  have hmajorant := hratio.const_mul 2 |>.add (integrable_const 2)
  have hmeas : Measurable (fun omega : Sample d =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2) :=
    (((measurable_cutoff_uncurry M L).comp
      (measurable_id.prodMk measurable_const)).inv).pow_const 2
  apply hmajorant.mono' hmeas.aestronglyMeasurable
  filter_upwards with omega
  have heq : inverseCutoffRatioMinusOne M L (-1) omega x =
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ - 1 := by
    simp [inverseCutoffRatioMinusOne, aCutoffAtInt]
  simp only [Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹))]
  change (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2 ≤
    2 * |inverseCutoffRatioMinusOne M L (-1) omega x| ^ 2 + 2
  rw [heq]
  have hs := sq_nonneg ((SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ - 2)
  rw [Real.rpow_two, sq_abs]
  nlinarith

private theorem integral_aCutoff_inv_apply_sq_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (x : Vec d) :
    ∫ omega : Sample d, (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2
        ∂M.P.toMeasure =
      ∫ omega : Sample d, (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0)⁻¹ ^ 2
        ∂M.P.toMeasure := by
  calc
    _ = ∫ omega : Sample d,
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
          (translatePotentialSequence x omega) 0)⁻¹ ^ 2 ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [aCutoff_translatePotentialSequence M L x omega 0, zero_add]
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence x)
        (potentialSequenceLaw_stationary M x)
        (fun omega : Sample d =>
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0)⁻¹ ^ 2)
        (integrable_aCutoff_inv_apply_sq M L 0).1

private theorem integrable_aCutoff_inv_sq_prod_volumeMeasureOn {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable
      (fun z : Sample d × Vec d =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)⁻¹ ^ 2)
      (M.P.toMeasure.prod (volumeMeasureOn (U : Set (Vec d)))) := by
  have hJoint : AEStronglyMeasurable
      (fun z : Sample d × Vec d =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)⁻¹ ^ 2)
      (M.P.toMeasure.prod (volumeMeasureOn (U : Set (Vec d)))) :=
    ((measurable_cutoff_uncurry M L).inv.pow_const 2).aestronglyMeasurable
  apply (integrable_prod_iff' hJoint).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x => integrable_aCutoff_inv_apply_sq M L x
  · have hEq :
        (fun x : Vec d => ∫ omega : Sample d,
          ‖(SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2‖ ∂M.P.toMeasure) =
          fun _ => ∫ omega : Sample d,
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega 0)⁻¹ ^ 2 ∂M.P.toMeasure := by
      funext x
      rw [show (fun omega : Sample d =>
          ‖(SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2‖) =
          fun omega => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2 by
        funext omega
        exact Real.norm_of_nonneg (sq_nonneg _)]
      exact integral_aCutoff_inv_apply_sq_eq_zero M L x
    rw [hEq]
    exact integrable_const _

private theorem integrable_aCutoff_inv_average_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun omega : Sample d =>
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) ^ 2) M.P.toMeasure := by
  have hSquareAverage : Integrable (fun omega : Sample d =>
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹ ^ 2)) M.P.toMeasure := by
    have hIntegral :=
      (integrable_aCutoff_inv_sq_prod_volumeMeasureOn M L U).integral_prod_left
    have hScaled := hIntegral.const_mul
      (volume (U : Set (Vec d))).toReal⁻¹
    simpa [Ch02.average, volumeMeasureOn] using hScaled
  have hInvAverageMeas : AEStronglyMeasurable (fun omega : Sample d =>
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹)) M.P.toMeasure := by
    have hJoint : StronglyMeasurable (fun z : Sample d × Vec d =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)⁻¹) :=
      (measurable_cutoff_uncurry M L).inv.stronglyMeasurable
    exact (hJoint.integral_prod_right'.const_mul
      (volume (U : Set (Vec d))).toReal⁻¹).aestronglyMeasurable
  apply hSquareAverage.mono' (hInvAverageMeas.pow 2)
  filter_upwards with omega
  simp only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
  have hcontInv : Continuous (fun x =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) :=
    (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).inv₀
      (fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).ne')
  exact square_average_le_average_square U
    hcontInv.measurable
    (fun x => inv_nonneg.mpr
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    (hcontInv.pow 2
      |>.continuousOn.integrableOn_compact
        U.isBoundedDomain.isBounded.isCompact_closure
      |>.mono_set subset_closure)

theorem aux_dedup_d106_averagedSymmPartInv_aCutoff_eq_scalar {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    Ch02.averagedSymmPartInv U (aCutoffCoeffOnData M L omega U).toCoeffOn =
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) • (1 : Mat d) := by
  let hdata := aCutoffCoeffOnData M L omega U
  unfold Ch02.averagedSymmPartInv Ch02.averageMat
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, Matrix.smul_apply, Matrix.one_apply,
      ↓reduceIte, smul_eq_mul, mul_one]
    unfold Ch02.average
    apply congrArg ((volume (U : Set (Vec d))).toReal⁻¹ * ·)
    apply integral_congr_ae
    filter_upwards [(aCutoffCoeffOnData M L omega U).aeBounds] with x hx
    rw [scalarMatrix, Homogenization.nonsing_inv_smul
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)]
    · simp
    · exact (lt_of_lt_of_le
        (aCutoffCoeffOnData M L omega U).lam_pos hx.1).ne'
    · simp

  · simp only [ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, Matrix.smul_apply, Matrix.one_apply,
      hij, ↓reduceIte, smul_eq_mul, mul_zero]
    unfold Ch02.average
    rw [mul_eq_zero]
    right
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [(aCutoffCoeffOnData M L omega U).aeBounds] with x hx
    rw [Homogenization.nonsing_inv_smul
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)]
    · simp [hij]
    · exact (lt_of_lt_of_le
        (aCutoffCoeffOnData M L omega U).lam_pos hx.1).ne'
    · simp

private theorem averagedSymmPartInv_aCutoff_eq_scalar {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    Ch02.averagedSymmPartInv U (aCutoffCoeffOnData M L omega U).toCoeffOn =
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) • (1 : Mat d) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d106_averagedSymmPartInv_aCutoff_eq_scalar (d := d) (M := M) (L := L) (U := U) (omega := omega)

theorem aux_dedup_d197_volumeAverage_pos_of_continuous_pos {d : ℕ}
    (U : Ch02.Domain d) {f : Vec d → ℝ} (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x) :
    0 < Homogenization.volumeAverage (U : Set (Vec d)) f := by
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hint : IntegrableOn f (U : Set (Vec d)) :=
    hf.continuousOn.integrableOn_compact
      U.isBoundedDomain.isBounded.isCompact_closure |>.mono_set subset_closure
  have hnonneg : 0 ≤ᵐ[volume.restrict (U : Set (Vec d))] f := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    exact (hf_pos x).le
  have hsupp : 0 < (volume.restrict (U : Set (Vec d))) (Function.support f) := by
    have hsub : (U : Set (Vec d)) ⊆ Function.support f := by
      intro x hx
      exact (hf_pos x).ne'
    calc
      0 < volume (U : Set (Vec d)) := (ENNReal.toReal_pos_iff.mp hvol).1
      _ = (volume.restrict (U : Set (Vec d))) (U : Set (Vec d)) := by
        simp [U.measurableSet]
      _ ≤ (volume.restrict (U : Set (Vec d))) (Function.support f) := measure_mono hsub
  have hintpos : 0 < ∫ x in (U : Set (Vec d)), f x ∂volume :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hint).2 hsupp
  exact mul_pos (inv_pos.mpr hvol) hintpos

private theorem volumeAverage_pos_of_continuous_pos {d : ℕ}
    (U : Ch02.Domain d) {f : Vec d → ℝ} (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x) :
    0 < Homogenization.volumeAverage (U : Set (Vec d)) f := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d197_volumeAverage_pos_of_continuous_pos (d := d) (U := U) (f := f) (hf := hf) (hf_pos := hf_pos)

theorem aux_dedup_d118_abs_randomAStarInv_entry_le_inverse_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) (i j : Fin d) :
    |(randomAStarMatrix M L U omega)⁻¹ i j| ≤
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) := by
  have hd_ne : d ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  letI : NeZero d := ⟨hd_ne⟩
  let hdata := aCutoffCoeffOnData M L omega U
  let aomega := hdata.toCoeffOn
  let c := Ch02.average U (fun x =>
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U aomega hdata.isSymmetric
  have hc_pos : 0 < c := by
    exact volumeAverage_pos_of_continuous_pos U
      ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).inv₀
        (fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).ne'))
      (fun x => inv_pos.mpr (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x))
  have hAvg : Ch02.averagedSymmPartInv U aomega = c • (1 : Mat d) := by
    simpa [aomega, c, hdata] using
      averagedSymmPartInv_aCutoff_eq_scalar M L U omega
  have hAvgPos : (c • (1 : Mat d)).PosDef := Matrix.PosDef.one.smul hc_pos
  have hStarPos := Ch02.sigmaStarCoarse_posDef U aomega
  have hOrder : MatLoewnerLE (c • (1 : Mat d))⁻¹
      (Ch02.sigmaStarCoarse U aomega) := by
    simpa [hAvg] using hTheory.dirichlet_neumann_bracketing.1
  have hInvOrder := Homogenization.matLoewnerLE_inv_of_posDef
    hAvgPos.inv hStarPos hOrder
  have hSigmaInv : (Ch02.sigmaStarCoarse U aomega)⁻¹ =
      Ch02.sigmaStarInvCoarse U aomega := by
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U aomega)
  rw [hSigmaInv] at hInvOrder
  have hdet : IsUnit (c • (1 : Mat d)).det :=
    Homogenization.isUnit_det_smul (A := (1 : Mat d)) (by simp) hc_pos.ne'
  have hdouble : ((c • (1 : Mat d))⁻¹)⁻¹ = c • (1 : Mat d) :=
    Matrix.nonsing_inv_nonsing_inv _ hdet
  rw [hdouble] at hInvOrder
  have hInvPsd := Ch02.sigmaStarInvCoarse_posDef U aomega |>.posSemidef
  have hAvgPsd := hAvgPos.posSemidef
  have hNorm := Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    hInvPsd hAvgPsd hInvOrder
  have hrandom : (randomAStarMatrix M L U omega)⁻¹ =
      Ch02.sigmaStarInvCoarse U aomega := by
    change (aStarMatrix U aomega)⁻¹ = _
    rw [show aStarMatrix U aomega = Ch02.aStarCoarse U aomega by rfl,
      hTheory.derived_matrices.2.1]
    exact hSigmaInv
  calc
    |(randomAStarMatrix M L U omega)⁻¹ i j| =
        |Ch02.sigmaStarInvCoarse U aomega i j| := by rw [hrandom]
    _ ≤ Ch02.matrixOperatorNorm (Ch02.sigmaStarInvCoarse U aomega) :=
      Ch02.abs_entry_le_matrixOperatorNorm _ _ _
    _ ≤ Ch02.matrixOperatorNorm (c • (1 : Mat d)) := hNorm
    _ = c := Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hc_pos.le

private theorem abs_randomAStarInv_entry_le_inverse_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) (i j : Fin d) :
    |(randomAStarMatrix M L U omega)⁻¹ i j| ≤
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d118_abs_randomAStarInv_entry_le_inverse_average (d := d) (M := M) (L := L) (U := U) (omega := omega) (i := i) (j := j)

/-- Every entry of the inverse dual finite-cutoff coarse matrix is
square-integrable. -/
theorem integrable_randomAStarInv_entry_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (i j : Fin d) :
    Integrable (fun omega : Sample d =>
      (randomAStarMatrix M L U omega)⁻¹ i j ^ 2) M.P.toMeasure := by
  apply (integrable_aCutoff_inv_average_sq M L U).mono'
  · exact ((((integrable_randomAStarMatrix_inv M L U).eval i).eval j).1.pow 2)
  · filter_upwards with omega
    have havg : 0 ≤ Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) :=
      mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
        (integral_nonneg fun x => inv_nonneg.mpr
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    have hsq : (randomAStarMatrix M L U omega)⁻¹ i j ^ 2 ≤
        Ch02.average U (fun x =>
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) ^ 2 := by
      apply (sq_le_sq).2
      rw [abs_of_nonneg havg]
      exact abs_randomAStarInv_entry_le_inverse_average M L U omega i j
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq

theorem cutoffResponseJ_eq_randomMatrixQuadratics {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Vec d) (omega : Sample d) :
    J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U omega) p) +
        (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) - vecDot p q := by
  let hdata := aCutoffCoeffOnData M L omega U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  have hstar : (randomAStarMatrix M L U omega)⁻¹ =
      Ch02.sigmaStarInvCoarse U hdata.toCoeffOn := by
    change (aStarMatrix U hdata.toCoeffOn)⁻¹ = _
    rw [show aStarMatrix U hdata.toCoeffOn = Ch02.aStarCoarse U hdata.toCoeffOn by rfl,
      hTheory.derived_matrices.2.1]
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)
  have ha : randomAMatrix M L U omega =
      Ch02.sigmaCoarse U hdata.toCoeffOn := by
    change aMatrix U hdata.toCoeffOn = _
    exact hTheory.derived_matrices.1
  change Ch02.responseJ U hdata.toCoeffOn p q = _
  calc
    Ch02.responseJ U hdata.toCoeffOn p q =
        Ch02.symmetricDirichletNu U hdata.toCoeffOn p +
          Ch02.symmetricNeumannNu U hdata.toCoeffOn q - vecDot p q :=
      hTheory.response_dirichlet_neumann_split p q
    _ = (1 / 2 : ℝ) * vecDot p
          (matVecMul (Ch02.sigmaCoarse U hdata.toCoeffOn) p) +
        (1 / 2 : ℝ) * vecDot q
          (matVecMul (Ch02.sigmaStarInvCoarse U hdata.toCoeffOn) q) - vecDot p q := by
      rw [hTheory.dirichlet_value_by_sigma, hTheory.neumann_value_by_sigmaStarInv]
    _ = _ := by
      rw [ha, hstar]

theorem integrable_cutoffResponseJ {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Vec d) :
    Integrable (fun omega : Sample d =>
      J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q) M.P.toMeasure := by
  have hp := (integrable_matrix_quadratic (integrable_randomAMatrix M L U) p).const_mul
    (1 / 2 : ℝ)
  have hq := (integrable_matrix_quadratic (integrable_randomAStarMatrix_inv M L U) q).const_mul
    (1 / 2 : ℝ)
  apply (hp.add hq).sub (integrable_const (vecDot p q)) |>.congr
  filter_upwards with omega
  exact (cutoffResponseJ_eq_randomMatrixQuadratics M L U p q omega).symm

theorem expectedJDifference_eq_sub_unconditional {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n m : ℕ) (p q : Vec d) :
    expectedJDifference M L n m p q =
      expectedJ M L n p q - expectedJ M L m p q := by
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.expectedJDifference_eq_sub
  · simpa [aCutoffFamily] using integrable_cutoffResponseJ M L
      (Ch02.cubeDomain (originCube d (n : ℤ))) p q
  · simpa [aCutoffFamily] using integrable_cutoffResponseJ M L
      (Ch02.cubeDomain (originCube d (m : ℤ))) p q

theorem measurable_restricted_cutoffResponseJ {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Vec d) {G : Set (Sample d)} (hG : MeasurableSet G) :
    Measurable (G.indicator fun omega =>
      J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q) :=
  (measurable_cutoff_responseJ M L U p q).indicator hG

theorem integrable_restricted_cutoffResponseJ {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p q : Vec d) {G : Set (Sample d)} (hG : MeasurableSet G) :
    Integrable (G.indicator fun omega =>
      J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q) M.P.toMeasure :=
  (integrable_cutoffResponseJ M L U p q).indicator hG

theorem integrable_restricted_coarseEllipticityGoodEvent_responseJ {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ) (p q : Vec d) :
    Integrable ((coarseEllipticityGoodEvent M L m).indicator fun omega =>
      J (Ch02.cubeDomain (originCube d (m : ℤ)))
        (aCutoffCoeffOnData M L omega
          (Ch02.cubeDomain (originCube d (m : ℤ)))).toCoeffOn p q)
      M.P.toMeasure :=
  integrable_restricted_cutoffResponseJ M L
    (Ch02.cubeDomain (originCube d (m : ℤ))) p q
      (measurableSet_coarseEllipticityGoodEvent M L m)

theorem randomAMatrix_eq_rawSigmaCoarse {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    randomAMatrix M L (Ch02.cubeDomain Q) omega =
      Homogenization.sigmaCoarse (Homogenization.openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
  let hdata := aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain Q) hdata.toCoeffOn hdata.isSymmetric
  calc
    randomAMatrix M L (Ch02.cubeDomain Q) omega =
        Ch02.sigmaCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn :=
      hTheory.derived_matrices.1
    _ = Homogenization.sigmaCoarse (Homogenization.openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
      simpa [hdata, ScalarCoeffOnData.toCoeffOn] using
        Homogenization.Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse
          (Ch02.cubeDomain Q) hdata.toCoeffOn

theorem randomAMatrix_cube_eq_originCube_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    randomAMatrix M L (Ch02.cubeDomain Q) omega =
      randomAMatrix M L (Ch02.cubeDomain (originCube d Q.scale))
        (translatePotentialSequence (triadicCubeShift Q) omega) := by
  rw [randomAMatrix_eq_rawSigmaCoarse, randomAMatrix_eq_rawSigmaCoarse]
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [sigmaCoarse_translateSet_eq_translateCoeffField]
  apply congrArg (sigmaCoarse (openCubeSet (originCube d Q.scale)))
  funext x
  change scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + triadicCubeShift Q)) =
    scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
      (translatePotentialSequence (triadicCubeShift Q) omega) x)
  exact congrArg scalarMatrix
    (aCutoff_translatePotentialSequence M L (triadicCubeShift Q) omega x).symm

theorem randomAStarInv_eq_rawSigmaStarInvCoarse {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ =
      Homogenization.sigmaStarInvCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
  let hdata := aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain Q) hdata.toCoeffOn hdata.isSymmetric
  have hstar : (aStarMatrix (Ch02.cubeDomain Q) hdata.toCoeffOn)⁻¹ =
      Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn := by
    rw [show aStarMatrix (Ch02.cubeDomain Q) hdata.toCoeffOn =
      Ch02.aStarCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn by rfl,
      hTheory.derived_matrices.2.1]
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn)
  calc
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ =
        Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn := hstar
    _ = Homogenization.sigmaStarInvCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
      simpa [hdata, ScalarCoeffOnData.toCoeffOn] using
        Homogenization.Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse
          (Ch02.cubeDomain Q) hdata.toCoeffOn

theorem randomAStarInv_cube_eq_originCube_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : Sample d) (Q : TriadicCube d) :
    (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ =
      (randomAStarMatrix M L (Ch02.cubeDomain (originCube d Q.scale))
        (translatePotentialSequence (triadicCubeShift Q) omega))⁻¹ := by
  rw [randomAStarInv_eq_rawSigmaStarInvCoarse,
    randomAStarInv_eq_rawSigmaStarInvCoarse]
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [sigmaStarInvCoarse_translateSet_eq_translateCoeffField]
  apply congrArg (sigmaStarInvCoarse (openCubeSet (originCube d Q.scale)))
  funext x
  change scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + triadicCubeShift Q)) =
    scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
      (translatePotentialSequence (triadicCubeShift Q) omega) x)
  exact congrArg scalarMatrix
    (aCutoff_translatePotentialSequence M L (triadicCubeShift Q) omega x).symm

theorem integral_randomAMatrix_entry_cube_eq_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i j : Fin d) :
    ∫ omega, randomAMatrix M L (Ch02.cubeDomain Q) omega i j ∂M.P.toMeasure =
      ∫ omega, randomAMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale)) omega i j ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, randomAMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale))
        (translatePotentialSequence (triadicCubeShift Q) omega) i j
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [randomAMatrix_cube_eq_originCube_translate M L omega Q]
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift Q))
        (potentialSequenceLaw_stationary M (triadicCubeShift Q))
        (fun omega => randomAMatrix M L
          (Ch02.cubeDomain (originCube d Q.scale)) omega i j)
        (((integrable_randomAMatrix M L
          (Ch02.cubeDomain (originCube d Q.scale))).eval i).eval j).1

theorem integral_randomAStarInv_entry_cube_eq_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i j : Fin d) :
    ∫ omega, (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j
        ∂M.P.toMeasure =
      ∫ omega, (randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, (randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale))
        (translatePotentialSequence (triadicCubeShift Q) omega))⁻¹ i j
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [randomAStarInv_cube_eq_originCube_translate M L omega Q]
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift Q))
        (potentialSequenceLaw_stationary M (triadicCubeShift Q))
        (fun omega => (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j)
        ((((integrable_randomAStarMatrix_inv M L
          (Ch02.cubeDomain (originCube d Q.scale))).eval i).eval j).1)

theorem integral_randomAMatrix_entry_sq_cube_eq_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i j : Fin d) :
    ∫ omega, randomAMatrix M L (Ch02.cubeDomain Q) omega i j ^ 2
        ∂M.P.toMeasure =
      ∫ omega, randomAMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale)) omega i j ^ 2
        ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, (randomAMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale))
        (translatePotentialSequence (triadicCubeShift Q) omega) i j) ^ 2
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [randomAMatrix_cube_eq_originCube_translate M L omega Q]
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift Q))
        (potentialSequenceLaw_stationary M (triadicCubeShift Q))
        (fun omega => randomAMatrix M L
          (Ch02.cubeDomain (originCube d Q.scale)) omega i j ^ 2)
        (integrable_randomAMatrix_entry_sq M L
          (Ch02.cubeDomain (originCube d Q.scale)) i j).1

theorem integral_randomAStarInv_entry_sq_cube_eq_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (i j : Fin d) :
    ∫ omega, (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j ^ 2
        ∂M.P.toMeasure =
      ∫ omega, (randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j ^ 2
        ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, ((randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d Q.scale))
        (translatePotentialSequence (triadicCubeShift Q) omega))⁻¹ i j) ^ 2
        ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [randomAStarInv_cube_eq_originCube_translate M L omega Q]
    _ = _ := by
      simpa [Function.comp_def] using integral_comp_eq_of_map_eq
        (measurable_translatePotentialSequence (triadicCubeShift Q))
        (potentialSequenceLaw_stationary M (triadicCubeShift Q))
        (fun omega => (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d Q.scale)) omega)⁻¹ i j ^ 2)
        (integrable_randomAStarInv_entry_sq M L
          (Ch02.cubeDomain (originCube d Q.scale)) i j).1

end

end SubdiffusiveProcess.CoarseGrainingVocab
