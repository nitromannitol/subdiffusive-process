module

public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open SubdiffusiveProcess.CoarseGrainingVocab MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book
open scoped ENNReal MatrixOrder

noncomputable section

private theorem averageMat_scalarCoeff {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ} (ha : ScalarCoeffOnData U a) :
    Ch02.averageMat U ha.toCoeffOn.toCoeffField =
      Ch02.average U a • (1 : Homogenization.Mat d) := by
  unfold Ch02.averageMat
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ScalarCoeffOnData.toCoeffOn, scalarCoeffField, scalarMatrix]
  · simp [ScalarCoeffOnData.toCoeffOn, scalarCoeffField, scalarMatrix, hij,
      Ch02.average]

private theorem averagedSymmPartInv_scalarCoeff {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ} (ha : ScalarCoeffOnData U a) :
    Ch02.averagedSymmPartInv U ha.toCoeffOn =
      Ch02.average U (fun x => (a x)⁻¹) • (1 : Homogenization.Mat d) := by
  unfold Ch02.averagedSymmPartInv Ch02.averageMat
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, Matrix.smul_apply, Matrix.one_apply,
      ↓reduceIte, smul_eq_mul, mul_one]
    unfold Ch02.average
    apply congrArg ((volume (U : Set (Homogenization.Vec d))).toReal⁻¹ * ·)
    apply integral_congr_ae
    filter_upwards [ha.aeBounds] with x hx
    rw [scalarMatrix, Homogenization.nonsing_inv_smul (a x)]
    · simp
    · exact (lt_of_lt_of_le ha.lam_pos hx.1).ne'
    · simp
  · simp only [ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, Matrix.smul_apply, Matrix.one_apply,
      hij, ↓reduceIte, smul_eq_mul, mul_zero]
    unfold Ch02.average
    rw [mul_eq_zero]
    right
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [ha.aeBounds] with x hx
    rw [Homogenization.nonsing_inv_smul (a x)]
    · simp [hij]
    · exact (lt_of_lt_of_le ha.lam_pos hx.1).ne'
    · simp

private theorem scalar_integrableOn {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) : IntegrableOn a (U : Set (Homogenization.Vec d)) := by
  have hmeas : AEStronglyMeasurable a
      (volume.restrict (U : Set (Homogenization.Vec d))) := by
    have h := ha.aeStronglyMeasurable (0 : Fin d) (0 : Fin d)
    apply h.congr
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    simp [scalarCoeffField, scalarMatrix, restrictCoeffField, hx]
  refine Integrable.mono' (integrable_const ha.Lam) hmeas ?_
  filter_upwards [ha.aeBounds] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (lt_of_lt_of_le ha.lam_pos hx.1).le]
  exact hx.2

private theorem scalar_inv_integrableOn {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) :
    IntegrableOn (fun x => (a x)⁻¹) (U : Set (Homogenization.Vec d)) := by
  have hmeas : AEStronglyMeasurable a
      (volume.restrict (U : Set (Homogenization.Vec d))) := by
    have h := ha.aeStronglyMeasurable (0 : Fin d) (0 : Fin d)
    apply h.congr
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    simp [scalarCoeffField, scalarMatrix, restrictCoeffField, hx]
  refine Integrable.mono' (integrable_const ha.lam⁻¹)
    (hmeas.aemeasurable.inv.aestronglyMeasurable) ?_
  filter_upwards [ha.aeBounds] with x hx
  have hax : 0 < a x := lt_of_lt_of_le ha.lam_pos hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_pos.mpr hax).le]
  exact (inv_le_inv₀ hax ha.lam_pos).2 hx.1

private theorem volumeAverage_pos_of_pos_on {d : ℕ}
    {W : Set (Homogenization.Vec d)} {f : Homogenization.Vec d → ℝ}
    (hW : MeasurableSet W) (hvol : 0 < (volume W).toReal)
    (hint : IntegrableOn f W) (hf : ∀ x ∈ W, 0 < f x) :
    0 < volumeAverage W f := by
  have hvolE : 0 < volume W := (ENNReal.toReal_pos_iff.mp hvol).1
  have hnonneg : 0 ≤ᵐ[volume.restrict W] f := by
    filter_upwards [ae_restrict_mem hW] with x hx
    exact (hf x hx).le
  have hsupp : 0 < (volume.restrict W) (Function.support f) := by
    have hsub : W ⊆ Function.support f := by
      intro x hx
      exact (hf x hx).ne'
    calc
      0 < volume W := hvolE
      _ = (volume.restrict W) W := by simp [hW]
      _ ≤ (volume.restrict W) (Function.support f) := measure_mono hsub
  have hintpos : 0 < ∫ x in W, f x ∂volume :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hint).2 hsupp
  exact mul_pos (inv_pos.mpr hvol) hintpos

/-- A normalized scalar response is bounded by one half of the averaged
forward-plus-reciprocal ratio defect.  This is the sharp deterministic form
used by the manuscript's subunit response estimate. -/
theorem responseJ_le_half_scalar_ratio {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    {alpha : ℝ} (halpha : 0 < alpha) (ha_pos : ∀ x, 0 < a x)
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    J U ha.toCoeffOn ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) ≤
      (1 / 2 : ℝ) * Ch02.average U (fun x =>
        a x / alpha + alpha / a x - 2) := by
  let p : Homogenization.Vec d := (Real.sqrt alpha)⁻¹ • e
  let q : Homogenization.Vec d := Real.sqrt alpha • e
  let c := Ch02.average U a
  let h := Ch02.average U (fun x => (a x)⁻¹)
  have hvol : 0 < (volume (U : Set (Homogenization.Vec d))).toReal :=
    Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hc : 0 < c := by
    change 0 < volumeAverage (U : Set (Homogenization.Vec d)) a
    exact volumeAverage_pos_of_pos_on U.measurableSet hvol
      (scalar_integrableOn U ha) (fun x _ => ha_pos x)
  have hh : 0 < h := by
    change 0 < volumeAverage (U : Set (Homogenization.Vec d)) (fun x => (a x)⁻¹)
    exact volumeAverage_pos_of_pos_on U.measurableSet hvol
      (scalar_inv_integrableOn U ha) (fun x _ => inv_pos.mpr (ha_pos x))
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U ha.toCoeffOn ha.isSymmetric
  have hAavg := hTheory.dirichlet_neumann_bracketing.2.2 p
  rw [averageMat_scalarCoeff U ha] at hAavg
  have hHarm := hTheory.dirichlet_neumann_bracketing.1
  rw [averagedSymmPartInv_scalarCoeff U ha] at hHarm
  have hHpos : (h • (1 : Homogenization.Mat d)).PosDef := by
    exact Matrix.PosDef.one.smul hh
  have hHinvPos : ((h • (1 : Homogenization.Mat d))⁻¹).PosDef := hHpos.inv
  have hStarPos := Ch02.sigmaStarCoarse_posDef U ha.toCoeffOn
  have hHarm' : MatLoewnerLE (h • (1 : Homogenization.Mat d))⁻¹
      (Ch02.sigmaStarCoarse U ha.toCoeffOn) := by
    simpa only [h] using hHarm
  have hInvOrder := Homogenization.matLoewnerLE_inv_of_posDef
    hHinvPos hStarPos hHarm'
  have hSigmaInv : (Ch02.sigmaStarCoarse U ha.toCoeffOn)⁻¹ =
      Ch02.sigmaStarInvCoarse U ha.toCoeffOn := by
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U ha.toCoeffOn)
  rw [hSigmaInv] at hInvOrder
  have hdet : IsUnit (h • (1 : Homogenization.Mat d)).det :=
    Homogenization.isUnit_det_smul (A := (1 : Homogenization.Mat d))
      (by simp) hh.ne'
  have hdouble : ((h • (1 : Homogenization.Mat d))⁻¹)⁻¹ =
      h • (1 : Homogenization.Mat d) :=
    Matrix.nonsing_inv_nonsing_inv _ hdet
  rw [hdouble] at hInvOrder
  have hq := hInvOrder q
  have hp := hAavg
  have hsplit := hTheory.response_dirichlet_neumann_split p q
  rw [hTheory.dirichlet_value_by_sigma p,
    hTheory.neumann_value_by_sigmaStarInv q] at hsplit
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.mpr halpha
  have hpNorm : vecNormSq p = alpha⁻¹ := by
    simp [p, vecNormSq_smul, he, Real.sq_sqrt halpha.le]
  have hqNorm : vecNormSq q = alpha := by
    simp [q, vecNormSq_smul, he, Real.sq_sqrt halpha.le]
  have hpq : vecDot p q = 1 := by
    have he' : vecDot e e = 1 := he
    simp [p, q, vecDot_smul_left, vecDot_smul_right, he', hsqrt.ne']
  have hp' : vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) ≤
      c * alpha⁻¹ := by
    have hone : vecDot p (matVecMul (1 : Homogenization.Mat d) p) =
        vecNormSq p := by
      change dotProduct p (Matrix.mulVec (1 : Homogenization.Mat d) p) =
        dotProduct p p
      rw [Matrix.one_mulVec]
    simp only [smul_matVecMul, vecDot_smul_right, hone, hpNorm] at hp
    linarith
  have hq' : vecDot q
      (matVecMul (Ch02.sigmaStarInvCoarse U ha.toCoeffOn) q) ≤ h * alpha := by
    have hone : vecDot q (matVecMul (1 : Homogenization.Mat d) q) =
        vecNormSq q := by
      change dotProduct q (Matrix.mulVec (1 : Homogenization.Mat d) q) =
        dotProduct q q
      rw [Matrix.one_mulVec]
    simp only [smul_matVecMul, vecDot_smul_right, hone, hqNorm] at hq
    linarith
  change J U ha.toCoeffOn p q ≤ _
  change Ch02.responseJ U ha.toCoeffOn p q ≤ _
  rw [hsplit, hpq]
  have hraw :
      (1 / 2 : ℝ) * vecDot p
          (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) +
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (Ch02.sigmaStarInvCoarse U ha.toCoeffOn) q) - 1 ≤
        (1 / 2 : ℝ) * (c * alpha⁻¹ + h * alpha) - 1 := by
    linarith
  let f1 : Homogenization.Vec d → ℝ := fun x => alpha⁻¹ * a x
  let f2 : Homogenization.Vec d → ℝ := fun x => alpha * (a x)⁻¹
  let fcross : Homogenization.Vec d → ℝ := fun x =>
    (1 / 2 : ℝ) * (f1 x + f2 x - 2)
  have hf1 : IntegrableOn f1 (U : Set (Homogenization.Vec d)) :=
    (scalar_integrableOn U ha).const_mul alpha⁻¹
  have hf2 : IntegrableOn f2 (U : Set (Homogenization.Vec d)) :=
    (scalar_inv_integrableOn U ha).const_mul alpha
  have havg1 : volumeAverage (U : Set (Homogenization.Vec d)) f1 =
      alpha⁻¹ * c := by
    simpa [f1, c, Ch02.average, Pi.smul_def, smul_eq_mul] using! volumeAverage_smul
      (U : Set (Homogenization.Vec d)) alpha⁻¹ a
  have havg2 : volumeAverage (U : Set (Homogenization.Vec d)) f2 =
      alpha * h := by
    simpa [f2, h, Ch02.average, Pi.smul_def, smul_eq_mul] using! volumeAverage_smul
      (U : Set (Homogenization.Vec d)) alpha (fun x => (a x)⁻¹)
  have hvolne : (volume (U : Set (Homogenization.Vec d))).toReal ≠ 0 := hvol.ne'
  have havgCross : volumeAverage (U : Set (Homogenization.Vec d)) fcross =
      (1 / 2 : ℝ) * (c * alpha⁻¹ + h * alpha) - 1 := by
    have hfcross_eq : fcross = (1 / 2 : ℝ) •
        ((f1 + f2) - fun _ => (2 : ℝ)) := by
      funext x
      rfl
    rw [hfcross_eq, volumeAverage_smul,
      volumeAverage_sub (hf1.add hf2) (integrable_const 2),
      volumeAverage_add hf1 hf2, havg1, havg2,
      volumeAverage_const (c := (2 : ℝ)) hvolne]
    ring
  rw [← havgCross] at hraw
  have hcrossTarget : volumeAverage (U : Set (Homogenization.Vec d)) fcross =
      (1 / 2 : ℝ) * Ch02.average U (fun x =>
        a x / alpha + alpha / a x - 2) := by
    have hfcross_eq : fcross = (1 / 2 : ℝ) • (fun x =>
        a x / alpha + alpha / a x - 2) := by
      funext x
      simp [fcross, f1, f2, div_eq_mul_inv, mul_comm]
    rw [hfcross_eq, volumeAverage_smul]
    rfl
  rw [hcrossTarget] at hraw
  exact hraw

/-- Unit-sphere form of `responseJ_le_half_scalar_ratio`. -/
theorem paperScalarProbeMaxOn_le_half_scalar_ratio {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) {alpha : ℝ} (halpha : 0 < alpha)
    (ha_pos : ∀ x, 0 < a x) :
    paperScalarProbeMaxOn U ha.toCoeffOn alpha ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * Ch02.average U (fun x =>
        a x / alpha + alpha / a x - 2)) := by
  unfold paperScalarProbeMaxOn
  apply iSup_le
  intro e
  apply ENNReal.ofReal_le_ofReal
  exact responseJ_le_half_scalar_ratio U ha halpha ha_pos e e.property

/-- A normalized scalar response is bounded by the averaged forward and
reciprocal ratio defects.  This is the deterministic content used in the
subunit branch of `e.direct.J.bound.subunit`.

The proof was already the internal engine of `normalizedDefect_le_ratio_energy`;
it is public here so later graph nodes can reuse that engine without copying
the variational argument. -/
theorem responseJ_le_scalar_ratio_energy {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    {alpha : ℝ} (halpha : 0 < alpha) (ha_pos : ∀ x, 0 < a x)
    (henergyInt : IntegrableOn (fun x =>
      (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2)
      (U : Set (Homogenization.Vec d)))
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    J U ha.toCoeffOn ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) ≤
      Ch02.average U (fun x =>
        (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2) := by
  let p : Homogenization.Vec d := (Real.sqrt alpha)⁻¹ • e
  let q : Homogenization.Vec d := Real.sqrt alpha • e
  let c := Ch02.average U a
  let h := Ch02.average U (fun x => (a x)⁻¹)
  have hvol : 0 < (volume (U : Set (Homogenization.Vec d))).toReal :=
    Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hc : 0 < c := by
    change 0 < volumeAverage (U : Set (Homogenization.Vec d)) a
    exact volumeAverage_pos_of_pos_on U.measurableSet hvol
      (scalar_integrableOn U ha) (fun x _ => ha_pos x)
  have hh : 0 < h := by
    change 0 < volumeAverage (U : Set (Homogenization.Vec d)) (fun x => (a x)⁻¹)
    exact volumeAverage_pos_of_pos_on U.measurableSet hvol
      (scalar_inv_integrableOn U ha) (fun x _ => inv_pos.mpr (ha_pos x))
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U ha.toCoeffOn ha.isSymmetric
  have hAavg := hTheory.dirichlet_neumann_bracketing.2.2 p
  rw [averageMat_scalarCoeff U ha] at hAavg
  have hHarm := hTheory.dirichlet_neumann_bracketing.1
  rw [averagedSymmPartInv_scalarCoeff U ha] at hHarm
  have hHpos : (h • (1 : Homogenization.Mat d)).PosDef := by
    exact Matrix.PosDef.one.smul hh
  have hHinvPos : ((h • (1 : Homogenization.Mat d))⁻¹).PosDef := hHpos.inv
  have hStarPos := Ch02.sigmaStarCoarse_posDef U ha.toCoeffOn
  have hHarm' : MatLoewnerLE (h • (1 : Homogenization.Mat d))⁻¹
      (Ch02.sigmaStarCoarse U ha.toCoeffOn) := by
    simpa only [h] using hHarm
  have hInvOrder := Homogenization.matLoewnerLE_inv_of_posDef
    hHinvPos hStarPos hHarm'
  have hSigmaInv : (Ch02.sigmaStarCoarse U ha.toCoeffOn)⁻¹ =
      Ch02.sigmaStarInvCoarse U ha.toCoeffOn := by
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U ha.toCoeffOn)
  rw [hSigmaInv] at hInvOrder
  have hdet : IsUnit (h • (1 : Homogenization.Mat d)).det :=
    Homogenization.isUnit_det_smul (A := (1 : Homogenization.Mat d))
      (by simp) hh.ne'
  have hdouble : ((h • (1 : Homogenization.Mat d))⁻¹)⁻¹ =
      h • (1 : Homogenization.Mat d) :=
    Matrix.nonsing_inv_nonsing_inv _ hdet
  rw [hdouble] at hInvOrder
  have hq := hInvOrder q
  have hp := hAavg
  have hsplit := hTheory.response_dirichlet_neumann_split p q
  rw [hTheory.dirichlet_value_by_sigma p,
    hTheory.neumann_value_by_sigmaStarInv q] at hsplit
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.mpr halpha
  have hpNorm : vecNormSq p = alpha⁻¹ := by
    simp [p, vecNormSq_smul, he, Real.sq_sqrt halpha.le]
  have hqNorm : vecNormSq q = alpha := by
    simp [q, vecNormSq_smul, he, Real.sq_sqrt halpha.le]
  have hpq : vecDot p q = 1 := by
    have he' : vecDot e e = 1 := he
    simp [p, q, vecDot_smul_left, vecDot_smul_right, he', hsqrt.ne']
  have hp' : vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) ≤
      c * alpha⁻¹ := by
    have hp0 := hp
    have hone : vecDot p (matVecMul (1 : Homogenization.Mat d) p) = vecNormSq p := by
      change dotProduct p (Matrix.mulVec (1 : Homogenization.Mat d) p) = dotProduct p p
      rw [Matrix.one_mulVec]
    simp only [smul_matVecMul, vecDot_smul_right, hone, hpNorm] at hp0
    linarith
  have hq' : vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U ha.toCoeffOn) q) ≤
      h * alpha := by
    have hq0 := hq
    have hone : vecDot q (matVecMul (1 : Homogenization.Mat d) q) = vecNormSq q := by
      change dotProduct q (Matrix.mulVec (1 : Homogenization.Mat d) q) = dotProduct q q
      rw [Matrix.one_mulVec]
    simp only [smul_matVecMul, vecDot_smul_right, hone, hqNorm] at hq0
    exact (by linarith)
  change J U ha.toCoeffOn p q ≤ _
  change Ch02.responseJ U ha.toCoeffOn p q ≤ _
  rw [hsplit, hpq]
  have hraw :
      (1 / 2 : ℝ) * vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) +
          (1 / 2 : ℝ) * vecDot q
            (matVecMul (Ch02.sigmaStarInvCoarse U ha.toCoeffOn) q) - 1 ≤
        (1 / 2 : ℝ) * (c * alpha⁻¹ + h * alpha) - 1 := by
    linarith
  refine hraw.trans ?_
  let f1 : Homogenization.Vec d → ℝ := fun x => alpha⁻¹ * a x
  let f2 : Homogenization.Vec d → ℝ := fun x => alpha * (a x)⁻¹
  let fcross : Homogenization.Vec d → ℝ := fun x =>
    (1 / 2 : ℝ) * (f1 x + f2 x - 2)
  have hf1 : IntegrableOn f1 (U : Set (Homogenization.Vec d)) :=
    (scalar_integrableOn U ha).const_mul alpha⁻¹
  have hf2 : IntegrableOn f2 (U : Set (Homogenization.Vec d)) :=
    (scalar_inv_integrableOn U ha).const_mul alpha
  have hfcross : IntegrableOn fcross (U : Set (Homogenization.Vec d)) :=
    ((hf1.add hf2).sub (integrable_const 2)).const_mul (1 / 2 : ℝ)
  have hpoint : ∀ x, fcross x ≤
      (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2 := by
    intro x
    have hx := mul_inv_sub_one_sq_le (a x / alpha) (div_pos (ha_pos x) halpha)
    have hane : a x ≠ 0 := (ha_pos x).ne'
    have halphane : alpha ≠ 0 := halpha.ne'
    have hinv : (a x / alpha)⁻¹ = alpha / a x := by
      field_simp
    rw [hinv] at hx
    have hid : (a x / alpha) * (alpha / a x - 1) ^ 2 =
        a x / alpha + alpha / a x - 2 := by
      field_simp
      ring
    rw [hid] at hx
    dsimp [fcross, f1, f2]
    rw [show alpha⁻¹ * a x = a x / alpha by field_simp,
      show alpha * (a x)⁻¹ = alpha / a x by rw [div_eq_mul_inv]]
    linarith
  have havgMono : volumeAverage (U : Set (Homogenization.Vec d)) fcross ≤
      volumeAverage (U : Set (Homogenization.Vec d)) (fun x =>
        (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2) := by
    unfold volumeAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
    exact integral_mono hfcross henergyInt hpoint
  have hvolne : (volume (U : Set (Homogenization.Vec d))).toReal ≠ 0 := hvol.ne'
  have havg1 : volumeAverage (U : Set (Homogenization.Vec d)) f1 = alpha⁻¹ * c := by
    simpa [f1, c, Ch02.average, Pi.smul_def, smul_eq_mul] using! volumeAverage_smul
      (U : Set (Homogenization.Vec d)) alpha⁻¹ a
  have havg2 : volumeAverage (U : Set (Homogenization.Vec d)) f2 = alpha * h := by
    simpa [f2, h, Ch02.average, Pi.smul_def, smul_eq_mul] using! volumeAverage_smul
      (U : Set (Homogenization.Vec d)) alpha (fun x => (a x)⁻¹)
  have havgCross : volumeAverage (U : Set (Homogenization.Vec d)) fcross =
      (1 / 2 : ℝ) * (c * alpha⁻¹ + h * alpha) - 1 := by
    have hfcross_eq : fcross = (1 / 2 : ℝ) •
        ((f1 + f2) - fun _ => (2 : ℝ)) := by
      funext x
      rfl
    rw [hfcross_eq, volumeAverage_smul,
      volumeAverage_sub (hf1.add hf2) (integrable_const 2),
      volumeAverage_add hf1 hf2, havg1, havg2,
      volumeAverage_const (c := (2 : ℝ)) hvolne]
    ring
  change (1 / 2 : ℝ) * (c * alpha⁻¹ + h * alpha) - 1 ≤
    volumeAverage (U : Set (Homogenization.Vec d)) (fun x =>
      (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2)
  rw [← havgCross]
  exact havgMono

/-- Unit-sphere version of `responseJ_le_scalar_ratio_energy`. -/
theorem paperScalarProbeMaxOn_le_scalar_ratio_energy {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) {a : Homogenization.Vec d → ℝ}
    (ha : ScalarCoeffOnData U a) {alpha : ℝ} (halpha : 0 < alpha)
    (ha_pos : ∀ x, 0 < a x)
    (henergyInt : IntegrableOn (fun x =>
      (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2)
      (U : Set (Homogenization.Vec d))) :
    paperScalarProbeMaxOn U ha.toCoeffOn alpha ≤
      ENNReal.ofReal (Ch02.average U (fun x =>
        (a x / alpha - 1) ^ 2 + (alpha / a x - 1) ^ 2)) := by
  unfold paperScalarProbeMaxOn
  apply iSup_le
  intro e
  apply ENNReal.ofReal_le_ofReal
  exact responseJ_le_scalar_ratio_energy U ha halpha ha_pos henergyInt e e.property

theorem normalizedDefect_le_ratio_energy {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hhom : 0 < ahom M m) :
    normalizedDefect M m U ω ≤
      ENNReal.ofReal (Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x / ahom M m - 1) ^ 2 +
          (ahom M m / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x - 1) ^ 2)) := by
  let a : Homogenization.Vec d → ℝ := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω
  let ha : ScalarCoeffOnData U a := aCutoffCoeffOnData M m ω U
  have ha_pos : ∀ x, 0 < a x := fun x =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M m ω x
  have henergyContinuous : Continuous (fun x =>
      (a x / ahom M m - 1) ^ 2 + (ahom M m / a x - 1) ^ 2) := by
    exact ((((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m ω).div_const _).sub
      continuous_const).pow 2).add
      (((continuous_const.div
        (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M m ω)
        (fun x => (ha_pos x).ne')).sub continuous_const).pow 2)
  have henergyInt : IntegrableOn (fun x =>
      (a x / ahom M m - 1) ^ 2 + (ahom M m / a x - 1) ^ 2)
      (U : Set (Homogenization.Vec d)) := by
    exact (henergyContinuous.continuousOn.integrableOn_compact
      U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  rw [normalizedDefect]
  exact paperScalarProbeMaxOn_le_scalar_ratio_energy U ha hhom ha_pos henergyInt

end

end SubdiffusiveProcess.CoarseGrainingVocab
