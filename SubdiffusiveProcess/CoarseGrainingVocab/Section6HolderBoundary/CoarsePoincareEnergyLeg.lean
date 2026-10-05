module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.BesovVocabularyBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ScalarEnergyIdentity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.RoughDirichletMinimality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DirichletEnergyPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor
public import SubdiffusiveProcess.Section2.CoarseGrainedPoincare

@[expose] public section

/-!
# Boundary Holder Step 6: coarse Poincare to scalar cutoff energy

This file composes the branch-independent fractional Poincare output with the
proved frozen Section 2 coarse-grained Poincare theorem.  The coefficient
energy is then identified with the normalized `L²` norm of
`sqrt (aCutoff) * grad u`.  No pointwise/pathwise ellipticity constant enters.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The fixed loss from removing the paper's leading `s^(1/q)` normalization
at `s = 1/2`, `q = 2`. -/
def coarsePoincareNormalizationPrice : ℝ :=
  (Real.rpow (1 / 2 : ℝ) (1 / 2 : ℝ))⁻¹

theorem coarsePoincareNormalizationPrice_pos :
    0 < coarsePoincareNormalizationPrice := by
  unfold coarsePoincareNormalizationPrice
  exact inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

/-- For the scalar cutoff family, the coefficient-energy norm in the frozen
Section 2 theorem is exactly the physical normalized weighted-gradient norm. -/
theorem coefficientEnergyNorm_aCutoffFamily_eq_weightedGrad
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    coefficientEnergyNorm Q (aCutoffFamily M L omega) u.grad =
      vectorNormalizedL2On (openCubeSet Q)
        (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) •
          u.grad x) := by
  rw [Section6Holder.vectorNormalizedL2On_sqrt_aCutoff_eq]
  unfold coefficientEnergyNorm
  congr 1
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [volumeAverage_openCubeSet_eq_cubeAverage]
  apply cubeAverage_eq_of_eq_on_cubeSet
  intro x hx
  change vecDot (u.grad x)
      (matVecMul (scalarCoeffField
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x) (u.grad x)) = _
  rw [Section6HolderInterior.vecDot_matVecMul_scalarCoeffField_eq_sq]
  · exact Section6HolderInterior.euclideanNorm_sqrt_smul_sq
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) u.grad
      (fun y ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega y).le) x
  · exact fun y ↦ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega y).le

/-- The frozen coarse-grained Poincare theorem, read without the paper's
leading `s^(1/q)` normalization at the fixed Holder exponent. -/
theorem scaleNormalizedNegativeBesov_le_coarsePoincareEnergy
    (hd : 2 ≤ d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q))
    (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm (originCube d m) (1 / 2 : ℝ)
        (.finite 2) u.grad ≤
      coarsePoincareNormalizationPrice *
        (paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) *
          Real.rpow (lambda (originCube d m) (1 / 2 : ℝ) (.finite 2) a)
            (-1 / 2) *
          coefficientEnergyNorm (originCube d m) a u.grad) := by
  have : NeZero d := ⟨by omega⟩
  have hzeroL2 : MemVectorL2 (openCubeSet (originCube d m))
      (fun _ ↦ (0 : Vec d)) := by
    rw [MemVectorL2, volumeMeasureOn]
    exact MemLp.zero
  have hpaper := (_root_.SubdiffusiveProcess.Section2.coarse_grained_poincare hd a haSymm
    (1 / 2 : ℝ) (by norm_num) (by norm_num) (.finite 2) (by norm_num)
    m u (fun _ ↦ (0 : Vec d)) hzeroL2 isSolenoidalOn_zero).1
  let c : ℝ := Real.rpow (1 / 2 : ℝ) (1 / 2 : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hpaperEq : paperScaleNormalizedNegativeBesovVectorNorm
      (originCube d m) (1 / 2 : ℝ) (.finite 2) u.grad =
      c * Ch03.scaleNormalizedNegativeBesovVectorNorm
        (originCube d m) (1 / 2 : ℝ) (.finite 2) u.grad := rfl
  rw [hpaperEq] at hpaper
  calc
    Ch03.scaleNormalizedNegativeBesovVectorNorm
        (originCube d m) (1 / 2 : ℝ) (.finite 2) u.grad =
        c⁻¹ * (c * Ch03.scaleNormalizedNegativeBesovVectorNorm
          (originCube d m) (1 / 2 : ℝ) (.finite 2) u.grad) := by
      field_simp
    _ ≤ c⁻¹ *
        (paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) *
          Real.rpow (lambda (originCube d m) (1 / 2 : ℝ) (.finite 2) a)
            (-1 / 2) *
          coefficientEnergyNorm (originCube d m) a u.grad) :=
      mul_le_mul_of_nonneg_left hpaper (inv_nonneg.mpr hc.le)
    _ = coarsePoincareNormalizationPrice *
        (paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) *
          Real.rpow (lambda (originCube d m) (1 / 2 : ℝ) (.finite 2) a)
            (-1 / 2) *
          coefficientEnergyNorm (originCube d m) a u.grad) := by
      rfl

/-- Fractional Poincare followed by the proved frozen Section 2 estimate and
the scalar cutoff energy identity.  The only coefficient factor left visible
is the multiscale `lambda`; its good-event bound is supplied separately by the
dimension-only `EnergyFactor` comparison. -/
theorem normalizedL2On_fluctuation_le_coarsePoincareWeightedGrad
    [NeZero d] (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℤ)
    (u : H1Function (openCubeSet (originCube d m))) :
    cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
        normalizedL2On (openCubeSet (originCube d m))
          (fun y ↦ u.toFun y -
            volumeAverage (openCubeSet (originCube d m)) u.toFun) ≤
      Section6HolderInterior.interiorFractionalPoincareConst d *
        (coarsePoincareNormalizationPrice *
          (paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) *
            Real.rpow (lambda (originCube d m) (1 / 2 : ℝ) (.finite 2)
              (aCutoffFamily M L omega)) (-1 / 2) *
            vectorNormalizedL2On (openCubeSet (originCube d m))
              (fun x ↦ Real.sqrt
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • u.grad x))) := by
  have hfrac := Section6HolderInterior.normalizedL2On_fluctuation_le_scaleNormalized
    (originCube d m) u
  have hcoarse := scaleNormalizedNegativeBesov_le_coarsePoincareEnergy hd
    (aCutoffFamily M L omega)
    (fun Q ↦ (aCutoffTriadicData M L omega).onCube Q |>.isSymmetric)
    m u
  refine hfrac.trans ?_
  have hC : 0 ≤ Section6HolderInterior.interiorFractionalPoincareConst d :=
    Section6HolderInterior.interiorFractionalPoincareConst_nonneg d
  have hmul := mul_le_mul_of_nonneg_left hcoarse hC
  rw [coefficientEnergyNorm_aCutoffFamily_eq_weightedGrad] at hmul
  exact hmul

/-- The local good-scale error gives the lower ellipticity cap needed by the
coarse Poincare leg.  This uses the all-scale `q = 2` comparison exported by
`Section6Dirichlet.EnergyFactor`; the resulting constant is dimension-only.
In particular, no pointwise/pathwise ellipticity bound is used. -/
theorem exists_localBoundaryCoarsePoincareLowerCap (d : ℕ) [NeZero d] :
    ∃ E₀ B : ℝ, 0 < E₀ ∧ 0 < B ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 2 ≤ L → ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let A := aCutoffFamily M L (translatePotentialSample y omega)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d (n + 2) z)
        sigma * (lambda Q (1 / 2 : ℝ) (.finite 2) A)⁻¹ ≤ B := by
  obtain ⟨E₀, _B₀, hE₀, _hB₀, hcaps⟩ :=
    Section6HarmonicApproximation.exists_localBoundaryEllipticityCaps d
  let B : ℝ := 1 + 2 * E₀ ^ 2 + Real.sqrt 2 * E₀
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨E₀, B, hE₀, hB, ?_⟩
  intro M s hs L m n hnL z x y omega hx hcontain hgood
  let Q := originCube d ((n : ℤ) - 2)
  let A := aCutoffFamily M L (translatePotentialSample y omega)
  let sigma := tailAverage M L (n + 2) omega (translatedCube d (n + 2) z)
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hs.1
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  have hlocal := (hcaps M s hs L m n hnL z x y omega hx hcontain hgood).1
  let E := Ch02.HomogenizationErrorOnCube Q (s / 6) .infinity (.finite 2) A
    (scalarMatrix (d := d) sigma)
  have hE0 : 0 ≤ E :=
    LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg
      Q A (scalarMatrix (d := d) sigma) (by linarith only [hs0])
  have hEle : E ≤ E₀ := by simpa only [Q, A, sigma, E] using hlocal
  have hratio :=
    Section6Dirichlet.ErrorComparison.max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul
      Q A (by linarith only [hs0] : 0 < s / 6) hsigma
  have hsq : E ^ 2 ≤ E₀ ^ 2 := pow_le_pow_left₀ hE0 hEle 2
  have henvelope : 1 + 2 * E ^ 2 + Real.sqrt 2 * E ≤ B := by
    dsimp only [B]
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith only [hsq, hEle, hsqrt]
  have hlower6 : sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ ≤ B :=
    (le_max_right _ _).trans (hratio.trans henvelope)
  have hmono : Ch02.lambdaSq Q (s / 6) (.finite 2) A ≤
      Ch02.lambdaSq Q (1 / 2 : ℝ) (.finite 2) A :=
    Ch02.lambdaSq_finite_mono Q A (by linarith only [hs0])
      (by linarith only [hs.2]) (by norm_num)
  have hinv : (Ch02.lambdaSq Q (1 / 2 : ℝ) (.finite 2) A)⁻¹ ≤
      (Ch02.lambdaSq Q (s / 6) (.finite 2) A)⁻¹ :=
    inv_anti₀ (Ch02.lambdaSq_finite_pos Q A
      (by linarith only [hs0]) (by norm_num)) hmono
  exact (mul_le_mul_of_nonneg_left hinv hsigma.le).trans hlower6

/-- The dimension-only constant in the composed fractional/coarse-Poincare
energy leg. -/
def boundaryCoarsePoincareEnergyConst (d : ℕ) [NeZero d] : ℝ :=
  1 + Section6HolderInterior.interiorFractionalPoincareConst d *
      coarsePoincareNormalizationPrice *
      paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2)

theorem boundaryCoarsePoincareEnergyConst_pos (d : ℕ) [NeZero d] :
    0 < boundaryCoarsePoincareEnergyConst d := by
  unfold boundaryCoarsePoincareEnergyConst
    Section6HolderInterior.interiorFractionalPoincareConst
    coarsePoincareNormalizationPrice paperPoincareGeometricFactor
  have hdisc : 0 < Ch02.geometricDiscount (1 / 2 : ℝ) 2 :=
    Ch02.book_geometricDiscount_pos (by norm_num)
  have hfrac := Section6HolderInterior.interiorFractionalPoincareConst_nonneg d
  have hnorm := (coarsePoincareNormalizationPrice_pos).le
  have hgeom : 0 ≤ Real.rpow (Ch02.geometricDiscount (1 / 2 : ℝ) 2) (-2⁻¹) :=
    Real.rpow_nonneg hdisc.le _
  positivity

/-- Abstract deterministic composition of the frozen coarse-Poincare row with
a normalized lower-ellipticity cap. -/
theorem sqrt_mul_normalizedL2On_fluctuation_le_weightedGrad
    [NeZero d] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℤ)
    {sigma K : ℝ} (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hcap : sigma *
      (lambda (originCube d m) (1 / 2 : ℝ) (.finite 2)
        (aCutoffFamily M L omega))⁻¹ ≤ K)
    (u : H1Function (openCubeSet (originCube d m))) :
    Real.sqrt sigma *
        (cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
          normalizedL2On (openCubeSet (originCube d m))
            (fun y ↦ u.toFun y -
              volumeAverage (openCubeSet (originCube d m)) u.toFun)) ≤
      boundaryCoarsePoincareEnergyConst d * Real.sqrt K *
        vectorNormalizedL2On (openCubeSet (originCube d m))
          (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) •
            u.grad x) := by
  let lam := lambda (originCube d m) (1 / 2 : ℝ) (.finite 2)
    (aCutoffFamily M L omega)
  let E := vectorNormalizedL2On (openCubeSet (originCube d m))
    (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) • u.grad x)
  have hbase := normalizedL2On_fluctuation_le_coarsePoincareWeightedGrad
    hd M L omega m u
  have hlam0 : 0 ≤ lam :=
    Ch02.lambdaSq_finite_nonneg (originCube d m) (aCutoffFamily M L omega)
      (by norm_num) (by norm_num)
  have hlam := Section6HarmonicApproximation.rpow_neg_half_le_of_lower_ratio_cap
    hlam0 hsigma hK (by simpa only [lam] using hcap)
  have hlam' : Real.rpow lam (-1 / 2) ≤ Real.sqrt K * Real.sqrt sigma⁻¹ := by
    convert hlam using 1
    norm_num
  have hsqrtCancel : Real.sqrt sigma * Real.sqrt sigma⁻¹ = 1 := by
    rw [Real.sqrt_inv]
    exact mul_inv_cancel₀ (Real.sqrt_pos.2 hsigma).ne'
  have hpair : Real.sqrt sigma * Real.rpow lam (-1 / 2) ≤ Real.sqrt K := by
    calc
      Real.sqrt sigma * Real.rpow lam (-1 / 2) ≤
          Real.sqrt sigma * (Real.sqrt K * Real.sqrt sigma⁻¹) :=
        mul_le_mul_of_nonneg_left hlam' (Real.sqrt_nonneg _)
      _ = Real.sqrt K * (Real.sqrt sigma * Real.sqrt sigma⁻¹) := by ring
      _ = Real.sqrt K := by rw [hsqrtCancel, mul_one]
  have hE0 : 0 ≤ E := Section6Iteration.normalizedL2On_nonneg _ _
  have hfront0 : 0 ≤ Section6HolderInterior.interiorFractionalPoincareConst d *
      coarsePoincareNormalizationPrice *
      paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) :=
    mul_nonneg
      (mul_nonneg (Section6HolderInterior.interiorFractionalPoincareConst_nonneg d)
        coarsePoincareNormalizationPrice_pos.le)
      (by
        unfold paperPoincareGeometricFactor
        exact Real.rpow_nonneg
          (Ch02.book_geometricDiscount_pos (by norm_num)).le _)
  have hfront_le : Section6HolderInterior.interiorFractionalPoincareConst d *
      coarsePoincareNormalizationPrice *
      paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) ≤
        boundaryCoarsePoincareEnergyConst d := by
    unfold boundaryCoarsePoincareEnergyConst
    linarith
  calc
    Real.sqrt sigma *
        (cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
          normalizedL2On (openCubeSet (originCube d m))
            (fun y ↦ u.toFun y -
              volumeAverage (openCubeSet (originCube d m)) u.toFun))
      ≤ Real.sqrt sigma *
          (Section6HolderInterior.interiorFractionalPoincareConst d *
            (coarsePoincareNormalizationPrice *
              (paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2) *
                Real.rpow lam (-1 / 2) * E))) :=
        mul_le_mul_of_nonneg_left (by simpa only [lam, E] using hbase)
          (Real.sqrt_nonneg _)
    _ = (Section6HolderInterior.interiorFractionalPoincareConst d *
          coarsePoincareNormalizationPrice *
          paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2)) *
        (Real.sqrt sigma * Real.rpow lam (-1 / 2)) * E := by ring
    _ ≤ (Section6HolderInterior.interiorFractionalPoincareConst d *
          coarsePoincareNormalizationPrice *
          paperPoincareGeometricFactor (1 / 2 : ℝ) (.finite 2)) *
        Real.sqrt K * E := by
      refine mul_le_mul_of_nonneg_right ?_ hE0
      exact mul_le_mul_of_nonneg_left hpair hfront0
    _ ≤ boundaryCoarsePoincareEnergyConst d * Real.sqrt K * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront_le (Real.sqrt_nonneg _)) hE0
    _ = boundaryCoarsePoincareEnergyConst d * Real.sqrt K *
        vectorNormalizedL2On (openCubeSet (originCube d m))
          (fun x ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) •
            u.grad x) := by rfl

/-- The preceding composition on the boundary comparison cube selected in
Step 6.  Its constants are dimension-only and its only stochastic hypothesis
is the manuscript good-scale event. -/
theorem exists_localBoundaryFluctuation_le_weightedGrad (d : ℕ) [NeZero d] :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, n + 2 ≤ L → ∀ z x y omega,
        x ∈ truncatedCube d m (n - 3) z →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        omega ∈ goodEvent M none (n + 2) z 1 (s / 8) →
        let Q := originCube d ((n : ℤ) - 2)
        let sigma := tailAverage M L (n + 2) omega
          (translatedCube d (n + 2) z)
        ∀ u : H1Function (openCubeSet Q),
          Real.sqrt sigma *
              (cubeBesovScaleWeight (1 : ℝ) Q *
                normalizedL2On (openCubeSet Q)
                  (fun p ↦ u.toFun p - volumeAverage (openCubeSet Q) u.toFun)) ≤
            C * Real.sqrt B *
              vectorNormalizedL2On (openCubeSet Q)
                (fun p ↦ Real.sqrt
                  (_root_.SubdiffusiveProcess.Model.aCutoff M L
                    (translatePotentialSample y omega) p) • u.grad p) := by
  obtain ⟨E₀, B, hE₀, hB, hcap⟩ :=
    exists_localBoundaryCoarsePoincareLowerCap d
  refine ⟨boundaryCoarsePoincareEnergyConst d, B,
    boundaryCoarsePoincareEnergyConst_pos d, hB, ?_⟩
  intro M s hs L m n hnL z x y omega hx hcontain hgood
  dsimp only
  intro u
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d (n + 2) z) := by
    have h := tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
    rw [Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample] at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using! h
  exact sqrt_mul_normalizedL2On_fluctuation_le_weightedGrad
    M.shellPrefix.dimension M L (translatePotentialSample y omega)
      ((n : ℤ) - 2) hsigma hB.le
      (hcap M s hs L m n hnL z x y omega hx hcontain hgood) u

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
