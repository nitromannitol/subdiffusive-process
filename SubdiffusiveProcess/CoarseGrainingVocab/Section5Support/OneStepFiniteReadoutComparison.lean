import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.AnnealedDualMeanDefect
import SubdiffusiveProcess.CoarseGrainingVocab.DeltaLogSquaredTail
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualPrefixSuffix
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
import SubdiffusiveProcess.Frozen.Section4.CoarseGrainedBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite source-block readouts

This module packages the `e.homogenize.at.scale.m` input used in the final
one-step substitution.  The normalized response controls both annealed
finite-volume quadratic forms; cutoff monotonicity then transports the
same-scale estimate to the source cutoff.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal MatrixOrder

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The expected response is exactly the sum of its annealed primal and
inverse-star quadratic legs. -/
theorem expectedJ_eq_annealed_quadratics {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k : ℕ)
    (p q : Vec d) :
    expectedJ M L k p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul
        (abar M L (Ch02.cubeDomain (originCube d (k : ℤ)))) p) +
      (1 / 2 : ℝ) * vecDot q (matVecMul
        (abarStarInv M L (Ch02.cubeDomain (originCube d (k : ℤ)))) q) -
      vecDot p q := by
  let U := Ch02.cubeDomain (originCube d (k : ℤ))
  have hpoint : ∀ omega,
      J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q =
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (randomAMatrix M L U omega) p) +
        (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) -
        vecDot p q := by
    intro omega
    let hdata := aCutoffCoeffOnData M L omega U
    have htheory := Ch02.responseSymmetricDirichletNeumannTheory
      U hdata.toCoeffOn hdata.isSymmetric
    have hsplit := htheory.response_dirichlet_neumann_split p q
    rw [htheory.dirichlet_value_by_sigma,
      htheory.neumann_value_by_sigmaStarInv] at hsplit
    have hstar : (aStarMatrix U hdata.toCoeffOn)⁻¹ =
        Ch02.sigmaStarInvCoarse U hdata.toCoeffOn := by
      rw [show aStarMatrix U hdata.toCoeffOn =
        Ch02.sigmaStarCoarse U hdata.toCoeffOn by
          exact htheory.derived_matrices.2.1]
      unfold Ch02.sigmaStarCoarse
      exact Matrix.nonsing_inv_nonsing_inv _
        (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)
    rw [← htheory.derived_matrices.1, ← hstar] at hsplit
    simpa [randomAMatrix, randomAStarMatrix, hdata] using hsplit
  have hA : Integrable (fun omega => (1 / 2 : ℝ) * vecDot p
      (matVecMul (randomAMatrix M L U omega) p)) M.P.toMeasure := by
    have hmat := integrable_randomAMatrix M L U
    unfold vecDot matVecMul
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro i _hi
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro j _hj
    exact (((hmat.eval i).eval j).mul_const (p j))
  have hB : Integrable (fun omega => (1 / 2 : ℝ) * vecDot q
      (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q)) M.P.toMeasure := by
    have hmat := integrable_randomAStarMatrix_inv M L U
    unfold vecDot matVecMul
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro i _hi
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro j _hj
    exact (((hmat.eval i).eval j).mul_const (q j))
  change (∫ omega, J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q
      ∂M.P.toMeasure) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  let A := fun omega => (1 / 2 : ℝ) * vecDot p
    (matVecMul (randomAMatrix M L U omega) p)
  let B := fun omega => (1 / 2 : ℝ) * vecDot q
    (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q)
  let D := fun _ : Sample d => vecDot p q
  change (∫ omega, ((A + B) - D) omega ∂M.P.toMeasure) = _
  calc
    _ = (∫ omega, (A + B) omega ∂M.P.toMeasure) -
        ∫ omega, D omega ∂M.P.toMeasure :=
      integral_sub (hA.add hB) (integrable_const _)
    _ = ((∫ omega, A omega ∂M.P.toMeasure) +
          ∫ omega, B omega ∂M.P.toMeasure) -
        ∫ omega, D omega ∂M.P.toMeasure := by
      exact congrArg (fun x ↦ x - ∫ omega, D omega ∂M.P.toMeasure)
        (integral_add hA hB)
    _ = _ := by
      rw [← integral_randomAMatrix_quadratic M L U p]
      rw [← integral_randomAStarMatrix_inv_quadratic M L U q]
      simp [A, B, D]

/-- An `L¹` normalized-defect bound controls every fixed expected response. -/
theorem expectedJ_le_of_normalizedDefect_lpnorm_one_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) {eps : ℝ} (heps : 0 ≤ eps)
    (hdefect : paperENNRealLpNorm M.P.toMeasure 1
      (normalizedDefect M L
        (Ch02.cubeDomain (originCube d (k : ℤ)))) ≤ ENNReal.ofReal eps) :
    expectedJ M L k ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) ≤ eps := by
  let U := Ch02.cubeDomain (originCube d (k : ℤ))
  let X : Sample d → ℝ≥0∞ := normalizedDefect M L U
  let Y : Sample d → ℝ := fun omega =>
    J U (aCutoffCoeffOnData M L omega U).toCoeffOn
      ((Real.sqrt (ahom M L))⁻¹ • e)
      (Real.sqrt (ahom M L) • e)
  have hYX : ∀ omega, ENNReal.ofReal (Y omega) ≤ X omega := by
    intro omega
    unfold X Y normalizedDefect paperScalarProbeMaxOn
    exact le_iSup (fun z : {z : Vec d // vecNormSq z = 1} =>
      ENNReal.ofReal (J U (aCutoffCoeffOnData M L omega U).toCoeffOn
        ((Real.sqrt (ahom M L))⁻¹ • (z : Vec d))
        (Real.sqrt (ahom M L) • (z : Vec d)))) ⟨e, he⟩
  have hYint : Integrable Y M.P.toMeasure := by
    simpa [Y, U] using integrable_cutoffResponseJ M L U
      ((Real.sqrt (ahom M L))⁻¹ • e)
      (Real.sqrt (ahom M L) • e)
  have hYnonneg : ∀ omega, 0 ≤ Y omega := by
    intro omega
    exact Ch02.responseJ_nonneg U _ _ _
  have hlinX : ∫⁻ omega, X omega ∂M.P.toMeasure ≤ ENNReal.ofReal eps := by
    simpa only [paperENNRealLpNorm, ENNReal.rpow_one, inv_one] using hdefect
  have hlinY : ∫⁻ omega, ENNReal.ofReal (Y omega) ∂M.P.toMeasure ≤
      ENNReal.ofReal eps :=
    (lintegral_mono hYX).trans hlinX
  have hof : ENNReal.ofReal (∫ omega, Y omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal eps := by
    rw [ofReal_integral_eq_lintegral_ofReal hYint
      (Filter.Eventually.of_forall hYnonneg)]
    exact hlinY
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hof
  rw [ENNReal.toReal_ofReal (integral_nonneg hYnonneg),
    ENNReal.toReal_ofReal heps] at hreal
  simpa only [Y, U] using hreal

/-- Scalar form of `expectedJ_eq_annealed_quadratics` under the isotropic
centered-cube readouts. -/
theorem expectedJ_eq_scalar_readouts {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) :
    expectedJ M L k ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) =
      (1 / 2 : ℝ) * (ahom M L)⁻¹ * abarScalarReadout M L k +
        (1 / 2 : ℝ) * ahom M L *
          oneStepAnnealedDualReadout M L k - 1 := by
  rw [expectedJ_eq_annealed_quadratics]
  rw [abar_eq_abarScalarReadout_smul_one M L k]
  rw [abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M L k]
  have ha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  simp only [smul_matVecMul, vecDot_smul_right, vecDot_smul_left]
  rw [show matVecMul (1 : Mat d) ((Real.sqrt (ahom M L))⁻¹ • e) =
      (Real.sqrt (ahom M L))⁻¹ • e by exact Matrix.one_mulVec _,
    show matVecMul (1 : Mat d) (Real.sqrt (ahom M L) • e) =
      Real.sqrt (ahom M L) • e by exact Matrix.one_mulVec _]
  simp only [vecDot_smul_right]
  rw [show vecDot e e = 1 by exact he]
  field_simp [(Real.sqrt_pos.2 ha).ne']
  rw [Real.sq_sqrt ha.le]
  rw [show Real.sqrt (ahom M L) ^ 4 = ahom M L ^ 2 by
    calc
      Real.sqrt (ahom M L) ^ 4 =
          (Real.sqrt (ahom M L) ^ 2) ^ 2 := by ring
      _ = ahom M L ^ 2 := by rw [Real.sq_sqrt ha.le]]
  ring

/-- A fixed-probe mean response bounds both same-cutoff finite readouts. -/
theorem sameScale_readouts_le_of_expectedJ
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L k : ℕ)
    (e : Vec d) (he : vecNormSq e = 1) {eps : ℝ}
    (hJ : expectedJ M L k ((Real.sqrt (ahom M L))⁻¹ • e)
      (Real.sqrt (ahom M L) • e) ≤ eps) :
    abarScalarReadout M L k ≤ (1 + 2 * eps) * ahom M L ∧
      oneStepAnnealedDualReadout M L k ≤
        (1 + 2 * eps) * (ahom M L)⁻¹ := by
  let a := ahom M L
  let primal := abarScalarReadout M L k
  let dual := oneStepAnnealedDualReadout M L k
  have ha : 0 < a :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L)
  have hpLower : a ≤ primal := by
    have hpLower0 : ahom M L ≤ abarScalarReadout M L k :=
      le_of_tendsto (tendsto_abarScalarReadout_ahom M L)
        (Filter.eventually_atTop.2 ⟨k, fun n hn =>
          antitone_abarScalarReadout M L hn⟩)
    exact hpLower0
  let i : Fin d := Classical.choice inferInstance
  have hdLower : a⁻¹ ≤ dual := by
    have h :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ahom_inv_le_abarStarInv_originCube_entry
        M L k i
    rw [abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M L k] at h
    simpa [dual] using h
  have hformula := expectedJ_eq_scalar_readouts M L k e he
  have hraw :
      (1 / 2 : ℝ) * a⁻¹ * primal + (1 / 2 : ℝ) * a * dual - 1 ≤ eps := by
    simpa only [a, primal, dual] using hformula.symm.trans_le hJ
  have hainv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hdualProd : 1 ≤ a * dual := by
    have h := mul_le_mul_of_nonneg_left hdLower ha.le
    nlinarith
  have hprimalProd : 1 ≤ a⁻¹ * primal := by
    have h := mul_le_mul_of_nonneg_left hpLower (inv_nonneg.mpr ha.le)
    calc
      1 = a⁻¹ * a := by field_simp
      _ ≤ a⁻¹ * primal := h
  constructor
  · have hratio : a⁻¹ * primal ≤ 1 + 2 * eps := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hratio ha.le
    dsimp only [primal, a] at hmul ⊢
    calc
      abarScalarReadout M L k = ahom M L *
          ((ahom M L)⁻¹ * abarScalarReadout M L k) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      _ ≤ ahom M L * (1 + 2 * eps) := hmul
      _ = (1 + 2 * eps) * ahom M L := by ring
  · have hratio : a * dual ≤ 1 + 2 * eps := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr ha.le)
    dsimp only [dual, a] at hmul ⊢
    calc
      oneStepAnnealedDualReadout M L k = (ahom M L)⁻¹ *
          (ahom M L * oneStepAnnealedDualReadout M L k) := by
        rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      _ ≤ (ahom M L)⁻¹ * (1 + 2 * eps) := hmul
      _ = (1 + 2 * eps) * (ahom M L)⁻¹ := by ring

/-! ## Source-cutoff comparison -/

/-- The annealed cutoff-ordering price across the literal localization
buffer is linear in the manuscript's `delta^2 |log delta|` loss. -/
theorem exp_two_tauSq_mul_oneStepLocalizationDepth_le
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hsmall : M.delta ≤ (1 : ℝ) / 264) :
    Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
        (oneStepLocalizationDepth M.delta : ℝ)) ≤
      1 + 528 * M.delta ^ 2 * |Real.log M.delta| := by
  let x := 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
    (oneStepLocalizationDepth M.delta : ℝ)
  let y := M.delta ^ 2 * |Real.log M.delta|
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyDelta : y ≤ M.delta := by
    exact delta_sq_mul_abs_log_le_self M.shellPrefix.delta_pos hdeltaOne
  have hdepthNat : oneStepLocalizationDepth M.delta ≤
      sharpStartScale M.delta := by
    exact sourceStartScale_le_sharpStartScale
      M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  have hdepth : (oneStepLocalizationDepth M.delta : ℝ) ≤
      132 * |Real.log M.delta| := by
    have hcast : (oneStepLocalizationDepth M.delta : ℝ) ≤
        (sharpStartScale M.delta : ℝ) := by exact_mod_cast hdepthNat
    exact hcast.trans (by
      have h := sharpStartScale_add_one_le
        M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
      linarith)
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ M.delta ^ 2 := by
    have hlogTwo : Real.log 2 / 2 ≤ 1 := by
      linarith [Real.log_two_lt_d9]
    exact (tauSq_le_delta_sq M).trans
      (mul_le_of_le_one_left (sq_nonneg _) hlogTwo)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg
      (mul_nonneg (by norm_num) M.G4.tauSq_pos.le) (Nat.cast_nonneg _)
  have hxy : x ≤ 264 * y := by
    dsimp only [x, y]
    calc
      2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
          (oneStepLocalizationDepth M.delta : ℝ) ≤
          2 * M.delta ^ 2 * (oneStepLocalizationDepth M.delta : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htau (by norm_num)) (Nat.cast_nonneg _)
      _ ≤ 2 * M.delta ^ 2 * (132 * |Real.log M.delta|) := by
        exact mul_le_mul_of_nonneg_left hdepth (by positivity)
      _ = 264 * (M.delta ^ 2 * |Real.log M.delta|) := by ring
  have hx1 : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    calc
      x ≤ 264 * y := hxy
      _ ≤ 264 * M.delta := mul_le_mul_of_nonneg_left hyDelta (by norm_num)
      _ ≤ 1 := by nlinarith
  have hexp := Real.abs_exp_sub_one_le hx1
  have hsub0 : 0 ≤ Real.exp x - 1 := by
    exact sub_nonneg.mpr (by simpa using Real.exp_monotone hx0)
  rw [abs_of_nonneg hsub0, abs_of_nonneg hx0] at hexp
  dsimp only [x, y] at hxy ⊢
  nlinarith

theorem oneStepLocalizationScale_lt_of_source
    {d n : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n) :
    oneStepLocalizationScale n M.delta < n := by
  have hdeltaOne : M.delta < 1 :=
    M.shellPrefix.delta_le_half.trans_lt (by norm_num)
  have hlog : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos hdeltaOne
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hratio : 0 < |Real.log M.delta / Real.log 3| := by
    exact abs_pos.mpr (div_ne_zero hlog.ne hlogThree.ne')
  have hdepthPos : 0 < oneStepLocalizationDepth M.delta := by
    rw [oneStepLocalizationDepth, oneStepSourceLogThreeCeil]
    exact Nat.mul_pos (by norm_num) (Nat.ceil_pos.mpr hratio)
  exact Nat.sub_lt_of_pos_le hdepthPos (oneStepLocalizationDepth_le hsource)

/-- Cutoff monotonicity transports the primal finite source-cell readout to
the same-scale readout at the localization cutoff. -/
theorem abarScalarReadout_source_le
    {d n : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n) :
    abarScalarReadout M n (oneStepLocalizationScale n M.delta) ≤
      abarScalarReadout M (oneStepLocalizationScale n M.delta)
        (oneStepLocalizationScale n M.delta) := by
  let k := oneStepLocalizationScale n M.delta
  let U := Ch02.cubeDomain (originCube d (k : ℤ))
  have hkn : k < n := oneStepLocalizationScale_lt_of_source M hsource
  have hmatrix :=
    (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).1 M U n k hkn |>.1
  rw [show abar M n U = abarScalarReadout M n k • (1 : Mat d) by
      simpa only [U, k] using abar_eq_abarScalarReadout_smul_one M n k,
    show abar M k U = abarScalarReadout M k k • (1 : Mat d) by
      simpa only [U, k] using abar_eq_abarScalarReadout_smul_one M k k] at hmatrix
  exact Homogenization.Book.Ch04.scalar_le_of_matLoewnerLE_smul_one hmatrix

/-- The inverse-star finite source-cell readout pays precisely the annealed
fresh-shell exponential when moved to the localization cutoff. -/
theorem oneStepAnnealedDualReadout_source_le
    {d n : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n) :
    oneStepAnnealedDualReadout M n (oneStepLocalizationScale n M.delta) ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
        (oneStepLocalizationDepth M.delta : ℝ)) *
        oneStepAnnealedDualReadout M (oneStepLocalizationScale n M.delta)
          (oneStepLocalizationScale n M.delta) := by
  let k := oneStepLocalizationScale n M.delta
  let U := Ch02.cubeDomain (originCube d (k : ℤ))
  let x := 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
    (oneStepLocalizationDepth M.delta : ℝ)
  have hkn : k < n := oneStepLocalizationScale_lt_of_source M hsource
  have hgap : n - k = oneStepLocalizationDepth M.delta := by
    have hadd := oneStepLocalizationScale_add_depth hsource
    dsimp only [k]
    omega
  have hmatrix :=
    (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).1 M U n k hkn |>.2.2.1
  rw [hgap,
    show abarStarInv M n U =
        oneStepAnnealedDualReadout M n k • (1 : Mat d) by
      simpa only [U, k] using
        abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M n k,
    show abarStarInv M k U =
        oneStepAnnealedDualReadout M k k • (1 : Mat d) by
      simpa only [U, k] using
        abarStarInv_originCube_eq_oneStepAnnealedDualReadout_smul_one M k k,
    smul_smul] at hmatrix
  have hscalar :=
    Homogenization.Book.Ch04.scalar_le_of_matLoewnerLE_smul_one hmatrix
  have hscalar' : Real.exp (-x) * oneStepAnnealedDualReadout M n k ≤
      oneStepAnnealedDualReadout M k k := by
    have hexp : Real.exp (-x) = Real.exp
        (-2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
          (oneStepLocalizationDepth M.delta : ℝ)) := by
      congr 1
      dsimp only [x]
      ring
    rw [hexp]
    exact hscalar
  have hmul := mul_le_mul_of_nonneg_left hscalar' (Real.exp_pos x).le
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  change Real.exp x * (Real.exp (-x) *
      oneStepAnnealedDualReadout M n k) ≤
    Real.exp x * oneStepAnnealedDualReadout M k k at hmul
  calc
    oneStepAnnealedDualReadout M n k =
        Real.exp x * (Real.exp (-x) *
          oneStepAnnealedDualReadout M n k) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp x * oneStepAnnealedDualReadout M k k := hmul
    _ = _ := by rfl

/-- The homogenized coefficient at the localization cutoff is controlled by
the source-cutoff coefficient with the same exponential price. -/
theorem ahom_localizationScale_le
    {d n : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n) :
    ahom M (oneStepLocalizationScale n M.delta) ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
        (oneStepLocalizationDepth M.delta : ℝ)) * ahom M n := by
  let k := oneStepLocalizationScale n M.delta
  have hkn : k < n := oneStepLocalizationScale_lt_of_source M hsource
  have hgap : n - k = oneStepLocalizationDepth M.delta := by
    have hadd := oneStepLocalizationScale_add_depth hsource
    dsimp only [k]
    omega
  have h :=
    (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 M n k hkn |>.2
  simpa only [k, hgap] using h

/-- The Section 4 headline and annealed cutoff ordering give the two finite
source-cell coefficient comparisons used in the one-step variational close. -/
theorem exists_source_readouts_le_ahom
    (d : ℕ) [NeZero d] :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 < B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ),
        M.delta ≤ delta0 →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        abarScalarReadout M n (oneStepLocalizationScale n M.delta) ≤
            (1 + B * M.delta ^ 2 * |Real.log M.delta|) * ahom M n ∧
          oneStepAnnealedDualReadout M n
              (oneStepLocalizationScale n M.delta) ≤
            (1 + B * M.delta ^ 2 * |Real.log M.delta|) * (ahom M n)⁻¹ := by
  obtain ⟨_c, C, _hc, hC, hcoarse⟩ :=
    SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)
  let A : ℝ := 4 * C * Real.log 3
  let B : ℝ := 528 + A + 528 * A
  let delta0 : ℝ := min ((1 : ℝ) / 264) C⁻¹
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨delta0, B, hdelta0, hB, ?_⟩
  intro M n hM hsource
  let k := oneStepLocalizationScale n M.delta
  let y := M.delta ^ 2 * |Real.log M.delta|
  let eps := C * Real.log 3 * M.delta ^ 2
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hlog : (1 : ℝ) / 2 ≤ |Real.log M.delta| := by
    have hlogNonpos := Real.log_nonpos M.shellPrefix.delta_pos.le hdeltaOne
    rw [abs_of_nonpos hlogNonpos]
    have hmono : Real.log M.delta ≤ Real.log ((1 : ℝ) / 2) :=
      Real.log_le_log M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    norm_num at hmono
    linarith
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyDelta : y ≤ M.delta := by
    exact delta_sq_mul_abs_log_le_self M.shellPrefix.delta_pos hdeltaOne
  have hyOne : y ≤ 1 := hyDelta.trans hdeltaOne
  have hsmall264 : M.delta ≤ (1 : ℝ) / 264 :=
    hM.trans (min_le_left _ _)
  have hsmallC : M.delta ≤ C⁻¹ := hM.trans (min_le_right _ _)
  have hCdelta : C * y ≤ 1 := by
    calc
      C * y ≤ C * M.delta := mul_le_mul_of_nonneg_left hyDelta hC.le
      _ ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left hsmallC hC.le
      _ = 1 := mul_inv_cancel₀ hC.ne'
  have hlogPos : 0 < |Real.log M.delta| :=
    lt_of_lt_of_le (by norm_num) hlog
  have hproductPos : 0 < C * M.delta ^ 2 * |Real.log M.delta| := by
    exact mul_pos (mul_pos hC (sq_pos_of_pos M.shellPrefix.delta_pos)) hlogPos
  have hxiUpper :
      1 ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    have hinv := (one_le_inv₀ hproductPos).2 (by
      simpa only [y, mul_assoc] using hCdelta)
    have hinvEq : (C * M.delta ^ 2 * |Real.log M.delta|)⁻¹ =
        C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]
      ring
    rw [← hinvEq]
    exact hinv
  have hdefect := (hcoarse M 1 (by norm_num) hxiUpper k).1
  have hdefect' : paperENNRealLpNorm M.P.toMeasure 1
      (normalizedDefect M k
        (Ch02.cubeDomain (originCube d (k : ℤ)))) ≤
      ENNReal.ofReal eps := by
    convert hdefect using 1
    norm_num [eps]
  let e : Vec d := Pi.single (0 : Fin d) 1
  have he : vecNormSq e = 1 := by
    change vecNormSq (Pi.single (0 : Fin d) 1) = 1
    rw [vecNormSq, vecDot, Finset.sum_eq_single (0 : Fin d)]
    · simp
    · intro b _hb hb
      simp [hb]
    · simp
  have hJ := expectedJ_le_of_normalizedDefect_lpnorm_one_le
    M k k e he (by dsimp [eps]; positivity) hdefect'
  have hsame := sameScale_readouts_le_of_expectedJ M k k e he hJ
  have hsameFactor : 1 + 2 * eps ≤ 1 + A * y := by
    dsimp only [eps, A, y]
    have hsq : M.delta ^ 2 ≤ 2 *
        (M.delta ^ 2 * |Real.log M.delta|) := by
      have hm := mul_le_mul_of_nonneg_left hlog (sq_nonneg M.delta)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg hC.le (Real.log_pos (show (1 : ℝ) < 3 by norm_num)).le)
    nlinarith
  have hE := exp_two_tauSq_mul_oneStepLocalizationDepth_le M hsmall264
  let E := Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
    (oneStepLocalizationDepth M.delta : ℝ))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hfactor0 : 0 ≤ 1 + 2 * eps := by dsimp [eps]; positivity
  have hfactorA0 : 0 ≤ 1 + A * y := by positivity
  have hproduct : E * (1 + A * y) ≤ 1 + B * y := by
    have hE' : E ≤ 1 + 528 * y := by
      simpa only [E, y, mul_assoc] using hE
    have hright0 : 0 ≤ 1 + 528 * y := by positivity
    calc
      E * (1 + A * y) ≤ (1 + 528 * y) * (1 + A * y) :=
        mul_le_mul_of_nonneg_right hE' hfactorA0
      _ ≤ 1 + B * y := by
        dsimp only [B]
        have hyy : y ^ 2 ≤ y := by nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hyOne)]
        have hAyy : A * y ^ 2 ≤ A * y :=
          mul_le_mul_of_nonneg_left hyy hA.le
        nlinarith
  have hcutPrimal := abarScalarReadout_source_le M hsource
  have hcutDual := oneStepAnnealedDualReadout_source_le M hsource
  have hahomLoc := ahom_localizationScale_le M hsource
  have hahomOrder :=
    (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 M n k
      (oneStepLocalizationScale_lt_of_source M hsource) |>.1
  have han : 0 < ahom M n :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M n)
  have hak : 0 < ahom M k :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M k)
  constructor
  · calc
      abarScalarReadout M n k ≤ abarScalarReadout M k k := hcutPrimal
      _ ≤ (1 + 2 * eps) * ahom M k := hsame.1
      _ ≤ (1 + A * y) * ahom M k :=
        mul_le_mul_of_nonneg_right hsameFactor hak.le
      _ ≤ (1 + A * y) * (E * ahom M n) :=
        mul_le_mul_of_nonneg_left hahomLoc hfactorA0
      _ = E * (1 + A * y) * ahom M n := by ring
      _ ≤ (1 + B * y) * ahom M n :=
        mul_le_mul_of_nonneg_right hproduct han.le
      _ = _ := by dsimp only [y]; ring
  · have hinvOrder : (ahom M k)⁻¹ ≤ (ahom M n)⁻¹ :=
      (inv_le_inv₀ hak han).2 hahomOrder
    calc
      oneStepAnnealedDualReadout M n k ≤
          E * oneStepAnnealedDualReadout M k k := hcutDual
      _ ≤ E * ((1 + 2 * eps) * (ahom M k)⁻¹) :=
        mul_le_mul_of_nonneg_left hsame.2 hE0
      _ ≤ E * ((1 + A * y) * (ahom M k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hE0
        exact mul_le_mul_of_nonneg_right hsameFactor (inv_nonneg.mpr hak.le)
      _ ≤ E * ((1 + A * y) * (ahom M n)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hE0
        exact mul_le_mul_of_nonneg_left hinvOrder hfactorA0
      _ = (E * (1 + A * y)) * (ahom M n)⁻¹ := by ring
      _ ≤ (1 + B * y) * (ahom M n)⁻¹ :=
        mul_le_mul_of_nonneg_right hproduct (inv_nonneg.mpr han.le)
      _ = _ := by dsimp only [y]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
