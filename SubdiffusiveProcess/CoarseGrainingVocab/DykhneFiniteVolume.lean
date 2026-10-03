module

public import SubdiffusiveProcess.CoarseGrainingVocab.PlanarDualitySupport
public import Homogenization.CoarseGraining.OriginCubeSymmetry
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.Ambient.CoefficientFieldHilbert
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Finite-volume planar conductivity duality

This file proves the algebraic and variational part of Dykhne duality on the
existing doubled `Mu` carrier.  The only analytic input is stated explicitly as
`PlanarHodgeExchangeOn`: a quarter turn exchanges zero-trace potential fields
and zero-normal-trace solenoidal fields.  CoarseGraining does not yet prove that
stream-function theorem on planar cubes.

There is no Algsuperdiff analogue of planar reciprocal duality.  The choice to
work first at finite volume and only then pass to annealed limits mirrors the
separation between finite-volume monotonicity and the scalar plateau in
`Algsuperdiff/Section3/Provider/Annealed/Monotonicity.lean` and
`Algsuperdiff/Section3/Provider/Base/AnnealedPlateau.lean`.
-/

/-- The quarter turn acts by `(x₂, -x₁)`. -/
theorem planarQuarterTurn_mulVec (v : Vec 2) :
    matVecMul planarQuarterTurn v = fun i => if i = 0 then v 1 else -v 0 := by
  funext i
  fin_cases i <;> simp [matVecMul, planarQuarterTurn_entries]

theorem planarQuarterTurn_mulVec_mulVec (v : Vec 2) :
    matVecMul planarQuarterTurn (matVecMul planarQuarterTurn v) = -v := by
  ext i
  fin_cases i <;> simp [planarQuarterTurn_mulVec]

theorem planarQuarterTurn_vecDot (v w : Vec 2) :
    vecDot (matVecMul planarQuarterTurn v) (matVecMul planarQuarterTurn w) = vecDot v w := by
  simp [vecDot, planarQuarterTurn_mulVec]
  ring

theorem planarQuarterTurn_transpose :
    matTranspose planarQuarterTurn = -planarQuarterTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matTranspose, planarQuarterTurn_entries]

theorem planarQuarterTurn_mul_self :
    planarQuarterTurn * planarQuarterTurn = -(1 : Mat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, planarQuarterTurn_entries]

/-- For scalar coefficients, the library's signed-permutation action is just
physical precomposition by the quarter turn. -/
theorem rotateCoeffField_planarQuarterTurn_scalarCoeffField (b : Vec 2 → ℝ) :
    rotateCoeffField planarQuarterTurn (scalarCoeffField b) =
      scalarCoeffField (fun x => b (matVecMul planarQuarterTurn x)) := by
  funext x
  simp [rotateCoeffField, scalarCoeffField,
    planarQuarterTurn_isSignedPermutation.transpose_mul_self]

private theorem signFlip_mul_swap_eq_planarQuarterTurn :
    signFlipMatrix 1 * Matrix.swap ℝ 0 1 = planarQuarterTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signFlipMatrix, planarQuarterTurn_entries, Matrix.swap]

private theorem swap_mul_signFlip_eq_planarQuarterTurn_transpose :
    Matrix.swap ℝ 0 1 * signFlipMatrix 1 = matTranspose planarQuarterTurn := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signFlipMatrix, planarQuarterTurn_entries, matTranspose, Matrix.swap]

private theorem rotateCoeffField_comp (R S : Mat 2) (a : CoeffField 2) :
    rotateCoeffField R (rotateCoeffField S a) = rotateCoeffField (S * R) a := by
  funext x
  simp only [rotateCoeffField, matVecMul_mul, Matrix.mul_assoc]
  rw [show matTranspose (S * R) = matTranspose R * matTranspose S by
    exact Matrix.transpose_mul S R]
  rw [Matrix.mul_assoc]

private theorem rotateCoeffField_swap_signFlip_scalarCoeffField (b : Vec 2 → ℝ) :
    rotateCoeffField (Matrix.swap ℝ 0 1)
        (rotateCoeffField (signFlipMatrix 1) (scalarCoeffField b)) =
      rotateCoeffField planarQuarterTurn (scalarCoeffField b) := by
  rw [rotateCoeffField_comp, signFlip_mul_swap_eq_planarQuarterTurn]

private theorem blockMatConj_swap_signFlip_eq_planarQuarterTurn
    (A : BlockMat 2) :
    blockMatConj (Matrix.swap ℝ 0 1) (blockMatConj (signFlipMatrix 1) A) =
      {
        upperLeft := matTranspose planarQuarterTurn * A.upperLeft * planarQuarterTurn
        upperRight := matTranspose planarQuarterTurn * A.upperRight * planarQuarterTurn
        lowerLeft := matTranspose planarQuarterTurn * A.lowerLeft * planarQuarterTurn
        lowerRight := matTranspose planarQuarterTurn * A.lowerRight * planarQuarterTurn
      } := by
  rcases A with ⟨A, B, C, D⟩
  simp only [blockMatConj]
  congr 1 <;>
    simp only [← Matrix.mul_assoc,
      swap_mul_signFlip_eq_planarQuarterTurn_transpose] <;>
    rw [Matrix.mul_assoc, signFlip_mul_swap_eq_planarQuarterTurn]

/-- The doubled planar duality transform on constant block vectors. -/
def planarDualBlockVec (lambda : ℝ) (P : BlockVec 2) : BlockVec 2 :=
  (lambda⁻¹ • matVecMul planarQuarterTurn P.2,
    lambda • matVecMul planarQuarterTurn P.1)

/-- The doubled planar duality transform on competitor fields. -/
def planarDualBlockState (lambda : ℝ) (X : BlockState 2) : BlockState 2 where
  potential := fun x => lambda⁻¹ • matVecMul planarQuarterTurn (X.flux x)
  flux := fun x => lambda • matVecMul planarQuarterTurn (X.potential x)

@[simp] theorem planarDualBlockState_potential (lambda : ℝ) (X : BlockState 2) (x : Vec 2) :
    (planarDualBlockState lambda X).potential x =
      lambda⁻¹ • matVecMul planarQuarterTurn (X.flux x) := rfl

@[simp] theorem planarDualBlockState_flux (lambda : ℝ) (X : BlockState 2) (x : Vec 2) :
    (planarDualBlockState lambda X).flux x =
      lambda • matVecMul planarQuarterTurn (X.potential x) := rfl

theorem planarDualBlockVec_twice {lambda : ℝ} (hlambda : lambda ≠ 0) (P : BlockVec 2) :
    planarDualBlockVec lambda (planarDualBlockVec lambda P) = -P := by
  rcases P with ⟨p, q⟩
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [planarDualBlockVec, planarQuarterTurn_mulVec, hlambda]

theorem planarDualBlockState_twice {lambda : ℝ} (hlambda : lambda ≠ 0)
    (X : BlockState 2) :
    planarDualBlockState lambda (planarDualBlockState lambda X) =
      { potential := fun x => -X.potential x
        flux := fun x => -X.flux x } := by
  apply BlockState.ext <;> funext x i <;> fin_cases i <;>
    simp [planarDualBlockState, planarQuarterTurn_mulVec, hlambda]

/-- A scalar conductivity and its reciprocal Dykhne transform. -/
def planarReciprocalScalarField (lambda : ℝ) (b : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun x => lambda ^ 2 * (b x)⁻¹

private theorem blockMatrixOfCoeff_scalarMatrix {s : ℝ} (hs : 0 < s) :
    blockMatrixOfCoeff (scalarMatrix (d := 2) s) =
      { upperLeft := scalarMatrix (d := 2) s
        upperRight := 0
        lowerLeft := 0
        lowerRight := scalarMatrix (d := 2) s⁻¹ } := by
  simpa [Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
    (Ch02.constantBlockMatrix_scalarMatrix (d := 2) hs)

/-- Pointwise energy invariance under the scalar reciprocal/block-swap transform. -/
theorem blockEnergyDensity_planarReciprocalScalarField
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x) (X : BlockState 2) (x : Vec 2) :
    blockEnergyDensity
        (fun y => scalarMatrix (planarReciprocalScalarField lambda b y))
        (planarDualBlockState lambda X) x =
      blockEnergyDensity (fun y => scalarMatrix (b y)) X x := by
  have hdual : 0 < planarReciprocalScalarField lambda b x :=
    mul_pos (sq_pos_of_pos hlambda) (inv_pos.mpr (hb x))
  rw [blockEnergyDensity, blockEnergyDensity, blockCoeffField, blockCoeffField,
    blockMatrixOfCoeff_scalarMatrix hdual, blockMatrixOfCoeff_scalarMatrix (hb x)]
  simp [BlockState.eval, planarDualBlockState, blockMatVecMul,
    matVecMul_scalarMatrix, matVecMul, blockVecDot, vecDot, planarQuarterTurn_mulVec,
    planarReciprocalScalarField]
  field_simp [hlambda.ne', (hb x).ne']
  ring

/-- The missing analytic input in the current library: in the plane, a
quarter turn exchanges zero-boundary gradients and zero-normal divergence-free
fields.  The rest of finite-volume Dykhne duality is algebraic. -/
structure PlanarHodgeExchangeOn (U : Set (Vec 2)) : Prop where
  potential_to_solenoidalZeroNormalTrace :
    ∀ {f : Vec 2 → Vec 2}, IsPotentialZeroTraceOn U f →
      IsSolenoidalZeroNormalTraceOn U
        (fun x => matVecMul planarQuarterTurn (f x))
  solenoidalZeroNormalTrace_to_potential :
    ∀ {g : Vec 2 → Vec 2}, MemVectorL2 U g →
      IsSolenoidalZeroNormalTraceOn U g →
      IsPotentialZeroTraceOn U
        (fun x => matVecMul planarQuarterTurn (g x))

private theorem setIntegral_vecDot_planarQuarterTurn_euclideanGradient_eq_zero
    {U : Set (Vec 2)} {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huCompact : HasCompactSupport u)
    (huSupport : tsupport u ⊆ U) (φ : H1Function U) :
    ∫ x in U,
        vecDot (matVecMul planarQuarterTurn (euclideanGradient u x)) (φ.grad x)
          ∂MeasureTheory.volume = 0 := by
  let du₀ : Vec 2 → ℝ := euclideanCoordDeriv 0 u
  let du₁ : Vec 2 → ℝ := euclideanCoordDeriv 1 u
  have hdu₀Smooth : ContDiff ℝ (⊤ : ℕ∞) du₀ :=
    contDiff_euclideanCoordDeriv hu 0
  have hdu₁Smooth : ContDiff ℝ (⊤ : ℕ∞) du₁ :=
    contDiff_euclideanCoordDeriv hu 1
  have hdu₀Compact : HasCompactSupport du₀ :=
    hasCompactSupport_euclideanCoordDeriv huCompact 0
  have hdu₁Compact : HasCompactSupport du₁ :=
    hasCompactSupport_euclideanCoordDeriv huCompact 1
  have hdu₀Support : tsupport du₀ ⊆ U :=
    (tsupport_euclideanCoordDeriv_subset_tsupport 0 u).trans huSupport
  have hdu₁Support : tsupport du₁ ⊆ U :=
    (tsupport_euclideanCoordDeriv_subset_tsupport 1 u).trans huSupport
  have hweak₀ := φ.hasWeakGradient 0 du₁ hdu₁Smooth hdu₁Compact hdu₁Support
  have hweak₁ := φ.hasWeakGradient 1 du₀ hdu₀Smooth hdu₀Compact hdu₀Support
  have hmixed :
      (fun x => (fderiv ℝ du₁ x) (basisVec 0)) =
        fun x => (fderiv ℝ du₀ x) (basisVec 1) := by
    funext x
    exact euclideanCoordSecondDeriv_comm hu 1 0 x
  have hpair :
      ∫ x in U, φ.grad x 0 * du₁ x ∂MeasureTheory.volume =
        ∫ x in U, φ.grad x 1 * du₀ x ∂MeasureTheory.volume := by
    have hleft :
        ∫ x in U, φ x * (fderiv ℝ du₁ x) (basisVec 0) ∂MeasureTheory.volume =
          -∫ x in U, φ.grad x 0 * du₁ x ∂MeasureTheory.volume := by
      simpa [du₁] using hweak₀
    have hright :
        ∫ x in U, φ x * (fderiv ℝ du₀ x) (basisVec 1) ∂MeasureTheory.volume =
          -∫ x in U, φ.grad x 1 * du₀ x ∂MeasureTheory.volume := by
      simpa [du₀] using hweak₁
    have hleft' :
        ∫ x in U, φ x * (fderiv ℝ du₀ x) (basisVec 1) ∂MeasureTheory.volume =
          -∫ x in U, φ.grad x 0 * du₁ x ∂MeasureTheory.volume := by
      calc
        ∫ x in U, φ x * (fderiv ℝ du₀ x) (basisVec 1) ∂MeasureTheory.volume =
            ∫ x in U, φ x * (fderiv ℝ du₁ x) (basisVec 0)
              ∂MeasureTheory.volume := by
                apply MeasureTheory.integral_congr_ae
                exact Filter.Eventually.of_forall fun x => by
                  exact congrArg (fun z : ℝ => φ x * z) (congrFun hmixed x).symm
        _ = -∫ x in U, φ.grad x 0 * du₁ x ∂MeasureTheory.volume := hleft
    linarith [hleft', hright]
  calc
    ∫ x in U,
        vecDot (matVecMul planarQuarterTurn (euclideanGradient u x)) (φ.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, (du₁ x * φ.grad x 0 - du₀ x * φ.grad x 1)
          ∂MeasureTheory.volume := by
            congr 1
            funext x
            simp [du₀, du₁, euclideanGradient, euclideanCoordDeriv,
              vecDot, planarQuarterTurn_mulVec]
            ring
    _ = 0 := by
      rw [MeasureTheory.integral_sub]
      · rw [show ∫ x in U, du₁ x * φ.grad x 0 ∂MeasureTheory.volume =
            ∫ x in U, φ.grad x 0 * du₁ x ∂MeasureTheory.volume by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun x => mul_comm _ _,
          show ∫ x in U, du₀ x * φ.grad x 1 ∂MeasureTheory.volume =
            ∫ x in U, φ.grad x 1 * du₀ x ∂MeasureTheory.volume by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun x => mul_comm _ _,
          hpair]
        ring
      · have hdu₁Mem : MemScalarL2 U du₁ := by
          exact (hdu₁Smooth.continuous.memLp_of_hasCompactSupport hdu₁Compact).restrict U
        exact hdu₁Mem.integrable_mul (φ.grad_memL2 0)
      · have hdu₀Mem : MemScalarL2 U du₀ := by
          exact (hdu₀Smooth.continuous.memLp_of_hasCompactSupport hdu₀Compact).restrict U
        exact hdu₀Mem.integrable_mul (φ.grad_memL2 1)

/-- The elementary half of the planar stream-function exchange: rotating a
zero-trace weak gradient by a quarter turn gives a divergence-free field with
zero normal trace.  The proof follows the repository's `H¹₀` smooth
approximation route and uses symmetry of classical mixed derivatives before
passing to the `L²` limit. -/
theorem IsPotentialZeroTraceOn.planarQuarterTurn_isSolenoidalZeroNormalTraceOn
    {U : Set (Vec 2)} {f : Vec 2 → Vec 2} (hf : IsPotentialZeroTraceOn U f) :
    IsSolenoidalZeroNormalTraceOn U
      (fun x => matVecMul planarQuarterTurn (f x)) := by
  rcases hf with ⟨u, rfl⟩
  intro φ
  let F : ℕ → Vec 2 → ℝ := fun n x =>
    (fderiv ℝ (u.approx n) x) (basisVec 1)
  let G : ℕ → Vec 2 → ℝ := fun n x =>
    (fderiv ℝ (u.approx n) x) (basisVec 0)
  have hFMem : ∀ n, MemScalarL2 U (F n) := by
    intro n
    exact (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.memLp_of_hasCompactSupport
        ((u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec 1))
      |>.restrict U
  have hGMem : ∀ n, MemScalarL2 U (G n) := by
    intro n
    exact (((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.memLp_of_hasCompactSupport
        ((u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec 0))
      |>.restrict U
  have hFConv : Filter.Tendsto (fun n => toScalarL2 (hFMem n)) Filter.atTop
      (nhds (toScalarL2 (u.toH1Function.grad_memL2 1))) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm hFMem (u.toH1Function.grad_memL2 1)
      (u.tendsto_approx_grad 1)
  have hGConv : Filter.Tendsto (fun n => toScalarL2 (hGMem n)) Filter.atTop
      (nhds (toScalarL2 (u.toH1Function.grad_memL2 0))) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm hGMem (u.toH1Function.grad_memL2 0)
      (u.tendsto_approx_grad 0)
  have hfirst := tendsto_integral_mul_of_tendsto_toScalarL2
    (φ.grad_memL2 0) hFMem (u.toH1Function.grad_memL2 1) hFConv
  have hsecond := tendsto_integral_mul_of_tendsto_toScalarL2
    (φ.grad_memL2 1) hGMem (u.toH1Function.grad_memL2 0) hGConv
  have hzero : ∀ n,
      ∫ x in U, φ.grad x 0 * F n x ∂MeasureTheory.volume -
          ∫ x in U, φ.grad x 1 * G n x ∂MeasureTheory.volume = 0 := by
    intro n
    have hsmooth := setIntegral_vecDot_planarQuarterTurn_euclideanGradient_eq_zero
      (u.approx_smooth n) (u.approx_hasCompactSupport n) (u.approx_support_subset n) φ
    have hsmooth' :
        ∫ x in U, (F n x * φ.grad x 0 - G n x * φ.grad x 1)
            ∂MeasureTheory.volume = 0 := by
      simpa [F, G, euclideanGradient, vecDot, planarQuarterTurn_mulVec,
        euclideanCoordDeriv, sub_eq_add_neg] using! hsmooth
    calc
      ∫ x in U, φ.grad x 0 * F n x ∂MeasureTheory.volume -
          ∫ x in U, φ.grad x 1 * G n x ∂MeasureTheory.volume =
          ∫ x in U, F n x * φ.grad x 0 ∂MeasureTheory.volume -
            ∫ x in U, G n x * φ.grad x 1 ∂MeasureTheory.volume := by
              simp_rw [mul_comm]
      _ = ∫ x in U, (F n x * φ.grad x 0 - G n x * φ.grad x 1)
            ∂MeasureTheory.volume := by
              simpa only [Pi.mul_apply, Pi.sub_apply] using
                (MeasureTheory.integral_sub
                  ((hFMem n).integrable_mul (φ.grad_memL2 0))
                  ((hGMem n).integrable_mul (φ.grad_memL2 1))).symm
      _ = 0 := hsmooth'
  have hlimit := hfirst.sub hsecond
  have htarget :
      ∫ x in U, φ.grad x 0 * u.toH1Function.grad x 1 ∂MeasureTheory.volume -
          ∫ x in U, φ.grad x 1 * u.toH1Function.grad x 0 ∂MeasureTheory.volume = 0 := by
    exact tendsto_nhds_unique (hlimit.congr' (Filter.Eventually.of_forall hzero)) tendsto_const_nhds
  calc
    ∫ x in U,
        vecDot (matVecMul planarQuarterTurn (u.toH1Function.grad x)) (φ.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, (u.toH1Function.grad x 1 * φ.grad x 0 -
          u.toH1Function.grad x 0 * φ.grad x 1) ∂MeasureTheory.volume := by
            congr 1
            funext x
            simp [vecDot, planarQuarterTurn_mulVec]
            ring
    _ = 0 := by
      rw [MeasureTheory.integral_sub]
      · simpa [mul_comm] using htarget
      · exact (u.toH1Function.grad_memL2 1).integrable_mul (φ.grad_memL2 0)
      · exact (u.toH1Function.grad_memL2 0).integrable_mul (φ.grad_memL2 1)

/-- The boundary-condition twin of the preceding weak-Jacobian identity:
quarter-turning an arbitrary `H¹` gradient is solenoidal against zero-trace
tests. -/
theorem IsPotentialOn.planarQuarterTurn_isSolenoidalOn
    {U : Set (Vec 2)} {f : Vec 2 → Vec 2} (hf : IsPotentialOn U f) :
    IsSolenoidalOn U (fun x => matVecMul planarQuarterTurn (f x)) := by
  rcases hf with ⟨u, rfl⟩
  intro φ
  let F : ℕ → Vec 2 → ℝ := fun n x =>
    (fderiv ℝ (φ.approx n) x) (basisVec 0)
  let G : ℕ → Vec 2 → ℝ := fun n x =>
    (fderiv ℝ (φ.approx n) x) (basisVec 1)
  have hFMem : ∀ n, MemScalarL2 U (F n) := by
    intro n
    exact (((φ.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.memLp_of_hasCompactSupport
        ((φ.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec 0))
      |>.restrict U
  have hGMem : ∀ n, MemScalarL2 U (G n) := by
    intro n
    exact (((φ.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.memLp_of_hasCompactSupport
        ((φ.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec 1))
      |>.restrict U
  have hFConv : Filter.Tendsto (fun n => toScalarL2 (hFMem n)) Filter.atTop
      (nhds (toScalarL2 (φ.toH1Function.grad_memL2 0))) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm hFMem (φ.toH1Function.grad_memL2 0)
      (φ.tendsto_approx_grad 0)
  have hGConv : Filter.Tendsto (fun n => toScalarL2 (hGMem n)) Filter.atTop
      (nhds (toScalarL2 (φ.toH1Function.grad_memL2 1))) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm hGMem (φ.toH1Function.grad_memL2 1)
      (φ.tendsto_approx_grad 1)
  have hfirst := tendsto_integral_mul_of_tendsto_toScalarL2
    (u.grad_memL2 1) hFMem (φ.toH1Function.grad_memL2 0) hFConv
  have hsecond := tendsto_integral_mul_of_tendsto_toScalarL2
    (u.grad_memL2 0) hGMem (φ.toH1Function.grad_memL2 1) hGConv
  have hzero : ∀ n,
      ∫ x in U, u.grad x 1 * F n x ∂MeasureTheory.volume -
          ∫ x in U, u.grad x 0 * G n x ∂MeasureTheory.volume = 0 := by
    intro n
    have hsmooth := setIntegral_vecDot_planarQuarterTurn_euclideanGradient_eq_zero
      (φ.approx_smooth n) (φ.approx_hasCompactSupport n) (φ.approx_support_subset n) u
    have hsmooth' :
        ∫ x in U, (G n x * u.grad x 0 - F n x * u.grad x 1)
            ∂MeasureTheory.volume = 0 := by
      simpa [F, G, euclideanGradient, vecDot, planarQuarterTurn_mulVec,
        euclideanCoordDeriv, sub_eq_add_neg] using! hsmooth
    have hsplit :
        ∫ x in U, G n x * u.grad x 0 ∂MeasureTheory.volume -
            ∫ x in U, F n x * u.grad x 1 ∂MeasureTheory.volume = 0 := by
      calc
        ∫ x in U, G n x * u.grad x 0 ∂MeasureTheory.volume -
            ∫ x in U, F n x * u.grad x 1 ∂MeasureTheory.volume =
            ∫ x in U, (G n x * u.grad x 0 - F n x * u.grad x 1)
              ∂MeasureTheory.volume := by
                simpa only [Pi.mul_apply, Pi.sub_apply] using
                  (MeasureTheory.integral_sub
                    ((hGMem n).integrable_mul (u.grad_memL2 0))
                    ((hFMem n).integrable_mul (u.grad_memL2 1))).symm
        _ = 0 := hsmooth'
    have hsplit' :
        ∫ x in U, u.grad x 0 * G n x ∂MeasureTheory.volume -
            ∫ x in U, u.grad x 1 * F n x ∂MeasureTheory.volume = 0 := by
      simpa [mul_comm] using hsplit
    linarith [hsplit']
  have hlimit := hfirst.sub hsecond
  have htarget :
      ∫ x in U, u.grad x 1 * φ.toH1Function.grad x 0 ∂MeasureTheory.volume -
          ∫ x in U, u.grad x 0 * φ.toH1Function.grad x 1 ∂MeasureTheory.volume = 0 := by
    exact tendsto_nhds_unique (hlimit.congr' (Filter.Eventually.of_forall hzero)) tendsto_const_nhds
  calc
    ∫ x in U,
        vecDot (matVecMul planarQuarterTurn (u.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, (u.grad x 1 * φ.toH1Function.grad x 0 -
          u.grad x 0 * φ.toH1Function.grad x 1) ∂MeasureTheory.volume := by
            congr 1
            funext x
            simp [vecDot, planarQuarterTurn_mulVec]
            ring
    _ = 0 := by
      rw [MeasureTheory.integral_sub]
      · exact htarget
      · exact (u.grad_memL2 1).integrable_mul (φ.toH1Function.grad_memL2 0)
      · exact (u.grad_memL2 0).integrable_mul (φ.toH1Function.grad_memL2 1)

/-- Weak planar Poincaré lemma without a boundary condition: every `L²`
divergence-free field on `U` has a quarter-turned `H¹` potential. -/
def PlanarStreamFunctionOn (U : Set (Vec 2)) : Prop :=
  ∀ {g : Vec 2 → Vec 2}, MemVectorL2 U g → IsSolenoidalOn U g →
    IsPotentialOn U (fun x => matVecMul planarQuarterTurn (g x))

/-- Zero-normal/zero-trace version of the weak planar Poincaré lemma. -/
def PlanarZeroNormalStreamFunctionOn (U : Set (Vec 2)) : Prop :=
  ∀ {g : Vec 2 → Vec 2}, MemVectorL2 U g →
    IsSolenoidalZeroNormalTraceOn U g →
      IsPotentialZeroTraceOn U (fun x => matVecMul planarQuarterTurn (g x))

/-- The full exchange package reduces to the genuine stream-function
converse: its opposite direction is the unconditional weak-Jacobian identity
proved above. -/
theorem planarHodgeExchangeOn_of_planarZeroNormalStreamFunctionOn
    {U : Set (Vec 2)} (hstream : PlanarZeroNormalStreamFunctionOn U) :
    PlanarHodgeExchangeOn U where
  potential_to_solenoidalZeroNormalTrace hf :=
    IsPotentialZeroTraceOn.planarQuarterTurn_isSolenoidalZeroNormalTraceOn hf
  solenoidalZeroNormalTrace_to_potential hgMem hg := hstream hgMem hg

theorem memVectorL2_planarQuarterTurn {U : Set (Vec 2)} {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) :
    MemVectorL2 U (fun x => matVecMul planarQuarterTurn (f x)) := by
  simpa using! (matContinuousLinearMap planarQuarterTurn).comp_memLp' hf

theorem isBlockMuAdmissible_planarDual
    {U : Set (Vec 2)} (hHodge : PlanarHodgeExchangeOn U)
    {lambda : ℝ} (P : BlockVec 2) {X : BlockState 2}
    (hX : IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U (planarDualBlockVec lambda P)
      (planarDualBlockState lambda X) := by
  have hpotEq :
      (fun x => (planarDualBlockState lambda X).potential x -
        (planarDualBlockVec lambda P).1) =
      fun x => lambda⁻¹ • matVecMul planarQuarterTurn (X.flux x - P.2) := by
    funext x
    simp [planarDualBlockState, planarDualBlockVec, sub_eq_add_neg,
      matVecMul_add, matVecMul_neg]
  have hfluxEq :
      (fun x => (planarDualBlockState lambda X).flux x -
        (planarDualBlockVec lambda P).2) =
      fun x => lambda • matVecMul planarQuarterTurn (X.potential x - P.1) := by
    funext x
    simp [planarDualBlockState, planarDualBlockVec, sub_eq_add_neg,
      matVecMul_add, matVecMul_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpotEq]
    exact (memVectorL2_planarQuarterTurn hX.fluxCorrection_memL2).const_smul lambda⁻¹
  · rw [hpotEq]
    exact isPotentialZeroTraceOn_smul
      (hHodge.solenoidalZeroNormalTrace_to_potential
        hX.fluxCorrection_memL2 hX.isSolenoidalZeroNormalTrace) _
  · rw [hfluxEq]
    exact (memVectorL2_planarQuarterTurn hX.potentialCorrection_memL2).const_smul lambda
  · rw [hfluxEq]
    exact isSolenoidalZeroNormalTraceOn_smul
      (hHodge.potential_to_solenoidalZeroNormalTrace hX.isPotentialZeroTrace) _

def negBlockVec {d : ℕ} (P : BlockVec d) : BlockVec d := (-P.1, -P.2)

def negBlockState {d : ℕ} (X : BlockState d) : BlockState d where
  potential := fun x => -X.potential x
  flux := fun x => -X.flux x

@[simp] theorem negBlockVec_negBlockVec {d : ℕ} (P : BlockVec d) :
    negBlockVec (negBlockVec P) = P := by
  rcases P with ⟨p, q⟩
  simp [negBlockVec]

theorem isBlockMuAdmissible_neg {d : ℕ} {U : Set (Vec d)}
    (P : BlockVec d) {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U (negBlockVec P) (negBlockState X) := by
  have hpotEq :
      (fun x => (negBlockState X).potential x - (negBlockVec P).1) =
        (-1 : ℝ) • (fun x => X.potential x - P.1) := by
    funext x i
    simp [negBlockState, negBlockVec]
    ring
  have hfluxEq :
      (fun x => (negBlockState X).flux x - (negBlockVec P).2) =
        (-1 : ℝ) • (fun x => X.flux x - P.2) := by
    funext x i
    simp [negBlockState, negBlockVec]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpotEq]
    exact hX.potentialCorrection_memL2.const_smul (-1)
  · rw [hpotEq]
    exact isPotentialZeroTraceOn_smul hX.isPotentialZeroTrace _
  · rw [hfluxEq]
    exact hX.fluxCorrection_memL2.const_smul (-1)
  · rw [hfluxEq]
    exact isSolenoidalZeroNormalTraceOn_smul hX.isSolenoidalZeroNormalTrace _

theorem blockEnergyDensity_negBlockState {d : ℕ} (a : CoeffField d)
    (X : BlockState d) (x : Vec d) :
    blockEnergyDensity a (negBlockState X) x = blockEnergyDensity a X x := by
  have heval : (negBlockState X).eval x = (-1 : ℝ) • X.eval x := by
    apply Prod.ext <;> ext i <;> simp [negBlockState, BlockState.eval]
  rw [blockEnergyDensity, heval, blockMatVecMul_smul,
    blockVecDot_smul_left, blockVecDot_smul_right]
  simp [blockEnergyDensity]

theorem planarReciprocalScalarField_twice
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x) :
    planarReciprocalScalarField lambda (planarReciprocalScalarField lambda b) = b := by
  funext x
  simp only [planarReciprocalScalarField]
  field_simp [hlambda.ne', (hb x).ne']

theorem planarDualBlockVec_twice_eq_negBlockVec {lambda : ℝ}
    (hlambda : lambda ≠ 0) (P : BlockVec 2) :
    planarDualBlockVec lambda (planarDualBlockVec lambda P) = negBlockVec P := by
  rw [planarDualBlockVec_twice hlambda]
  rcases P with ⟨p, q⟩
  rfl

theorem planarDualBlockState_twice_eq_negBlockState {lambda : ℝ}
    (hlambda : lambda ≠ 0) (X : BlockState 2) :
    planarDualBlockState lambda (planarDualBlockState lambda X) = negBlockState X := by
  rw [planarDualBlockState_twice hlambda]
  rfl

theorem blockEnergyDensity_planarReciprocalScalarField_inverse
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x) (X : BlockState 2) (x : Vec 2) :
    blockEnergyDensity (fun y => scalarMatrix (b y))
        (negBlockState (planarDualBlockState lambda X)) x =
      blockEnergyDensity
        (fun y => scalarMatrix (planarReciprocalScalarField lambda b y)) X x := by
  have hdual : ∀ y, 0 < planarReciprocalScalarField lambda b y := fun y =>
    mul_pos (sq_pos_of_pos hlambda) (inv_pos.mpr (hb y))
  have h := blockEnergyDensity_planarReciprocalScalarField
    hlambda hdual X x
  rw [planarReciprocalScalarField_twice hlambda hb] at h
  rw [blockEnergyDensity_negBlockState]
  exact h

theorem muValueSet_planarReciprocalScalarField
    {U : Set (Vec 2)} (hHodge : PlanarHodgeExchangeOn U)
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x) (P : BlockVec 2) :
    muValueSet U (planarDualBlockVec lambda P)
        (fun x => scalarMatrix (planarReciprocalScalarField lambda b x)) =
      muValueSet U P (fun x => scalarMatrix (b x)) := by
  ext value
  constructor
  · rintro ⟨X, hX, hvalue⟩
    refine ⟨negBlockState (planarDualBlockState lambda X), ?_, ?_⟩
    · have htwice := isBlockMuAdmissible_planarDual (lambda := lambda) hHodge
        (planarDualBlockVec lambda P) hX
      rw [planarDualBlockVec_twice_eq_negBlockVec hlambda.ne'] at htwice
      simpa using isBlockMuAdmissible_neg (negBlockVec P) htwice
    · calc
        value = volumeAverage U
            (blockEnergyDensity
              (fun x => scalarMatrix (planarReciprocalScalarField lambda b x)) X) := hvalue
        _ = volumeAverage U
            (blockEnergyDensity (fun x => scalarMatrix (b x))
              (negBlockState (planarDualBlockState lambda X))) := by
              congr 1
              funext x
              exact (blockEnergyDensity_planarReciprocalScalarField_inverse
                hlambda hb X x).symm
  · rintro ⟨X, hX, hvalue⟩
    refine ⟨planarDualBlockState lambda X,
      isBlockMuAdmissible_planarDual (lambda := lambda) hHodge P hX, ?_⟩
    calc
      value = volumeAverage U (blockEnergyDensity (fun x => scalarMatrix (b x)) X) := hvalue
      _ = volumeAverage U
          (blockEnergyDensity
            (fun x => scalarMatrix (planarReciprocalScalarField lambda b x))
            (planarDualBlockState lambda X)) := by
            congr 1
            funext x
            exact (blockEnergyDensity_planarReciprocalScalarField hlambda hb X x).symm

theorem Mu_planarReciprocalScalarField
    {U : Set (Vec 2)} (hHodge : PlanarHodgeExchangeOn U)
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x) (P : BlockVec 2) :
    Mu U (planarDualBlockVec lambda P)
        (fun x => scalarMatrix (planarReciprocalScalarField lambda b x)) =
      Mu U P (fun x => scalarMatrix (b x)) := by
  simp only [Mu]
  rw [muValueSet_planarReciprocalScalarField hHodge hlambda hb P]

/-- The block-matrix congruence induced by planar scalar duality. -/
noncomputable def planarDualBlockMatrix (lambda : ℝ) (A : BlockMat 2) : BlockMat 2 where
  upperLeft := lambda ^ 2 •
    (matTranspose planarQuarterTurn * A.lowerRight * planarQuarterTurn)
  upperRight := matTranspose planarQuarterTurn * A.lowerLeft * planarQuarterTurn
  lowerLeft := matTranspose planarQuarterTurn * A.upperRight * planarQuarterTurn
  lowerRight := (lambda ^ 2)⁻¹ •
    (matTranspose planarQuarterTurn * A.upperLeft * planarQuarterTurn)

theorem planarDualBlockVec_neg (lambda : ℝ) (P : BlockVec 2) :
    planarDualBlockVec lambda (negBlockVec P) = negBlockVec (planarDualBlockVec lambda P) := by
  rcases P with ⟨p, q⟩
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [planarDualBlockVec, negBlockVec, planarQuarterTurn_mulVec]

theorem planarDualBlockVec_neg_planarDualBlockVec {lambda : ℝ}
    (hlambda : lambda ≠ 0) (P : BlockVec 2) :
    planarDualBlockVec lambda (negBlockVec (planarDualBlockVec lambda P)) = P := by
  rw [planarDualBlockVec_neg, planarDualBlockVec_twice_eq_negBlockVec hlambda]
  exact negBlockVec_negBlockVec P

theorem blockQuadratic_planarDualBlockMatrix {lambda : ℝ}
    (hlambda : lambda ≠ 0) (A : BlockMat 2) (P : BlockVec 2) :
    blockVecDot (planarDualBlockVec lambda P)
        (blockMatVecMul (planarDualBlockMatrix lambda A)
          (planarDualBlockVec lambda P)) =
      blockVecDot P (blockMatVecMul A P) := by
  rcases P with ⟨p, q⟩
  simp [planarDualBlockVec, planarDualBlockMatrix, blockVecDot, blockMatVecMul,
    matVecMul, vecDot, planarQuarterTurn, matTranspose, Matrix.mul_apply]
  field_simp [hlambda]
  ring

theorem planarDualBlockMatrix_isSymmetric {lambda : ℝ} {A : BlockMat 2}
    (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (planarDualBlockMatrix lambda A) := by
  have hB : matTranspose A.upperLeft = A.upperLeft := by
    ext i j
    simpa [matTranspose, blockMatEntry] using! hA (Sum.inl j) (Sum.inl i)
  have hD : matTranspose A.lowerRight = A.lowerRight := by
    ext i j
    simpa [matTranspose, blockMatEntry] using! hA (Sum.inr j) (Sum.inr i)
  have hUR : matTranspose A.upperRight = A.lowerLeft := by
    ext i j
    simpa [matTranspose, blockMatEntry] using! hA (Sum.inl j) (Sum.inr i)
  have hLL : matTranspose A.lowerLeft = A.upperRight := by
    ext i j
    simpa [matTranspose, blockMatEntry] using! hA (Sum.inr j) (Sum.inl i)
  have hul : matTranspose (planarDualBlockMatrix lambda A).upperLeft =
      (planarDualBlockMatrix lambda A).upperLeft := by
    simp only [planarDualBlockMatrix]
    simp only [matTranspose] at hD ⊢
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp [hD, Matrix.mul_assoc]
  have hlr : matTranspose (planarDualBlockMatrix lambda A).lowerRight =
      (planarDualBlockMatrix lambda A).lowerRight := by
    simp only [planarDualBlockMatrix]
    simp only [matTranspose] at hB ⊢
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp [hB, Matrix.mul_assoc]
  have hur : matTranspose (planarDualBlockMatrix lambda A).upperRight =
      (planarDualBlockMatrix lambda A).lowerLeft := by
    simp only [planarDualBlockMatrix]
    simp only [matTranspose] at hLL ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp [hLL, Matrix.mul_assoc]
  have hll : matTranspose (planarDualBlockMatrix lambda A).lowerLeft =
      (planarDualBlockMatrix lambda A).upperRight := by
    simp only [planarDualBlockMatrix]
    simp only [matTranspose] at hUR ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp [hUR, Matrix.mul_assoc]
  intro alpha beta
  cases alpha with
  | inl i =>
      cases beta with
      | inl j =>
          have h := congrArg (fun M : Mat 2 => M j i) hul
          simpa [blockMatEntry, matTranspose] using h
      | inr j =>
          have h := congrArg (fun M : Mat 2 => M j i) hur
          simpa [blockMatEntry, matTranspose] using h
  | inr i =>
      cases beta with
      | inl j =>
          have h := congrArg (fun M : Mat 2 => M j i) hll
          simpa [blockMatEntry, matTranspose] using h
      | inr j =>
          have h := congrArg (fun M : Mat 2 => M j i) hlr
          simpa [blockMatEntry, matTranspose] using h

/-- Conditional finite-volume Dykhne duality.  Once the planar stream-function
exchange is supplied on `U`, the canonical coarse block matrix of
`lambda² / b` is the explicit congruence swapping the primal and dual blocks. -/
theorem IsCoarseBlockMatrix.planarReciprocalScalar
    {U : Set (Vec 2)} (hHodge : PlanarHodgeExchangeOn U)
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x) {A : BlockMat 2}
    (hA : IsCoarseBlockMatrix U (fun x => scalarMatrix (b x)) A) :
    IsCoarseBlockMatrix U
      (fun x => scalarMatrix (planarReciprocalScalarField lambda b x))
      (planarDualBlockMatrix lambda A) := by
  refine ⟨planarDualBlockMatrix_isSymmetric hA.1, ?_⟩
  intro X
  let P : BlockVec 2 := negBlockVec (planarDualBlockVec lambda X)
  have hTP : planarDualBlockVec lambda P = X := by
    exact planarDualBlockVec_neg_planarDualBlockVec hlambda.ne' X
  calc
    Mu U X (fun x => scalarMatrix (planarReciprocalScalarField lambda b x)) =
        Mu U (planarDualBlockVec lambda P)
          (fun x => scalarMatrix (planarReciprocalScalarField lambda b x)) := by rw [hTP]
    _ = Mu U P (fun x => scalarMatrix (b x)) :=
      Mu_planarReciprocalScalarField hHodge hlambda hb P
    _ = (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul A P) := hA.2 P
    _ = (1 / 2 : ℝ) * blockVecDot (planarDualBlockVec lambda P)
        (blockMatVecMul (planarDualBlockMatrix lambda A)
          (planarDualBlockVec lambda P)) := by
          rw [blockQuadratic_planarDualBlockMatrix hlambda.ne' A P]
    _ = (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul (planarDualBlockMatrix lambda A) X) := by rw [hTP]

theorem coarseBlockMatrix_planarReciprocalScalarField_of_isCoarseBlockMatrix
    {U : Set (Vec 2)} (hHodge : PlanarHodgeExchangeOn U)
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x)
    (hA : IsCoarseBlockMatrix U (fun x => scalarMatrix (b x))
      (coarseBlockMatrix U (fun x => scalarMatrix (b x)))) :
    coarseBlockMatrix U
        (fun x => scalarMatrix (planarReciprocalScalarField lambda b x)) =
      planarDualBlockMatrix lambda
        (coarseBlockMatrix U (fun x => scalarMatrix (b x))) := by
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix
    (IsCoarseBlockMatrix.planarReciprocalScalar hHodge hlambda hb hA)).symm

private theorem isCoarseBlockMatrix_ch02_scalarCoeffOnData
    {U : Ch02.Domain 2} {b : Vec 2 → ℝ} (h : ScalarCoeffOnData U b) :
    IsCoarseBlockMatrix (U : Set (Vec 2)) (scalarCoeffField b)
      (Ch02.coarseBlockMatrix U h.toCoeffOn) := by
  refine ⟨Ch02.isSymmetricBlockMat_coarseBlockMatrix U h.toCoeffOn, ?_⟩
  intro P
  calc
    Mu (U : Set (Vec 2)) P (scalarCoeffField b) =
        Ch02.doubledMu U h.toCoeffOn P :=
      (Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U h.toCoeffOn P).symm
    _ = (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (Ch02.coarseBlockMatrix U h.toCoeffOn) P) :=
      (Ch02.doubledMuTheory U h.toCoeffOn).doubledMu_eq_coarseBlockMatrix P

private theorem ch02_coarseBlockMatrix_planarQuarterTurn_originCube
    {n : ℤ} {b : Vec 2 → ℝ}
    (h : ScalarCoeffOnData (Ch02.cubeDomain (originCube 2 n)) b)
    (hrot : ScalarCoeffOnData (Ch02.cubeDomain (originCube 2 n))
      (fun x => b (matVecMul planarQuarterTurn x))) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube 2 n)) hrot.toCoeffOn =
      {
        upperLeft := matTranspose planarQuarterTurn *
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn).upperLeft *
          planarQuarterTurn
        upperRight := matTranspose planarQuarterTurn *
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn).upperRight *
          planarQuarterTurn
        lowerLeft := matTranspose planarQuarterTurn *
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn).lowerLeft *
          planarQuarterTurn
        lowerRight := matTranspose planarQuarterTurn *
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn).lowerRight *
          planarQuarterTurn
      } := by
  let U : Set (Vec 2) := openCubeSet (originCube 2 n)
  let A := Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn
  have hA : IsCoarseBlockMatrix U (scalarCoeffField b) A :=
    isCoarseBlockMatrix_ch02_scalarCoeffOnData h
  have hflip := IsCoarseBlockMatrix.signFlip_openCubeSet_originCube hA (1 : Fin 2)
  have hswap := IsCoarseBlockMatrix.swap_openCubeSet_originCube hflip (0 : Fin 2) (1 : Fin 2)
  have hfield :
      rotateCoeffField (Matrix.swap ℝ 0 1)
          (rotateCoeffField (signFlipMatrix 1) (scalarCoeffField b)) =
        scalarCoeffField (fun x => b (matVecMul planarQuarterTurn x)) := by
    rw [rotateCoeffField_swap_signFlip_scalarCoeffField,
      rotateCoeffField_planarQuarterTurn_scalarCoeffField]
  have hmatrix :
      blockMatConj (Matrix.swap ℝ 0 1) (blockMatConj (signFlipMatrix 1) A) =
        {
          upperLeft := matTranspose planarQuarterTurn * A.upperLeft * planarQuarterTurn
          upperRight := matTranspose planarQuarterTurn * A.upperRight * planarQuarterTurn
          lowerLeft := matTranspose planarQuarterTurn * A.lowerLeft * planarQuarterTurn
          lowerRight := matTranspose planarQuarterTurn * A.lowerRight * planarQuarterTurn
        } := blockMatConj_swap_signFlip_eq_planarQuarterTurn A
  have htransport : IsCoarseBlockMatrix U
      (scalarCoeffField (fun x => b (matVecMul planarQuarterTurn x)))
      {
        upperLeft := matTranspose planarQuarterTurn * A.upperLeft * planarQuarterTurn
        upperRight := matTranspose planarQuarterTurn * A.upperRight * planarQuarterTurn
        lowerLeft := matTranspose planarQuarterTurn * A.lowerLeft * planarQuarterTurn
        lowerRight := matTranspose planarQuarterTurn * A.lowerRight * planarQuarterTurn
      } := by
    rw [← hfield, ← hmatrix]
    exact hswap
  have hcanonical := isCoarseBlockMatrix_ch02_scalarCoeffOnData hrot
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcanonical).trans
    (eq_coarseBlockMatrix_of_isCoarseBlockMatrix htransport).symm

/-- Quarter-turn covariance of the inverse starred matrix on a centered cube. -/
theorem aStarMatrix_inv_planarQuarterTurn_originCube
    {n : ℤ} {b : Vec 2 → ℝ}
    (h : ScalarCoeffOnData (Ch02.cubeDomain (originCube 2 n)) b)
    (hrot : ScalarCoeffOnData (Ch02.cubeDomain (originCube 2 n))
      (fun x => b (matVecMul planarQuarterTurn x))) :
    (aStarMatrix (Ch02.cubeDomain (originCube 2 n)) hrot.toCoeffOn)⁻¹ =
      matTranspose planarQuarterTurn *
        (aStarMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn)⁻¹ *
        planarQuarterTurn := by
  have hfull := congrArg BlockMat.lowerRight
    (ch02_coarseBlockMatrix_planarQuarterTurn_originCube h hrot)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn h.isSymmetric
  have hRotTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain (originCube 2 n)) hrot.toCoeffOn hrot.isSymmetric
  have hInv :
      (Ch02.aStarCoarse (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn)⁻¹ =
        Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn := by
    rw [hTheory.derived_matrices.2.1, Ch02.sigmaStarCoarse]
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn)
  have hRotInv :
      (Ch02.aStarCoarse (Ch02.cubeDomain (originCube 2 n)) hrot.toCoeffOn)⁻¹ =
        Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube 2 n)) hrot.toCoeffOn := by
    rw [hRotTheory.derived_matrices.2.1, Ch02.sigmaStarCoarse]
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse
        (Ch02.cubeDomain (originCube 2 n)) hrot.toCoeffOn)
  simpa only [Ch02.coarseBlockMatrix_lowerRight, hInv, hRotInv] using hfull

theorem aux_dedup_d223_planarQuarterTurn_double_conjugation (A : Mat 2) :
    matTranspose planarQuarterTurn *
        (matTranspose planarQuarterTurn * A * planarQuarterTurn) *
      planarQuarterTurn = A := by
  rw [planarQuarterTurn_transpose]
  simp only [neg_mul, mul_neg, neg_neg]
  simp only [← Matrix.mul_assoc, planarQuarterTurn_mul_self]
  rw [Matrix.mul_assoc, planarQuarterTurn_mul_self]
  simp

private theorem planarQuarterTurn_double_conjugation (A : Mat 2) :
    matTranspose planarQuarterTurn *
        (matTranspose planarQuarterTurn * A * planarQuarterTurn) *
      planarQuarterTurn = A := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d223_planarQuarterTurn_double_conjugation (A := A)

private noncomputable def planarTruncatedRotatedCoeffOnData
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) (N : ℝ)
    (hN : 1 ≤ N) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2)
    (U : Ch02.Domain 2) :
    ScalarCoeffOnData U
      (fun x => planarTruncatedCutoff M m N omega
        (matVecMul planarQuarterTurn x)) where
  lam := planarLambda M m * N⁻¹
  Lam := planarLambda M m * N
  lam_pos := mul_pos (planarLambda_pos M m)
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hN))
  lam_le_Lam := mul_le_mul_of_nonneg_left
    (((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hN)).mpr hN).trans hN)
    (planarLambda_pos M m).le
  aeStronglyMeasurable := by
    intro i j
    have hcont : Continuous (fun x : Vec 2 =>
        scalarMatrix (d := 2)
          (planarTruncatedCutoff M m N omega (matVecMul planarQuarterTurn x))) :=
      ((continuous_planarTruncatedCutoff M m N omega).comp
        (matContinuousLinearMap planarQuarterTurn).continuous).smul continuous_const
    have hentry : Continuous (fun x : Vec 2 =>
        scalarMatrix (d := 2)
          (planarTruncatedCutoff M m N omega (matVecMul planarQuarterTurn x)) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hcont)
    have hmeas : AEStronglyMeasurable
        (fun x : Vec 2 => scalarMatrix (d := 2)
          (planarTruncatedCutoff M m N omega (matVecMul planarQuarterTurn x)) i j)
        (volumeMeasureOn (U : Set (Vec 2))) :=
      hentry.aestronglyMeasurable
    have hmem : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec 2)), x ∈ (U : Set (Vec 2)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    refine hmeas.congr ?_
    filter_upwards [hmem] with x hx
    simp only [scalarCoeffField, restrictCoeffField_apply_of_mem hx]
  aeBounds := Filter.Eventually.of_forall fun x =>
    ⟨planarTruncatedCutoff_lower M m hN omega (matVecMul planarQuarterTurn x),
      planarTruncatedCutoff_upper M m N omega (matVecMul planarQuarterTurn x)⟩

/-- Exact finite-volume block duality on the public Chapter 2 carrier,
conditional only on the planar stream-function exchange for the domain. -/
theorem ch02_coarseBlockMatrix_planarReciprocal
    {U : Ch02.Domain 2} (hHodge : PlanarHodgeExchangeOn (U : Set (Vec 2)))
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x)
    (h : ScalarCoeffOnData U b)
    (hdual : ScalarCoeffOnData U (planarReciprocalScalarField lambda b)) :
    Ch02.coarseBlockMatrix U hdual.toCoeffOn =
      planarDualBlockMatrix lambda (Ch02.coarseBlockMatrix U h.toCoeffOn) := by
  have hsource := isCoarseBlockMatrix_ch02_scalarCoeffOnData h
  have hfromSource := IsCoarseBlockMatrix.planarReciprocalScalar
    hHodge hlambda hb hsource
  have hcanonical := isCoarseBlockMatrix_ch02_scalarCoeffOnData hdual
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcanonical).trans
    (eq_coarseBlockMatrix_of_isCoarseBlockMatrix hfromSource).symm

/-- Primal/dual matrix form of finite-volume Dykhne duality.  The reciprocal
coefficient's Dirichlet coarse matrix is the rotated inverse of the original
coefficient's Neumann coarse matrix, with the exact factor `lambda²`. -/
theorem aMatrix_planarReciprocal_eq_rotated_aStarMatrix_inv
    {U : Ch02.Domain 2} (hHodge : PlanarHodgeExchangeOn (U : Set (Vec 2)))
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x)
    (h : ScalarCoeffOnData U b)
    (hdual : ScalarCoeffOnData U (planarReciprocalScalarField lambda b)) :
    aMatrix U hdual.toCoeffOn =
      lambda ^ 2 •
        (matTranspose planarQuarterTurn * (aStarMatrix U h.toCoeffOn)⁻¹ *
          planarQuarterTurn) := by
  have hfull := congrArg BlockMat.upperLeft
    (ch02_coarseBlockMatrix_planarReciprocal hHodge hlambda hb h hdual)
  have hSourceTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U h.toCoeffOn h.isSymmetric
  have hDualTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdual.toCoeffOn hdual.isSymmetric
  have hbDual : Ch02.bCoarse U hdual.toCoeffOn = Ch02.aCoarse U hdual.toCoeffOn := by
    calc
      Ch02.bCoarse U hdual.toCoeffOn = Ch02.sigmaCoarse U hdual.toCoeffOn :=
        hDualTheory.derived_matrices.2.2
      _ = Ch02.aCoarse U hdual.toCoeffOn := hDualTheory.derived_matrices.1.symm
  have hstarInv :
      (Ch02.aStarCoarse U h.toCoeffOn)⁻¹ = Ch02.sigmaStarInvCoarse U h.toCoeffOn := by
    rw [hSourceTheory.derived_matrices.2.1, Ch02.sigmaStarCoarse]
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U h.toCoeffOn)
  simpa only [Ch02.coarseBlockMatrix_upperLeft, planarDualBlockMatrix,
    hbDual, hstarInv, Ch02.sigmaStarInvCoarse, aMatrix] using! hfull

/-- Centered-cube specialization in which the full Hodge premise has been
reduced to the genuine zero-normal stream-function converse. -/
theorem aMatrix_planarReciprocal_originCube_of_planarZeroNormalStreamFunctionOn
    (n : ℤ)
    (hstream : PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)))
    {lambda : ℝ} (hlambda : 0 < lambda) {b : Vec 2 → ℝ}
    (hb : ∀ x, 0 < b x)
    (h : ScalarCoeffOnData (Ch02.cubeDomain (originCube 2 n)) b)
    (hdual : ScalarCoeffOnData (Ch02.cubeDomain (originCube 2 n))
      (planarReciprocalScalarField lambda b)) :
    aMatrix (Ch02.cubeDomain (originCube 2 n)) hdual.toCoeffOn =
      lambda ^ 2 •
        (matTranspose planarQuarterTurn *
          (aStarMatrix (Ch02.cubeDomain (originCube 2 n)) h.toCoeffOn)⁻¹ *
          planarQuarterTurn) := by
  exact aMatrix_planarReciprocal_eq_rotated_aStarMatrix_inv
    (planarHodgeExchangeOn_of_planarZeroNormalStreamFunctionOn hstream)
    hlambda hb h hdual

/-- Inverse starred finite-volume matrix for the truncated planar field. -/
noncomputable def planarTruncatedRandomAStarInvMatrix
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) (N : ℝ)
    (hN : 1 ≤ N) (U : Ch02.Domain 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2) : Mat 2 :=
  (aStarMatrix U (planarTruncatedCoeffOnData M m N hN omega U).toCoeffOn)⁻¹

/-- Annealed inverse starred finite-volume matrix for the truncated field. -/
noncomputable def planarTruncatedAbarStarInv
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) (N : ℝ)
    (hN : 1 ≤ N) (U : Ch02.Domain 2) : Mat 2 :=
  ∫ omega, planarTruncatedRandomAStarInvMatrix M m N hN U omega
    ∂M.P.toMeasure

/-- Samplewise finite-volume identity for the self-dual truncated GMC field,
conditional only on the weak zero-normal stream-function theorem.  The two
quarter-turn conjugations cancel exactly. -/
theorem planarTruncatedRandomAMatrix_planarDualPotentialSample_of_streamFunction
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (n : ℤ)
    (hstream : PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)))
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2) :
    planarTruncatedRandomAMatrix M m N hN
        (Ch02.cubeDomain (originCube 2 n))
        (planarDualPotentialSample planarQuarterTurn
          planarQuarterTurn_isSignedPermutation omega) =
      planarLambda M m ^ 2 •
        planarTruncatedRandomAStarInvMatrix M m N hN
          (Ch02.cubeDomain (originCube 2 n)) omega := by
  let U := Ch02.cubeDomain (originCube 2 n)
  let T := planarDualPotentialSample planarQuarterTurn
    planarQuarterTurn_isSignedPermutation
  let b : Vec 2 → ℝ := planarTruncatedCutoff M m N omega
  let bRot : Vec 2 → ℝ := fun x => b (matVecMul planarQuarterTurn x)
  let hBase : ScalarCoeffOnData U b := planarTruncatedCoeffOnData M m N hN omega U
  let hRot : ScalarCoeffOnData U bRot :=
    planarTruncatedRotatedCoeffOnData M m N hN omega U
  let hSampleDual : ScalarCoeffOnData U (planarTruncatedCutoff M m N (T omega)) :=
    planarTruncatedCoeffOnData M m N hN (T omega) U
  have hdualEq :
      planarTruncatedCutoff M m N (T omega) =
        planarReciprocalScalarField (planarLambda M m) bRot := by
    funext x
    exact planarTruncatedCutoff_planarDualPotentialSample M m hN
      planarQuarterTurn planarQuarterTurn_isSignedPermutation omega x
  let hDual : ScalarCoeffOnData U
      (planarReciprocalScalarField (planarLambda M m) bRot) := hdualEq ▸ hSampleDual
  have hdet := aMatrix_planarReciprocal_originCube_of_planarZeroNormalStreamFunctionOn
    n hstream (planarLambda_pos M m)
    (fun x => planarTruncatedCutoff_pos M m hN omega
      (matVecMul planarQuarterTurn x)) hRot hDual
  have hcov := aStarMatrix_inv_planarQuarterTurn_originCube hBase hRot
  change aMatrix U hSampleDual.toCoeffOn =
    planarLambda M m ^ 2 • (aStarMatrix U hBase.toCoeffOn)⁻¹
  have hleft : aMatrix U hSampleDual.toCoeffOn = aMatrix U hDual.toCoeffOn := by
    apply Ch02.aCoarse_eq_ofAEEq
    filter_upwards with x
    ext i j
    change scalarMatrix (planarTruncatedCutoff M m N (T omega) x) i j =
      scalarMatrix (planarReciprocalScalarField (planarLambda M m) bRot x) i j
    rw [congrFun hdualEq x]
  rw [hleft, hdet, hcov, planarQuarterTurn_double_conjugation]

private def matrixConjugationLinearMap (R : Mat 2) : Mat 2 →ₗ[ℝ] Mat 2 where
  toFun A := matTranspose R * A * R
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp

private noncomputable def matrixConjugationCLM (R : Mat 2) : Mat 2 →L[ℝ] Mat 2 :=
  LinearMap.toContinuousLinearMap (matrixConjugationLinearMap R)

@[simp] private theorem matrixConjugationCLM_apply (R A : Mat 2) :
    matrixConjugationCLM R A = matTranspose R * A * R :=
  rfl

/-- Law-transport assembly for the annealed finite-volume Dykhne identity.
The hypotheses deliberately expose the two remaining analytic obligations:
measurability/integrability of the truncated coarse observables and the
pointwise rotated reciprocal identity. -/
theorem planarTruncatedAbar_eq_rotated_planarTruncatedAbarStarInv_of_pointwise
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (n : ℤ)
    (hA : Integrable
      (planarTruncatedRandomAMatrix M m N hN
        (Ch02.cubeDomain (originCube 2 n))) M.P.toMeasure)
    (hStar : Integrable
      (planarTruncatedRandomAStarInvMatrix M m N hN
        (Ch02.cubeDomain (originCube 2 n))) M.P.toMeasure)
    (hpoint : ∀ omega,
      planarTruncatedRandomAMatrix M m N hN
          (Ch02.cubeDomain (originCube 2 n))
          (planarDualPotentialSample planarQuarterTurn
            planarQuarterTurn_isSignedPermutation omega) =
        planarLambda M m ^ 2 •
          (matTranspose planarQuarterTurn *
            planarTruncatedRandomAStarInvMatrix M m N hN
              (Ch02.cubeDomain (originCube 2 n)) omega *
            planarQuarterTurn)) :
    planarTruncatedAbar M m N hN (Ch02.cubeDomain (originCube 2 n)) =
      planarLambda M m ^ 2 •
        (matTranspose planarQuarterTurn *
          planarTruncatedAbarStarInv M m N hN
            (Ch02.cubeDomain (originCube 2 n)) *
          planarQuarterTurn) := by
  let T : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 :=
    planarDualPotentialSample planarQuarterTurn planarQuarterTurn_isSignedPermutation
  let A : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 → Mat 2 :=
    planarTruncatedRandomAMatrix M m N hN (Ch02.cubeDomain (originCube 2 n))
  let B : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 → Mat 2 :=
    planarTruncatedRandomAStarInvMatrix M m N hN (Ch02.cubeDomain (originCube 2 n))
  have hinvariant : ∫ omega, A (T omega) ∂M.P.toMeasure =
      ∫ omega, A omega ∂M.P.toMeasure :=
    integral_comp_eq_of_map_eq (E := Fin 2 → Fin 2 → ℝ)
      (measurable_planarDualPotentialSample planarQuarterTurn
        planarQuarterTurn_isSignedPermutation)
      (potentialSequenceLaw_planarDual M planarQuarterTurn
        planarQuarterTurn_isSignedPermutation) A hA.aestronglyMeasurable
  let C : Mat 2 →L[ℝ] Mat 2 := matrixConjugationCLM planarQuarterTurn
  have hconj :
      ∫ omega, C (B omega) ∂M.P.toMeasure =
        C (∫ omega, B omega ∂M.P.toMeasure) :=
    C.integral_comp_comm hStar
  calc
    planarTruncatedAbar M m N hN (Ch02.cubeDomain (originCube 2 n)) =
        ∫ omega, A omega ∂M.P.toMeasure := rfl
    _ = ∫ omega, A (T omega) ∂M.P.toMeasure := hinvariant.symm
    _ = ∫ omega, planarLambda M m ^ 2 • C (B omega) ∂M.P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by simpa [A, B, C, T] using hpoint omega
    _ = planarLambda M m ^ 2 •
        (∫ omega, C (B omega) ∂M.P.toMeasure) := by
      rw [MeasureTheory.integral_smul]
    _ = planarLambda M m ^ 2 • C (∫ omega, B omega ∂M.P.toMeasure) := by
      rw [hconj]
    _ = planarLambda M m ^ 2 •
        (matTranspose planarQuarterTurn *
          planarTruncatedAbarStarInv M m N hN
            (Ch02.cubeDomain (originCube 2 n)) * planarQuarterTurn) := rfl

/-- Concrete self-dual-law assembly.  Because the GMC law already includes
the physical quarter-turn `x ↦ R x`, origin-cube covariance cancels the two
matrix conjugations from deterministic reciprocal duality; the applicable
pointwise identity therefore has no residual conjugation. -/
theorem planarTruncatedAbar_eq_planarLambda_sq_smul_planarTruncatedAbarStarInv_of_pointwise
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (n : ℤ)
    (hA : Integrable
      (planarTruncatedRandomAMatrix M m N hN
        (Ch02.cubeDomain (originCube 2 n))) M.P.toMeasure)
    (hpoint : ∀ omega,
      planarTruncatedRandomAMatrix M m N hN
          (Ch02.cubeDomain (originCube 2 n))
          (planarDualPotentialSample planarQuarterTurn
            planarQuarterTurn_isSignedPermutation omega) =
        planarLambda M m ^ 2 •
          planarTruncatedRandomAStarInvMatrix M m N hN
            (Ch02.cubeDomain (originCube 2 n)) omega) :
    planarTruncatedAbar M m N hN (Ch02.cubeDomain (originCube 2 n)) =
      planarLambda M m ^ 2 •
        planarTruncatedAbarStarInv M m N hN
          (Ch02.cubeDomain (originCube 2 n)) := by
  let T : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 :=
    planarDualPotentialSample planarQuarterTurn planarQuarterTurn_isSignedPermutation
  let A : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 → Mat 2 :=
    planarTruncatedRandomAMatrix M m N hN (Ch02.cubeDomain (originCube 2 n))
  let B : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample 2 → Mat 2 :=
    planarTruncatedRandomAStarInvMatrix M m N hN (Ch02.cubeDomain (originCube 2 n))
  have hinvariant : ∫ omega, A (T omega) ∂M.P.toMeasure =
      ∫ omega, A omega ∂M.P.toMeasure :=
    integral_comp_eq_of_map_eq (E := Fin 2 → Fin 2 → ℝ)
      (measurable_planarDualPotentialSample planarQuarterTurn
        planarQuarterTurn_isSignedPermutation)
      (potentialSequenceLaw_planarDual M planarQuarterTurn
        planarQuarterTurn_isSignedPermutation) A hA.aestronglyMeasurable
  calc
    planarTruncatedAbar M m N hN (Ch02.cubeDomain (originCube 2 n)) =
        ∫ omega, A omega ∂M.P.toMeasure := rfl
    _ = ∫ omega, A (T omega) ∂M.P.toMeasure := hinvariant.symm
    _ = ∫ omega, planarLambda M m ^ 2 • B omega ∂M.P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun omega => by simpa [A, B, T] using hpoint omega
    _ = planarLambda M m ^ 2 • ∫ omega, B omega ∂M.P.toMeasure := by
      rw [MeasureTheory.integral_smul]
    _ = planarLambda M m ^ 2 •
        planarTruncatedAbarStarInv M m N hN
          (Ch02.cubeDomain (originCube 2 n)) := rfl

/-- Annealed finite-volume Dykhne identity for the truncated GMC field,
conditional precisely on the weak zero-normal stream-function theorem and
integrability of the primal truncated coarse observable. -/
theorem planarTruncatedAbar_eq_planarLambda_sq_smul_planarTruncatedAbarStarInv_of_streamFunction
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) {N : ℝ}
    (hN : 1 ≤ N) (n : ℤ)
    (hstream : PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)))
    (hA : Integrable
      (planarTruncatedRandomAMatrix M m N hN
        (Ch02.cubeDomain (originCube 2 n))) M.P.toMeasure) :
    planarTruncatedAbar M m N hN (Ch02.cubeDomain (originCube 2 n)) =
      planarLambda M m ^ 2 •
        planarTruncatedAbarStarInv M m N hN
          (Ch02.cubeDomain (originCube 2 n)) := by
  exact
    planarTruncatedAbar_eq_planarLambda_sq_smul_planarTruncatedAbarStarInv_of_pointwise
      M m hN n hA
      (planarTruncatedRandomAMatrix_planarDualPotentialSample_of_streamFunction
        M m hN n hstream)

end

end SubdiffusiveProcess.CoarseGrainingVocab
