import SubdiffusiveProcess.Static.CutoffCoarsePoincare
import Homogenization.Book.Ch04.Theorems.DilationLaw

/-! # Coarse Poincaré after physical rescaling to the unit cube -/

open MeasureTheory Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The normalized energy in the unit coordinates of the physical cube. -/
def cutoffUnitEnergy {d : ℕ} (M : GMCModel d) (L m : ℕ)
    (ω : PotentialSample d) (F : Vec d → Vec d) : ℝ :=
  (ahom M L)⁻¹ * ∫ x, aCutoff M L ω ((3 : ℝ) ^ m • x) * vecDot (F x) (F x)
    ∂normalizedCubeMeasure (originCube d 0)

theorem cutoffUnitEnergy_nonneg {d : ℕ} (M : GMCModel d) (L m : ℕ)
    (ω : PotentialSample d) (F : Vec d → Vec d) :
    0 ≤ cutoffUnitEnergy M L m ω F := by
  apply mul_nonneg (inv_nonneg.mpr (ahom_pos M L).le)
  apply integral_nonneg
  intro x
  exact mul_nonneg (aCutoff_pos M L ω _).le (vecNormSq_nonneg (F x))

theorem coefficientEnergyNorm_rescaled_cutoff_sq {d : ℕ} [NeZero d]
    (M : GMCModel d) (L m : ℕ) (ω : PotentialSample d) (F : Vec d → Vec d) :
    coefficientEnergyNorm (originCube d 0)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (rescaleReg m (aCutoffRegCoeffField M L ω))
        ((aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L ω).of_rescaleCoeffField m))
      F ^ 2 = ahom M L * cutoffUnitEnergy M L m ω F := by
  have hscalar : ∀ x, vecDot (F x) (matVecMul
      (((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (rescaleReg m (aCutoffRegCoeffField M L ω))
        ((aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L ω).of_rescaleCoeffField m)).coeffOn
          (originCube d 0)).toCoeffField x) (F x)) =
      aCutoff M L ω ((3 : ℝ) ^ m • x) * vecDot (F x) (F x) := by
    intro x
    change vecDot (F x) (matVecMul (scalarMatrix (aCutoff M L ω ((3 : ℝ) ^ m • x))) (F x)) = _
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
  unfold coefficientEnergyNorm
  simp_rw [hscalar]
  have henergy : 0 ≤ ∫ x, aCutoff M L ω ((3 : ℝ) ^ m • x) * vecDot (F x) (F x)
      ∂normalizedCubeMeasure (originCube d 0) := integral_nonneg fun x =>
        mul_nonneg (aCutoff_pos M L ω _).le (vecNormSq_nonneg (F x))
  rw [Real.sq_sqrt henergy]
  unfold cutoffUnitEnergy
  rw [← mul_assoc, mul_inv_cancel₀ (ahom_pos M L).ne', one_mul]

/-- The coefficient rescaling preserves coarse ellipticity and gives one
almost-sure event for every native `H¹` function on the unit cube. -/
theorem cutoff_rescaledCoarsePoincare_ae {d : ℕ} [NeZero d]
    (M : GMCModel d) (L m : ℕ) (z : Vec d) :
    ∀ᵐ ω ∂M.P.toMeasure,
      ∀ u : H1Function (openCubeSet (originCube d 0)),
        paperScaleNormalizedNegativeBesovVectorNorm (originCube d 0)
            (1 / 16) (.finite 1) u.grad ^ 2 ≤
          paperPoincareGeometricFactor (1 / 16) (.finite 1) ^ 2 *
            cutoffLowerInv M L m z ω *
              cutoffUnitEnergy M L m (translatePotentialSample z ω) u.grad := by
  filter_upwards [cutoffLowerInv_ae_eq M L m z] with ω hω
  intro u
  let Q := originCube d 0
  let η := translatePotentialSample z ω
  let a := rescaleReg m (aCutoffRegCoeffField M L η)
  have ha : Ch04.AELocallyUniformlyEllipticField a :=
    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L η).of_rescaleCoeffField m
  let A := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hsym : ∀ R, Ch02.CoeffOn.IsSymmetric (A.coeffOn R) := by
    intro R
    filter_upwards with x
    change (scalarMatrix (aCutoff M L η ((3 : ℝ) ^ m • x))).IsSymm
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [scalarMatrix, Matrix.smul_apply, Matrix.one_apply, eq_comm]
  have hP := (SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare M.shellPrefix.dimension A hsym
    (1 / 16) (by norm_num) (by norm_num) (.finite 1) (by norm_num) (0 : ℤ)
    u (fun _ => 0) (Section6HolderInterior.memVectorL2_zero _)
    (Section6HolderInterior.isSolenoidalOn_zero _)).1
  have hN : 0 ≤ paperScaleNormalizedNegativeBesovVectorNorm Q (1 / 16) (.finite 1)
      u.grad := by
    unfold paperScaleNormalizedNegativeBesovVectorNorm
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    unfold Ch03.scaleNormalizedNegativeBesovVectorNorm
    apply Real.sSup_nonneg'
    exact ⟨_, ⟨0, rfl⟩, Ch03.negativeBesovVectorPartialNormFinite_nonneg Q _ _ _ _⟩
  have hsq := pow_le_pow_left₀ hN hP 2
  change _ ≤ (paperPoincareGeometricFactor (1 / 16) (.finite 1) *
    Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A) (-1 / 2 : ℝ) *
      coefficientEnergyNorm Q A u.grad) ^ 2 at hsq
  have hlambda : 0 ≤ Ch02.lambdaSq Q (1 / 16) (.finite 1) A :=
    Ch02.lambdaSq_finite_nonneg _ _ (by norm_num) (by norm_num)
  have hpow : Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A)
      (-1 / 2 : ℝ) ^ 2 = (Ch02.lambdaSq Q (1 / 16) (.finite 1) A)⁻¹ := by
    rw [show Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A) (-1 / 2 : ℝ) =
      (Real.sqrt (Ch02.lambdaSq Q (1 / 16) (.finite 1) A))⁻¹ by
        calc
          _ = (Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A) (1 / 2 : ℝ))⁻¹ := by
            convert Real.rpow_neg hlambda (1 / 2 : ℝ) using 1 <;> norm_num
          _ = _ := congrArg Inv.inv (Real.sqrt_eq_rpow _).symm,
      inv_pow, Real.sq_sqrt hlambda]
  rw [mul_pow, mul_pow, hpow, coefficientEnergyNorm_rescaled_cutoff_sq] at hsq
  have hscaleEq : Ch04.lambdaSqCoeffField (originCube d (m : ℤ)) (1 / 16) (.finite 1)
      (aCutoffRegCoeffField M L η) = Ch02.lambdaSq Q (1 / 16) (.finite 1) A := by
    have hscale := Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L η) m 0 (1 / 16) (.finite 1)
    have hunit : Ch04.lambdaSqCoeffField Q (1 / 16) (.finite 1) a =
        Ch02.lambdaSq Q (1 / 16) (.finite 1) A := by
      unfold Ch04.lambdaSqCoeffField
      rw [dif_pos ha]
    simpa only [Nat.add_zero, ← hunit] using hscale.symm
  rw [hω, hscaleEq]
  change _ ≤ _ * (ahom M L * (Ch02.lambdaSq Q _ _ A)⁻¹) * _
  convert hsq using 1 <;> ring

end SubdiffusiveProcess.Static
