module

public import SubdiffusiveProcess.Static.CutoffCoarseEllipticity
public import SubdiffusiveProcess.Section2.CoarseGrainedPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CoefficientEnergyBridge

@[expose] public section

/-! # The finite cutoff coarse Poincaré estimate in the local time units

This connects the measurable inverse ellipticity supplier with the native
negative Besov norm of an arbitrary `H¹` gradient. It retains the physical
cube, before the final fractional and affine readout.
-/

open MeasureTheory Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The physical energy after division by the homogenized coefficient. -/
def cutoffNormalizedEnergy {d : ℕ} (M : GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (ω : PotentialSample d) (F : Vec d → Vec d) : ℝ :=
  (ahom M L)⁻¹ * ∫ x, aCutoff M L ω x * vecDot (F x) (F x)
    ∂normalizedCubeMeasure Q

theorem cutoffNormalizedEnergy_nonneg {d : ℕ} (M : GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (ω : PotentialSample d) (F : Vec d → Vec d) :
    0 ≤ cutoffNormalizedEnergy M L Q ω F := by
  apply mul_nonneg (inv_nonneg.mpr (ahom_pos M L).le)
  apply integral_nonneg
  intro x
  exact mul_nonneg (aCutoff_pos M L ω x).le (vecNormSq_nonneg (F x))

/-- Identification of the canonical regular coefficient and the literal
cutoff family, for every admissible coarse norm. -/
theorem lambdaSqCoeffField_cutoff_eq {d : ℕ} [NeZero d]
    (M : GMCModel d) (L : ℕ) (Q : TriadicCube d) (ω : PotentialSample d)
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    Ch04.lambdaSqCoeffField Q s q (aCutoffRegCoeffField M L ω) =
      Ch02.lambdaSq Q s q (aCutoffFamily M L ω) := by
  unfold Ch04.lambdaSqCoeffField
  rw [dite_eq_left (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L ω)]
  apply Ch02.lambdaSq_eq_ofAEEq
  intro R
  exact Filter.Eventually.of_forall fun x => by
    simp [aCutoffFamily, aCutoffTriadicData, ScalarTriadicCoeffData.toTriadicCoeffFamily,
      aCutoffCoeffOnData, ScalarCoeffOnData.toCoeffOn, aCutoffRegCoeffField,
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField, scalarCoeffField]

theorem coefficientEnergyNorm_cutoff_sq {d : ℕ} (M : GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (ω : PotentialSample d) (F : Vec d → Vec d) :
    coefficientEnergyNorm Q (aCutoffFamily M L ω) F ^ 2 =
      ahom M L * cutoffNormalizedEnergy M L Q ω F := by
  have hscalar : ∀ x, vecDot (F x)
      (matVecMul (((aCutoffFamily M L ω).coeffOn Q).toCoeffField x) (F x)) =
      aCutoff M L ω x * vecDot (F x) (F x) := by
    intro x
    change vecDot (F x) (matVecMul (scalarMatrix (aCutoff M L ω x)) (F x)) = _
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
  unfold coefficientEnergyNorm
  simp_rw [hscalar]
  have henergy : 0 ≤ ∫ x, aCutoff M L ω x * vecDot (F x) (F x)
      ∂normalizedCubeMeasure Q := integral_nonneg fun x =>
        mul_nonneg (aCutoff_pos M L ω x).le (vecNormSq_nonneg (F x))
  rw [Real.sq_sqrt henergy]
  unfold cutoffNormalizedEnergy
  rw [← mul_assoc, mul_inv_cancel₀ (ahom_pos M L).ne', one_mul]

/-- On every translated physical cube the squared coarse gradient norm is
controlled by the measurable normalized lower ellipticity and normalized
energy, on one event for all `H¹` functions. -/
theorem cutoff_coarsePoincare_ae {d : ℕ} [NeZero d]
    (M : GMCModel d) (L m : ℕ) (z : Vec d) :
    ∀ᵐ ω ∂M.P.toMeasure,
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        paperScaleNormalizedNegativeBesovVectorNorm (originCube d (m : ℤ))
            (1 / 16) (.finite 1) u.grad ^ 2 ≤
          paperPoincareGeometricFactor (1 / 16) (.finite 1) ^ 2 *
            cutoffLowerInv M L m z ω *
              cutoffNormalizedEnergy M L (originCube d (m : ℤ))
                (translatePotentialSample z ω) u.grad := by
  filter_upwards [cutoffLowerInv_ae_eq M L m z] with ω hω
  intro u
  let Q := originCube d (m : ℤ)
  let η := translatePotentialSample z ω
  let A := aCutoffFamily M L η
  have hsym : ∀ R, Ch02.CoeffOn.IsSymmetric (A.coeffOn R) := by
    intro R
    filter_upwards with x
    change (scalarMatrix (aCutoff M L η x)).IsSymm
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [scalarMatrix, Matrix.smul_apply, Matrix.one_apply, eq_comm]
  have hP := (_root_.SubdiffusiveProcess.Section2.coarse_grained_poincare M.shellPrefix.dimension A hsym
    (1 / 16) (by norm_num) (by norm_num) (.finite 1) (by norm_num) (m : ℤ)
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
      coefficientEnergyNorm Q (aCutoffFamily M L η) u.grad) ^ 2 at hsq
  have hlambda : 0 ≤ Ch02.lambdaSq Q (1 / 16) (.finite 1) A :=
    Ch02.lambdaSq_finite_nonneg _ _ (by norm_num) (by norm_num)
  have hpow : Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A)
      (-1 / 2 : ℝ) ^ 2 = (Ch02.lambdaSq Q (1 / 16) (.finite 1) A)⁻¹ := by
    rw [show Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A) (-1 / 2 : ℝ) =
      (Real.sqrt (Ch02.lambdaSq Q (1 / 16) (.finite 1) A))⁻¹ by
        calc
          _ = (Real.rpow (Ch02.lambdaSq Q (1 / 16) (.finite 1) A) (1 / 2 : ℝ))⁻¹ := by
            convert Real.rpow_neg hlambda (1 / 2 : ℝ) using 1 ; norm_num
          _ = _ := congrArg Inv.inv (Real.sqrt_eq_rpow _).symm,
      inv_pow, Real.sq_sqrt hlambda]
  rw [mul_pow, mul_pow, hpow, coefficientEnergyNorm_cutoff_sq] at hsq
  rw [hω, lambdaSqCoeffField_cutoff_eq]
  change _ ≤ _ * (ahom M L * (Ch02.lambdaSq Q _ _ A)⁻¹) * _
  convert hsq using 1 ; ring

end SubdiffusiveProcess.Static
