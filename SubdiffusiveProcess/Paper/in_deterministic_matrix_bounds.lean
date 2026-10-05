module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization

@[expose] public section

/-!
# Deterministic matrix ellipticity and scalar bounds

Auxiliary matrix estimates for the deterministic implication.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section CoreMatrix
open SubdiffusiveProcess
open Homogenization.Book.Ch02
open Homogenization (Vec vecDot vecNormSq matVecMul vecNormSq_nonneg matVecMul_mul)
open scoped ENNReal NNReal

/-- Upper trace bound: `trace σ(Q; a) ≤ d · Λ_{s,q}(Q; a)`.

Each diagonal entry is at most the operator norm of `σ`, which is at most that of `b`
(`0 ≤ σ ≤ b` in Loewner order, both positive semidefinite), which is at most `Λ`
(`oneCube_b_le_LambdaSq`). -/
theorem aux_in_deterministic_matrix_bounds_trace_le {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s)
    {q : MultiscaleExponent} (hq : q.IsAdmissible) :
    Matrix.trace (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * LambdaSq Q s q a := by
  have hσpsd : (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).PosSemidef :=
    posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm
      (sigmaStarCoarse_posDef (cubeDomain Q) (a.coeffOn Q)).posSemidef
      (sigmaCoarse_isSymm (cubeDomain Q) (a.coeffOn Q))
      (sigmaStarCoarse_le_sigmaCoarse (cubeDomain Q) (a.coeffOn Q))
  have hnorm : matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
      matrixNorm (bCoarse (cubeDomain Q) (a.coeffOn Q)) :=
    matrixNorm_le_of_matLoewnerLE_of_posSemidef hσpsd
      (bCoarse_posSemidef (cubeDomain Q) (a.coeffOn Q))
      (sigmaCoarse_le_bCoarse (cubeDomain Q) (a.coeffOn Q))
  have hb : matrixNorm (bCoarse (cubeDomain Q) (a.coeffOn Q)) ≤ LambdaSq Q s q a :=
    oneCube_b_le_LambdaSq Q a hs hq
  have hentry : ∀ i : Fin d, sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i i ≤
      matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := by
    intro i
    rw [matrixNorm_eq_matrixOperatorNorm]
    exact (le_abs_self _).trans (abs_entry_le_matrixOperatorNorm _ i i)
  calc Matrix.trace (sigmaCoarse (cubeDomain Q) (a.coeffOn Q))
        = ∑ i : Fin d, sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i i := rfl
    _ ≤ ∑ _i : Fin d, matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) :=
        Finset.sum_le_sum fun i _ => hentry i
    _ = (d : ℝ) * matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := by
        simp
    _ ≤ (d : ℝ) * LambdaSq Q s q a :=
        mul_le_mul_of_nonneg_left (hnorm.trans hb) (Nat.cast_nonneg d)

/-- Lower quadratic bound: `λ_{s,q}(Q; a) · |x|² ≤ x · σ(Q; a) x`.

With `S = σ_*⁻¹(Q)` positive definite and `S σ_* = 1`,
`|x|² ≤ ‖S‖ · x·σ_* x` (upstream), `x·σ_* x ≤ x·σ x` (Loewner), and
`λ ≤ ‖S‖⁻¹` (`lambdaSq_le_oneCube`). -/
theorem aux_in_deterministic_matrix_bounds_quad_ge {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s)
    {q : MultiscaleExponent} (hq : q.IsAdmissible) (x : Fin d → ℝ) :
    lambdaSq Q s q a * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).mulVec x := by
  have hSpd := sigmaStarInvCoarse_posDef (cubeDomain Q) (a.coeffOn Q)
  have hSpos : 0 < matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)) :=
    matrixNorm_pos_of_posDef hSpd
  have hleft : ∀ ξ : Homogenization.Vec d,
      matVecMul (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q))
        (matVecMul (sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, sigmaStarInvCoarse_mul_sigmaStarCoarse
      (isUnit_det_sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q))]
    exact Matrix.one_mulVec ξ
  have h1 : vecNormSq x ≤
      matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)) *
        vecDot x (matVecMul (sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) :=
    vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      hSpd.posSemidef hleft x
  have h2 : vecDot x (matVecMul (sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) ≤
      vecDot x (matVecMul (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
    have h := sigmaStarCoarse_le_sigmaCoarse (cubeDomain Q) (a.coeffOn Q) x
    linarith
  have h3 : lambdaSq Q s q a ≤
      (matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)))⁻¹ :=
    lambdaSq_le_oneCube Q a hs hq
  have hX : 0 ≤ vecNormSq x := vecNormSq_nonneg x
  have h4 : lambdaSq Q s q a * vecNormSq x ≤
      vecDot x (matVecMul (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
    calc lambdaSq Q s q a * vecNormSq x
        ≤ (matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)))⁻¹ *
            vecNormSq x := mul_le_mul_of_nonneg_right h3 hX
      _ ≤ (matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)))⁻¹ *
            (matrixNorm (sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)) *
              vecDot x (matVecMul (sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hSpos.le)
      _ = vecDot x (matVecMul (sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
          rw [← mul_assoc, inv_mul_cancel₀ hSpos.ne', one_mul]
      _ ≤ vecDot x (matVecMul (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := h2
  exact h4

/-- Scalar assembly.  If `cell ≤ λ/s_N`, `Λ/s_N ≤ cell⁻¹`, `trace ≤ d Λ` and
`λ |x|² ≤ x·σx`, then for every `Cbound ≥ d / cell²`,
`Cbound⁻¹ · (s_N⁻¹ trace) · |x|² ≤ s_N⁻¹ · x·σx`.  Positivity of `s_N` is derived from
the lower bound, not assumed. -/
theorem aux_in_deterministic_matrix_bounds_scalar
    (d T Qd X sNv lam Lam cell Cbound : ℝ) (hd : 0 ≤ d) (hcell : 0 < cell)
    (hlam : 0 < lam) (hlo : cell ≤ lam / sNv) (hhi : Lam / sNv ≤ cell⁻¹)
    (hT : T ≤ d * Lam) (hQ : lam * X ≤ Qd) (hX : 0 ≤ X)
    (hC : d / cell ^ 2 ≤ Cbound) (hCpos : 0 < Cbound) :
    Cbound⁻¹ * (sNv⁻¹ * T) * X ≤ sNv⁻¹ * Qd := by
  have hsN : 0 < sNv := by
    by_contra h
    push Not at h
    have : lam / sNv ≤ 0 := div_nonpos_of_nonneg_of_nonpos hlam.le h
    linarith
  have hsNinv : 0 < sNv⁻¹ := inv_pos.2 hsN
  have h1 : sNv⁻¹ * T ≤ d / cell := by
    calc sNv⁻¹ * T ≤ sNv⁻¹ * (d * Lam) := mul_le_mul_of_nonneg_left hT hsNinv.le
      _ = d * (Lam / sNv) := by rw [div_eq_mul_inv]; ring
      _ ≤ d * cell⁻¹ := mul_le_mul_of_nonneg_left hhi hd
      _ = d / cell := by rw [div_eq_mul_inv]
  have h2 : Cbound⁻¹ * (d / cell) ≤ cell := by
    rw [inv_mul_le_iff₀ hCpos]
    calc d / cell = d / cell ^ 2 * cell := by field_simp
      _ ≤ Cbound * cell := mul_le_mul_of_nonneg_right hC hcell.le
  have h3 : cell * X ≤ sNv⁻¹ * Qd := by
    calc cell * X ≤ (lam / sNv) * X := mul_le_mul_of_nonneg_right hlo hX
      _ = sNv⁻¹ * (lam * X) := by rw [div_eq_mul_inv]; ring
      _ ≤ sNv⁻¹ * Qd := mul_le_mul_of_nonneg_left hQ hsNinv.le
  calc Cbound⁻¹ * (sNv⁻¹ * T) * X ≤ Cbound⁻¹ * (d / cell) * X := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hCpos.le)
    _ ≤ cell * X := mul_le_mul_of_nonneg_right h2 hX
    _ ≤ sNv⁻¹ * Qd := h3


/-- The literal exponent `(2 : ℝ≥0∞)` of `in_J.lam_eq`/`Lam_eq` is admissible. -/
theorem aux_in_deterministic_matrix_bounds_two_admissible :
    (if (2 : ℝ≥0∞) = ⊤ then MultiscaleExponent.infinity
      else MultiscaleExponent.finite (2 : ℝ≥0∞).toReal).IsAdmissible := by
  rw [ite_eq_right ENNReal.ofNat_ne_top]
  simp

/-- Chart-level R3: for the actual `in_J` chart of a root cube, normalized by any scalar
`sNv` with `cell ≤ λ/sNv` and `Λ/sNv ≤ cell⁻¹`, the normalized coarse matrix
`sNv⁻¹ • σ(□₀; chart)` satisfies the trace-ellipticity bound for every `Cbound ≥ d/cell²`. -/
theorem aux_in_deterministic_matrix_bounds_chart
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (sigma cell Cbound : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (hcell : 0 < cell)
    (hC : (d : ℝ) / cell ^ 2 ≤ Cbound) (hCpos : 0 < Cbound)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (sNv : ℝ)
    (hlo : cell ≤ I.lam z r hr a z r sigma 2 / sNv)
    (hhi : I.Lam z r hr a z r sigma 2 / sNv ≤ cell⁻¹) (x : Fin d → ℝ) :
    Cbound⁻¹ * Matrix.trace (sNv⁻¹ • Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart z r hr a z r).coeffOn (Homogenization.originCube d 0))) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (sNv⁻¹ • Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart z r hr a z r).coeffOn (Homogenization.originCube d 0))).mulVec x := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := subset_rfl
  have hq2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hlamEq := I.lam_eq z r hr a z r hr hsub sigma hsigma 2 hq2
  have hLamEq := I.Lam_eq z r hr a z r hr hsub sigma hsigma 2 hq2
  have htr := aux_in_deterministic_matrix_bounds_trace_le (Homogenization.originCube d 0)
    (I.chart z r hr a z r) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible
  have hqd := aux_in_deterministic_matrix_bounds_quad_ge (Homogenization.originCube d 0)
    (I.chart z r hr a z r) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible x
  rw [← hLamEq] at htr
  rw [← hlamEq] at hqd
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact aux_in_deterministic_matrix_bounds_scalar (d : ℝ) _ _ _ sNv _ _ cell Cbound
    (Nat.cast_nonneg d) hcell (I.lam_pos z r hr a z r sigma 2) hlo hhi htr hqd
    (dotProduct_self_star_nonneg x) hC hCpos

/-- `λ_{s,q}(Q; a) ≤ Λ_{s,q}(Q; a)`: test the lower bound on the first unit vector and
bound the diagonal entry `σ₀₀ ≤ ‖σ‖ ≤ ‖b‖ ≤ Λ`. -/
theorem aux_in_deterministic_matrix_bounds_lam_le_Lam {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s)
    {q : MultiscaleExponent} (hq : q.IsAdmissible) :
    lambdaSq Q s q a ≤ LambdaSq Q s q a := by
  have hlo := aux_in_deterministic_matrix_bounds_quad_ge Q a hs hq (Pi.single 0 1)
  have hee : (Pi.single 0 1 : Fin d → ℝ) ⬝ᵥ (Pi.single 0 1 : Fin d → ℝ) = 1 := by simp
  have hσe : (Pi.single 0 1 : Fin d → ℝ) ⬝ᵥ
      (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).mulVec (Pi.single 0 1) =
      sigmaCoarse (cubeDomain Q) (a.coeffOn Q) 0 0 := by
    simp [Matrix.mulVec_single]
  rw [hee, mul_one, hσe] at hlo
  have hσpsd : (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).PosSemidef :=
    posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm
      (sigmaStarCoarse_posDef (cubeDomain Q) (a.coeffOn Q)).posSemidef
      (sigmaCoarse_isSymm (cubeDomain Q) (a.coeffOn Q))
      (sigmaStarCoarse_le_sigmaCoarse (cubeDomain Q) (a.coeffOn Q))
  have hnorm : matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
      matrixNorm (bCoarse (cubeDomain Q) (a.coeffOn Q)) :=
    matrixNorm_le_of_matLoewnerLE_of_posSemidef hσpsd
      (bCoarse_posSemidef (cubeDomain Q) (a.coeffOn Q))
      (sigmaCoarse_le_bCoarse (cubeDomain Q) (a.coeffOn Q))
  have hb : matrixNorm (bCoarse (cubeDomain Q) (a.coeffOn Q)) ≤ LambdaSq Q s q a :=
    oneCube_b_le_LambdaSq Q a hs hq
  have hentry : sigmaCoarse (cubeDomain Q) (a.coeffOn Q) 0 0 ≤
      matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := by
    rw [matrixNorm_eq_matrixOperatorNorm]
    exact (le_abs_self _).trans (abs_entry_le_matrixOperatorNorm _ 0 0)
  exact hlo.trans (hentry.trans (hnorm.trans hb))

/-- Chart-level `λ ≤ Λ` for the `in_J` coarse ellipticities at `q = 2`. -/
theorem aux_in_deterministic_matrix_bounds_chart_lam_le_Lam
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) :
    I.lam z r hr a z r sigma 2 ≤ I.Lam z r hr a z r sigma 2 := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := subset_rfl
  have hq2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  rw [I.lam_eq z r hr a z r hr hsub sigma hsigma 2 hq2,
    I.Lam_eq z r hr a z r hr hsub sigma hsigma 2 hq2]
  exact aux_in_deterministic_matrix_bounds_lam_le_Lam (Homogenization.originCube d 0)
    (I.chart z r hr a z r) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible

/-- Scalar step for the `Uq` half of `traceEstimate`: from `cell ≤ λ/s_N`,
`Λ/s_N ≤ cell⁻¹` and `λ ≤ Λ`, every `Cbound ≥ cell⁻¹` gives
`Cbound⁻¹ s_N ≤ Λ ≤ Cbound s_N`.  Positivity of `s_N` is derived, not assumed. -/
theorem aux_in_deterministic_matrix_bounds_Uq_scalar (sNv lam Lam cell Cbound : ℝ)
    (hcell : 0 < cell) (hlam : 0 < lam) (hlo : cell ≤ lam / sNv)
    (hhi : Lam / sNv ≤ cell⁻¹) (hlL : lam ≤ Lam) (hC : cell⁻¹ ≤ Cbound) :
    Cbound⁻¹ * sNv ≤ Lam ∧ Lam ≤ Cbound * sNv := by
  have hsN : 0 < sNv := by
    by_contra h
    push Not at h
    have : lam / sNv ≤ 0 := div_nonpos_of_nonneg_of_nonpos hlam.le h
    linarith
  have hCinv : Cbound⁻¹ ≤ cell := inv_le_of_inv_le₀ hcell hC
  refine ⟨?_, ?_⟩
  · calc Cbound⁻¹ * sNv ≤ cell * sNv := mul_le_mul_of_nonneg_right hCinv hsN.le
      _ ≤ lam := (le_div_iff₀ hsN).1 hlo
      _ ≤ Lam := hlL
  · calc Lam ≤ cell⁻¹ * sNv := (div_le_iff₀ hsN).1 hhi
      _ ≤ Cbound * sNv := mul_le_mul_of_nonneg_right hC hsN.le

/-- The assembly note's suggested constant `d / (w₀² cell²)`, `w₀ = geometricWeight σ 2 0`,
is also sufficient for R3: it dominates the proved threshold `d / cell²`, since
`0 < w₀ ≤ 1`. -/
theorem aux_in_deterministic_matrix_bounds_sketch_constant (d : ℕ) (sigma cell : ℝ)
    (hsigma : 0 < sigma) (hcell : 0 < cell) :
    0 < geometricWeight sigma 2 0 ∧ geometricWeight sigma 2 0 ≤ 1 ∧
      (d : ℝ) / cell ^ 2 ≤ (d : ℝ) / (geometricWeight sigma 2 0 ^ 2 * cell ^ 2) := by
  have hw : geometricWeight sigma 2 0 = 1 - Real.rpow 3 (-sigma * 2) := by
    simp [geometricWeight, geometricDiscount]
  have hlt : Real.rpow 3 (-sigma * 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpos : 0 < Real.rpow 3 (-sigma * 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hw0 : 0 < geometricWeight sigma 2 0 := by rw [hw]; linarith
  have hw1 : geometricWeight sigma 2 0 ≤ 1 := by rw [hw]; linarith
  refine ⟨hw0, hw1, ?_⟩
  have hc2 : 0 < cell ^ 2 := by positivity
  have hsq : geometricWeight sigma 2 0 ^ 2 ≤ 1 := by
    rw [sq]; exact (mul_le_of_le_one_left hw0.le hw1).trans hw1
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by positivity)
  calc geometricWeight sigma 2 0 ^ 2 * cell ^ 2 ≤ 1 * cell ^ 2 :=
        mul_le_mul_of_nonneg_right hsq hc2.le
    _ = cell ^ 2 := one_mul _

end CoreMatrix
end SubdiffusiveProcess.Paper

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable



theorem in_deterministic_matrix_bounds
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (sigma cell Cbound : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hC : (d : ℝ) / cell ^ 2 ≤ Cbound) (hCpos : 0 < Cbound)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Enl Shift : Type)
    (rootLevel : Enl × Shift → ℤ)
    (rootSide : Enl × Shift → ℝ)
    (rootCentre : Enl × Shift → SpatialCoordinates d)
    (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
    (N : ℕ) (omega : BilateralField d)
    (hEll : ∀ U : Enl × Shift,
      cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) :
    ∀ (Uroot : Enl × Shift) (x : Fin d → ℝ),
      Cbound⁻¹ * Matrix.trace (AEN N Uroot omega) * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (AEN N Uroot omega).mulVec x := by
  intro Uroot x
  have h := hEll Uroot
  rw [hEllLoN N Uroot omega, hEllHiN N Uroot omega] at h
  rw [hAEN N Uroot omega]
  exact aux_in_deterministic_matrix_bounds_chart I sigma cell Cbound hsigma hcell.1 hC hCpos
    (rootCentre Uroot) (rootSide Uroot) (rootPos Uroot)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
      (rootCentre Uroot) (rootPos Uroot))
    (sN N (rootLevel Uroot) (rootCentre Uroot) omega) h.1 h.2 x

/-- The threshold `max 1 (max (d / cell²) cell⁻¹)`: chosen from the frozen outer binders
`d`, `cell` only; every larger `Cbound` meets the side conditions of
`aux_in_deterministic_matrix_bounds_R3` and `aux_in_deterministic_matrix_bounds_Uq`.  (For `2 ≤ d` and
`cell ∈ (0,1)` it equals `max 1 (d / cell²)`.) -/
theorem aux_in_deterministic_matrix_bounds_threshold (d : ℕ) (cell : ℝ) :
    ∃ C3 : ℝ, 1 ≤ C3 ∧ ∀ Cbound : ℝ, C3 ≤ Cbound →
      (d : ℝ) / cell ^ 2 ≤ Cbound ∧ cell⁻¹ ≤ Cbound ∧ 0 < Cbound :=
  ⟨max 1 (max ((d : ℝ) / cell ^ 2) cell⁻¹), le_max_left _ _, fun _ hC =>
    ⟨((le_max_left _ _).trans (le_max_right _ _)).trans hC,
      ((le_max_right _ _).trans (le_max_right _ _)).trans hC,
      lt_of_lt_of_le one_pos ((le_max_left _ _).trans hC)⟩⟩



theorem aux_in_deterministic_matrix_bounds_Uq
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (sigma cell Cbound : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hC : cell⁻¹ ≤ Cbound)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
    (Enl Shift : Type)
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (_hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (_hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
    (N : ℕ) (omega : BilateralField d)
    (hEll : ∀ U : Enl × Shift,
      cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) :
          ∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega := by
  have hL : rootLevel qRoot = (k : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]; simp
  have hS : rootSide qRoot = qside := by
    rw [hrootSide, hL, hqside]
  have hCtr : rootCentre qRoot = qcenter := by
    rw [hqRoot, hrootCentre, hshift, smul_zero, add_zero]
  have hmove : ∀ (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), c = qcenter → r = qside →
      I.lam c r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr)
          c r sigma 2 =
        I.lam qcenter qside hqpos
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
          qcenter qside sigma 2 ∧
      I.Lam c r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N c hr)
          c r sigma 2 =
        I.Lam qcenter qside hqpos
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
          qcenter qside sigma 2 := by
    rintro c r hr rfl rfl
    exact ⟨rfl, rfl⟩
  obtain ⟨hlamq, hLamq⟩ :=
    hmove (rootCentre qRoot) (rootSide qRoot) (rootPos qRoot) hCtr hS
  have h := hEll qRoot
  rw [hEllLoN N qRoot omega, hEllHiN N qRoot omega, hlamq, hLamq, hL, hCtr] at h
  obtain ⟨hlo, hup⟩ := aux_in_deterministic_matrix_bounds_Uq_scalar _ _ _ cell Cbound hcell.1
    (I.lam_pos _ _ _ _ _ _ _ _) h.1 h.2
    (aux_in_deterministic_matrix_bounds_chart_lam_le_Lam I sigma hsigma qcenter qside hqpos _) hC
  exact ⟨_, rfl, hlo, hup⟩


end SubdiffusiveProcess.Paper


