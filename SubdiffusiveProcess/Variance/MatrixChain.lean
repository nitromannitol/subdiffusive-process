module

public import Homogenization.Ambient.MatrixOrderBridge
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import SubdiffusiveProcess.Lfgc.PsdNorm

@[expose] public section

/-!
# The deterministic matrix chain of `l.var.bounds`

For positive definite `U i` (the coarse matrices `a(R)`), symmetric `S i` (the coarse matrices
`a_*^{-1}(R)`), a symmetric `B` (= `β⁻¹`), a parent pair `(U0, S0)` and the averages
`Ū = avg U`, `S̄ = avg S`, the paper's chain

`a_*^{-1}(parent) ≥ a^{-1}(parent) ≥ Ū⁻¹`,  `S̄ ≤ Ū⁻¹ + avg (S i - 2B + B (U i) B)`,
`avg (S i - 2B + B (U i) B) ≤ avg tr(S i - 2B + B (U i) B) · Id`

is proved for the quadratic forms.  The arithmetic–harmonic mean identity of the paper reduces here
to the positivity of `(B - Ū⁻¹) Ū (B - Ū⁻¹) = B Ū B - 2B + Ū⁻¹`.
Nothing in this file mentions coarse-graining.
-/

open Homogenization Homogenization.Book.Ch02
open scoped Matrix

namespace SubdiffusiveProcess.Variance

variable {d : ℕ}

theorem vecDot_eq_dotProduct (x y : Vec d) : vecDot x y = x ⬝ᵥ y := rfl

theorem matVecMul_eq_mulVec (A : Mat d) (x : Vec d) : matVecMul A x = A.mulVec x := rfl

theorem vecNormSq_eq_dotProduct (x : Vec d) : vecNormSq x = x ⬝ᵥ x := rfl

/-- The average `(card s)⁻¹ • ∑_{i ∈ s} F i` of a family of matrices. -/
noncomputable def avgMat {ι : Type*} (s : Finset ι) (F : ι → Mat d) : Mat d :=
  ((s.card : ℝ)⁻¹) • ∑ i ∈ s, F i

theorem quad_avgMat {ι : Type*} (s : Finset ι) (F : ι → Mat d) (v : Vec d) :
    vecDot v (matVecMul (avgMat s F) v) =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, vecDot v (matVecMul (F i) v) := by
  simp only [avgMat, vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.smul_mulVec,
    Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum, smul_eq_mul]

theorem isSymm_of_posSemidef {A : Mat d} (hA : A.PosSemidef) : A.IsSymm := by
  have h := hA.isHermitian
  simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem quad_nonneg_of_posSemidef {A : Mat d} (hA : A.PosSemidef) (v : Vec d) :
    0 ≤ vecDot v (matVecMul A v) := by
  have := hA.dotProduct_mulVec_nonneg v
  simpa [vecDot_eq_dotProduct, matVecMul_eq_mulVec] using this

theorem posSemidef_of_quad {A : Mat d} (hA : A.IsSymm)
    (h : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A v)) : A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  · intro v
    simpa [vecDot_eq_dotProduct, matVecMul_eq_mulVec] using h v

theorem posDef_of_quad {A : Mat d} (hA : A.IsSymm)
    (h : ∀ v : Vec d, v ≠ 0 → 0 < vecDot v (matVecMul A v)) : A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  · intro v hv
    simpa [vecDot_eq_dotProduct, matVecMul_eq_mulVec] using h v hv

theorem quad_pos_of_posDef {A : Mat d} (hA : A.PosDef) {v : Vec d} (hv : v ≠ 0) :
    0 < vecDot v (matVecMul A v) := by
  have := hA.dotProduct_mulVec_pos hv
  simpa [vecDot_eq_dotProduct, matVecMul_eq_mulVec] using this

theorem isSymm_of_posDef {A : Mat d} (hA : A.PosDef) : A.IsSymm :=
  isSymm_of_posSemidef hA.posSemidef

theorem isSymm_avgMat {ι : Type*} (s : Finset ι) (F : ι → Mat d) (hF : ∀ i ∈ s, (F i).IsSymm) :
    (avgMat s F).IsSymm := by
  unfold avgMat Matrix.IsSymm
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  exact Finset.sum_congr rfl fun i hi => hF i hi

/-- The average of positive definite matrices is positive definite. -/
theorem posDef_avgMat {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ι → Mat d)
    (hF : ∀ i ∈ s, (F i).PosDef) : (avgMat s F).PosDef := by
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  refine posDef_of_quad (isSymm_avgMat s F fun i hi => isSymm_of_posDef (hF i hi)) ?_
  intro v hv
  rw [quad_avgMat]
  exact mul_pos (inv_pos.mpr hcard)
    (Finset.sum_pos (fun i hi => quad_pos_of_posDef (hF i hi) hv) hs)

/-- The average of positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_avgMat {ι : Type*} (s : Finset ι) (F : ι → Mat d)
    (hF : ∀ i ∈ s, (F i).PosSemidef) : (avgMat s F).PosSemidef := by
  refine posSemidef_of_quad (isSymm_avgMat s F fun i hi => isSymm_of_posSemidef (hF i hi)) ?_
  intro v
  rw [quad_avgMat]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i hi => quad_nonneg_of_posSemidef (hF i hi) v)

theorem quad_sub (A B : Mat d) (v : Vec d) :
    vecDot v (matVecMul (A - B) v) = vecDot v (matVecMul A v) - vecDot v (matVecMul B v) := by
  simp only [vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.sub_mulVec, dotProduct_sub]

theorem quad_add (A B : Mat d) (v : Vec d) :
    vecDot v (matVecMul (A + B) v) = vecDot v (matVecMul A v) + vecDot v (matVecMul B v) := by
  simp only [vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.add_mulVec, dotProduct_add]

theorem quad_smul (c : ℝ) (A : Mat d) (v : Vec d) :
    vecDot v (matVecMul (c • A) v) = c * vecDot v (matVecMul A v) := by
  simp only [vecDot_eq_dotProduct, matVecMul_eq_mulVec, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

theorem isSymm_inv_of_posDef {A : Mat d} (hA : A.PosDef) : A⁻¹.IsSymm :=
  isSymm_of_posDef hA.inv

/-- `B Ū B - 2B + Ū⁻¹ = (B - Ū⁻¹) Ū (B - Ū⁻¹) ≥ 0`: the arithmetic–harmonic mean step. -/
theorem posSemidef_amhm {U B : Mat d} (hU : U.PosDef) (hB : B.IsSymm) :
    (B * U * B - (2 : ℝ) • B + U⁻¹).PosSemidef := by
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hdet
  have hC : (B - U⁻¹)ᴴ = B - U⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      hB, isSymm_inv_of_posDef hU]
  have h := hU.posSemidef.conjTranspose_mul_mul_same (B - U⁻¹)
  rw [hC] at h
  have e : (B - U⁻¹) * U * (B - U⁻¹) = B * U * B - (2 : ℝ) • B + U⁻¹ := by
    calc (B - U⁻¹) * U * (B - U⁻¹)
        = B * U * B - B * (U * U⁻¹) - (U⁻¹ * U) * B + U⁻¹ * (U * U⁻¹) := by noncomm_ring
      _ = B * U * B - (2 : ℝ) • B + U⁻¹ := by
        rw [h1, h2]; simp [two_smul]; abel
  rwa [e] at h

theorem quad_le_trace_of_posSemidef {A : Mat d} (hA : A.PosSemidef) (v : Vec d) :
    vecDot v (matVecMul A v) ≤ Matrix.trace A * vecNormSq v :=
  (SubdiffusiveProcess.Lfgc.quad_le_matrixNorm A v).trans
    (mul_le_mul_of_nonneg_right (matrixNorm_le_trace_of_posSemidef A hA)
      (SubdiffusiveProcess.Lfgc.vecNormSq_nonneg' v))

theorem avgMat_chain_K {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (S U : ι → Mat d) (B : Mat d) :
    avgMat s (fun i => S i - (2 : ℝ) • B + B * U i * B) =
      avgMat s S - (2 : ℝ) • B + B * avgMat s U * B := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hsum : ∑ x ∈ s, B * U x * B = B * (∑ x ∈ s, U x) * B := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hconst : ∑ _x ∈ s, ((2 : ℝ) • B) = (s.card : ℝ) • ((2 : ℝ) • B) := by
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  unfold avgMat
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hconst, hsum]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  match_scalars <;> field_simp

/-- The deterministic chain: `0 ≤ S̄ - S0 ≤ (avg tr K) Id` in the quadratic-form order. -/
theorem chain {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (U S : ι → Mat d) (U0 S0 B : Mat d)
    (hB : B.IsSymm) (hU : ∀ i ∈ s, (U i).PosDef) (hU0 : U0.PosDef)
    (hK : ∀ i ∈ s, (S i - (2 : ℝ) • B + B * U i * B).PosSemidef)
    (hK0 : (S0 - U0⁻¹).PosSemidef)
    (hUsub : ∀ v, vecDot v (matVecMul U0 v) ≤ vecDot v (matVecMul (avgMat s U) v))
    (hSsub : ∀ v, vecDot v (matVecMul S0 v) ≤ vecDot v (matVecMul (avgMat s S) v))
    (v : Vec d) :
    0 ≤ vecDot v (matVecMul (avgMat s S - S0) v) ∧
      vecDot v (matVecMul (avgMat s S - S0) v) ≤
        (s.card : ℝ)⁻¹ * (∑ i ∈ s, Matrix.trace (S i - (2 : ℝ) • B + B * U i * B)) *
          vecNormSq v := by
  refine ⟨?_, ?_⟩
  · rw [quad_sub]; linarith [hSsub v]
  · have hUbPD := posDef_avgMat s hs U hU
    have hAM := posSemidef_amhm hUbPD hB
    have hKpsd : (avgMat s (fun i => S i - (2 : ℝ) • B + B * U i * B)).PosSemidef :=
      posSemidef_avgMat s _ hK
    have hUlow := matLoewnerLE_inv_of_posDef hU0 hUbPD
      (fun x => by have := hUsub x; linarith) v
    have hS0low := quad_nonneg_of_posSemidef hK0 v
    rw [quad_sub] at hS0low
    have hAMv := quad_nonneg_of_posSemidef hAM v
    rw [quad_add, quad_sub, quad_smul] at hAMv
    have h3 := quad_le_trace_of_posSemidef hKpsd v
    have htr : Matrix.trace (avgMat s (fun i => S i - (2 : ℝ) • B + B * U i * B)) =
        (s.card : ℝ)⁻¹ * ∑ i ∈ s, Matrix.trace (S i - (2 : ℝ) • B + B * U i * B) := by
      unfold avgMat
      rw [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    rw [htr] at h3
    have hQ := avgMat_chain_K s hs S U B
    have h3' : vecDot v (matVecMul (avgMat s (fun i => S i - (2 : ℝ) • B + B * U i * B)) v) =
        vecDot v (matVecMul (avgMat s S) v) - 2 * vecDot v (matVecMul B v) +
          vecDot v (matVecMul (B * avgMat s U * B) v) := by
      rw [hQ, quad_add, quad_sub, quad_smul]
    rw [h3'] at h3
    rw [quad_sub]
    nlinarith [hUlow, hS0low, hAMv, h3]

theorem quad_sandwich (B U : Mat d) (hB : B.IsSymm) (v : Vec d) :
    vecDot v (matVecMul (B * U * B) v) = vecDot (matVecMul B v) (matVecMul U (matVecMul B v)) := by
  simp only [vecDot_eq_dotProduct, matVecMul_eq_mulVec, ← Matrix.mulVec_mulVec]
  have hv : Matrix.vecMul v B = B.mulVec v := by
    rw [← Matrix.vecMul_transpose, hB.eq]
  rw [Matrix.dotProduct_mulVec, hv]

theorem diag_eq_quad (A : Mat d) (i : Fin d) :
    A i i = vecDot (Pi.single i 1) (matVecMul A (Pi.single i 1)) := by
  classical
  simp [vecDot, matVecMul, Pi.single_apply]

theorem trace_eq_sum_quad (A : Mat d) :
    Matrix.trace A = ∑ i : Fin d, vecDot (Pi.single i 1) (matVecMul A (Pi.single i 1)) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun i _ => diag_eq_quad A i

end SubdiffusiveProcess.Variance
