module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section

/-!
# Relative scalar responses of a pair of symmetric matrices on the affine slopes

For symmetric matrices `A` (the reference affine energy matrix) and `B`, `relativeResponse A B c v`
is `(v·Bv − c v·Av) / tr A`. The finite set of slopes `e_i`, `e_i + e_j` determines a symmetric
matrix by polarization (`entry_polarization`); under positive semidefiniteness of `A`, `tr A > 0`
and the form order `m A ≤ B ≤ M A`, the relative response is bounded by `4 M` on the slopes for every
`c ∈ [0, M]` (`relativeResponse_abs_le`).
-/

open scoped BigOperators

namespace SubdiffusiveProcess.Lane3.RelSlopes
noncomputable section

/-- The relative scalar response `(p·A_F p - c p·A_E p)/tr A_E` of paper line 3405
at a slope `v`. -/
def relativeResponse {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  (v ⬝ᵥ B.mulVec v - c * (v ⬝ᵥ A.mulVec v)) / Matrix.trace A

/-- The finite affine set of slopes `e_i`, `e_i + e_j` used for polarization. -/
def IsAffineSlope {d : ℕ} (v : Fin d → ℝ) : Prop :=
  (∃ i : Fin d, v = Pi.single i (1 : ℝ)) ∨
    (∃ i j : Fin d, v = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))

theorem single_dotProduct_mulVec_single {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    Pi.single i (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single j (1 : ℝ)) = A i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem symm_apply_swap {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) (i j : Fin d) : A j i = A i j := by
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.transpose_apply] using h

theorem pair_quadForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (i j : Fin d) :
    (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) ⬝ᵥ
        A.mulVec (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) =
      A i i + A j j + 2 * A i j := by
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    symm_apply_swap hA i j]
  ring

theorem diff_quadForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (i j : Fin d) :
    (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ⬝ᵥ
        A.mulVec (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) =
      A i i + A j j - 2 * A i j := by
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    symm_apply_swap hA i j]
  ring

/-- Polarization: every entry of the centred matrix is a combination of three
relative scalar responses (paper line 3446, "after polarization over the finite
affine set"). -/
theorem entry_polarization {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (c : ℝ) (i j : Fin d) :
    ((Matrix.trace A)⁻¹ • (B - c • A)) i j =
      (relativeResponse A B c (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)) -
        relativeResponse A B c (Pi.single i (1 : ℝ)) -
        relativeResponse A B c (Pi.single j (1 : ℝ))) / 2 := by
  simp only [relativeResponse, pair_quadForm A hA, pair_quadForm B hB,
    single_dotProduct_mulVec_single, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The trace is the sum of the diagonal quadratic values. -/
theorem trace_eq_sum_quadForm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace A = ∑ j : Fin d,
      Pi.single j (1 : ℝ) ⬝ᵥ A.mulVec (Pi.single j (1 : ℝ)) := by
  simp only [single_dotProduct_mulVec_single]
  rfl

/-- On a slope, the quadratic value of a positive semidefinite matrix is at most
four times its trace. -/
theorem quadForm_le_four_trace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ A.mulVec v)
    (v : Fin d → ℝ) (hv : IsAffineSlope v) :
    v ⬝ᵥ A.mulVec v ≤ 4 * Matrix.trace A := by
  have hdiag : ∀ j : Fin d, 0 ≤ A j j := by
    intro j
    have h := hpsd (Pi.single j (1 : ℝ))
    rwa [single_dotProduct_mulVec_single] at h
  have hle : ∀ j : Fin d, A j j ≤ Matrix.trace A := by
    intro j
    have h := Finset.single_le_sum (f := fun l : Fin d => A l l)
      (fun l _ => hdiag l) (Finset.mem_univ j)
    simpa [Matrix.trace, Matrix.diag] using h
  have htr : 0 ≤ Matrix.trace A := (hdiag ⟨0, by
    rcases hv with ⟨i, _⟩ | ⟨i, _, _⟩ <;> exact lt_of_le_of_lt (Nat.zero_le _) i.2⟩).trans
      (hle _)
  rcases hv with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · rw [single_dotProduct_mulVec_single]
    linarith [hle i]
  · rw [pair_quadForm A hA]
    have hd := hpsd (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))
    rw [diff_quadForm A hA] at hd
    linarith [hle i, hle j]

/-- The relative scalar is bounded by `4 M` on the slopes under the form order. -/
theorem relativeResponse_abs_le {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ A.mulVec v)
    (m M c : ℝ) (hm : 0 ≤ m) (hc0 : 0 ≤ c) (hcM : c ≤ M)
    (htr : 0 < Matrix.trace A)
    (hord : ∀ v : Fin d → ℝ, m * (v ⬝ᵥ A.mulVec v) ≤ v ⬝ᵥ B.mulVec v ∧
      v ⬝ᵥ B.mulVec v ≤ M * (v ⬝ᵥ A.mulVec v))
    (v : Fin d → ℝ) (hv : IsAffineSlope v) :
    |relativeResponse A B c v| ≤ 4 * M := by
  have hq := quadForm_le_four_trace A hA hpsd v hv
  have hq0 := hpsd v
  have hB0 : 0 ≤ v ⬝ᵥ B.mulVec v := le_trans (mul_nonneg hm hq0) (hord v).1
  have hBle : v ⬝ᵥ B.mulVec v ≤ M * (4 * Matrix.trace A) :=
    (hord v).2.trans (mul_le_mul_of_nonneg_left hq (hc0.trans hcM))
  have hcle : c * (v ⬝ᵥ A.mulVec v) ≤ M * (4 * Matrix.trace A) :=
    mul_le_mul hcM hq hq0 (hc0.trans hcM)
  have hc0' : 0 ≤ c * (v ⬝ᵥ A.mulVec v) := mul_nonneg hc0 hq0
  unfold relativeResponse
  rw [abs_div, abs_of_pos htr, div_le_iff₀ htr, abs_le]
  constructor <;> nlinarith

end
end SubdiffusiveProcess.Lane3.RelSlopes
