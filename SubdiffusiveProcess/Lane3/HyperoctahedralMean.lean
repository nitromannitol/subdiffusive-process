import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic




open Matrix

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

/-- Invariance under the coordinate reflections and the coordinate
permutations forces a matrix to be scalar (paper lines 3468-3470). -/
theorem eq_smul_one_of_hyperoctahedral_invariant (d : ℕ) (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hrefl : ∀ (i j k : Fin d),
      A j k = (if j = i then -(1 : ℝ) else 1) * (if k = i then -(1 : ℝ) else 1) * A j k)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) (j k : Fin d), A (σ j) (σ k) = A j k) :
    ∃ c : ℝ, A = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hz : Fin d := ⟨0, hd⟩
  refine ⟨A hz hz, ?_⟩
  ext j k
  by_cases hjk : j = k
  · subst hjk
    have hswap := hperm (Equiv.swap hz j) hz hz
    rw [Equiv.swap_apply_left] at hswap
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact hswap
  · have h := hrefl j j k
    rw [if_pos rfl, if_neg (fun hkj => hjk hkj.symm)] at h
    have hzero : A j k = 0 := by linarith [h]
    simp only [Matrix.smul_apply, Matrix.one_apply_ne hjk, smul_eq_mul, mul_zero]
    exact hzero

/-- A scalar matrix of zero trace vanishes (paper lines 3472-3475). -/
theorem eq_zero_of_smul_one_of_trace_eq_zero (d : ℕ) (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (hA : A = c • (1 : Matrix (Fin d) (Fin d) ℝ))
    (htr : Matrix.trace A = 0) : A = 0 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have htrace : Matrix.trace A = c * (d : ℝ) := by
    rw [hA, Matrix.trace_smul, Matrix.trace_one]
    simp [Fintype.card_fin]
  have hc : c = 0 := by
    rw [htrace] at htr
    exact (mul_eq_zero.mp htr).resolve_right (ne_of_gt hdR)
  rw [hA, hc, zero_smul]


/-- The diagonal entry as a quadratic form value at a standard basis vector. -/
theorem single_dotProduct_mulVec_single {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ A.mulVec (Pi.single i (1 : ℝ)) = A i i := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']

/-- `c_k ∈ [m, M]`, paper line 3461: the ratio of traces inherits the
pointwise form order. -/
theorem trace_ratio_mem_Icc_of_form_order {d : ℕ} (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (m M : ℝ) (htr : 0 < Matrix.trace AE)
    (hord : ∀ x : Fin d → ℝ, m * (x ⬝ᵥ AE.mulVec x) ≤ x ⬝ᵥ AF.mulVec x ∧
      x ⬝ᵥ AF.mulVec x ≤ M * (x ⬝ᵥ AE.mulVec x)) :
    m ≤ Matrix.trace AF / Matrix.trace AE ∧
      Matrix.trace AF / Matrix.trace AE ≤ M := by
  have hdiag : ∀ i : Fin d, m * AE i i ≤ AF i i ∧ AF i i ≤ M * AE i i := by
    intro i
    have h := hord (Pi.single i (1 : ℝ))
    rwa [single_dotProduct_mulVec_single, single_dotProduct_mulVec_single] at h
  have hlow : m * Matrix.trace AE ≤ Matrix.trace AF := by
    rw [Matrix.trace, Matrix.trace, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hdiag i).1
  have hup : Matrix.trace AF ≤ M * Matrix.trace AE := by
    rw [Matrix.trace, Matrix.trace, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hdiag i).2
  constructor
  · rw [le_div_iff₀ htr]
    linarith
  · rw [div_le_iff₀ htr]
    linarith

end Lane3
end SubdiffusiveProcess
