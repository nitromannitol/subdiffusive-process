import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Finite-dimensional polarization of response forms

A pair `(R false, R true)` of nonnegative symmetric quadratic forms on `ℝ^d` whose relative
difference from a reference pair is controlled on the polarization bank
`{e_i} ∪ {e_i + e_j}` has maximal normalized eigenvalue within a dimensional multiple of the
error.  This is pure finite-dimensional linear algebra (polarization of symmetric forms and the
Rayleigh quotient); no PDE input is used.
-/

open Finset

namespace SubdiffusiveProcess.Polarization

variable {d : ℕ}

/-- The quadratic form of a matrix. -/
def quadForm (G : Fin d → Fin d → ℝ) (p : Fin d → ℝ) : ℝ := ∑ i, ∑ j, p i * p j * G i j

theorem quadForm_smul (G : Fin d → Fin d → ℝ) (t : ℝ) (p : Fin d → ℝ) :
    quadForm G (t • p) = t ^ 2 * quadForm G p := by
  unfold quadForm
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem quadForm_sub (G H : Fin d → Fin d → ℝ) (p : Fin d → ℝ) :
    quadForm G p - quadForm H p = quadForm (fun i j => G i j - H i j) p := by
  unfold quadForm
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

theorem quadForm_add (G H : Fin d → Fin d → ℝ) (p : Fin d → ℝ) :
    quadForm G p + quadForm H p = quadForm (fun i j => G i j + H i j) p := by
  unfold quadForm
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

theorem quadForm_const_mul (G : Fin d → Fin d → ℝ) (c : ℝ) (p : Fin d → ℝ) :
    c * quadForm G p = quadForm (fun i j => c * G i j) p := by
  unfold quadForm
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

/-- Values on the basis vector `e_i`. -/
theorem quadForm_single (G : Fin d → Fin d → ℝ) (i : Fin d) :
    quadForm G (Pi.single i 1) = G i i := by
  unfold quadForm
  rw [sum_eq_single i]
  · rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · simp
  · intro k _ hk; simp [Pi.single_apply, hk]
  · simp

/-- Polarization: the value at `e_i + e_j` of a symmetric form. -/
theorem quadForm_single_add (G : Fin d → Fin d → ℝ) (hG : ∀ i j, G i j = G j i) (i j : Fin d) :
    quadForm G (Pi.single i 1 + Pi.single j 1) = G i i + G j j + 2 * G i j := by
  classical
  unfold quadForm
  have h : ∀ a b : Fin d, ((Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) a) *
      ((Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) b) * G a b =
      (if a = i then 1 else 0) * (if b = i then 1 else 0) * G a b +
      (if a = i then 1 else 0) * (if b = j then 1 else 0) * G a b +
      (if a = j then 1 else 0) * (if b = i then 1 else 0) * G a b +
      (if a = j then 1 else 0) * (if b = j then 1 else 0) * G a b := by
    intro a b
    simp only [Pi.add_apply, Pi.single_apply]
    ring
  simp only [h, sum_add_distrib]
  simp [sum_ite_eq', hG j i]
  ring

/-- Entries are recovered from the values on the polarization bank. -/
theorem entry_bound (G : Fin d → Fin d → ℝ) (hG : ∀ i j, G i j = G j i) {M : ℝ}
    (h1 : ∀ i, |quadForm G (Pi.single i 1)| ≤ M)
    (h2 : ∀ i j, |quadForm G (Pi.single i 1 + Pi.single j 1)| ≤ M) (i j : Fin d) :
    |G i j| ≤ 2 * M := by
  have e1 := h1 i
  have e2 := h1 j
  have e3 := h2 i j
  rw [quadForm_single] at e1 e2
  rw [quadForm_single_add G hG] at e3
  rw [abs_le] at e1 e2 e3 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-- A matrix with bounded entries has bounded Rayleigh quotients on the unit sphere. -/
theorem quadForm_le_of_entries (G : Fin d → Fin d → ℝ) {m : ℝ} (hm : ∀ i j, |G i j| ≤ m)
    (e : Fin d → ℝ) (he : ∑ i, e i ^ 2 = 1) : |quadForm G e| ≤ d * m := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    simp [quadForm]
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm ⟨0, hdpos⟩ ⟨0, hdpos⟩)
  calc |quadForm G e| ≤ ∑ i, ∑ j, |e i * e j * G i j| := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |e i| * |e j| * m := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hm i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = m * (∑ i, |e i|) ^ 2 := by
        rw [sq, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        ring
    _ ≤ m * (d * ∑ i, e i ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hm0
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin d))) (f := fun i => |e i|)
        simpa [sq_abs] using this
    _ = d * m := by rw [he]; ring

end SubdiffusiveProcess.Polarization
