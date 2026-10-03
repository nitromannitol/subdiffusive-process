module

public import SubdiffusiveProcess.Lane3.RelativeResponseSlopes
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators
namespace SubdiffusiveProcess.Lane3

/-- All real slopes define a closed matrix locus, so no countable-slope replacement is needed. -/
theorem measurableSet_trace_coercivity {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ i j, Measurable (fun ω => A ω i j))
    (c : ℝ) :
    MeasurableSet {ω | 0 < Matrix.trace (A ω) ∧
      ∀ x : Fin d → ℝ, c * Matrix.trace (A ω) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A ω).mulVec x} := by
  letI : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))
  letI : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have hm : Measurable A := measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hA i)
  have hc : IsClosed {B : Matrix (Fin d) (Fin d) ℝ |
      ∀ x : Fin d → ℝ, c * Matrix.trace B * (x ⬝ᵥ x) ≤ x ⬝ᵥ B.mulVec x} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_le
    · simp only [Matrix.trace, Matrix.diag]
      fun_prop
    · simp only [dotProduct, Matrix.mulVec]
      fun_prop
  have ht : Measurable (fun ω => Matrix.trace (A ω)) := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.measurable_sum _ (fun i _ => hA i i)
  exact (measurableSet_lt measurable_const ht).inter (hc.measurableSet.preimage hm)

/-- A positive lower quadratic bound forces positive trace in positive dimension. -/
theorem trace_pos_of_quadratic_lower {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℝ) (lo : ℝ) (hlo : 0 < lo)
    (hA : ∀ x : Fin d → ℝ, lo * (x ⬝ᵥ x) ≤ x ⬝ᵥ A.mulVec x) :
    0 < Matrix.trace A := by
  have hd : 0 < d := NeZero.pos d
  have hdiag : ∀ i : Fin d, lo ≤ A i i := by
    intro i
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hA (Pi.single i 1)
  have hsum : (d : ℝ) * lo ≤ Matrix.trace A := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdiag i)
    simpa [Matrix.trace, Matrix.diag] using h
  exact (mul_pos (Nat.cast_pos.mpr hd) hlo).trans_le hsum

/-- Positive scalar normalization preserves the trace lower quadratic inequality. -/
theorem trace_coercivity_smul {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (s c : ℝ) (hs : 0 < s)
    (ht : 0 < Matrix.trace A)
    (hA : ∀ x : Fin d → ℝ, c * Matrix.trace A * (x ⬝ᵥ x) ≤ x ⬝ᵥ A.mulVec x) :
    0 < Matrix.trace (s • A) ∧
      ∀ x : Fin d → ℝ, c * Matrix.trace (s • A) * (x ⬝ᵥ x) ≤
        x ⬝ᵥ (s • A).mulVec x := by
  constructor
  · simpa using mul_pos hs ht
  · intro x
    have h := mul_le_mul_of_nonneg_left (hA x) hs.le
    simpa [Matrix.trace_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      mul_assoc, mul_left_comm] using h

end SubdiffusiveProcess.Lane3
