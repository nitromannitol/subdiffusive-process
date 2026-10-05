module

public import SubdiffusiveProcess.Analysis.RelativeScoreComparison
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! Discounted finite suprema preserve one-sided relative comparison.
All extended-valued coordinates are assumed finite on the finite index set;
the lemma makes no assertion about an infinite supremum or discarded tail.
-/
open scoped ENNReal
namespace SubdiffusiveProcess

/-- A finite discounted supremum inherits the same one-sided relative error. -/
theorem finite_discounted_relative_comparison {I : Type*} (S : Finset I)
    (w a b : I → ℝ≥0∞) (eta : ℝ) (heta : 0 ≤ eta)
    (hw : ∀ i ∈ S, w i ≤ 1) (ha : ∀ i ∈ S, a i ≠ ⊤) (hb : ∀ i ∈ S, b i ≠ ⊤)
    (hcomp : ∀ i ∈ S, (a i).toReal ≤ (1 + eta) * (b i).toReal + eta) :
    (S.sup (fun i => w i * a i)).toReal ≤
      (1 + eta) * (S.sup (fun i => w i * b i)).toReal + eta := by
  have hwfin i hi : w i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hw i hi)
  have hBfin : S.sup (fun i => w i * b i) ≠ ⊤ := by
    apply ne_of_lt
    apply (Finset.sup_lt_iff (by exact ENNReal.zero_lt_top)).mpr
    intro i hi
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (hwfin i hi) (hb i hi))
  have heta1 : 0 ≤ 1 + eta := by linarith only [heta]
  apply ENNReal.toReal_le_of_le_ofReal
    (add_nonneg (mul_nonneg heta1 ENNReal.toReal_nonneg) heta)
  apply Finset.sup_le
  intro i hi
  rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top (hwfin i hi) (ha i hi))]
  apply ENNReal.ofReal_le_ofReal
  rw [ENNReal.toReal_mul]
  have hw1 : (w i).toReal ≤ 1 :=
    (ENNReal.toReal_mono ENNReal.one_ne_top (hw i hi)).trans_eq ENNReal.toReal_one
  have hstep := discounted_relative_le ENNReal.toReal_nonneg hw1 heta (hcomp i hi)
  have hupper := ENNReal.toReal_mono hBfin
    (Finset.le_sup (f := fun i => w i * b i) hi)
  rw [ENNReal.toReal_mul] at hupper
  exact hstep.trans (add_le_add (mul_le_mul_of_nonneg_left hupper heta1) le_rfl)

end SubdiffusiveProcess
