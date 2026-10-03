module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

@[expose] public section

/-! Finite nonnegative weighted sums preserve a common Lᵖ moment bound.
No independence assumption or infinite summation is involved. -/

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess

/-- A finite weighted envelope has moment bound equal to the sum of the weighted bounds. -/
theorem finite_weighted_memLp_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (F : ι → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hmem : ∀ i, MemLp (F i) p μ)
    (hbound : ∀ i, eLpNorm (F i) p μ ≤ ENNReal.ofReal C) :
    MemLp (fun omega => ∑ i, weight i * F i omega) p μ ∧
      eLpNorm (fun omega => ∑ i, weight i * F i omega) p μ ≤
        ENNReal.ofReal ((∑ i, weight i) * C) := by
  have hwm : ∀ i, MemLp (fun omega => weight i * F i omega) p μ :=
    fun i => by simpa only [Pi.smul_def, smul_eq_mul] using (hmem i).const_smul (weight i)
  refine ⟨memLp_finset_sum Finset.univ (fun i _ => hwm i), ?_⟩
  have hsum := eLpNorm_sum_le (μ := μ) (p := p) (s := Finset.univ)
    (f := fun i omega => weight i * F i omega) hp
  have heq : (fun omega => ∑ i, weight i * F i omega) =
      ∑ i, (fun omega => weight i * F i omega) := by
    funext omega
    simp only [Finset.sum_apply]
  refine (congrArg (fun g : Ω → ℝ => eLpNorm g p μ) heq).le.trans (hsum.trans ?_)
  rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (hweight i) hC)]
  apply Finset.sum_le_sum
  intro i _hi
  calc
    eLpNorm (fun omega => weight i * F i omega) p μ ≤
        ‖weight i‖ₑ * eLpNorm (F i) p μ := eLpNorm_const_smul_le (c := weight i) (f := F i) (p := p) (μ := μ)
    _ ≤ ENNReal.ofReal (weight i) * ENNReal.ofReal C := by
      rw [Real.enorm_eq_ofReal (hweight i)]
      exact mul_le_mul_right (hbound i) _
    _ = ENNReal.ofReal (weight i * C) := (ENNReal.ofReal_mul (hweight i)).symm

end SubdiffusiveProcess
