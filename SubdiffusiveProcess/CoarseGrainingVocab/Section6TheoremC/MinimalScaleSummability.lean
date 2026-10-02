import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory
open scoped ENNReal

/-! ### The geometric domination -/

/-- The minimal-scale tail is dominated termwise by a geometric sequence.
The positive part `(k-A)_+` is at least `k - A`, so the exponential decays at
least at rate `e/D` in `k`. -/
theorem expTail_le_geometric {A C D e : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (he : 0 < e) (k : ℕ) :
    C * Real.exp (-(e * max ((k : ℝ) - A) 0) / D) ≤
      C * Real.exp (e / D * A) * Real.exp (-(e / D)) ^ k := by
  have hmax : (k : ℝ) - A ≤ max ((k : ℝ) - A) 0 := le_max_left _ _
  have h1 : e * (k : ℝ) - e * A ≤ e * max ((k : ℝ) - A) 0 := by
    have h := mul_le_mul_of_nonneg_left hmax he.le
    linarith
  have hexp : -(e * max ((k : ℝ) - A) 0) / D ≤
      e / D * A + -(e / D) * (k : ℝ) := by
    rw [div_le_iff₀ hD]
    have hrw : (e / D * A + -(e / D) * (k : ℝ)) * D = e * A - e * (k : ℝ) := by
      field_simp
      ring
    rw [hrw]
    linarith
  calc C * Real.exp (-(e * max ((k : ℝ) - A) 0) / D)
      ≤ C * Real.exp (e / D * A + -(e / D) * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hC
    _ = C * Real.exp (e / D * A) * Real.exp (-(e / D)) ^ k := by
        rw [Real.exp_add, ← Real.exp_nat_mul, mul_comm (-(e / D)) (k : ℝ)]
        ring

/-- The minimal-scale tail of `e.limiting.Holder.minimal.scale` is summable. -/
theorem summable_expTail {A C D e : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (he : 0 < e) :
    Summable fun k : ℕ ↦ C * Real.exp (-(e * max ((k : ℝ) - A) 0) / D) := by
  have hratio : Real.exp (-(e / D)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (div_pos he hD))
  have hgeom : Summable fun k : ℕ ↦
      C * Real.exp (e / D * A) * Real.exp (-(e / D)) ^ k :=
    (summable_geometric_of_lt_one (Real.exp_nonneg _) hratio).mul_left _
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hgeom
  · exact mul_nonneg hC (Real.exp_nonneg _)
  · exact expTail_le_geometric hC hD he k

/-! ### Finiteness of the total mass -/

/-- The `ℝ≥0∞` sum of the minimal-scale tail bounds is finite, which is the
hypothesis of Borel–Cantelli. -/
theorem tsum_ofReal_expTail_ne_top {A C D e : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (he : 0 < e) :
    (∑' k : ℕ, ENNReal.ofReal
      (C * Real.exp (-(e * max ((k : ℝ) - A) 0) / D))) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k ↦ mul_nonneg hC (Real.exp_nonneg _))
    (summable_expTail hC hD he)]
  exact ENNReal.ofReal_ne_top

/-! ### The Borel–Cantelli conclusion -/



theorem ae_eventually_not_mem_of_expTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A C D e : ℝ} (hC : 0 ≤ C) (hD : 0 < D) (he : 0 < e)
    {s : ℕ → Set Ω}
    (hs : ∀ m : ℕ, μ (s m) ≤
      ENNReal.ofReal (C * Real.exp (-(e * max ((m : ℝ) - A) 0) / D))) :
    ∀ᵐ ω ∂μ, ∀ᶠ m : ℕ in Filter.atTop, ω ∉ s m := by
  refine measure_setOf_frequently_eq_zero ?_
  refine ne_top_of_le_ne_top (tsum_ofReal_expTail_ne_top (A := A) hC hD he) ?_
  exact ENNReal.tsum_le_tsum hs

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
