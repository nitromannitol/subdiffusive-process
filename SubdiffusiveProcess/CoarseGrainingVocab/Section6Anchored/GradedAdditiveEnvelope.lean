module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GammaTwoEnvelope

@[expose] public section

/-!
# The additive form of the graded `Γ₂` envelope

`GammaTwoEnvelope.lean` delivers the *multiplicative* envelope
`X k i ω ≤ C_ω · √(k+1) · a k`: the random constant multiplies the graded
price.  The value-maximal display  is *additive*,

```
max_{z, j} |∑_{k ≤ j} (g_k(z) - g_k(0))| ≤ C δ n + C_ω,
```

with a **deterministic** slope and the random constant only additive.  The
distinction is not cosmetic downstream: the slope becomes the exponent `κ` of
`e.finite.cutoff.coefficient.polynomial.growth`, which the statement
requires to be deterministic and in `(0,1)`.  A multiplicative envelope would
produce a random `κ`.

The additive form costs nothing extra probabilistically.  Fix the threshold at
`t = 1` in the row estimate `measureReal_sqrtGradedRowEvent_le`; the row
failure probability is then already `exp (-2(k+1))`, summable in `k`, so
Borel–Cantelli gives an almost sure *last* bad row.  Above it the deterministic
threshold `λ √(k+1) · a k` holds outright, and the finitely many rows below it
are dominated by one finite maximum over a finite index set.

As in `GammaTwoEnvelope.lean`, Borel–Cantelli is
`MeasureTheory.ae_finite_setOf_mem`, which is outer-measure valued: **no
measurability of the bad events is used**.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {mu : Measure Ω}

/-! ## The row sum at the unit threshold -/

private theorem summable_unitRowBound :
    Summable fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) * (1 : ℝ) ^ 2)) := by
  have hq0 : (0 : ℝ) ≤ Real.exp (-2) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 : ℝ) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (by norm_num : (-2 : ℝ) < 0)
  have hgeom : Summable fun k : ℕ => Real.exp (-2 : ℝ) ^ (k + 1) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_right _).congr
      fun k => (pow_succ _ k).symm
  refine hgeom.congr fun k => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem sqrtGradedScale_nonneg {lam : ℝ} {a : ℕ → ℝ} (hlam : 1 ≤ lam)
    (ha : ∀ k, 0 ≤ a k) (k : ℕ) : 0 ≤ sqrtGradedScale lam a k := by
  refine mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (ha k)

/-! ## The envelope -/

/-- **The additive graded `Γ₂` envelope.**  Rows `I k` of finitely many
observables with a common `Γ₂` scale `a k` and row entropy
`card (I k) ≤ exp (growth (k+1))` obey, almost surely and simultaneously in
every row, the *deterministic* threshold `λ √(k+1) · a k` up to one additive
almost surely finite random constant.

This is the shape of `e.finite.cutoff.value.maximal.bound`
with a deterministic slope plus `C_ω`. -/
theorem ae_exists_forall_le_sqrtGradedScale_add_of_isBigOWith_gammaTwo
    [IsFiniteMeasure mu] (I : ℕ → Finset ι) (X : ℕ → ι → Ω → ℝ) (a : ℕ → ℝ)
    {growth lam : ℝ} (hgrowth : 0 ≤ growth) (hlam : 1 ≤ lam)
    (hlam2 : growth + 2 ≤ lam ^ 2) (ha : ∀ k, 0 ≤ a k)
    (hcard : ∀ k, ((I k).card : ℝ) ≤ Real.exp (growth * ((k : ℝ) + 1)))
    (hX : ∀ k, ∀ i ∈ I k, IsBigOWith mu (gammaSigma 2) (X k i) (a k)) :
    ∀ᵐ omega ∂mu, ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ i ∈ I k,
      X k i omega ≤ sqrtGradedScale lam a k + C := by
  set E : ℕ → Set Ω := fun k => sqrtGradedRowEvent I X a lam 1 k with hE_def
  have hrow : ∀ k, mu.real (E k) ≤ Real.exp (-(2 * ((k : ℝ) + 1) * (1 : ℝ) ^ 2)) :=
    measureReal_sqrtGradedRowEvent_le (mu := mu) I X a hgrowth hlam hlam2
      le_rfl hcard hX
  have hEbound : ∀ k,
      mu (E k) ≤ ENNReal.ofReal (Real.exp (-(2 * ((k : ℝ) + 1) * (1 : ℝ) ^ 2))) := by
    intro k
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top mu (E k))
      (Real.exp_pos _).le).2 (hrow k)
  have htsum : (∑' k : ℕ, mu (E k)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le)
      summable_unitRowBound]
    exact ENNReal.ofReal_ne_top
  refine (MeasureTheory.ae_finite_setOfPred_mem (μ := mu) (s := E) htsum).mono ?_
  intro omega hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨B, hB⟩ :=
    ((Finset.range (N + 1)).biUnion
      fun k => (I k).image fun i => X k i omega).exists_le
  refine ⟨max 0 B, le_max_left _ _, fun k i hi => ?_⟩
  have hscale : 0 ≤ sqrtGradedScale lam a k := sqrtGradedScale_nonneg hlam ha k
  by_cases hk : k ≤ N
  · have hmem : X k i omega ∈
        (Finset.range (N + 1)).biUnion fun k => (I k).image fun i => X k i omega :=
      Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega),
        Finset.mem_image_of_mem _ hi⟩
    have hle := hB _ hmem
    have := le_max_right (0 : ℝ) B
    linarith
  · have hnotrow : omega ∉ E k := by
      intro hmem
      exact hk (hN (show k ∈ {k : ℕ | omega ∈ E k} from hmem))
    have hnot : omega ∉ upperTailEvent (X k i) (sqrtGradedScale lam a k * 1) := by
      intro hmem
      exact hnotrow (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hmem⟩⟩)
    rw [mem_upperTailEvent, not_lt, mul_one] at hnot
    have := le_max_left (0 : ℝ) B
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
