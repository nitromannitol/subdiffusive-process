module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Numeric

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper

/-- The cell-maximum step of `mfd:lem-coercivity`, paper lines 440–441.

Carried-input tick list:
- Probability space and finite real exponent `1 ≤ q`: the standing setting of
  the summation at lines 448–454.
- Nonnegative a.e. strongly measurable cell variables and bounds `Cc k ≥ 0`:
  the explicit data of the parent finite-sum statement. In the paper's
  application their moment bound is equation `eq:mfd-cell-moment`, lines
  435–439; its proof is not assumed here for arbitrary cell data.
- The concrete range has `3 ^ (d * k)` cells, as counted at lines 440–441,
  with negative depth reindexed by `k : ℕ`.

Concludes both measurability of the actual finite maximum and its moment
bound. Neither property of the maximum is a hypothesis. The geometric
discount and the disorder threshold belong to the subsequent summation.
-/
theorem lane4_cell_maximum_moment :
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ)
    (d : ℕ) (q : ℝ), 0 < d → 1 ≤ q →
  ∀ (Y : ℕ → ℕ → Ω → ℝ) (Cc : ℕ → ℝ), (∀ k, 0 ≤ Cc k) →
    (∀ k j, 0 ≤ Y k j) →
    (∀ k j, AEStronglyMeasurable (Y k j) μ) →
    (∀ k j, eLpNorm (Y k j) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (Cc k)) →
  ∀ k : ℕ,
    AEStronglyMeasurable (fun om =>
      (Finset.range (3 ^ (d * k)) |>.sup'
        (Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by norm_num))) fun j => Y k j om)) μ ∧
    eLpNorm (fun om =>
      (Finset.range (3 ^ (d * k)) |>.sup'
        (Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by norm_num))) fun j => Y k j om))
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cc k * (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
  intro Ω mΩ μ hμ d q hd hq Y Cc hCc hY hYmeas hYmom k
  let s : Finset ℕ := Finset.range (3 ^ (d * k))
  let hs : s.Nonempty := by
    dsimp [s]
    exact Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by norm_num))
  let f : Ω → ℝ := fun om => s.sup' hs (fun j => Y k j om)
  have hfmeas : AEStronglyMeasurable f μ := by
    have hfun : AEStronglyMeasurable (s.sup' hs (fun j : ℕ => Y k j)) μ := by
      refine Finset.sup'_induction hs (p := fun g : Ω → ℝ => AEStronglyMeasurable g μ)
        (fun j : ℕ => Y k j) ?_ ?_
      · intro f₁ hf₁ f₂ hf₂
        exact hf₁.sup hf₂
      · intro j hj
        exact hYmeas k j
    have heq : (s.sup' hs (fun j : ℕ => Y k j)) = f := by
      funext om
      simp [f, Finset.sup'_apply]
    exact heq ▸ hfun
  refine ⟨?_, ?_⟩
  · simpa [f, s, hs] using hfmeas
  · have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hp0 : ENNReal.ofReal q ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hqpos]
    have hptop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
    let g : Ω → ℝ := fun om => f om ^ q
    let h : ℕ → Ω → ℝ := fun j om => Y k j om ^ q
    have hf_nonneg : ∀ om, 0 ≤ f om := by
      intro om
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hs (fun j => Y k j om)
      rw [show f om = Y k j om by simpa [f] using hjeq]
      exact hY k j om
    have hpow_le_sum : ∀ om, g om ≤ (∑ j ∈ s, h j om) := by
      intro om
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' hs (fun j => Y k j om)
      change f om ^ q ≤ ∑ j ∈ s, Y k j om ^ q
      rw [show f om = Y k j om by simpa [f] using hjeq]
      refine Finset.single_le_sum (s := s) (f := fun i => Y k i om ^ q) ?_ hj
      intro i hi
      exact Real.rpow_nonneg (hY k i om) q
    have hsum_nonneg : ∀ om, 0 ≤ (∑ j ∈ s, h j om) := by
      intro om
      exact Finset.sum_nonneg (fun j hj => Real.rpow_nonneg (hY k j om) q)
    have hg_le : eLpNorm g 1 μ ≤ eLpNorm (∑ j ∈ s, h j) 1 μ := by
      apply eLpNorm_mono_real ((hfmeas.aemeasurable.pow_const q).aestronglyMeasurable)
      intro om
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf_nonneg om) q)]
      simpa only [Finset.sum_apply] using hpow_le_sum om
    have hsum_le : eLpNorm (∑ j ∈ s, h j) 1 μ ≤ ∑ j ∈ s, eLpNorm (h j) 1 μ := by
      exact eLpNorm_sum_le (by norm_num)
    have hterm : ∀ j ∈ s, eLpNorm (h j) 1 μ ≤ (ENNReal.ofReal (Cc k)) ^ q := by
      intro j hj
      have hpow := eLpNorm_norm_rpow (μ := μ) (p := (1 : ℝ≥0∞)) (Y k j) (hYmeas k j) hqpos
      have hnonneg : ∀ om, 0 ≤ Y k j om := fun om => hY k j om
      have hrewrite : eLpNorm (h j) 1 μ = eLpNorm (Y k j) (ENNReal.ofReal q) μ ^ q := by
        simpa [h, Real.norm_eq_abs, abs_of_nonneg, hnonneg] using hpow
      rw [hrewrite]
      exact ENNReal.rpow_le_rpow (hYmom k j) hqpos.le
    have hsum_bound : eLpNorm g 1 μ ≤ (s.card : ℝ≥0∞) * (ENNReal.ofReal (Cc k)) ^ q := by
      calc
        eLpNorm g 1 μ ≤ eLpNorm (∑ j ∈ s, h j) 1 μ := hg_le
        _ ≤ ∑ j ∈ s, eLpNorm (h j) 1 μ := hsum_le
        _ ≤ ∑ _j ∈ s, (ENNReal.ofReal (Cc k)) ^ q :=
          Finset.sum_le_sum (fun j hj => hterm j hj)
        _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal (Cc k)) ^ q := by
          simp [Finset.sum_const, mul_comm]
    have hnorm_pow : eLpNorm f (ENNReal.ofReal q) μ ^ q = eLpNorm g 1 μ := by
      have hpow := eLpNorm_norm_rpow (μ := μ) (p := (1 : ℝ≥0∞)) f hfmeas hqpos
      simpa [g, Real.norm_eq_abs, abs_of_nonneg, hf_nonneg, one_mul] using hpow.symm
    have hpow_bound : eLpNorm f (ENNReal.ofReal q) μ ^ q ≤
        (s.card : ℝ≥0∞) * (ENNReal.ofReal (Cc k)) ^ q := by
      rw [hnorm_pow]
      exact hsum_bound
    have hqinv : q * (1 / q) = 1 := by
      field_simp
    have hcard_root : (s.card : ℝ≥0∞) ^ (1 / q) =
        ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
      rw [show s.card = 3 ^ (d * k) by simp [s], Nat.cast_pow]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
      norm_num
      congr 1
    have hC_root : ((ENNReal.ofReal (Cc k)) ^ q) ^ (1 / q) =
        ENNReal.ofReal (Cc k) := by
      rw [← ENNReal.rpow_mul, hqinv, ENNReal.rpow_one]
    have hbase_target :
        ((s.card : ℝ≥0∞) * (ENNReal.ofReal (Cc k)) ^ q) ^ (1 / q) =
          ENNReal.ofReal (Cc k * (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      rw [hC_root, hcard_root]
      rw [mul_comm]
      rw [← ENNReal.ofReal_mul (hCc k)]
    have hf_bound : eLpNorm f (ENNReal.ofReal q) μ ≤
        ((s.card : ℝ≥0∞) * (ENNReal.ofReal (Cc k)) ^ q) ^ (1 / q) := by
      simpa [one_div] using (ENNReal.le_rpow_inv_iff hqpos).2 hpow_bound
    have hfinal := hf_bound.trans_eq hbase_target
    simpa [f, s, hs] using hfinal

end Paper
