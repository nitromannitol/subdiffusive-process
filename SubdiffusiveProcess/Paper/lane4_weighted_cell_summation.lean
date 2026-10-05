module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Numeric

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lane4_weighted_cell_summation_sup
    (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (q : ℝ) (hq : 0 < q)
    (s : Finset ℕ) (hs : s.Nonempty) (C : ℝ)
    (Y : ℕ → Ω → ℝ) (hY_nonneg : ∀ j x, 0 ≤ Y j x)
    (hY_meas : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hY_norm : ∀ j, eLpNorm (Y j) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun x => s.sup' hs (fun j => Y j x)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal C * (s.card : ℝ≥0∞) ^ (1 / q) := by
  let : MeasurableSpace Ω := mΩ
  have hpow (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f μ) :
      eLpNorm (fun x => f x ^ q) 1 μ =
        eLpNorm f (ENNReal.ofReal q) μ ^ q := by
    have h := eLpNorm_norm_rpow (μ := μ) (p := (1 : ℝ≥0∞)) f hfm hq
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (hf _)] using h
  have hM_meas : AEStronglyMeasurable (fun x => s.sup' hs (fun j => Y j x)) μ := by
    have hm : AEStronglyMeasurable (s.sup' hs Y) μ := by
      refine Finset.sup'_induction hs (p := fun f : Ω → ℝ => AEStronglyMeasurable f μ)
        Y (fun f hf g hg => hf.sup hg) (fun j _ => hY_meas j)
    have heq : s.sup' hs Y = (fun x => s.sup' hs (fun j => Y j x)) := by
      funext x
      simp only [Finset.sup'_apply]
    exact heq ▸ hm
  have hM_nonneg : ∀ x, 0 ≤ s.sup' hs (fun j => Y j x) := by
    intro x
    obtain ⟨j, hj, hj_eq⟩ := Finset.exists_mem_eq_sup' hs (fun j => Y j x)
    rw [hj_eq]
    exact hY_nonneg j x
  have hY_pow_meas : ∀ j, AEStronglyMeasurable (fun x => Y j x ^ q) μ := by
    intro j
    exact (Real.continuous_rpow_const hq.le).comp_aestronglyMeasurable (hY_meas j)
  have hM_pow_le : ∀ x,
      (s.sup' hs (fun j => Y j x)) ^ q ≤ ∑ j ∈ s, (Y j x) ^ q := by
    intro x
    obtain ⟨j, hj, hj_eq⟩ := Finset.exists_mem_eq_sup' hs (fun j => Y j x)
    rw [hj_eq]
    exact Finset.single_le_sum (fun i hi => Real.rpow_nonneg (hY_nonneg i x) q) hj
  have hpow_le :
      eLpNorm (fun x => s.sup' hs (fun j => Y j x)) (ENNReal.ofReal q) μ ^ q ≤
        (s.card : ℝ≥0∞) * (ENNReal.ofReal C) ^ q := by
    calc
      eLpNorm (fun x => s.sup' hs (fun j => Y j x)) (ENNReal.ofReal q) μ ^ q =
          eLpNorm (fun x => (s.sup' hs (fun j => Y j x)) ^ q) 1 μ :=
        (hpow (fun x => s.sup' hs (fun j => Y j x)) hM_nonneg hM_meas).symm
      _ ≤ eLpNorm (fun x => ∑ j ∈ s, (Y j x) ^ q) 1 μ := by
        apply eLpNorm_mono ((Real.continuous_rpow_const hq.le).comp_aestronglyMeasurable hM_meas)
        intro x
        have hleft : 0 ≤ (s.sup' hs (fun j => Y j x)) ^ q :=
          Real.rpow_nonneg (hM_nonneg x) q
        have hright : 0 ≤ ∑ j ∈ s, (Y j x) ^ q := by
          apply Finset.sum_nonneg
          intro j hj
          exact Real.rpow_nonneg (hY_nonneg j x) q
        simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using
          hM_pow_le x
      _ ≤ ∑ j ∈ s, eLpNorm (fun x => (Y j x) ^ q) 1 μ := by
        have heq : (∑ j ∈ s, (fun x => (Y j x) ^ q)) =
            (fun x => ∑ j ∈ s, (Y j x) ^ q) := by
          funext x
          simp
        rw [← heq]
        exact eLpNorm_sum_le (p := (1 : ℝ≥0∞)) (μ := μ)
          (f := fun j x => (Y j x) ^ q) (s := s)
          (by norm_num)
      _ = ∑ j ∈ s, eLpNorm (Y j) (ENNReal.ofReal q) μ ^ q := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpow (Y j) (hY_nonneg j) (hY_meas j)]
      _ ≤ ∑ j ∈ s, (ENNReal.ofReal C) ^ q := by
        apply Finset.sum_le_sum
        intro j hj
        exact ENNReal.rpow_le_rpow (hY_norm j) hq.le
      _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal C) ^ q := by
        simp [Finset.sum_const]
  have hroot := ENNReal.rpow_le_rpow hpow_le (by positivity : 0 ≤ (1 / q : ℝ))
  calc
    eLpNorm (fun x => s.sup' hs (fun j => Y j x)) (ENNReal.ofReal q) μ =
        (eLpNorm (fun x => s.sup' hs (fun j => Y j x)) (ENNReal.ofReal q) μ ^ q) ^ (1 / q) := by
          rw [← ENNReal.rpow_mul]
          rw [mul_one_div]
          simp [ne_of_gt hq]
    _ ≤ ((s.card : ℝ≥0∞) * (ENNReal.ofReal C) ^ q) ^ (1 / q) := hroot
    _ = ENNReal.ofReal C * (s.card : ℝ≥0∞) ^ (1 / q) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (1 / q : ℝ))]
      rw [← ENNReal.rpow_mul]
      rw [mul_one_div]
      simp [ne_of_gt hq, mul_comm]

theorem aux_lane4_weighted_cell_summation_card_rpow
    (d k : ℕ) (q : ℝ) (hq : 0 < q) :
    ((3 ^ (d * k) : ℕ) : ℝ≥0∞) ^ (1 / q) =
      ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
  rw [← ENNReal.ofReal_natCast (3 ^ (d * k))]
  rw [show ((3 ^ (d * k) : ℕ) : ℝ) = (3 : ℝ) ^ (d * k) by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  field_simp



theorem lane4_weighted_cell_summation :
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ)
    (d : ℕ) (s q : ℝ), 0 < s → 0 < d → 2 * (d : ℝ) / s ≤ q → 1 ≤ q →
  ∀ (Y : ℕ → ℕ → Ω → ℝ) (Cc : ℕ → ℝ), (∀ k, 0 ≤ Cc k) →
    -- `Y k j` is the value on the `j`-th cell at scale `k`; there are at most `3^(d*k)` cells at that scale.
    (∀ k j, 0 ≤ Y k j) →
    (∀ k j, AEStronglyMeasurable (Y k j) μ) →
    (∀ k j, eLpNorm (Y k j) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (Cc k)) →
  ∀ n : ℕ,
    eLpNorm (fun om => ∑ k ∈ Finset.range n,
        (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (Finset.range (3 ^ (d * k)) |>.sup'
            (Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by norm_num))) fun j => Y k j om))
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n,
        Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
  intro Ω mΩ μ hμ d s q hs hd hscale hq Y Cc hCc hY_nonneg hY_meas hY_norm n
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure μ := hμ
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
  have hq_pos : 0 < q := by
    have hpos : 0 < 2 * (d : ℝ) / s :=
      div_pos (mul_pos (by norm_num) hd_real) hs
    exact lt_of_lt_of_le hpos hscale
  have hq_ennreal : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hrange (k : ℕ) : (Finset.range (3 ^ (d * k))).Nonempty := by
    apply Finset.nonempty_range_iff.mpr
    exact pow_ne_zero (d * k) (by norm_num : (3 : ℕ) ≠ 0)
  let M : ℕ → Ω → ℝ := fun k om =>
    (Finset.range (3 ^ (d * k))).sup'
      (Finset.nonempty_range_iff.mpr (pow_ne_zero _ (by norm_num)))
      (fun j => Y k j om)
  have hM_nonneg : ∀ k om, 0 ≤ M k om := by
    intro k om
    dsimp [M]
    obtain ⟨j, hj, hj_eq⟩ := Finset.exists_mem_eq_sup' (hrange k)
      (fun j => Y k j om)
    rw [hj_eq]
    exact hY_nonneg k j om
  have hM_meas : ∀ k, AEStronglyMeasurable (M k) μ := by
    intro k
    have hsup :
        (fun om => (Finset.range (3 ^ (d * k))).sup' (hrange k)
          (fun j => Y k j om)) =
          (Finset.range (3 ^ (d * k))).sup' (hrange k) (fun j => Y k j) := by
      funext om
      exact (Finset.apply_sup'_eq_sup'_comp (hrange k)
        (fun f : Ω → ℝ => f om) (by intros; rfl)).symm
    dsimp [M]
    rw [hsup]
    refine Finset.sup'_induction (H := hrange k) (f := fun j => Y k j)
      (p := fun f => AEStronglyMeasurable f μ) ?_ ?_
    · intro a ha b hb
      exact ha.sup hb
    · intro j hj
      exact hY_meas k j
  have hcell : ∀ k,
      eLpNorm (M k) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (Cc k) *
          ((3 ^ (d * k) : ℕ) : ℝ≥0∞) ^ (1 / q) := by
    intro k
    have haux := aux_lane4_weighted_cell_summation_sup Ω mΩ μ q hq_pos
      (Finset.range (3 ^ (d * k))) (hrange k) (Cc k) (fun j om => Y k j om)
      (fun j om => hY_nonneg k j om) (fun j => hY_meas k j)
      (fun j => hY_norm k j)
    simpa only [Finset.card_range] using haux
  have hterm : ∀ k : ℕ,
      eLpNorm (fun om => (3 : ℝ) ^ (-(s * (k : ℝ))) * M k om)
          (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
    intro k
    have hweight : 0 ≤ (3 : ℝ) ^ (-(s * (k : ℝ))) := by positivity
    have hcard := aux_lane4_weighted_cell_summation_card_rpow d k q hq_pos
    calc
      eLpNorm (fun om => (3 : ℝ) ^ (-(s * (k : ℝ))) * M k om)
          (ENNReal.ofReal q) μ =
          ‖(3 : ℝ) ^ (-(s * (k : ℝ)))‖ₑ *
            eLpNorm (M k) (ENNReal.ofReal q) μ := by
        rw [show (fun om => (3 : ℝ) ^ (-(s * (k : ℝ))) * M k om) =
            (3 : ℝ) ^ (-(s * (k : ℝ))) • M k by rfl]
        exact eLpNorm_const_smul _ _ _ _
      _ ≤ ‖(3 : ℝ) ^ (-(s * (k : ℝ)))‖ₑ *
          (ENNReal.ofReal (Cc k) *
            ((3 ^ (d * k) : ℕ) : ℝ≥0∞) ^ (1 / q)) := by
        exact mul_le_mul_right (hcell k) _
      _ = ENNReal.ofReal (Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
        rw [Real.enorm_eq_ofReal hweight, hcard]
        calc
          ENNReal.ofReal ((3 : ℝ) ^ (-(s * (k : ℝ)))) *
              (ENNReal.ofReal (Cc k) *
                ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q))) =
              (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (k : ℝ)))) *
                ENNReal.ofReal (Cc k)) *
                ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by ring
          _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (k : ℝ))) * Cc k) *
                ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
            rw [ENNReal.ofReal_mul hweight]
          _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (k : ℝ))) * Cc k *
                (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hweight (hCc k))]
          _ = ENNReal.ofReal (Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
                (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
            congr 1
            ring
  let W : ℕ → Ω → ℝ := fun k om =>
    (3 : ℝ) ^ (-(s * (k : ℝ))) * M k om
  have hsum_bound :
      eLpNorm (fun om => ∑ k ∈ Finset.range n, W k om)
        (ENNReal.ofReal q) μ ≤
        ∑ k ∈ Finset.range n, eLpNorm (W k) (ENNReal.ofReal q) μ := by
      have heq : (∑ k ∈ Finset.range n, W k) =
          (fun om => ∑ k ∈ Finset.range n, W k om) := by
        funext om
        simp
      rw [← heq]
      exact eLpNorm_sum_le (p := ENNReal.ofReal q) (μ := μ)
        (f := W)
        (s := Finset.range n)
        hq_ennreal
  have hfinal :
      eLpNorm (fun om => ∑ k ∈ Finset.range n, W k om)
        (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n,
        Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
    calc
      eLpNorm (fun om => ∑ k ∈ Finset.range n, W k om)
        (ENNReal.ofReal q) μ ≤
        ∑ k ∈ Finset.range n, eLpNorm (W k) (ENNReal.ofReal q) μ := hsum_bound
      _ ≤ ∑ k ∈ Finset.range n,
        ENNReal.ofReal (Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [W] using hterm k
      _ = ENNReal.ofReal (∑ k ∈ Finset.range n,
        Cc k * (3 : ℝ) ^ (-(s * (k : ℝ))) *
          (3 : ℝ) ^ ((d : ℝ) * (k : ℝ) / q)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro k hk
        exact mul_nonneg (mul_nonneg (hCc k)
          (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by rfl
  simpa [W, M] using hfinal

end SubdiffusiveProcess.Paper
