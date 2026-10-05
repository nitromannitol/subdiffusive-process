module

public import SubdiffusiveProcess.RareIntervals.Config
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.IntervalPackingIndependence

@[expose] public section

/-!
# Probability estimates for the rare-interval lemma

* `measure_config_le`: for a fixed separated configuration of scheme intervals, the events factorize and
  the probability of the intersection is at most `exp (-lam * ∑ (j+1))`.
* `measure_long_le`: union bound for the events with `j ≥ N`.
-/

namespace SubdiffusiveProcess.RareIntervals

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Fixed separated configuration: independence factorization and the bound `exp (-lam ∑ (j+1))`. -/
theorem measure_config_le (S : Scheme) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℤ → MeasurableSpace Ω} (hind : iIndep m μ) (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (E : ℤ → ℕ → Set Ω)
    (hE : ∀ k j, MeasurableSet[⨆ i ∈ Finset.Icc (S.lo k j) (S.hi k j), m i] (E k j))
    (lam : ℝ) (hP : ∀ k j, μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1)))))
    (F : Finset (ℤ × ℕ)) (hF : SepFam S F) :
    μ (⋂ x ∈ F, E x.1 x.2) ≤
      ENNReal.ofReal (Real.exp (-(lam * ∑ x ∈ F, ((x.2 : ℝ) + 1)))) := by
  have hprod := SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.measure_biInter_eq_prod_of_iIndep_finsetBlocks
    hind hm F (fun x : ℤ × ℕ => Finset.Icc (S.lo x.1 x.2) (S.hi x.1 x.2))
    (fun x hx y hy hxy => (hF x hx y hy hxy).disjoint) (fun x => E x.1 x.2) (fun x _ => hE x.1 x.2)
  rw [hprod]
  calc ∏ x ∈ F, μ (E x.1 x.2)
      ≤ ∏ x ∈ F, ENNReal.ofReal (Real.exp (-(lam * ((x.2 : ℝ) + 1)))) :=
        Finset.prod_le_prod (fun x _ => hP x.1 x.2)
    _ = ENNReal.ofReal (∏ x ∈ F, Real.exp (-(lam * ((x.2 : ℝ) + 1)))) :=
        (ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (Real.exp (-(lam * ∑ x ∈ F, ((x.2 : ℝ) + 1)))) := by
        rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- Union bound over `k ∈ [a, a+N-1]` and the long intervals `j ≥ N`. -/
theorem measure_long_le {μ : Measure Ω} (E : ℤ → ℕ → Set Ω) (lam : ℝ) (hlam : 1 ≤ lam)
    (hP : ∀ k j, μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1)))))
    (a : ℤ) (N : ℕ) :
    μ (⋃ k ∈ Finset.Icc a (a + (N : ℤ) - 1), ⋃ i : ℕ, E k (N + i)) ≤
      ENNReal.ofReal (2 * N * Real.exp (-(lam * N))) := by
  set q : ℝ := Real.exp (-lam) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hqhalf : q ≤ 1 / 2 := by
    have h1 : Real.exp (-lam) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    rw [hq]
    calc Real.exp (-lam) ≤ Real.exp (-1) := h1
      _ = (Real.exp 1)⁻¹ := h3
      _ ≤ 1 / 2 := by
        rw [one_div]; exact inv_anti₀ (by norm_num) h2
  have hq1 : q < 1 := by linarith
  set f : ℕ → ℝ := fun i => Real.exp (-(lam * (((N + i : ℕ) : ℝ) + 1))) with hf
  have hfeq : ∀ i, f i = Real.exp (-(lam * ((N : ℝ) + 1))) * q ^ i := by
    intro i
    rw [hf, hq, ← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    ring_nf
  have hfnn : ∀ i, 0 ≤ f i := fun i => (Real.exp_pos _).le
  have hsum : Summable f := by
    have : Summable (fun i : ℕ => Real.exp (-(lam * ((N : ℝ) + 1))) * q ^ i) :=
      (summable_geometric_of_lt_one hq0.le hq1).mul_left _
    exact (summable_congr hfeq).mpr this
  have htsum : ∑' i, f i ≤ 2 * Real.exp (-(lam * N)) := by
    have h1 : ∑' i, f i = Real.exp (-(lam * ((N : ℝ) + 1))) * (1 - q)⁻¹ := by
      simp_rw [hfeq]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
    have h2 : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h3 : Real.exp (-(lam * ((N : ℝ) + 1))) ≤ Real.exp (-(lam * N)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [h1]
    calc Real.exp (-(lam * ((N : ℝ) + 1))) * (1 - q)⁻¹
        ≤ Real.exp (-(lam * N)) * 2 := mul_le_mul h3 h2 (inv_nonneg.mpr (by linarith)) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(lam * N)) := by ring
  have hk : ∀ k : ℤ, μ (⋃ i : ℕ, E k (N + i)) ≤ ENNReal.ofReal (2 * Real.exp (-(lam * N))) := by
    intro k
    calc μ (⋃ i : ℕ, E k (N + i)) ≤ ∑' i : ℕ, μ (E k (N + i)) := measure_iUnion_le _
      _ ≤ ∑' i : ℕ, ENNReal.ofReal (f i) := ENNReal.tsum_le_tsum (fun i => hP k (N + i))
      _ = ENNReal.ofReal (∑' i, f i) := (ENNReal.ofReal_tsum_of_nonneg hfnn hsum).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal htsum
  calc μ (⋃ k ∈ Finset.Icc a (a + (N : ℤ) - 1), ⋃ i : ℕ, E k (N + i))
      ≤ ∑ k ∈ Finset.Icc a (a + (N : ℤ) - 1), μ (⋃ i : ℕ, E k (N + i)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.Icc a (a + (N : ℤ) - 1), ENNReal.ofReal (2 * Real.exp (-(lam * N))) :=
        Finset.sum_le_sum (fun k _ => hk k)
    _ = (N : ENNReal) * ENNReal.ofReal (2 * Real.exp (-(lam * N))) := by
        rw [Finset.sum_const, Int.card_Icc]
        have : (a + (N : ℤ) - 1 + 1 - a).toNat = N := by omega
        rw [this, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * N * Real.exp (-(lam * N))) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end SubdiffusiveProcess.RareIntervals
