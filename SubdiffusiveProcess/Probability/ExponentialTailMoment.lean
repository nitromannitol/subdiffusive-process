module

public import SubdiffusiveProcess.Probability.AbsoluteSeries
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecificLimits.Normed
@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess

/-- An exponential tail for a natural-valued allowance yields the requested exponential moment whenever the moment rate is strictly below the tail rate. The model tail remains an explicit input. -/
theorem integrable_exp_nat_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → ℕ) (hB : Measurable B)
    (C a t : ℝ) (_hC : 0 ≤ C) (_ht : 0 ≤ t) (hgap : t < a)
    (htail : ∀ n : ℕ,
      μ.real {ω : Ω | n < B ω} ≤ C * Real.exp (-a * (n : ℝ))) :
    Integrable (fun ω => Real.exp (t * (B ω : ℝ))) μ ∧
      (∫ ω, Real.exp (t * (B ω : ℝ)) ∂μ) ≤
        1 + C * Real.exp t / (1 - Real.exp (t - a)) := by
  let ν : Measure ℕ := μ.map B
  have : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact inferInstance
  let q : ℕ → ℝ := fun n => ν.real {n} * Real.exp (t * (n : ℝ))
  let r : ℝ := Real.exp (t - a)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hν_succ (n : ℕ) : ν.real {n + 1} ≤ C * Real.exp (-a * (n : ℝ)) := by
    calc
      ν.real {n + 1} ≤ ν.real {k : ℕ | n < k} :=
        measureReal_mono (by
          intro k hk
          simp only [mem_singleton_iff] at hk
          simp only [mem_ofPred_eq]
          omega)
      _ = μ.real {ω : Ω | n < B ω} := by
        dsimp [ν]
        rw [map_measureReal_apply hB (by measurability)]
        congr 1
      _ ≤ C * Real.exp (-a * (n : ℝ)) := htail n
  have hq0 : q 0 ≤ 1 := by
    dsimp [q]
    simp
  have hq_succ (n : ℕ) : q (n + 1) ≤ C * Real.exp t * r ^ n := by
    have he : Real.exp (t * ((n + 1 : ℕ) : ℝ)) = Real.exp t * Real.exp (t * (n : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
      ring
    have hnon : 0 ≤ Real.exp (t * ((n + 1 : ℕ) : ℝ)) := (Real.exp_pos _).le
    calc
      q (n + 1) = ν.real {n + 1} * Real.exp (t * ((n + 1 : ℕ) : ℝ)) := rfl
      _ ≤ (C * Real.exp (-a * (n : ℝ))) * Real.exp (t * ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (hν_succ n) hnon
      _ = C * Real.exp t * r ^ n := by
        rw [he]
        calc
          C * Real.exp (-a * (n : ℝ)) * (Real.exp t * Real.exp (t * (n : ℝ))) =
              C * Real.exp t * (Real.exp (-a * (n : ℝ)) * Real.exp (t * (n : ℝ))) := by ring
          _ = C * Real.exp t * Real.exp ((n : ℝ) * (t - a)) := by
                rw [← Real.exp_add]
                congr 2
                ring
          _ = C * Real.exp t * r ^ n := by rw [Real.exp_nat_mul]
  have hq_nonneg (n : ℕ) : 0 ≤ q n :=
    mul_nonneg measureReal_nonneg (Real.exp_pos _).le
  have hgeom : Summable (fun n : ℕ => C * Real.exp t * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (C * Real.exp t)
  have hq_tail : Summable (fun n : ℕ => q (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => hq_nonneg (n + 1)) hq_succ hgeom
  have hq : Summable q := (summable_nat_add_iff 1).mp (by simpa using hq_tail)
  have hfν : Integrable (fun n : ℕ => Real.exp (t * (n : ℝ))) ν := by
    refine ⟨measurable_of_countable _ |>.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
    rw [lt_top_iff_ne_top]
    let qnn : ℕ → ℝ≥0 := fun n => NNReal.mk (q n) (hq_nonneg n)
    have hqnn : Summable qnn := NNReal.summable_coe.mp (by simpa only [qnn, NNReal.coe_mk] using hq)
    have htop : (∑' n, (qnn n : ℝ≥0∞)) ≠ ∞ :=
      ENNReal.tsum_coe_ne_top_iff_summable.mpr hqnn
    convert htop using 1
    congr 1 with n
    let mnn : ℝ≥0 := NNReal.mk (ν.real {n}) measureReal_nonneg
    have hm : ν {n} = (mnn : ℝ≥0∞) := by
      exact (ENNReal.ofReal_toReal (measure_ne_top ν {n})).symm.trans
        (ENNReal.ofReal_eq_coe_nnreal ENNReal.toReal_nonneg)
    rw [hm]
    rw [enorm_eq_nnnorm]
    rw [← ENNReal.coe_mul]
    apply congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞))
    apply NNReal.eq
    simp only [NNReal.coe_mul, qnn, q, mnn,
      Real.nnnorm_of_nonneg (Real.exp_pos _).le, NNReal.coe_mk, mul_comm]
  have hf : Integrable (fun ω => Real.exp (t * (B ω : ℝ))) μ := by
    simpa [ν, Function.comp_def] using hfν.comp_measurable hB
  refine ⟨hf, ?_⟩
  have hint_map : (∫ ω, Real.exp (t * (B ω : ℝ)) ∂μ) =
      ∫ n : ℕ, Real.exp (t * (n : ℝ)) ∂ν := by
    exact (integral_map hB.aemeasurable hfν.aestronglyMeasurable).symm
  rw [hint_map, integral_countable hfν]
  change (∑' n, q n) ≤ _
  calc
    (∑' n, q n) = q 0 + ∑' n, q (n + 1) := by
      rw [← hq.sum_add_tsum_nat_add 1]
      simp
    _ ≤ 1 + ∑' n, C * Real.exp t * r ^ n :=
      add_le_add hq0 (hq_tail.tsum_le_tsum hq_succ hgeom)
    _ = 1 + C * Real.exp t / (1 - Real.exp (t - a)) := by
      rw [Summable.tsum_mul_left _ (summable_geometric_of_lt_one hr0 hr1),
        tsum_geometric_of_lt_one hr0 hr1]
      simp [r, div_eq_mul_inv]

end SubdiffusiveProcess
