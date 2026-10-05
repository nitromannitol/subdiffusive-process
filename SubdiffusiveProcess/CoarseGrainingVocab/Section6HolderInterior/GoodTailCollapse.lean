module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodStoppingDepthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TailBridge

@[expose] public section

/-!
# Collapsing the good-scale stopping tail to a single Γ₁ exponential

The proved good-scale tails
(`Section6Stopping.measure_goodStoppingDepth_tail_le_sum_exp`,
`Section6Cutoff.exists_measure_cutoffGoodStoppingDepth_tail_le_sum_exp`)
bound the tail by an *un-summed* series

```text
  ∑_{n < m-q+1} 3^{d(m-n)} · exp(-R·(m-n+1)) ,
```

each term carrying the spatial entropy factor `3^{d(m-n)}` of the grid at scale
`n`.  Once the rate `R` beats the entropy — `R ≥ 2 d log 3 + 2`, which the
Hölder parameter choice arranges — the series collapses geometrically to a
single exponential at half the rate.  That collapse is proved here once, in
real form and in `ENNReal` form, and then applied to both proved tails.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The entropy-beating geometric collapse**, in real form. -/
theorem sum_entropy_exp_le (d : ℕ) {r : ℝ} (q m : ℕ) (hq : q ≤ m)
    (hr : 2 * ((d : ℝ) * Real.log 3) + 2 ≤ r) :
    ∑ n ∈ Finset.range (m - q + 1),
        ((3 : ℕ) ^ (d * (m - n)) : ℝ) * Real.exp (-r * ((m : ℝ) - (n : ℝ) + 1))
      ≤ 2 * Real.exp (-(r / 2) * (q : ℝ)) := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdlog0 : 0 ≤ (d : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg d) hlog3pos.le
  have hr2 : (2 : ℝ) ≤ r := by linarith
  have hdlog : (d : ℝ) * Real.log 3 ≤ r / 2 - 1 := by linarith
  have hterm : ∀ n ∈ Finset.range (m - q + 1),
      ((3 : ℕ) ^ (d * (m - n)) : ℝ) * Real.exp (-r * ((m : ℝ) - (n : ℝ) + 1))
        ≤ Real.exp (-(r / 2) * (q : ℝ)) *
            Real.exp (-(r / 2) * ((m - q - n : ℕ) : ℝ)) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnm : n ≤ m := by omega
    set i : ℕ := m - q - n with hi
    have hji : m - n = q + i := by omega
    have hcast : ((m : ℝ) - (n : ℝ)) = ((m - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hnm]
    have h3 : ((3 : ℕ) ^ (d * (m - n)) : ℝ)
        = Real.exp (((d * (m - n) : ℕ) : ℝ) * Real.log 3) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      push_cast
      ring
    rw [h3, hcast, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hji]
    push_cast
    nlinarith [hdlog, hr2, Nat.cast_nonneg (α := ℝ) q, Nat.cast_nonneg (α := ℝ) i]
  calc ∑ n ∈ Finset.range (m - q + 1),
        ((3 : ℕ) ^ (d * (m - n)) : ℝ) * Real.exp (-r * ((m : ℝ) - (n : ℝ) + 1))
      ≤ ∑ n ∈ Finset.range (m - q + 1),
          Real.exp (-(r / 2) * (q : ℝ)) *
            Real.exp (-(r / 2) * ((m - q - n : ℕ) : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.exp (-(r / 2) * (q : ℝ)) *
          ∑ n ∈ Finset.range (m - q + 1),
            Real.exp (-(r / 2) * ((m - q - n : ℕ) : ℝ)) := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (-(r / 2) * (q : ℝ)) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        have hreflect : ∑ n ∈ Finset.range (m - q + 1),
            Real.exp (-(r / 2) * ((m - q - n : ℕ) : ℝ))
            = ∑ n ∈ Finset.range (m - q + 1),
              Real.exp (-(r / 2) * ((n : ℕ) : ℝ)) := by
          have := Finset.sum_range_reflect
            (fun n : ℕ => Real.exp (-(r / 2) * ((n : ℕ) : ℝ))) (m - q + 1)
          simpa using this
        rw [hreflect]
        have hbound : ∀ n ∈ Finset.range (m - q + 1),
            Real.exp (-(r / 2) * ((n : ℕ) : ℝ)) ≤ ((1 : ℝ) / 2) ^ n := by
          intro n _
          have hbase : Real.exp (-(r / 2)) ≤ (1 : ℝ) / 2 := by
            have hstep : Real.exp (-(r / 2)) ≤ Real.exp (-1) :=
              Real.exp_le_exp.mpr (by linarith)
            have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
              nlinarith [Real.add_one_le_exp (1 : ℝ)]
            have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
              rw [← Real.exp_add]; norm_num
            have he : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
              nlinarith [Real.exp_pos (-1), hexp1, hprod]
            linarith
          calc Real.exp (-(r / 2) * (n : ℝ)) = (Real.exp (-(r / 2))) ^ n := by
                rw [mul_comm, Real.exp_nat_mul]
            _ ≤ ((1 : ℝ) / 2) ^ n := pow_le_pow_left₀ (Real.exp_nonneg _) hbase n
        calc ∑ n ∈ Finset.range (m - q + 1), Real.exp (-(r / 2) * ((n : ℕ) : ℝ))
            ≤ ∑ n ∈ Finset.range (m - q + 1), ((1 : ℝ) / 2) ^ n :=
              Finset.sum_le_sum hbound
          _ ≤ 2 := sum_geometric_two_le _
    _ = 2 * Real.exp (-(r / 2) * (q : ℝ)) := by ring

/-- The same collapse in `ENNReal`, in the exact shape of the proved tails. -/
theorem sum_entropy_ofReal_exp_le (d : ℕ) {r : ℝ} (q m : ℕ) (hq : q ≤ m)
    (hr : 2 * ((d : ℝ) * Real.log 3) + 2 ≤ r) :
    ∑ n ∈ Finset.range (m - q + 1),
        ((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-r * ((m : ℝ) - (n : ℝ) + 1)))
      ≤ ENNReal.ofReal (2 * Real.exp (-(r / 2) * (q : ℝ))) := by
  have hstep : ∀ n ∈ Finset.range (m - q + 1),
      ((3 ^ (d * (m - n)) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-r * ((m : ℝ) - (n : ℝ) + 1)))
        = ENNReal.ofReal (((3 : ℕ) ^ (d * (m - n)) : ℝ) *
            Real.exp (-r * ((m : ℝ) - (n : ℝ) + 1))) := by
    intro n _
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Nat.cast_pow, ENNReal.ofReal_natCast]
  rw [Finset.sum_congr rfl hstep,
    ← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (sum_entropy_exp_le d q m hq hr)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
