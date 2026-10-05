module

public import SubdiffusiveProcess.Probability.ExponentialTailMoment
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

/-! A measurable last-exception allowance for a sequence of exponentially
unlikely bad prefix events.  The construction preserves the exponential rate.
It does not supply the model-specific tail estimate for those events.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SubdiffusiveProcess

/-- The geometric tail of exponentially unlikely events has the same rate. -/
theorem measure_union_exponential_tail
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (bad : ℕ → Set Omega) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 < A)
    (htail : ∀ m, mu (bad m) ≤ ENNReal.ofReal (C * Real.exp (-A * (m : ℝ))))
    (n : ℕ) :
    mu (⋃ j : ℕ, bad (n + j)) ≤
      ENNReal.ofReal (C / (1 - Real.exp (-A)) * Real.exp (-A * (n : ℝ))) := by
  have hbase : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hA)
  have hgeom : Summable (fun j : ℕ => Real.exp (-A) ^ j) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hbase
  have hfactor j : C * Real.exp (-A * ((n + j : ℕ) : ℝ)) =
      (C * Real.exp (-A * (n : ℝ))) * Real.exp (-A) ^ j := by
    rw [Nat.cast_add, mul_add, Real.exp_add, mul_comm (-A) (j : ℝ), Real.exp_nat_mul]
    ring
  calc
    mu (⋃ j : ℕ, bad (n + j)) ≤ ∑' j : ℕ, mu (bad (n + j)) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal
        ((C * Real.exp (-A * (n : ℝ))) * Real.exp (-A) ^ j) :=
      ENNReal.tsum_le_tsum (fun j => (htail (n + j)).trans_eq (congrArg _ (hfactor j)))
    _ = ENNReal.ofReal
        (∑' j : ℕ, (C * Real.exp (-A * (n : ℝ))) * Real.exp (-A) ^ j) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun j => mul_nonneg (mul_nonneg hC (Real.exp_pos _).le)
          (pow_nonneg (Real.exp_pos _).le j))
        (hgeom.mul_left _)).symm
    _ = ENNReal.ofReal (C / (1 - Real.exp (-A)) * Real.exp (-A * (n : ℝ))) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hbase]
      congr 1
      ring

/-- Exponential prefix tails yield a measurable finite allowance, outside a
null set, after which every prefix is good. -/
theorem exists_prefix_allowance_of_exponential_tails
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (bad : ℕ → Set Omega) (hbad : ∀ m, MeasurableSet (bad m))
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 < A)
    (htail : ∀ m, mu (bad m) ≤ ENNReal.ofReal (C * Real.exp (-A * (m : ℝ)))) :
    ∃ B : Omega → ℕ, Measurable B ∧
      (∀ n, mu.real {omega | n < B omega} ≤
        C / (1 - Real.exp (-A)) * Real.exp (-A * (n : ℝ))) ∧
      (∀ᵐ omega ∂mu, ∀ m, B omega ≤ m → omega ∉ bad m) := by
  classical
  let good : ℕ → Set Omega := fun n => {omega | ∀ m, n ≤ m → omega ∉ bad m}
  have hgood n : MeasurableSet (good n) := by
    simpa only [good, ofPred_forall, Set.compl_def] using
      MeasurableSet.iInter (fun m => MeasurableSet.iInter (fun _ : n ≤ m =>
        (hbad m).compl))
  let carrier : Set Omega := ⋃ n, good n
  have hcarrier : MeasurableSet carrier := MeasurableSet.iUnion hgood
  have hex (omega : Omega) : ∃ n, omega ∈ carrier → omega ∈ good n := by
    by_cases h : omega ∈ carrier
    · obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun hc => (h hc).elim⟩
  let B : Omega → ℕ := fun omega => Nat.find (hex omega)
  have hB : Measurable B := by
    apply measurable_find hex
    intro n
    convert hcarrier.compl.union (hgood n) using 1
    ext omega
    exact imp_iff_not_or
  refine ⟨B, hB, ?_, ?_⟩
  · intro n
    have hsubset : {omega | n < B omega} ⊆ ⋃ j : ℕ, bad (n + j) := by
      intro omega homega
      have hnot : ¬ omega ∈ good n := by
        intro hn
        have hfind := Nat.find_min' (hex omega) (fun _ => hn)
        exact (not_le_of_gt homega) hfind
      change ¬ (∀ m, n ≤ m → omega ∉ bad m) at hnot
      push Not at hnot
      obtain ⟨m, hnm, hm⟩ := hnot
      exact mem_iUnion.mpr ⟨m - n, by rwa [Nat.add_sub_of_le hnm]⟩
    have hbound := (measure_mono hsubset).trans
      (measure_union_exponential_tail mu bad C A hC hA htail n)
    have hden : 0 < 1 - Real.exp (-A) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hA))
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (div_nonneg hC hden.le) (Real.exp_pos _).le))
  · have hbase : Real.exp (-A) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hA)
    have hsum : Summable (fun m : ℕ => C * Real.exp (-A * (m : ℝ))) := by
      have hgeom := (summable_geometric_of_lt_one (Real.exp_pos (-A)).le hbase).mul_left C
      convert hgeom using 1
      ext m
      rw [mul_comm (-A) (m : ℝ), Real.exp_nat_mul]
    have htsum : (∑' m, mu (bad m)) ≠ ∞ :=
      ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum htail)
    filter_upwards [ae_eventually_notMem htsum] with omega homega
    obtain ⟨n, hn⟩ := eventually_atTop.mp homega
    have hc : omega ∈ carrier := mem_iUnion.mpr ⟨n, hn⟩
    exact Nat.find_spec (hex omega) hc

end SubdiffusiveProcess
