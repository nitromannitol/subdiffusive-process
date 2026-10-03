module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialFieldArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.IntervalConfiguration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport

@[expose] public section

/-!
# Exponential-field concentration assembly

This file implements the finite last-radius split and the packed-configuration
union bound in Appendix B's proposition
`p.concentration.for.scales.exp.field`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

def expFieldBad {d : ℕ} (s : ℝ) (h k : ℕ) : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | ∃ j : ℕ, omega ∈ expFieldBlockExceeds (d := d) s k j h}

def expFieldSmallBad {d : ℕ} (s : ℝ) (h M k : ℕ) : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | ∃ j ≤ M, omega ∈ expFieldBlockExceeds (d := d) s k j h}

def expFieldLargeBad {d : ℕ} (s : ℝ) (h M k : ℕ) : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | ∃ j, M + 1 ≤ j ∧ omega ∈ expFieldBlockExceeds (d := d) s k j h}

theorem measurableSet_expFieldBad {d : ℕ} (s : ℝ) (h k : ℕ) :
    MeasurableSet (expFieldBad (d := d) s h k) := by
  simp only [expFieldBad, Set.setOf_exists]
  exact MeasurableSet.iUnion fun j ↦ measurableSet_expFieldBlockExceeds s k j h

theorem measurableSet_expFieldSmallBad {d : ℕ}
    (s : ℝ) (h M k : ℕ) :
    MeasurableSet (expFieldSmallBad (d := d) s h M k) := by
  have heq : expFieldSmallBad (d := d) s h M k =
      ⋃ j ∈ Finset.range (M + 1), expFieldBlockExceeds (d := d) s k j h := by
    ext omega
    simp only [expFieldSmallBad, Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hE⟩
      exact ⟨j, ⟨by omega, hE⟩⟩
    · rintro ⟨j, hj, hE⟩
      exact ⟨j, by omega, hE⟩
  rw [heq]
  exact Finset.measurableSet_biUnion _ fun j _ ↦
    measurableSet_expFieldBlockExceeds s k j h

theorem measurableSet_expFieldLargeBad {d : ℕ}
    (s : ℝ) (h M k : ℕ) :
    MeasurableSet (expFieldLargeBad (d := d) s h M k) := by
  have heq : expFieldLargeBad (d := d) s h M k =
      ⋃ q : ℕ, expFieldBlockExceeds (d := d) s k (M + 1 + q) h := by
    ext omega
    simp only [expFieldLargeBad, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hE⟩
      exact ⟨j - (M + 1), by simpa [show M + 1 + (j - (M + 1)) = j by omega]⟩
    · rintro ⟨q, hE⟩
      exact ⟨M + 1 + q, by omega, hE⟩
  rw [heq]
  exact MeasurableSet.iUnion fun q ↦
    measurableSet_expFieldBlockExceeds s k (M + 1 + q) h

theorem expFieldBad_subset_small_union_large {d : ℕ}
    (s : ℝ) (h M k : ℕ) :
    expFieldBad (d := d) s h k ⊆
      expFieldSmallBad s h M k ∪ expFieldLargeBad s h M k := by
  rintro omega ⟨j, hj⟩
  by_cases hjM : j ≤ M
  · exact Or.inl ⟨j, hjM, hj⟩
  · exact Or.inr ⟨j, by omega, hj⟩

/-- A high density of arbitrary-radius failures forces a half-density in one
of the finite-radius or large-radius parts. -/
theorem expField_density_split {d : ℕ}
    (s theta : ℝ) (h m0 M : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hbad : theta ≤ intervalEventDensity
      (expFieldBad (d := d) s h) m0 M omega) :
    theta / 2 ≤ intervalEventDensity
        (expFieldSmallBad (d := d) s h M) m0 M omega ∨
      theta / 2 ≤ intervalEventDensity
        (expFieldLargeBad (d := d) s h M) m0 M omega := by
  let I := Finset.Icc m0 (m0 + M)
  let B : ℕ → ℝ := fun k ↦ eventIndicator (expFieldBad (d := d) s h k) omega
  let S : ℕ → ℝ := fun k ↦ eventIndicator (expFieldSmallBad (d := d) s h M k) omega
  let L : ℕ → ℝ := fun k ↦ eventIndicator (expFieldLargeBad (d := d) s h M k) omega
  have hpoint : ∀ k, B k ≤ S k + L k := by
    intro k
    by_cases hb : omega ∈ expFieldBad (d := d) s h k
    · rcases expFieldBad_subset_small_union_large s h M k hb with hs | hl
      · by_cases hl : omega ∈ expFieldLargeBad (d := d) s h M k <;>
          simp [B, S, L, eventIndicator, hb, hs, hl]
      · by_cases hs : omega ∈ expFieldSmallBad (d := d) s h M k <;>
          simp [B, S, L, eventIndicator, hb, hs, hl]
    · by_cases hs : omega ∈ expFieldSmallBad (d := d) s h M k <;>
        by_cases hl : omega ∈ expFieldLargeBad (d := d) s h M k <;>
        simp [B, S, L, eventIndicator, hb, hs, hl]
  have hsum : ∑ k ∈ I, B k ≤ (∑ k ∈ I, S k) + ∑ k ∈ I, L k := by
    calc
      ∑ k ∈ I, B k ≤ ∑ k ∈ I, (S k + L k) :=
        Finset.sum_le_sum fun k _ ↦ hpoint k
      _ = _ := by rw [Finset.sum_add_distrib]
  have hden : 0 < ((M : ℝ) + 1) := by positivity
  have hbad' : theta ≤ (∑ k ∈ I, B k) / ((M : ℝ) + 1) := by
    simpa only [intervalEventDensity, I, B, Nat.cast_add, Nat.cast_one] using hbad
  have htotal : theta ≤
      (∑ k ∈ I, S k) / ((M : ℝ) + 1) +
        (∑ k ∈ I, L k) / ((M : ℝ) + 1) := by
    have hdiv := (div_le_div_iff_of_pos_right hden).2 hsum
    calc
      theta ≤ (∑ k ∈ I, B k) / ((M : ℝ) + 1) := hbad'
      _ ≤ (∑ k ∈ I, S k + ∑ k ∈ I, L k) /
          ((M : ℝ) + 1) := hdiv
      _ = _ := by ring
  by_contra hnone
  push_neg at hnone
  rcases hnone with ⟨hS, hL⟩
  have hS' : (∑ k ∈ I, S k) / ((M : ℝ) + 1) < theta / 2 := by
    simpa only [intervalEventDensity, I, S, Nat.cast_add, Nat.cast_one] using hS
  have hL' : (∑ k ∈ I, L k) / ((M : ℝ) + 1) < theta / 2 := by
    simpa only [intervalEventDensity, I, L, Nat.cast_add, Nat.cast_one] using hL
  linarith

private theorem summable_exp_neg_rate_nat (R : ℝ) (hR : 0 < R) :
    Summable fun q : ℕ ↦ Real.exp (-R * (q : ℝ)) := by
  have hq0 : 0 ≤ Real.exp (-R) := (Real.exp_pos _).le
  have hq1 : Real.exp (-R) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (neg_lt_zero.mpr hR)
  refine (summable_geometric_of_lt_one hq0 hq1).congr fun q ↦ ?_
  rw [← Real.exp_nat_mul (-R) q]
  congr 1
  ring

private theorem tsum_exp_neg_rate_nat (R : ℝ) (hR : 0 < R) :
    (∑' q : ℕ, Real.exp (-R * (q : ℝ))) =
      (1 - Real.exp (-R))⁻¹ := by
  have heq : ∀ q : ℕ, Real.exp (-R * (q : ℝ)) = Real.exp (-R) ^ q := by
    intro q
    rw [← Real.exp_nat_mul (-R) q]
    congr 1
    ring
  rw [tsum_congr heq]
  exact tsum_geometric_of_lt_one (Real.exp_pos _).le (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (neg_lt_zero.mpr hR))

theorem measure_expFieldLargeBad_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {h m0 window : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * M.delta ≤ s)
    (hsmallh : expFieldBlockConst d * M.delta * Real.sqrt (h : ℝ) ≤ s) :
    M.P.toMeasure (expFieldLargeBad (d := d) s h window m0) ≤
      ∑' q : ℕ, ENNReal.ofReal
        (Real.exp (-expFieldBlockRate s M.delta *
          (((window + 1 + q : ℕ) : ℝ) + 1))) := by
  have heq : expFieldLargeBad (d := d) s h window m0 =
      ⋃ q : ℕ, expFieldBlockExceeds (d := d) s m0 (window + 1 + q) h := by
    ext omega
    simp only [expFieldLargeBad, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hE⟩
      exact ⟨j - (window + 1), by
        simpa [show window + 1 + (j - (window + 1)) = j by omega]⟩
    · rintro ⟨q, hE⟩
      exact ⟨window + 1 + q, by omega, hE⟩
  rw [heq]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun q ↦ ?_)
  exact measure_expFieldBlockExceeds_le_ofReal_exp
    M hs hs1 hh hsmall hsmallh

theorem measure_expFieldLargeBad_le_two_mul_exp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {h m0 window : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * M.delta ≤ s)
    (hsmallh : expFieldBlockConst d * M.delta * Real.sqrt (h : ℝ) ≤ s)
    (hR : Real.log 2 ≤ expFieldBlockRate s M.delta) :
    M.P.toMeasure (expFieldLargeBad (d := d) s h window m0) ≤
      ENNReal.ofReal (2 * Real.exp (-expFieldBlockRate s M.delta *
        ((window : ℝ) + 2))) := by
  let R := expFieldBlockRate s M.delta
  have hRpos : 0 < R := by
    unfold R expFieldBlockRate
    exact div_pos (sq_pos_of_pos hs)
      (mul_pos (mul_pos (by norm_num) expFieldMomentDenom_pos)
        (sq_pos_of_pos M.shellPrefix.delta_pos))
  have hraw := measure_expFieldLargeBad_le M hs hs1 hh hsmall hsmallh
    (m0 := m0) (window := window)
  have hsum : Summable fun q : ℕ ↦
      Real.exp (-R * (((window + 1 + q : ℕ) : ℝ) + 1)) := by
    have hbase := summable_exp_neg_rate_nat R hRpos
    have heq : (fun q : ℕ ↦
        Real.exp (-R * (((window + 1 + q : ℕ) : ℝ) + 1))) =
      fun q : ℕ ↦ Real.exp (-R * ((window : ℝ) + 2)) *
        Real.exp (-R * (q : ℝ)) := by
      funext q
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [heq]
    exact hbase.mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ (Real.exp_pos _).le) hsum] at hraw
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  have hqhalf : Real.exp (-R) ≤ 1 / 2 := by
    have hneg : -R ≤ -Real.log 2 := neg_le_neg hR
    calc
      Real.exp (-R) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 hneg
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hden : (1 / 2 : ℝ) ≤ 1 - Real.exp (-R) := by linarith
  have hdenpos : 0 < 1 - Real.exp (-R) := by
    have hexp : Real.exp (-R) < 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (neg_lt_zero.mpr hRpos)
    linarith
  have hinv : (1 - Real.exp (-R))⁻¹ ≤ 2 := by
    calc
      (1 - Real.exp (-R))⁻¹ = 1 / (1 - Real.exp (-R)) := by rw [one_div]
      _ ≤ 1 / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hden
      _ = 2 := by norm_num
  have hfactor :
      (∑' q : ℕ, Real.exp (-R * (((window + 1 + q : ℕ) : ℝ) + 1))) =
        Real.exp (-R * ((window : ℝ) + 2)) * (1 - Real.exp (-R))⁻¹ := by
    rw [show (fun q : ℕ ↦
        Real.exp (-R * (((window + 1 + q : ℕ) : ℝ) + 1))) =
      fun q : ℕ ↦ Real.exp (-R * ((window : ℝ) + 2)) *
        Real.exp (-R * (q : ℝ)) by
        funext q
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring,
      tsum_mul_left, tsum_exp_neg_rate_nat R hRpos]
  rw [hfactor]
  change Real.exp (-R * ((window : ℝ) + 2)) * (1 - Real.exp (-R))⁻¹ ≤
    2 * Real.exp (-R * ((window : ℝ) + 2))
  calc
    _ ≤ Real.exp (-R * ((window : ℝ) + 2)) * 2 :=
      mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
    _ = _ := by ring

/-! ## Packed finite-radius configurations -/

def scaleCenterWindow (m0 M : ℕ) : Finset ℤ :=
  Finset.Icc (m0 : ℤ) ((m0 + M : ℕ) : ℤ)

def IsExpFieldPackedConfig (m0 M : ℕ) (U K : Finset ℤ)
    (radius : ℤ → ℕ) : Prop :=
  K ⊆ scaleCenterWindow m0 M ∧
    (∀ k ∈ K, radius k ≤ M) ∧
    (∀ a ∈ K, ∀ b ∈ K, a ≠ b →
      centeredIntIntervalsSeparated a (radius a) b (radius b)) ∧
    K.biUnion (fun k ↦ centeredIntInterval k (radius k)) = U

def expFieldPackedEvent {d : ℕ} (s : ℝ) (h m0 M : ℕ)
    (U : Finset ℤ) : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  if hex : ∃ K radius, IsExpFieldPackedConfig m0 M U K radius then
    let K := Classical.choose hex
    let radius := Classical.choose (Classical.choose_spec hex)
    ⋂ k ∈ K, expFieldBlockExceeds (d := d) s k.toNat (radius k) h
  else ∅

theorem mem_expFieldPackedEvent_of_config {d : ℕ}
    {s : ℝ} {h m0 M : ℕ} {U K : Finset ℤ} {radius : ℤ → ℕ}
    (hcfg : IsExpFieldPackedConfig m0 M U K radius)
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (homega : ∀ k ∈ K,
      omega ∈ expFieldBlockExceeds (d := d) s k.toNat (radius k) h) :
    omega ∈ expFieldPackedEvent (d := d) s h m0 M U := by
  classical
  let hex : ∃ K radius, IsExpFieldPackedConfig m0 M U K radius :=
    ⟨K, radius, hcfg⟩
  unfold expFieldPackedEvent
  rw [dif_pos hex]
  let K' : Finset ℤ := Classical.choose hex
  let radius' : ℤ → ℕ :=
    Classical.choose (Classical.choose_spec hex)
  have hcfg' : IsExpFieldPackedConfig m0 M U K' radius' :=
    Classical.choose_spec (Classical.choose_spec hex)
  have hinj := centeredIntInterval_configuration_injective K K' radius radius'
    hcfg.2.2.1 hcfg'.2.2.1 (hcfg.2.2.2.trans hcfg'.2.2.2.symm)
  simp only [Set.mem_iInter]
  intro k hk
  have hkK : k ∈ K := by rw [hinj.1]; exact hk
  have hr := hinj.2 k hkK
  simpa only [hr] using homega k hkK

private theorem packedConfig_centers_nonneg
    {m0 M : ℕ} {U K : Finset ℤ} {radius : ℤ → ℕ}
    (hcfg : IsExpFieldPackedConfig m0 M U K radius) :
    ∀ k ∈ K, 0 ≤ k := by
  intro k hk
  have hw := Finset.mem_Icc.mp (hcfg.1 hk)
  exact (Int.natCast_nonneg m0).trans hw.1

private theorem packedConfig_pairwiseDisjoint
    {m0 M : ℕ} {U K : Finset ℤ} {radius : ℤ → ℕ}
    (hcfg : IsExpFieldPackedConfig m0 M U K radius) :
    (K : Set ℤ).PairwiseDisjoint
      (fun k ↦ centeredIntInterval k (radius k)) := by
  intro a ha b hb hab
  change Disjoint (centeredIntInterval a (radius a))
    (centeredIntInterval b (radius b))
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact Finset.disjoint_left.mp (hcfg.2.2.1 a ha b hb hab).1 hxa
    (centeredIntInterval_subset_separatedIntInterval b (radius b) hxb)

private theorem packedConfig_union_card_eq
    {m0 M : ℕ} {U K : Finset ℤ} {radius : ℤ → ℕ}
    (hcfg : IsExpFieldPackedConfig m0 M U K radius) :
    U.card = ∑ k ∈ K, (2 * radius k + 1) := by
  rw [← hcfg.2.2.2, Finset.card_biUnion (packedConfig_pairwiseDisjoint hcfg)]
  simp

theorem measure_expFieldPackedEvent_le {d : ℕ}
    (Mdl : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {h m0 M : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * Mdl.delta ≤ s)
    (hsmallh : expFieldBlockConst d * Mdl.delta * Real.sqrt (h : ℝ) ≤ s)
    (U : Finset ℤ) :
    Mdl.P.toMeasure (expFieldPackedEvent (d := d) s h m0 M U) ≤
      ENNReal.ofReal (Real.exp
        (-expFieldBlockRate s Mdl.delta * (U.card : ℝ) / 2)) := by
  classical
  unfold expFieldPackedEvent
  split_ifs with hex
  · let K : Finset ℤ := Classical.choose hex
    let radius : ℤ → ℕ := Classical.choose (Classical.choose_spec hex)
    have hcfg : IsExpFieldPackedConfig m0 M U K radius :=
      Classical.choose_spec (Classical.choose_spec hex)
    have hfactor := measure_biInter_expFieldBlockExceeds_int_eq_prod
      Mdl s h K radius (packedConfig_centers_nonneg hcfg) hcfg.2.2.1
    rw [hfactor]
    calc
      ∏ k ∈ K, Mdl.P.toMeasure
          (expFieldBlockExceeds (d := d) s k.toNat (radius k) h) ≤
        ∏ k ∈ K, ENNReal.ofReal (Real.exp
          (-expFieldBlockRate s Mdl.delta * ((radius k : ℝ) + 1))) := by
        exact Finset.prod_le_prod fun k hk ↦
          measure_expFieldBlockExceeds_le_ofReal_exp
            Mdl hs hs1 hh hsmall hsmallh
      _ = ENNReal.ofReal (∏ k ∈ K, Real.exp
          (-expFieldBlockRate s Mdl.delta * ((radius k : ℝ) + 1))) :=
        (ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le).symm
      _ = ENNReal.ofReal (Real.exp
          (-expFieldBlockRate s Mdl.delta *
            (∑ k ∈ K, ((radius k : ℝ) + 1)))) := by
        congr 1
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (Real.exp
          (-expFieldBlockRate s Mdl.delta * (U.card : ℝ) / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have hR : 0 ≤ expFieldBlockRate s Mdl.delta := by
          unfold expFieldBlockRate
          exact (div_pos (sq_pos_of_pos hs)
            (mul_pos (mul_pos (by norm_num) expFieldMomentDenom_pos)
              (sq_pos_of_pos Mdl.shellPrefix.delta_pos))).le
        have hcard := packedConfig_union_card_eq hcfg
        have hsum : (U.card : ℝ) ≤
            2 * ∑ k ∈ K, ((radius k : ℝ) + 1) := by
          exact_mod_cast (show U.card ≤
            2 * ∑ k ∈ K, (radius k + 1) by
              rw [hcard]
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum
              intro k hk
              omega)
        nlinarith only [hsum, hR]
  · simp

noncomputable def expFieldSmallWitness {d : ℕ}
    (s : ℝ) (h M k : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℕ :=
  if hE : omega ∈ expFieldSmallBad (d := d) s h M k then
    Classical.choose hE else 0

theorem expFieldSmallWitness_le {d : ℕ}
    {s : ℝ} {h M k : ℕ} {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hE : omega ∈ expFieldSmallBad (d := d) s h M k) :
    expFieldSmallWitness s h M k omega ≤ M := by
  unfold expFieldSmallWitness
  rw [dif_pos hE]
  exact (Classical.choose_spec hE).1

theorem expFieldSmallWitness_mem {d : ℕ}
    {s : ℝ} {h M k : ℕ} {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (hE : omega ∈ expFieldSmallBad (d := d) s h M k) :
    omega ∈ expFieldBlockExceeds (d := d) s k
      (expFieldSmallWitness s h M k omega) h := by
  unfold expFieldSmallWitness
  rw [dif_pos hE]
  exact (Classical.choose_spec hE).2

/-- The finite-radius half-density event is covered by packed configuration
events whose shell-index union has the manuscript's one-sixth density. -/
theorem expField_smallDensity_subset_packedUnion {d : ℕ}
    (s theta : ℝ) (h m0 M : ℕ) :
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
        (expFieldSmallBad (d := d) s h M) m0 M omega} ⊆
      ⋃ U ∈ (threeScaleIndexWindow (m0 : ℤ) M).powerset,
        if theta * ((M : ℝ) + 1) / 6 ≤ (U.card : ℝ) then
          expFieldPackedEvent (d := d) s h m0 M U else ∅ := by
  classical
  intro omega homega
  let I : Finset ℕ := Finset.Icc m0 (m0 + M)
  let JN : Finset ℕ := I.filter fun k ↦
    omega ∈ expFieldSmallBad (d := d) s h M k
  let emb : ℕ ↪ ℤ := ⟨fun k ↦ (k : ℤ), Int.ofNat_injective⟩
  let J : Finset ℤ := JN.map emb
  let radius : ℤ → ℕ := fun k ↦
    expFieldSmallWitness s h M k.toNat omega
  have hJNcard : theta / 2 * ((M : ℝ) + 1) ≤ (JN.card : ℝ) := by
    have hden : 0 < ((M : ℝ) + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_right homega hden.le
    have hsum : (∑ k ∈ I,
        eventIndicator (expFieldSmallBad (d := d) s h M k) omega) =
        (JN.card : ℝ) := by
      rw [show (∑ k ∈ I,
          eventIndicator (expFieldSmallBad (d := d) s h M k) omega) =
        ∑ k ∈ JN, (1 : ℝ) by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hE : omega ∈ expFieldSmallBad (d := d) s h M k <;>
            simp [eventIndicator, hE]]
      simp
    rw [intervalEventDensity] at hmul
    rw [div_mul_cancel₀ _ hden.ne', hsum] at hmul
    exact hmul
  have hJcard : J.card = JN.card := by
    dsimp [J]
    exact Finset.card_map emb
  have hJmem : ∀ k ∈ J,
      (m0 : ℤ) ≤ k ∧ k ≤ ((m0 + M : ℕ) : ℤ) ∧
      omega ∈ expFieldSmallBad (d := d) s h M k.toNat := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hk
    dsimp [emb]
    have hnI := (Finset.mem_filter.mp hn).1
    have hnE := (Finset.mem_filter.mp hn).2
    have hnBounds := Finset.mem_Icc.mp hnI
    simpa only [Int.toNat_natCast] using ⟨by exact_mod_cast hnBounds.1,
      by exact_mod_cast hnBounds.2, hnE⟩
  have hradius : ∀ k ∈ J, radius k ≤ M := by
    intro k hk
    exact expFieldSmallWitness_le (hJmem k hk).2.2
  obtain ⟨K, hKJ, hKsep, hKcard⟩ :=
    exists_centeredIntInterval_packing_of_many_centers J radius
  let U : Finset ℤ := K.biUnion fun k ↦ centeredIntInterval k (radius k)
  have hcfg : IsExpFieldPackedConfig m0 M U K radius := by
    refine ⟨?_, ?_, hKsep, rfl⟩
    · intro k hk
      have hj := hJmem k (hKJ hk)
      exact Finset.mem_Icc.mpr ⟨hj.1, hj.2.1⟩
    · exact fun k hk ↦ hradius k (hKJ hk)
  have hUwindow : U ⊆ threeScaleIndexWindow (m0 : ℤ) M := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
    have hj := hJmem k (hKJ hk)
    have hr := hradius k (hKJ hk)
    simp only [centeredIntInterval, Finset.mem_Icc] at hxk
    rw [threeScaleIndexWindow, Finset.mem_Icc]
    constructor <;> omega
  have hUlarge : theta * ((M : ℝ) + 1) / 6 ≤ (U.card : ℝ) := by
    have hKcardR : (J.card : ℝ) ≤ 3 * (U.card : ℝ) := by
      exact_mod_cast hKcard
    rw [hJcard] at hKcardR
    nlinarith only [hJNcard, hKcardR]
  have homegaK : ∀ k ∈ K,
      omega ∈ expFieldBlockExceeds (d := d) s k.toNat (radius k) h := by
    intro k hk
    exact expFieldSmallWitness_mem (hJmem k (hKJ hk)).2.2
  simp only [Set.mem_iUnion]
  refine ⟨U, ⟨Finset.mem_powerset.mpr hUwindow, ?_⟩⟩
  rw [if_pos hUlarge]
  exact mem_expFieldPackedEvent_of_config hcfg homegaK

theorem measure_expFieldSmallDensity_le {d : ℕ}
    (Mdl : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {theta : ℝ}
    {h m0 M : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * Mdl.delta ≤ s)
    (hsmallh : expFieldBlockConst d * Mdl.delta * Real.sqrt (h : ℝ) ≤ s) :
    Mdl.P.toMeasure {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
        (expFieldSmallBad (d := d) s h M) m0 M omega} ≤
      ENNReal.ofReal (((2 : ℝ) ^ (3 * M + 1)) *
        Real.exp (-expFieldBlockRate s Mdl.delta * theta *
          ((M : ℝ) + 1) / 12)) := by
  let W := (threeScaleIndexWindow (m0 : ℤ) M).powerset
  let E : Finset ℤ → Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) := fun U ↦
    if theta * ((M : ℝ) + 1) / 6 ≤ (U.card : ℝ) then
      expFieldPackedEvent (d := d) s h m0 M U else ∅
  have hsub := expField_smallDensity_subset_packedUnion
    (d := d) s theta h m0 M
  have hR : 0 ≤ expFieldBlockRate s Mdl.delta := by
    unfold expFieldBlockRate
    exact (div_pos (sq_pos_of_pos hs)
      (mul_pos (mul_pos (by norm_num) expFieldMomentDenom_pos)
        (sq_pos_of_pos Mdl.shellPrefix.delta_pos))).le
  have hterm : ∀ U ∈ W, Mdl.P.toMeasure (E U) ≤
      ENNReal.ofReal (Real.exp (-expFieldBlockRate s Mdl.delta * theta *
        ((M : ℝ) + 1) / 12)) := by
    intro U hU
    unfold E
    split_ifs with hlarge
    · refine (measure_expFieldPackedEvent_le Mdl hs hs1 hh hsmall hsmallh U).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have hscaled := mul_le_mul_of_nonneg_left hlarge
        (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith only [hscaled, hR]
    · simp
  calc
    Mdl.P.toMeasure {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
        (expFieldSmallBad (d := d) s h M) m0 M omega} ≤
      Mdl.P.toMeasure (⋃ U ∈ W, E U) := measure_mono hsub
    _ ≤ ∑ U ∈ W, Mdl.P.toMeasure (E U) := measure_biUnion_finset_le W E
    _ ≤ ∑ _U ∈ W, ENNReal.ofReal
        (Real.exp (-expFieldBlockRate s Mdl.delta * theta *
          ((M : ℝ) + 1) / 12)) := Finset.sum_le_sum hterm
    _ = (W.card : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (-expFieldBlockRate s Mdl.delta * theta *
          ((M : ℝ) + 1) / 12)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (((2 : ℝ) ^ (3 * M + 1)) *
        Real.exp (-expFieldBlockRate s Mdl.delta * theta *
          ((M : ℝ) + 1) / 12)) := by
      rw [show W.card = 2 ^ (3 * M + 1) by
        exact card_powerset_threeScaleIndexWindow (m0 : ℤ) M]
      rw [← ENNReal.ofReal_natCast (2 ^ (3 * M + 1)),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      norm_cast

theorem measure_expFieldLargeDensity_le {d : ℕ}
    (Mdl : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {theta : ℝ} (htheta : 0 < theta)
    {h m0 M : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * Mdl.delta ≤ s)
    (hsmallh : expFieldBlockConst d * Mdl.delta * Real.sqrt (h : ℝ) ≤ s)
    (hR : Real.log 2 ≤ expFieldBlockRate s Mdl.delta) :
    Mdl.P.toMeasure {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
        (expFieldLargeBad (d := d) s h M) m0 M omega} ≤
      ENNReal.ofReal (2 * ((M : ℝ) + 1) *
        Real.exp (-expFieldBlockRate s Mdl.delta * ((M : ℝ) + 2))) := by
  let I := Finset.Icc m0 (m0 + M)
  have hsub : {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
      (expFieldLargeBad (d := d) s h M) m0 M omega} ⊆
      ⋃ k ∈ I, expFieldLargeBad (d := d) s h M k := by
    intro omega homega
    by_contra hnone
    have hall : ∀ k ∈ I, omega ∉ expFieldLargeBad (d := d) s h M k := by
      intro k hk hmem
      exact hnone (by simp only [Set.mem_iUnion]; exact ⟨k, ⟨hk, hmem⟩⟩)
    have hzero : intervalEventDensity
        (expFieldLargeBad (d := d) s h M) m0 M omega = 0 := by
      unfold intervalEventDensity
      have hsum : (∑ k ∈ Finset.Icc m0 (m0 + M),
          eventIndicator (expFieldLargeBad (d := d) s h M k) omega) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp [eventIndicator, hall k hk]
      rw [hsum, zero_div]
    change theta / 2 ≤ intervalEventDensity
      (expFieldLargeBad (d := d) s h M) m0 M omega at homega
    rw [hzero] at homega
    linarith
  calc
    Mdl.P.toMeasure {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
        (expFieldLargeBad (d := d) s h M) m0 M omega} ≤
      Mdl.P.toMeasure (⋃ k ∈ I, expFieldLargeBad (d := d) s h M k) :=
        measure_mono hsub
    _ ≤ ∑ k ∈ I, Mdl.P.toMeasure
        (expFieldLargeBad (d := d) s h M k) := measure_biUnion_finset_le I _
    _ ≤ ∑ _k ∈ I, ENNReal.ofReal (2 * Real.exp
        (-expFieldBlockRate s Mdl.delta * ((M : ℝ) + 2))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact measure_expFieldLargeBad_le_two_mul_exp
        Mdl hs hs1 hh hsmall hsmallh hR
    _ = (I.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp
        (-expFieldBlockRate s Mdl.delta * ((M : ℝ) + 2))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * ((M : ℝ) + 1) *
        Real.exp (-expFieldBlockRate s Mdl.delta * ((M : ℝ) + 2))) := by
      have hcard : I.card = M + 1 := by
        dsimp [I]
        rw [Nat.card_Icc]
        omega
      rw [hcard, ← ENNReal.ofReal_natCast (M + 1),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (M + 1))]
      congr 1
      push_cast
      ring

/-! ## Universal constant and final proposition -/

def expFieldConcentrationConst (d : ℕ) : ℝ :=
  1 + expFieldBlockConst d +
    192 * expFieldMomentDenom * (1 + Real.log 2)

theorem expFieldConcentrationConst_pos (d : ℕ) :
    0 < expFieldConcentrationConst d := by
  unfold expFieldConcentrationConst
  have hB := expFieldBlockConst_pos d
  have hD := expFieldMomentDenom_pos
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

private theorem expFieldConst_ge_block (d : ℕ) :
    expFieldBlockConst d ≤ expFieldConcentrationConst d := by
  unfold expFieldConcentrationConst
  have hD := expFieldMomentDenom_pos.le
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [expFieldBlockConst_pos d]

private theorem expFieldConst_sq_ge_rate {d : ℕ} :
    192 * expFieldMomentDenom * Real.log 2 ≤
      expFieldConcentrationConst d ^ 2 := by
  have hC : 1 ≤ expFieldConcentrationConst d := by
    unfold expFieldConcentrationConst
    have hB := (expFieldBlockConst_pos d).le
    have hD := expFieldMomentDenom_pos.le
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  have hpart : 192 * expFieldMomentDenom * Real.log 2 ≤
      expFieldConcentrationConst d := by
    unfold expFieldConcentrationConst
    have hB := (expFieldBlockConst_pos d).le
    have hD := expFieldMomentDenom_pos.le
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith
  nlinarith only [hC, hpart]

private theorem succ_le_two_pow_succ (M : ℕ) : M + 1 ≤ 2 ^ (M + 1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [pow_succ]
      omega

/-- Proposition `p.concentration.for.scales.exp.field`, specialized to the
GMC shell field (and hence with the manuscript's negative-index zero
extension built into `k-j`). -/
theorem concentration_exp_field {d : ℕ}
    (Mdl : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s theta : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    {h : ℕ} (hh : 1 ≤ h)
    (hsmall : Mdl.delta ≤ (expFieldConcentrationConst d)⁻¹ * s *
      Real.sqrt (min theta ((h : ℝ)⁻¹)) )
    (m0 window : ℕ) :
    Mdl.P.toMeasure {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta ≤ intervalEventDensity
        (expFieldBad (d := d) s h) m0 window omega} ≤
      ENNReal.ofReal (Real.exp
        (-(s ^ 2 * theta /
          (96 * expFieldMomentDenom * Mdl.delta ^ 2)) *
            ((window : ℝ) + 1))) := by
  let C := expFieldConcentrationConst d
  let B := expFieldBlockConst d
  let R := expFieldBlockRate s Mdl.delta
  have hdelta := Mdl.shellPrefix.delta_pos
  have hC : 0 < C := expFieldConcentrationConst_pos d
  have hB : 0 < B := expFieldBlockConst_pos d
  have hmin0 : 0 ≤ min theta ((h : ℝ)⁻¹) := by
    exact le_min htheta.le (inv_nonneg.mpr (Nat.cast_nonneg h))
  have hbudget : C * Mdl.delta ≤ s *
      Real.sqrt (min theta ((h : ℝ)⁻¹)) := by
    calc
      C * Mdl.delta ≤ C * (C⁻¹ * s *
          Real.sqrt (min theta ((h : ℝ)⁻¹))) :=
        mul_le_mul_of_nonneg_left hsmall hC.le
      _ = s * Real.sqrt (min theta ((h : ℝ)⁻¹)) := by
        field_simp [hC.ne']
  have hBoverC : B ≤ C := expFieldConst_ge_block d
  have hsmallB : B * Mdl.delta ≤ s := by
    have hsqrtOne : Real.sqrt (min theta ((h : ℝ)⁻¹)) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ((min_le_left _ _).trans htheta1)
    calc
      B * Mdl.delta ≤ C * Mdl.delta :=
        mul_le_mul_of_nonneg_right hBoverC hdelta.le
      _ ≤ s * Real.sqrt (min theta ((h : ℝ)⁻¹)) := hbudget
      _ ≤ s := mul_le_of_le_one_right hs.le hsqrtOne
  have hsmallBh : B * Mdl.delta * Real.sqrt (h : ℝ) ≤ s := by
    have hhR : 0 < (h : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
    have hminh : min theta ((h : ℝ)⁻¹) * (h : ℝ) ≤ 1 := by
      have hm := min_le_right theta ((h : ℝ)⁻¹)
      have hmul := mul_le_mul_of_nonneg_right hm hhR.le
      simpa [inv_mul_cancel₀ hhR.ne'] using hmul
    have hsqrtProd : Real.sqrt (min theta ((h : ℝ)⁻¹)) *
        Real.sqrt (h : ℝ) ≤ 1 := by
      calc
        _ = Real.sqrt (min theta ((h : ℝ)⁻¹) * (h : ℝ)) :=
          (Real.sqrt_mul hmin0 _).symm
        _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hminh
        _ = 1 := Real.sqrt_one
    calc
      B * Mdl.delta * Real.sqrt (h : ℝ) ≤
          C * Mdl.delta * Real.sqrt (h : ℝ) := by gcongr
      _ ≤ s * Real.sqrt (min theta ((h : ℝ)⁻¹)) *
          Real.sqrt (h : ℝ) :=
        mul_le_mul_of_nonneg_right hbudget (Real.sqrt_nonneg _)
      _ ≤ s := by
        calc
          _ = s * (Real.sqrt (min theta ((h : ℝ)⁻¹)) *
              Real.sqrt (h : ℝ)) := by ring
          _ ≤ s * 1 := mul_le_mul_of_nonneg_left hsqrtProd hs.le
          _ = s := mul_one _
  have hratio : C ^ 2 ≤ s ^ 2 * theta / Mdl.delta ^ 2 := by
    have hsq := pow_le_pow_left₀
      (mul_nonneg hC.le hdelta.le) hbudget 2
    have hsqrtSq : Real.sqrt (min theta ((h : ℝ)⁻¹)) ^ 2 =
        min theta ((h : ℝ)⁻¹) := Real.sq_sqrt hmin0
    have hminTheta := min_le_left theta ((h : ℝ)⁻¹)
    rw [le_div_iff₀ (sq_pos_of_pos hdelta)]
    nlinarith only [hsq, hsqrtSq, hminTheta, sq_nonneg s]
  have hRtheta : 96 * Real.log 2 ≤ R * theta := by
    have hCsq := expFieldConst_sq_ge_rate (d := d)
    have hrateEq : R * theta =
        (s ^ 2 * theta / Mdl.delta ^ 2) / (2 * expFieldMomentDenom) := by
      unfold R expFieldBlockRate
      field_simp [hdelta.ne', expFieldMomentDenom_pos.ne']
    rw [hrateEq, le_div_iff₀ (mul_pos (by norm_num) expFieldMomentDenom_pos)]
    nlinarith only [hCsq, hratio]
  have hRlog : Real.log 2 ≤ R := by
    have htheta0 := htheta.le
    have hR0 : 0 ≤ R := by
      unfold R expFieldBlockRate
      exact div_nonneg (sq_nonneg s)
        (mul_nonneg (mul_nonneg (by norm_num) expFieldMomentDenom_pos.le)
          (sq_nonneg Mdl.delta))
    have hmul := mul_le_mul_of_nonneg_left htheta1 hR0
    nlinarith only [hRtheta, hmul, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  let E := {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta ≤ intervalEventDensity
    (expFieldBad (d := d) s h) m0 window omega}
  let ES := {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
    (expFieldSmallBad (d := d) s h window) m0 window omega}
  let EL := {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | theta / 2 ≤ intervalEventDensity
    (expFieldLargeBad (d := d) s h window) m0 window omega}
  have hsub : E ⊆ ES ∪ EL := fun omega hbad ↦
    expField_density_split s theta h m0 window omega hbad
  have hES := measure_expFieldSmallDensity_le Mdl hs hs1 hh hsmallB hsmallBh
    (theta := theta) (m0 := m0) (M := window)
  have hEL := measure_expFieldLargeDensity_le Mdl hs hs1 htheta hh
    hsmallB hsmallBh hRlog (m0 := m0) (M := window)
  have hsmallNum : ((2 : ℝ) ^ (3 * window + 1)) *
      Real.exp (-R * theta * ((window : ℝ) + 1) / 12) ≤
      Real.exp (-R * theta * ((window : ℝ) + 1) / 24) := by
    have hpow : (2 : ℝ) ^ (3 * window + 1) =
        Real.exp (((3 * window + 1 : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [hpow, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hw : 0 ≤ (window : ℝ) + 1 := by positivity
    have hcount : (((3 * window + 1 : ℕ) : ℝ) ≤
        4 * ((window : ℝ) + 1)) := by
      push_cast
      nlinarith
    have hlog0 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hcountlog := mul_le_mul_of_nonneg_right hcount hlog0
    have hRwindow := mul_le_mul_of_nonneg_right hRtheta hw
    nlinarith only [hcountlog, hRwindow]
  have hlargeNum : 2 * ((window : ℝ) + 1) *
      Real.exp (-R * ((window : ℝ) + 2)) ≤
      Real.exp (-R * theta * ((window : ℝ) + 1) / 24) := by
    have hnat := succ_le_two_pow_succ window
    have hcoef : 2 * ((window : ℝ) + 1) ≤
        (2 : ℝ) ^ (window + 2) := by
      exact_mod_cast (show 2 * (window + 1) ≤ 2 ^ (window + 2) by
        rw [pow_succ]
        simpa [mul_comm] using Nat.mul_le_mul_left 2 hnat)
    have hpow : (2 : ℝ) ^ (window + 2) =
        Real.exp (((window + 2 : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (2 : ℝ) ^ (window + 2) *
          Real.exp (-R * ((window : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ = Real.exp ((((window + 2 : ℕ) : ℝ) * Real.log 2) -
          R * ((window : ℝ) + 2)) := by rw [hpow, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.2
        have hw : 0 ≤ (window : ℝ) + 1 := by positivity
        have hw2 : 0 ≤ (window : ℝ) + 2 := by positivity
        have htheta0 := htheta.le
        have hR0 : 0 ≤ R := by
          unfold R expFieldBlockRate
          exact div_nonneg (sq_nonneg s)
            (mul_nonneg (mul_nonneg (by norm_num) expFieldMomentDenom_pos.le)
              (sq_nonneg Mdl.delta))
        have hRbig : 2 * Real.log 2 ≤ R := by nlinarith only [hRtheta,
          htheta1, htheta0, hR0, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
        push_cast
        have hlogpart := mul_le_mul_of_nonneg_right hRbig hw2
        have hthetaW : theta * ((window : ℝ) + 1) ≤
            (window : ℝ) + 2 := by
          calc
            theta * ((window : ℝ) + 1) ≤ 1 * ((window : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right htheta1 hw
            _ ≤ (window : ℝ) + 2 := by linarith
        have hratepart := mul_le_mul_of_nonneg_left hthetaW hR0
        have hRW0 : 0 ≤ R * ((window : ℝ) + 2) := mul_nonneg hR0 hw2
        calc
          ((window : ℝ) + 2) * Real.log 2 - R * ((window : ℝ) + 2) ≤
              -(R * ((window : ℝ) + 2)) / 2 := by
            nlinarith only [hlogpart]
          _ ≤ -(R * (theta * ((window : ℝ) + 1))) / 24 := by
            nlinarith only [hratepart, hRW0]
          _ = -R * theta * ((window : ℝ) + 1) / 24 := by ring
  have hA : 48 * Real.log 2 ≤ R * theta * ((window : ℝ) + 1) := by
    have hw : 1 ≤ (window : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) window
      linarith
    have hmul := mul_le_mul_of_nonneg_left hw
      (mul_nonneg (show 0 ≤ R by
        unfold R expFieldBlockRate
        exact div_nonneg (sq_nonneg s)
          (mul_nonneg (mul_nonneg (by norm_num) expFieldMomentDenom_pos.le)
            (sq_nonneg Mdl.delta))) htheta.le)
    calc
      48 * Real.log 2 ≤ 96 * Real.log 2 := by
        have hlog0 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      _ ≤ R * theta := hRtheta
      _ = R * theta * 1 := by ring
      _ ≤ R * theta * ((window : ℝ) + 1) := hmul
  have habsorb : 2 * Real.exp (-R * theta * ((window : ℝ) + 1) / 24) ≤
      Real.exp (-R * theta * ((window : ℝ) + 1) / 48) := by
    have htwo : (2 : ℝ) = Real.exp (Real.log 2) :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
    rw [htwo, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith only [hA]
  calc
    Mdl.P.toMeasure E ≤ Mdl.P.toMeasure (ES ∪ EL) := measure_mono hsub
    _ ≤ Mdl.P.toMeasure ES + Mdl.P.toMeasure EL := measure_union_le _ _
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (3 * window + 1)) *
          Real.exp (-R * theta * ((window : ℝ) + 1) / 12)) +
        ENNReal.ofReal (2 * ((window : ℝ) + 1) *
          Real.exp (-R * ((window : ℝ) + 2))) := add_le_add hES hEL
    _ ≤ ENNReal.ofReal (Real.exp (-R * theta * ((window : ℝ) + 1) / 24)) +
        ENNReal.ofReal (Real.exp (-R * theta * ((window : ℝ) + 1) / 24)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hsmallNum) (ENNReal.ofReal_le_ofReal hlargeNum)
    _ = ENNReal.ofReal (2 * Real.exp (-R * theta * ((window : ℝ) + 1) / 24)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le] <;> try positivity
      congr 1
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-R * theta * ((window : ℝ) + 1) / 48)) :=
      ENNReal.ofReal_le_ofReal habsorb
    _ = ENNReal.ofReal (Real.exp
        (-(s ^ 2 * theta /
          (96 * expFieldMomentDenom * Mdl.delta ^ 2)) *
            ((window : ℝ) + 1))) := by
      congr 2
      unfold R expFieldBlockRate
      field_simp [hdelta.ne', expFieldMomentDenom_pos.ne']
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
