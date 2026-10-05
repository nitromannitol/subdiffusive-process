
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
public import MarkovProcess.Path.StoppedValueMeasurability

@[expose] public section

/-!
# Hitting a closed set after a stopping time

Support for the chronological-selection lemma
(setup `13619-13637`, proof
`13659-13670`);.

`hitAfter K a p` is the first time at or after `a` at which the continuous path
`p` meets `K`.  This file proves the two facts that the greedy recursion needs.

* `hitAfter_attained`: for a **closed** target the infimum is attained whenever
  it is finite (the corresponding statement for open
  targets is false).
* `measurableSet_inter_hitAfter_le`: the hitting time after a stopping time
  `S` is a stopping time, in the *history-indexed* form the recursion needs:
  the target is allowed to depend on the path through a countably valued index
  `idx` that is already known at time `S`.  The event
  `{hitAfter ≤ u}` is described by the countably many rational samples in
  `(S, u]` together with the endpoint, so no right-continuity of the filtration
  is used.

Everything is measure-free: no law, no completion, no exceptional set.
-/

set_option autoImplicit false

open Set MeasureTheory MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Elementary properties of `hitAfter` -/

/-- Nothing is hit before the starting time. -/
theorem le_hitAfter (K : Set (Vec d)) (a : ℝ≥0∞) (p : ContinuousPath (Vec d)) :
    a ≤ hitAfter K a p := by
  simp only [hitAfter]
  refine le_sInf ?_
  rintro s ⟨t, rfl, hs, -⟩
  exact hs

/-- A visit to `K` at a time at or after `a` bounds the hitting time. -/
theorem hitAfter_le_of_mem (K : Set (Vec d)) (a : ℝ≥0∞) (p : ContinuousPath (Vec d))
    (t : ℝ≥0) (hat : a ≤ (t : ℝ≥0∞)) (ht : p t ∈ K) : hitAfter K a p ≤ (t : ℝ≥0∞) := by
  simp only [hitAfter]
  exact sInf_le ⟨t, rfl, hat, ht⟩

/-- The empty target is never hit. -/
theorem hitAfter_empty (a : ℝ≥0∞) (p : ContinuousPath (Vec d)) :
    hitAfter (∅ : Set (Vec d)) a p = ⊤ := by
  rw [hitAfter]
  have h : {s : ℝ≥0∞ | ∃ t : ℝ≥0, (t : ℝ≥0∞) = s ∧ a ≤ s ∧ p t ∈ (∅ : Set (Vec d))} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨t, -, -, ht⟩ := hs
    exact ht
  rw [h, sInf_empty]

/-- **Attainment.** For a closed target a finite hitting time is realised by an actual
visit. -/
theorem hitAfter_attained (K : Set (Vec d)) (hK : IsClosed K) (a : ℝ≥0∞)
    (p : ContinuousPath (Vec d)) (h : hitAfter K a p < ⊤) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) = hitAfter K a p ∧ a ≤ (t : ℝ≥0∞) ∧ p t ∈ K := by
  have hTclosed : IsClosed {t : ℝ≥0 | a ≤ (t : ℝ≥0∞) ∧ p t ∈ K} :=
    (isClosed_Ici.preimage ENNReal.continuous_coe).inter (hK.preimage p.continuous)
  have hTne : {t : ℝ≥0 | a ≤ (t : ℝ≥0∞) ∧ p t ∈ K}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hempty : {s : ℝ≥0∞ | ∃ t : ℝ≥0, (t : ℝ≥0∞) = s ∧ a ≤ s ∧ p t ∈ K} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro s ⟨t, rfl, hat, ht⟩
      have hmem : t ∈ {t : ℝ≥0 | a ≤ (t : ℝ≥0∞) ∧ p t ∈ K} := ⟨hat, ht⟩
      rw [hne] at hmem
      exact hmem
    rw [hitAfter, hempty, sInf_empty] at h
    exact absurd rfl h.ne
  obtain ⟨hc1, hc2⟩ := hTclosed.csInf_mem hTne (OrderBot.bddBelow _)
  refine ⟨sInf {t : ℝ≥0 | a ≤ (t : ℝ≥0∞) ∧ p t ∈ K}, ?_, hc1, hc2⟩
  refine le_antisymm ?_ (hitAfter_le_of_mem K a p _ hc1 hc2)
  simp only [hitAfter]
  refine le_sInf ?_
  rintro s ⟨t, rfl, hat, ht⟩
  exact ENNReal.coe_le_coe.mpr (csInf_le (OrderBot.bddBelow _) ⟨hat, ht⟩)

/-- For a closed target, `hitAfter ≤ u` is an actual visit in `[S, u]`. -/
theorem hitAfter_le_coe_iff (K : Set (Vec d)) (hK : IsClosed K) (a : ℝ≥0∞)
    (p : ContinuousPath (Vec d)) (u : ℝ≥0) :
    hitAfter K a p ≤ (u : ℝ≥0∞) ↔ ∃ t : ℝ≥0, t ≤ u ∧ a ≤ (t : ℝ≥0∞) ∧ p t ∈ K := by
  constructor
  · intro hle
    obtain ⟨t, ht, hat, htK⟩ :=
      hitAfter_attained K hK a p (lt_of_le_of_lt hle (ENNReal.coe_lt_top))
    exact ⟨t, ENNReal.coe_le_coe.mp (ht.trans_le hle), hat, htK⟩
  · rintro ⟨t, htu, hat, htK⟩
    exact (hitAfter_le_of_mem K a p t hat htK).trans (ENNReal.coe_le_coe.mpr htu)

/-! ### Countable-sample description of a closed hit -/

/-- The distance from a coordinate to a fixed set is measurable in the canonical filtration
at any later time. -/
theorem measurable_infDist_coord (u q : ℝ≥0) (hqu : q ≤ u) (K : Set (Vec d)) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
      (fun p : ContinuousPath (Vec d) => Metric.infDist (p q) K) := by
  have hcoord : Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
      (ContinuousPath.coordinateProcess (alpha := Vec d) q) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le (⟨q, Set.mem_Iic.mpr hqu⟩ : Set.Iic u) le_rfl
  have hcoord' : Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) u,
      borel (Vec d)] (ContinuousPath.coordinateProcess (alpha := Vec d) q) :=
    hcoord.mono le_rfl (le_of_eq BorelSpace.measurable_eq.symm)
  exact (Metric.continuous_infDist_pt (s := K)).borel_measurable.comp hcoord'

/-- Continuity of the path near a visit time. -/
theorem exists_delta_infDist_lt (K : Set (Vec d)) (p : ContinuousPath (Vec d))
    (t : ℝ≥0) (ht : p t ∈ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ s : ℝ≥0, |(s : ℝ) - (t : ℝ)| < δ → Metric.infDist (p s) K < ε := by
  have hg : Continuous (fun s : ℝ≥0 => Metric.infDist (p s) K) :=
    (Metric.continuous_infDist_pt K).comp p.continuous
  have hzero : Metric.infDist (p t) K = 0 := Metric.infDist_zero_of_mem ht
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hg t ε hε
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hst : dist s t < δ := by rw [NNReal.dist_eq]; exact hs
  have h := hball s hst
  rw [Real.dist_eq, hzero, sub_zero] at h
  rw [abs_lt] at h
  exact h.2

/-- Compactness: arbitrarily small distance to a closed set on a compact time window forces an
actual visit. -/
theorem exists_mem_of_infDist_small (K : Set (Vec d)) (hK : IsClosed K)
    (hKne : K.Nonempty) (p : ContinuousPath (Vec d)) (a b : ℝ≥0) (hab : a ≤ b)
    (h : ∀ n : ℕ, ∃ q : ℝ≥0, a ≤ q ∧ q ≤ b ∧ Metric.infDist (p q) K < 1 / (n + 1 : ℝ)) :
    ∃ t : ℝ≥0, a ≤ t ∧ t ≤ b ∧ p t ∈ K := by
  have hg : Continuous (fun s : ℝ≥0 => Metric.infDist (p s) K) :=
    (Metric.continuous_infDist_pt K).comp p.continuous
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    (Set.nonempty_Icc.mpr hab) hg.continuousOn
  have hle : Metric.infDist (p t) K ≤ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hcon
    obtain ⟨q, hq1, hq2, hq3⟩ := h n
    have hmin' := hmin (Set.mem_Icc.mpr ⟨hq1, hq2⟩)
    simp only [mem_ofPred_eq] at hmin'
    linarith
  have hzero : Metric.infDist (p t) K = 0 := le_antisymm hle Metric.infDist_nonneg
  have hmemK : p t ∈ K := by
    by_contra hcon
    exact absurd hzero ((hK.notMem_iff_infDist_pos hKne).mp hcon).ne'
  exact ⟨t, ht.1, ht.2, hmemK⟩

/-- A strict `ENNReal` bound is witnessed by a rational sample. -/
theorem lt_coe_iff_exists_rat (S : ℝ≥0∞) (c : ℝ≥0) :
    S < (c : ℝ≥0∞) ↔ ∃ q : ℚ, S ≤ ((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ≥0∞) ∧
      Real.toNNReal (q : ℝ) < c := by
  constructor
  · intro hS
    have hne : S ≠ ⊤ := ne_top_of_lt hS
    have hStop : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hne
    have hlt : S.toNNReal < c := by
      refine ENNReal.coe_lt_coe.mp ?_
      rw [hStop]; exact hS
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.mpr hlt)
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (NNReal.coe_nonneg _) hq1)
    have hcoe : ((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ) = (q : ℝ) := Real.coe_toNNReal _ hq0
    refine ⟨q, ?_, ?_⟩
    · rw [← hStop]
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe, hcoe]
      exact hq1.le
    · rw [← NNReal.coe_lt_coe, hcoe]
      exact hq2
  · rintro ⟨q, hle, hlt⟩
    exact lt_of_le_of_lt hle (ENNReal.coe_lt_coe.mpr hlt)

/-- A rational sample close to a given time, inside a half-open window. -/
theorem exists_rat_near_of_lt {a b t : ℝ≥0} (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, a < Real.toNNReal (q : ℝ) ∧ Real.toNNReal (q : ℝ) ≤ b ∧
      |((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ) - (t : ℝ)| < δ := by
  have hab' : (a : ℝ) < (b : ℝ) := NNReal.coe_lt_coe.mpr hab
  have ha : (0 : ℝ) ≤ (a : ℝ) := NNReal.coe_nonneg a
  have hat' : (a : ℝ) ≤ (t : ℝ) := NNReal.coe_le_coe.mpr hat
  have htb' : (t : ℝ) ≤ (b : ℝ) := NNReal.coe_le_coe.mpr htb
  have hlr : max (a : ℝ) ((t : ℝ) - δ) < min (b : ℝ) ((t : ℝ) + δ) :=
    max_lt (lt_min hab' (by linarith)) (lt_min (by linarith) (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlr
  have hmax1 : (a : ℝ) ≤ max (a : ℝ) ((t : ℝ) - δ) := le_max_left _ _
  have hmax2 : (t : ℝ) - δ ≤ max (a : ℝ) ((t : ℝ) - δ) := le_max_right _ _
  have hmin1 : min (b : ℝ) ((t : ℝ) + δ) ≤ (b : ℝ) := min_le_left _ _
  have hmin2 : min (b : ℝ) ((t : ℝ) + δ) ≤ (t : ℝ) + δ := min_le_right _ _
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hcoe : ((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ) = (q : ℝ) := Real.coe_toNNReal _ hq0
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hcoe]; linarith
  · rw [← NNReal.coe_le_coe, hcoe]; linarith
  · rw [hcoe, abs_lt]; constructor <;> linarith

/-! ### The hitting time after a stopping time -/

variable {iota : Type*}

/-- On a history cell, the strict inequality `S < c` is measurable at any later time. -/
theorem measurableSet_inter_lt (idx : ContinuousPath (Vec d) → iota)
    (S : ContinuousPath (Vec d) → ℝ≥0∞)
    (hS : ∀ (n : iota) (v : ℝ≥0),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) v]
        ({p | idx p = n} ∩ {p | S p ≤ (v : ℝ≥0∞)}))
    (n : iota) (u c : ℝ≥0) (hcu : c ≤ u) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
      ({p | idx p = n} ∩ {p | S p < (c : ℝ≥0∞)}) := by
  have hset : {p : ContinuousPath (Vec d) | idx p = n} ∩ {p | S p < (c : ℝ≥0∞)}
      = ⋃ q : ℚ, (if Real.toNNReal (q : ℝ) < c then
          {p : ContinuousPath (Vec d) | idx p = n} ∩
            {p | S p ≤ ((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ≥0∞)} else ∅) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hn, hlt⟩
      obtain ⟨q, hq1, hq2⟩ := (lt_coe_iff_exists_rat (S p) c).mp hlt
      exact ⟨q, by rw [ite_eq_left hq2]; exact ⟨hn, hq1⟩⟩
    · rintro ⟨q, hq⟩
      by_cases hqc : Real.toNNReal (q : ℝ) < c
      · rw [ite_eq_left hqc] at hq
        exact ⟨hq.1, (lt_coe_iff_exists_rat (S p) c).mpr ⟨q, hq.2, hqc⟩⟩
      · rw [ite_eq_right hqc] at hq
        exact absurd hq (Set.notMem_empty p)
  rw [hset]
  refine MeasurableSet.iUnion fun q => ?_
  by_cases hqc : Real.toNNReal (q : ℝ) < c
  · rw [ite_eq_left hqc]
    exact (ContinuousPath.canonicalFiltration (alpha := Vec d)).mono
      (le_trans hqc.le hcu) _ (hS n (Real.toNNReal (q : ℝ)))
  · rw [ite_eq_right hqc]
    exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := Vec d) u)

/-- **The hitting time of a history-indexed closed target after a stopping time is a stopping
time**, in the refined form the greedy recursion needs: the event stays inside the history cell
`{idx = n}`. -/
theorem measurableSet_inter_hitAfter_le [Countable iota]
    (K : iota → Set (Vec d)) (hK : ∀ n, IsClosed (K n))
    (idx : ContinuousPath (Vec d) → iota) (S : ContinuousPath (Vec d) → ℝ≥0∞)
    (hS : ∀ (n : iota) (v : ℝ≥0),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) v]
        ({p | idx p = n} ∩ {p | S p ≤ (v : ℝ≥0∞)}))
    (n : iota) (u : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
      ({p | idx p = n} ∩ {p | hitAfter (K (idx p)) (S p) p ≤ (u : ℝ≥0∞)}) := by
  have hrw : {p : ContinuousPath (Vec d) | idx p = n} ∩
      {p | hitAfter (K (idx p)) (S p) p ≤ (u : ℝ≥0∞)}
      = {p : ContinuousPath (Vec d) | idx p = n} ∩
        {p | hitAfter (K n) (S p) p ≤ (u : ℝ≥0∞)} := by
    ext p
    simp only [Set.mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [h1] at h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h1]; exact h2⟩
  rw [hrw]
  rcases Set.eq_empty_or_nonempty (K n) with hKn | hKn
  · have hempty : {p : ContinuousPath (Vec d) | idx p = n} ∩
        {p | hitAfter (K n) (S p) p ≤ (u : ℝ≥0∞)} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro p ⟨-, h2⟩
      rw [mem_ofPred_eq, hKn, hitAfter_empty] at h2
      exact absurd (top_le_iff.mp h2) (ENNReal.coe_ne_top)
    rw [hempty]
    exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := Vec d) u)
  · have hsplit : {p : ContinuousPath (Vec d) | idx p = n} ∩
        {p | hitAfter (K n) (S p) p ≤ (u : ℝ≥0∞)}
        = (⋂ m : ℕ, ⋃ q : ℚ, (if Real.toNNReal (q : ℝ) ≤ u then
              ({p : ContinuousPath (Vec d) | idx p = n} ∩
                {p | S p < ((Real.toNNReal (q : ℝ) : ℝ≥0) : ℝ≥0∞)}) ∩
                {p | Metric.infDist (p (Real.toNNReal (q : ℝ))) (K n) < 1 / (m + 1 : ℝ)}
            else ∅))
          ∪ ((({p : ContinuousPath (Vec d) | idx p = n} ∩ {p | S p ≤ (u : ℝ≥0∞)}) \
              ({p : ContinuousPath (Vec d) | idx p = n} ∩ {p | S p < (u : ℝ≥0∞)})) ∩
              {p | p u ∈ K n}) := by
      ext p
      constructor
      · rintro ⟨hidx, hhit⟩
        obtain ⟨t, htu, hSt, htK⟩ :=
          (hitAfter_le_coe_iff (K n) (hK n) (S p) p u).mp hhit
        by_cases hSu : S p < (u : ℝ≥0∞)
        · refine Or.inl ?_
          refine Set.mem_iInter.mpr fun m => ?_
          have hSne : S p ≠ ⊤ := ne_top_of_lt hSu
          have hacoe : (((S p).toNNReal : ℝ≥0) : ℝ≥0∞) = S p := ENNReal.coe_toNNReal hSne
          have hau : (S p).toNNReal < u := by
            rw [← ENNReal.coe_lt_coe, hacoe]; exact hSu
          have hat : (S p).toNNReal ≤ t := by
            rw [← ENNReal.coe_le_coe, hacoe]; exact hSt
          obtain ⟨delta, hdelta, hball⟩ :=
            exists_delta_infDist_lt (K n) p t htK (1 / (m + 1 : ℝ)) (by positivity)
          obtain ⟨q, hq1, hq2, hq3⟩ := exists_rat_near_of_lt hau hat htu hdelta
          refine Set.mem_iUnion.mpr ⟨q, ?_⟩
          rw [ite_eq_left hq2]
          refine ⟨⟨hidx, ?_⟩, hball _ hq3⟩
          rw [mem_ofPred_eq, ← hacoe]
          exact ENNReal.coe_lt_coe.mpr hq1
        · refine Or.inr ⟨⟨⟨hidx, hSt.trans (ENNReal.coe_le_coe.mpr htu)⟩, ?_⟩, ?_⟩
          · exact fun hc => hSu hc.2
          · have hSeq : S p = (u : ℝ≥0∞) :=
              le_antisymm (hSt.trans (ENNReal.coe_le_coe.mpr htu)) (not_lt.mp hSu)
            have hut : u ≤ t := by
              rw [← ENNReal.coe_le_coe, ← hSeq]; exact hSt
            have : t = u := le_antisymm htu hut
            rw [mem_ofPred_eq, ← this]
            exact htK
      · rintro (h1 | h2)
        · have h0 := Set.mem_iInter.mp h1 0
          obtain ⟨q0, hq0⟩ := Set.mem_iUnion.mp h0
          by_cases hq0u : Real.toNNReal (q0 : ℝ) ≤ u
          swap
          · rw [ite_eq_right hq0u] at hq0; exact absurd hq0 (Set.notMem_empty p)
          rw [ite_eq_left hq0u] at hq0
          have hidx : idx p = n := hq0.1.1
          have hSlt : S p < ((Real.toNNReal (q0 : ℝ) : ℝ≥0) : ℝ≥0∞) := hq0.1.2
          have hSne : S p ≠ ⊤ := ne_top_of_lt hSlt
          have hacoe : (((S p).toNNReal : ℝ≥0) : ℝ≥0∞) = S p := ENNReal.coe_toNNReal hSne
          have hau : (S p).toNNReal ≤ u := by
            have : (S p).toNNReal ≤ Real.toNNReal (q0 : ℝ) := by
              rw [← ENNReal.coe_le_coe, hacoe]; exact hSlt.le
            exact this.trans hq0u
          have hfor : ∀ m : ℕ, ∃ q' : ℝ≥0, (S p).toNNReal ≤ q' ∧ q' ≤ u ∧
              Metric.infDist (p q') (K n) < 1 / (m + 1 : ℝ) := by
            intro m
            obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp h1 m)
            by_cases hqu : Real.toNNReal (q : ℝ) ≤ u
            swap
            · rw [ite_eq_right hqu] at hq; exact absurd hq (Set.notMem_empty p)
            rw [ite_eq_left hqu] at hq
            refine ⟨Real.toNNReal (q : ℝ), ?_, hqu, hq.2⟩
            rw [← ENNReal.coe_le_coe, hacoe]
            exact hq.1.2.le
          obtain ⟨t, hat, htu, htK⟩ :=
            exists_mem_of_infDist_small (K n) (hK n) hKn p (S p).toNNReal u hau hfor
          refine ⟨hidx, ?_⟩
          exact (hitAfter_le_of_mem (K n) (S p) p t
            (le_trans (le_of_eq hacoe.symm) (ENNReal.coe_le_coe.mpr hat)) htK).trans
            (ENNReal.coe_le_coe.mpr htu)
        · exact ⟨h2.1.1.1, hitAfter_le_of_mem (K n) (S p) p u h2.1.1.2 h2.2⟩
    rw [hsplit]
    refine MeasurableSet.union ?_ ?_
    · refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
      by_cases hqu : Real.toNNReal (q : ℝ) ≤ u
      · rw [ite_eq_left hqu]
        refine MeasurableSet.inter
          (measurableSet_inter_lt idx S hS n u (Real.toNNReal (q : ℝ)) hqu) ?_
        exact measurable_infDist_coord u (Real.toNNReal (q : ℝ)) hqu (K n)
          (measurableSet_Iio : MeasurableSet (Set.Iio (1 / (m + 1 : ℝ))))
      · rw [ite_eq_right hqu]
        exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := Vec d) u)
    · refine MeasurableSet.inter
        (MeasurableSet.diff (hS n u) (measurableSet_inter_lt idx S hS n u u le_rfl)) ?_
      exact (ContinuousPath.measurable_coordinateProcess_canonicalFiltration (alpha := Vec d) u)
        (hK n).measurableSet

/-- The hitting time of a history-indexed closed target after a stopping time is a stopping
time. -/
theorem isStoppingTime_hitAfterIdx [Countable iota]
    (K : iota → Set (Vec d)) (hK : ∀ n, IsClosed (K n))
    (idx : ContinuousPath (Vec d) → iota) (S : ContinuousPath (Vec d) → ℝ≥0∞)
    (hS : ∀ (n : iota) (v : ℝ≥0),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) v]
        ({p | idx p = n} ∩ {p | S p ≤ (v : ℝ≥0∞)})) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun p => hitAfter (K (idx p)) (S p) p) := by
  intro u
  have hcover : {p : ContinuousPath (Vec d) | hitAfter (K (idx p)) (S p) p ≤ (u : ℝ≥0∞)}
      = ⋃ n : iota, ({p : ContinuousPath (Vec d) | idx p = n} ∩
          {p | hitAfter (K (idx p)) (S p) p ≤ (u : ℝ≥0∞)}) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨idx p, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  show MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
    {p : ContinuousPath (Vec d) | hitAfter (K (idx p)) (S p) p ≤ (u : ℝ≥0∞)}
  rw [hcover]
  exact MeasurableSet.iUnion fun n => measurableSet_inter_hitAfter_le K hK idx S hS n u

/-! ### The state at a stopping time -/

/-- **Stopped evaluation.** On the event that the stopping time `e` is at most `u`, the position
of the path at `e` is measurable in the canonical filtration at `u` ("stopped-coordinate measurability"). -/
theorem measurableSet_inter_stoppedCoord (e : ContinuousPath (Vec d) → ℝ≥0∞)
    (he : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d)) e)
    (B : Set (Vec d)) (hB : MeasurableSet B) (u : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) u]
      ({p | e p ≤ (u : ℝ≥0∞)} ∩ {p | p (e p).toNNReal ∈ B}) := by
  set sigma : ContinuousPath (Vec d) → ℝ≥0 := fun p => (min (e p) (u : ℝ≥0∞)).toNNReal with hsig
  have hcoe : ∀ p, ((sigma p : ℝ≥0) : ℝ≥0∞) = min (e p) (u : ℝ≥0∞) := fun p =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hst : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun p => ((sigma p : ℝ≥0) : WithTop ℝ≥0)) := by
    have heq : (fun p => ((sigma p : ℝ≥0) : WithTop ℝ≥0))
        = fun p => min (e p) ((u : ℝ≥0) : WithTop ℝ≥0) := funext hcoe
    rw [heq]
    exact he.min_const u
  have hmeas : MeasurableSet[hst.measurableSpace] ((fun p => p (sigma p)) ⁻¹' B) :=
    ContinuousPath.measurable_eval_stoppingTime sigma hst hB
  have hsplit := ((hst.measurableSet _).mp hmeas).2 u
  have huniv : {p : ContinuousPath (Vec d) | ((sigma p : ℝ≥0) : WithTop ℝ≥0)
      ≤ ((u : ℝ≥0) : WithTop ℝ≥0)} = Set.univ := by
    ext p
    simp only [mem_ofPred_eq, Set.mem_univ, iff_true]
    show ((sigma p : ℝ≥0) : ℝ≥0∞) ≤ ((u : ℝ≥0) : ℝ≥0∞)
    rw [hcoe p]
    exact min_le_right (e p) ((u : ℝ≥0) : ℝ≥0∞)
  rw [huniv, Set.inter_univ] at hsplit
  have hfinal : {p : ContinuousPath (Vec d) | e p ≤ (u : ℝ≥0∞)} ∩
      {p | p (e p).toNNReal ∈ B}
      = {p : ContinuousPath (Vec d) | e p ≤ (u : ℝ≥0∞)} ∩ ((fun p => p (sigma p)) ⁻¹' B) := by
    ext p
    simp only [Set.mem_inter_iff, mem_ofPred_eq, Set.mem_preimage]
    refine and_congr_right fun hle => ?_
    have : sigma p = (e p).toNNReal := by
      simp only [hsig]
      rw [min_eq_left hle]
    rw [this]
  rw [hfinal]
  exact MeasurableSet.inter (he u) hsplit

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

end
