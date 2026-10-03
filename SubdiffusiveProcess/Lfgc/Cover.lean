module

public import Mathlib

@[expose] public section

/-!
# Interval-measurable tail covers

`IsTailCover P B A f` says that the set `A` is covered by a sequence `W h`, `h : ℕ+`, with
`W h` measurable for the σ-algebra `B h` and `P (W h) ≤ f h`.  This file proves the
combinators used to assemble such covers: monotonicity, finite unions, countable unions of
single window-measurable pieces, and the finite telescoping chain
`{t < Y n} ⊆ {θ₀ < Y 0} ∪ ⋃ {θ_ℓ < |Y ℓ - Y (ℓ-1)|}`, which needs no convergence.
It also records the Chebyshev bound in the form used for the chain increments.
It does not choose any window σ-algebra or law.
-/

open MeasureTheory
open scoped ENNReal

namespace SubdiffusiveProcess.Lfgc
variable {Ω : Type*} [MeasurableSpace Ω]

/-- `A` has an exponential-type cover: window-measurable sets `W h` with `P (W h) ≤ f h`. -/
def IsTailCover (P : Measure Ω) (B : ℕ+ → MeasurableSpace Ω) (A : Set Ω) (f : ℕ+ → ℝ≥0∞) :
    Prop :=
  ∃ W : ℕ+ → Set Ω, (∀ h, MeasurableSet[B h] (W h)) ∧ (∀ h, P (W h) ≤ f h) ∧ A ⊆ ⋃ h, W h

theorem IsTailCover.mono {P : Measure Ω} {B : ℕ+ → MeasurableSpace Ω} {A A' : Set Ω}
    {f f' : ℕ+ → ℝ≥0∞} (hc : IsTailCover P B A f) (hA : A' ⊆ A) (hf : ∀ h, f h ≤ f' h) :
    IsTailCover P B A' f' := by
  obtain ⟨W, hW, hP, hcov⟩ := hc
  exact ⟨W, hW, fun h => (hP h).trans (hf h), hA.trans hcov⟩

theorem isTailCover_empty (P : Measure Ω) (B : ℕ+ → MeasurableSpace Ω) (f : ℕ+ → ℝ≥0∞) :
    IsTailCover P B ∅ f :=
  ⟨fun _ => ∅, fun h => @MeasurableSet.empty Ω (B h), fun _ => by simp, Set.empty_subset _⟩

/-- Finite unions of covers add their bounds. -/
theorem IsTailCover.biUnion {ι : Type*} (s : Finset ι) {P : Measure Ω}
    {B : ℕ+ → MeasurableSpace Ω} {A : ι → Set Ω} {f : ι → ℕ+ → ℝ≥0∞}
    (hc : ∀ i ∈ s, IsTailCover P B (A i) (f i)) :
    IsTailCover P B (⋃ i ∈ s, A i) (fun h => ∑ i ∈ s, f i h) := by
  classical
  choose! W hW hP hcov using hc
  refine ⟨fun h => ⋃ i ∈ s, W i h, fun h => ?_, fun h => ?_, ?_⟩
  · exact Finset.measurableSet_biUnion s fun i hi => hW i hi h
  · exact (measure_biUnion_finset_le s _).trans (Finset.sum_le_sum fun i hi => hP i hi h)
  · intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨i, hi, hωi⟩ := hω
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hcov i hi hωi)
    exact ⟨h, i, hi, hh⟩

/-- Binary union. -/
theorem IsTailCover.union {P : Measure Ω} {B : ℕ+ → MeasurableSpace Ω} {A₁ A₂ : Set Ω}
    {f₁ f₂ : ℕ+ → ℝ≥0∞} (h₁ : IsTailCover P B A₁ f₁) (h₂ : IsTailCover P B A₂ f₂) :
    IsTailCover P B (A₁ ∪ A₂) (fun h => f₁ h + f₂ h) := by
  obtain ⟨W₁, hW₁, hP₁, hc₁⟩ := h₁
  obtain ⟨W₂, hW₂, hP₂, hc₂⟩ := h₂
  refine ⟨fun h => W₁ h ∪ W₂ h, fun h => (hW₁ h).union (hW₂ h), fun h => ?_, ?_⟩
  · exact (measure_union_le _ _).trans (add_le_add (hP₁ h) (hP₂ h))
  · intro ω hω
    rcases hω with hω | hω
    · obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hc₁ hω)
      exact Set.mem_iUnion.mpr ⟨h, Or.inl hh⟩
    · obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hc₂ hω)
      exact Set.mem_iUnion.mpr ⟨h, Or.inr hh⟩

/-- Unions over a countable index of covers add their bounds (as `tsum`). -/
theorem IsTailCover.iUnion {ι : Type*} [Countable ι] {P : Measure Ω}
    {B : ℕ+ → MeasurableSpace Ω} {A : ι → Set Ω} {f : ι → ℕ+ → ℝ≥0∞}
    (hc : ∀ i, IsTailCover P B (A i) (f i)) :
    IsTailCover P B (⋃ i, A i) (fun h => ∑' i, f i h) := by
  choose W hW hP hcov using hc
  refine ⟨fun h => ⋃ i, W i h, fun h => MeasurableSet.iUnion fun i => hW i h, fun h => ?_, ?_⟩
  · exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => hP i h)
  · intro ω hω
    obtain ⟨i, hωi⟩ := Set.mem_iUnion.mp hω
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hcov i hωi)
    exact Set.mem_iUnion.mpr ⟨h, Set.mem_iUnion.mpr ⟨i, hh⟩⟩

/-- A single set measurable for the window `B h₀` is covered by itself at `h₀`. -/
theorem isTailCover_single {P : Measure Ω} {B : ℕ+ → MeasurableSpace Ω} {A : Set Ω}
    (h₀ : ℕ+) (hA : MeasurableSet[B h₀] A) (f : ℕ+ → ℝ≥0∞) (hPA : P A ≤ f h₀) :
    IsTailCover P B A f := by
  classical
  refine ⟨fun h => if h = h₀ then A else ∅, fun h => ?_, fun h => ?_, ?_⟩
  · by_cases hh : h = h₀
    · subst hh; simpa using hA
    · simp only [hh, if_false]; exact @MeasurableSet.empty Ω (B h)
  · by_cases hh : h = h₀
    · subst hh; simpa using hPA
    · simp [hh]
  · intro ω hω
    exact Set.mem_iUnion.mpr ⟨h₀, by simp [hω]⟩

/-- Countably many window-measured pieces: piece `j` lives in window `hj j`. -/
theorem isTailCover_iUnion_pieces {ι : Type*} [Countable ι] {P : Measure Ω}
    {B : ℕ+ → MeasurableSpace Ω} (A : ι → Set Ω) (hj : ι → ℕ+)
    (hA : ∀ j, MeasurableSet[B (hj j)] (A j)) (G : ι → ℝ≥0∞) (hG : ∀ j, P (A j) ≤ G j)
    (f : ℕ+ → ℝ≥0∞) (hf : ∀ h, ∑' j, (if hj j = h then G j else 0) ≤ f h) :
    IsTailCover P B (⋃ j, A j) f := by
  classical
  have hc : ∀ j, IsTailCover P B (A j) (fun h => if hj j = h then G j else 0) :=
    fun j => isTailCover_single (hj j) (hA j) _ (by simpa using hG j)
  exact (IsTailCover.iUnion hc).mono subset_rfl hf

/-! ### The finite telescoping chain -/

/-- The events of the telescoping chain: the base event and the increment events. -/
def chainEvent (Y : ℕ → Ω → ℝ) (θ : ℕ → ℝ) : ℕ → Set Ω
  | 0 => {ω | θ 0 < Y 0 ω}
  | ℓ + 1 => {ω | θ (ℓ + 1) < |Y (ℓ + 1) ω - Y ℓ ω|}

omit [MeasurableSpace Ω] in
theorem chain_telescope_le (Y : ℕ → Ω → ℝ) (θ : ℕ → ℝ) (ω : Ω) :
    ∀ n : ℕ, (∀ ℓ ≤ n, ω ∉ chainEvent Y θ ℓ) → Y n ω ≤ ∑ ℓ ∈ Finset.range (n + 1), θ ℓ
  | 0, h => by
      have h0 := h 0 le_rfl
      simp only [chainEvent, Set.mem_setOf_eq, not_lt] at h0
      simpa using h0
  | n + 1, h => by
      have ih := chain_telescope_le Y θ ω n (fun ℓ hℓ => h ℓ (hℓ.trans (Nat.le_succ n)))
      have hn := h (n + 1) le_rfl
      simp only [chainEvent, Set.mem_setOf_eq, not_lt] at hn
      rw [Finset.sum_range_succ]
      have := (abs_le.mp hn).2
      linarith

omit [MeasurableSpace Ω] in
/-- The chain cover: exceeding `t` at the end of the chain forces a chain event. -/
theorem chain_cover (Y : ℕ → Ω → ℝ) (θ : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (ht : ∑ ℓ ∈ Finset.range (n + 1), θ ℓ ≤ t) :
    {ω | t < Y n ω} ⊆ ⋃ ℓ ∈ Finset.range (n + 1), chainEvent Y θ ℓ := by
  intro ω hω
  by_contra hno
  simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hno
  have := chain_telescope_le Y θ ω n (fun ℓ hℓ => hno ℓ (Nat.lt_succ_of_le hℓ))
  simp only [Set.mem_setOf_eq] at hω
  linarith

/-- Chebyshev at order `p` for the increment events. -/
theorem meas_lt_abs_le_eLpNorm (P : Measure Ω) {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    {p : ℝ} (hp : 0 < p) {θ : ℝ} (hθ : 0 < θ) :
    P {ω | θ < |f ω|} ≤ (eLpNorm f (ENNReal.ofReal p) P / ENNReal.ofReal θ) ^ p := by
  have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hθ' : ENNReal.ofReal θ ≠ 0 := by simpa using hθ
  have hsub : {ω | θ < |f ω|} ⊆ {ω | ENNReal.ofReal θ ≤ ‖f ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hω.le
  have h := meas_ge_le_mul_pow_eLpNorm_enorm (f := f) P hp' hpt hθ' (fun h => absurd h ENNReal.ofReal_ne_top)
  refine (measure_mono hsub).trans (h.trans_eq ?_)
  rw [ENNReal.toReal_ofReal hp.le, ENNReal.div_rpow_of_nonneg _ _ hp.le, ENNReal.inv_rpow,
    div_eq_mul_inv, mul_comm]

end SubdiffusiveProcess.Lfgc
namespace SubdiffusiveProcess.Lfgc
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Countably many pieces with pairwise distinct windows. -/
theorem isTailCover_iUnion_injective {P : Measure Ω} {B : ℕ+ → MeasurableSpace Ω}
    (A : ℕ → Set Ω) (hj : ℕ → ℕ+) (hinj : Function.Injective hj)
    (hA : ∀ j, MeasurableSet[B (hj j)] (A j)) (f : ℕ+ → ℝ≥0∞) (hP : ∀ j, P (A j) ≤ f (hj j)) :
    IsTailCover P B (⋃ j, A j) f := by
  classical
  refine isTailCover_iUnion_pieces A hj hA (fun j => P (A j)) (fun j => le_rfl) f fun h => ?_
  by_cases hex : ∃ j, hj j = h
  · obtain ⟨j, rfl⟩ := hex
    rw [tsum_eq_single j]
    · simp only [if_true]; exact hP j
    · intro j' hj'
      simp only [ite_eq_right_iff]
      intro h'
      exact absurd (hinj h') hj'
  · push_neg at hex
    simp only [hex, if_false, tsum_zero, zero_le]

end SubdiffusiveProcess.Lfgc
