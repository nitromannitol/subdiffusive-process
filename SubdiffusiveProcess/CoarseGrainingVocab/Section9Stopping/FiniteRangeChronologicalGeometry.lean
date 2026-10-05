module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ExitTime
public import MarkovProcess.Path.Exhaustion

@[expose] public section

/-!
# Chronological exit geometry for the Section 9 stopping construction

This file isolates the deterministic time-order and nested-exit facts used by the greedy
selection. The lifetime-path
lemmas allow infinite times and count death as exit. The final strict-containment result is
therefore stated for ordinary continuous paths; finite death can make two lifetime-path exit
times equal even when one spatial set is compactly contained in the other.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MarkovProcess Set
open scoped ENNReal NNReal

noncomputable section

/-! ## Abstract chronological time order -/

/-- The alternating time order `Tᵢ ≤ T̃ᵢ ≤ Tᵢ₊₁`. -/
def ChronologicalTimeOrder {Ω Time : Type*} [Preorder Time]
    (T Ttilde : ℕ → Ω → Time) : Prop :=
  ∀ i ω, T i ω ≤ Ttilde i ω ∧ Ttilde i ω ≤ T (i + 1) ω

/-- The entrance times in a chronological selection are monotone.

-/
theorem ChronologicalTimeOrder.monotone_entrance {Ω Time : Type*} [Preorder Time]
    {T Ttilde : ℕ → Ω → Time} (h : ChronologicalTimeOrder T Ttilde) (ω : Ω) :
    Monotone fun i ↦ T i ω :=
  monotone_nat_of_le_succ fun i ↦ (h i ω).1.trans (h i ω).2

/-- A selected exit precedes every later entrance.

-/
theorem ChronologicalTimeOrder.exit_le_entrance_of_lt {Ω Time : Type*} [Preorder Time]
    {T Ttilde : ℕ → Ω → Time} (h : ChronologicalTimeOrder T Ttilde)
    {ω : Ω} {i j : ℕ} (hij : i < j) : Ttilde i ω ≤ T j ω :=
  (h i ω).2.trans (h.monotone_entrance ω (Nat.succ_le_iff.mpr hij))

/-! ## Exit after a possibly infinite time -/

section Lifetime

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The first lifetime-path exit from `U` at or after `θ`.

This is the deterministic extended-time operation in the recursion. It does not assert the missing lifetime-path stopping-time
closure theorem.
-/
def lifetimeExitAfter (U : Set alpha) (θ : ℝ≥0∞) (path : LifetimePath alpha) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ θ ≤ s ∧
    LifetimePath.coordinate t path ∉ Cemetery.alive '' U}

/-- An exit constrained to occur after `θ` cannot precede `θ`.

This uses the recursion and infinity convention.
-/
theorem le_lifetimeExitAfter (U : Set alpha) (θ : ℝ≥0∞) (path : LifetimePath alpha) :
    θ ≤ lifetimeExitAfter U θ path := by
  apply le_sInf
  rintro s ⟨t, rfl, ht, _hnot⟩
  exact ht

/-- Leaving a smaller set after the same time occurs no later than leaving a larger set.

This uses the containment argument.
-/
theorem lifetimeExitAfter_mono_set {U D : Set alpha} (hUD : U ⊆ D)
    (θ : ℝ≥0∞) (path : LifetimePath alpha) :
    lifetimeExitAfter U θ path ≤ lifetimeExitAfter D θ path := by
  apply sInf_le_sInf
  rintro s ⟨t, hst, ht, hnotD⟩
  refine ⟨t, hst, ht, ?_⟩
  rintro ⟨x, hxU, hcoord⟩
  exact hnotD ⟨x, hUD hxU, hcoord⟩

/-- If `θ` is no later than the original exit, restricting the infimum to times after
`θ` does not change the exit time.

This uses the condition `θ₀ ≤ θ ≤ τ_D`.
-/
theorem lifetimeExitAfter_eq_exitTime_of_le (U : Set alpha) (path : LifetimePath alpha)
    {θ : ℝ≥0∞} (hθ : θ ≤ LifetimePath.exitTime U path) :
    lifetimeExitAfter U θ path = LifetimePath.exitTime U path := by
  apply congrArg sInf
  ext s
  constructor
  · rintro ⟨t, rfl, _ht, hnot⟩
    exact ⟨t, rfl, hnot⟩
  · rintro ⟨t, rfl, hnot⟩
    refine ⟨t, rfl, hθ.trans ?_, hnot⟩
    exact sInf_le ⟨t, rfl, hnot⟩

/-- A selected-cube exit after `θ` occurs no later than the ambient exit when the cube is
contained in the ambient set and `θ` has not passed the ambient exit.

This uses the containment row.
-/
theorem lifetimeExitAfter_le_exitTime {U D : Set alpha} (hUD : U ⊆ D)
    (path : LifetimePath alpha) {θ : ℝ≥0∞}
    (hθ : θ ≤ LifetimePath.exitTime D path) :
    lifetimeExitAfter U θ path ≤ LifetimePath.exitTime D path := by
  calc
    lifetimeExitAfter U θ path ≤ lifetimeExitAfter D θ path :=
      lifetimeExitAfter_mono_set hUD θ path
    _ = LifetimePath.exitTime D path := lifetimeExitAfter_eq_exitTime_of_le D path hθ

end Lifetime

/-! ## Strict containment for ordinary continuous paths -/

section Continuous

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- A continuous path that starts in `U` and exits `U` at finite time exits a containing open
set `D` strictly later when `closure U ⊆ D`.

This is the finite-time geometric assertion. It is stated on
`ContinuousPath`, exactly where continuity through the exit and the absence of finite cemetery
death justify the strict inequality.
-/
theorem continuousPath_exitTime_lt_of_closure_subset {U D : Set alpha}
    (hU : IsOpen U) (hD : IsOpen D) (hclosure : closure U ⊆ D)
    (path : ContinuousPath alpha) (hstart : path 0 ∈ U)
    (hfinite : ContinuousPath.exitTime U path ≠ ⊤) :
    ContinuousPath.exitTime U path < ContinuousPath.exitTime D path := by
  have hUD : U ⊆ D := subset_closure.trans hclosure
  have hle := ContinuousPath.exitTime_mono hUD path
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hfrontU :=
    ContinuousPath.coordinate_exitTime_mem_frontier U hU path hstart hfinite
  have hpointD :
      path ((ContinuousPath.exitTime U path).toNNReal) ∈ D :=
    hclosure (frontier_subset_closure hfrontU)
  have hfiniteD : ContinuousPath.exitTime D path ≠ ⊤ := by
    rw [← heq]
    exact hfinite
  have hfrontD := ContinuousPath.coordinate_exitTime_mem_frontier D hD path
    (hUD hstart) hfiniteD
  rw [← heq] at hfrontD
  have hpointNotD : path ((ContinuousPath.exitTime U path).toNNReal) ∉ D := by
    rw [hD.frontier_eq] at hfrontD
    exact hfrontD.2
  exact hpointNotD hpointD

/-- Consequently, equality of the two nested continuous-path exit times can occur only when
both are infinite.

This uses the equality exception.
-/
theorem continuousPath_exitTime_eq_imp_eq_top {U D : Set alpha}
    (hU : IsOpen U) (hD : IsOpen D) (hclosure : closure U ⊆ D)
    (path : ContinuousPath alpha) (hstart : path 0 ∈ U)
    (heq : ContinuousPath.exitTime U path = ContinuousPath.exitTime D path) :
    ContinuousPath.exitTime U path = ⊤ ∧ ContinuousPath.exitTime D path = ⊤ := by
  have htopU : ContinuousPath.exitTime U path = ⊤ := by
    by_contra hfinite
    exact (continuousPath_exitTime_lt_of_closure_subset hU hD hclosure path hstart hfinite).ne heq
  exact ⟨htopU, heq ▸ htopU⟩

end Continuous

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
