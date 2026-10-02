import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ExitTime
import MarkovProcess.Path.Exhaustion




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MarkovProcess Set
open scoped ENNReal NNReal

noncomputable section

/-! ## Abstract chronological time order -/



def ChronologicalTimeOrder {Ω Time : Type*} [Preorder Time]
    (T Ttilde : ℕ → Ω → Time) : Prop :=
  ∀ i ω, T i ω ≤ Ttilde i ω ∧ Ttilde i ω ≤ T (i + 1) ω



theorem ChronologicalTimeOrder.monotone_entrance {Ω Time : Type*} [Preorder Time]
    {T Ttilde : ℕ → Ω → Time} (h : ChronologicalTimeOrder T Ttilde) (ω : Ω) :
    Monotone fun i ↦ T i ω :=
  monotone_nat_of_le_succ fun i ↦ (h i ω).1.trans (h i ω).2



theorem ChronologicalTimeOrder.exit_le_entrance_of_lt {Ω Time : Type*} [Preorder Time]
    {T Ttilde : ℕ → Ω → Time} (h : ChronologicalTimeOrder T Ttilde)
    {ω : Ω} {i j : ℕ} (hij : i < j) : Ttilde i ω ≤ T j ω :=
  (h i ω).2.trans (h.monotone_entrance ω (Nat.succ_le_iff.mpr hij))

/-! ## Exit after a possibly infinite time -/

section Lifetime

variable {alpha : Type*} [TopologicalSpace alpha]



def lifetimeExitAfter (U : Set alpha) (θ : ℝ≥0∞) (path : LifetimePath alpha) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ θ ≤ s ∧
    LifetimePath.coordinate t path ∉ Cemetery.alive '' U}



theorem le_lifetimeExitAfter (U : Set alpha) (θ : ℝ≥0∞) (path : LifetimePath alpha) :
    θ ≤ lifetimeExitAfter U θ path := by
  apply le_sInf
  rintro s ⟨t, rfl, ht, _hnot⟩
  exact ht



theorem lifetimeExitAfter_mono_set {U D : Set alpha} (hUD : U ⊆ D)
    (θ : ℝ≥0∞) (path : LifetimePath alpha) :
    lifetimeExitAfter U θ path ≤ lifetimeExitAfter D θ path := by
  apply sInf_le_sInf
  rintro s ⟨t, hst, ht, hnotD⟩
  refine ⟨t, hst, ht, ?_⟩
  rintro ⟨x, hxU, hcoord⟩
  exact hnotD ⟨x, hUD hxU, hcoord⟩



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
