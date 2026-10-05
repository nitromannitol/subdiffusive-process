module

public import SubdiffusiveProcess.PartProcess.CoreClosure
public import SubdiffusiveProcess.DirichletForm.FOTLocalityCore

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- Bounded-energy `L²` limits remain in a graph-closed linear subspace. -/
theorem mem_graphClosed_of_tendsto_of_form_le (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    (D : Submodule ℝ (Lp ℝ 2 m)) (hD : GraphClosed E D)
    {u : ℕ → Lp ℝ 2 m} (hu : ∀ n, u n ∈ D)
    {z : Lp ℝ 2 m} (hz : Tendsto u atTop (𝓝 z)) {B : ℝ}
    (hB : ∀ n, E.form (u n) (u n) ≤ B) : z ∈ D := by
  classical
  set C : ℕ → Set (Lp ℝ 2 m) := fun n => convexHull ℝ (u '' Ici n) with hCdef
  have hCD : ∀ n, C n ⊆ E.domain := fun n =>
    convexHull_min (image_subset_iff.2 fun k _ => hD.1 (hu k)) E.domain.convex
  have hCsubD : ∀ n, C n ⊆ D := fun n =>
    convexHull_min (image_subset_iff.2 fun k _ => hu k) D.convex
  have hCanti : ∀ {n p : ℕ}, n ≤ p → C p ⊆ C n := fun hnp =>
    convexHull_mono (image_mono (Ici_subset_Ici.2 hnp))
  have huC : ∀ n, u n ∈ C n := fun n => subset_convexHull ℝ _ ⟨n, Set.self_mem_Ici, rfl⟩
  set q : Lp ℝ 2 m → ℝ := fun w => E.form w w with hqdef
  have hne : ∀ n, (q '' C n).Nonempty := fun n => ⟨q (u n), mem_image_of_mem q (huC n)⟩
  have hbdd : ∀ n, BddBelow (q '' C n) := fun n => by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact E.form_nonneg w (hCD n hw)
  set δ : ℕ → ℝ := fun n => sInf (q '' C n) with hδdef
  have hδle : ∀ n, ∀ w ∈ C n, δ n ≤ q w := fun n w hw =>
    csInf_le (hbdd n) (mem_image_of_mem q hw)
  have hδK : ∀ n, δ n ≤ B := fun n => (hδle n (u n) (huC n)).trans (hB n)
  have hδmono : Monotone δ := fun n p hnp =>
    csInf_le_csInf (hbdd n) (hne p) (image_mono (hCanti hnp))
  have hεpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ n, ∃ w ∈ C n, q w < δ n + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne n) (lt_add_of_pos_right (δ n) (hεpos n))
    exact ⟨w, hw, hlt⟩
  choose w hwC hwlt using hex
  have hwD : ∀ n, w n ∈ E.domain := fun n => hCD n (hwC n)
  -- the infima converge
  have hδbdd : BddAbove (range δ) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hδK n⟩
  set δ' : ℝ := ⨆ n, δ n with hδ'def
  have hδlim : Tendsto δ atTop (𝓝 δ') := tendsto_atTop_ciSup hδmono hδbdd
  have hδle' : ∀ n, δ n ≤ δ' := fun n => le_ciSup hδbdd n
  -- `w` is Cauchy for the form
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (w p - w r) (w p - w r) < ε := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 hδlim) (ε / 8) (by positivity)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (ε / 8) (by positivity)
    refine ⟨max N₁ N₂, fun p hp r hr => ?_⟩
    set n := max N₁ N₂
    have hsmall : ∀ k ≥ n, 1 / ((k : ℝ) + 1) < ε / 8 := fun k hk => by
      have := hN₂ k (le_of_max_le_right hk)
      rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos k)] at this
      exact this
    have hδn : δ' - δ n < ε / 8 := by
      have := hN₁ n (le_max_left _ _)
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hδle' n))] at this
      exact this
    have hmid : (1 / 2 : ℝ) • w p + (1 / 2 : ℝ) • w r ∈ C n :=
      convex_convexHull ℝ _ (hCanti hp (hwC p)) (hCanti hr (hwC r)) (by norm_num) (by norm_num)
        (by norm_num)
    have h1 := hδle n _ hmid
    have hpar := E.form_sub_self_add_four_mul_midpoint (hwD p) (hwD r)
    have hp' : q (w p) < δ' + ε / 8 := by
      have := hwlt p; have := hδle' p; have := hsmall p hp; linarith
    have hr' : q (w r) < δ' + ε / 8 := by
      have := hwlt r; have := hδle' r; have := hsmall r hr; linarith
    simp only [hqdef] at h1 hp' hr'
    linarith
  -- `w` converges to `z` in `L²`
  have hwz : Tendsto w atTop (𝓝 z) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hz ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hball : C N ⊆ Metric.ball z ε :=
      convexHull_min (image_subset_iff.2 fun k hk => hN k hk) (convex_ball z ε)
    exact hball (hCanti hn (hwC n))
  obtain ⟨hzD, hE1⟩ := E.mem_domain_of_tendsto_of_formCauchy w hwD z hwz hcauchy
  exact hD.2 w z (fun n => hCsubD n (hwC n)) hzD hE1


end SubdiffusiveProcess.PartProcess
