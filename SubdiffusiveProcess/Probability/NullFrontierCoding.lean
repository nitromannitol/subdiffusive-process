import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Instances.CantorSet

/-! Real coding by a countable basis of continuity sets. -/
noncomputable section
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology ENNReal
namespace SubdiffusiveProcess.Probability

theorem exists_null_frontier_basis {X : Type*} [MetricSpace X] [SeparableSpace X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ (∀ n, ν (frontier (U n)) = 0) ∧
      ∀ (x : X) (s : Set X), IsOpen s → x ∈ s → ∃ n, x ∈ U n ∧ U n ⊆ s := by
  classical
  obtain ⟨c, hc⟩ := exists_dense_seq X
  let a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ha : ∀ k, 0 < a k := fun k => by dsimp [a]; positivity
  have hex : ∀ p : ℕ × ℕ, ∃ r ∈ Ioo (a p.2) (2 * a p.2),
      ν (frontier (ball (c p.1) r)) = 0 := by
    intro p
    simpa only [thickening_singleton] using
      exists_null_frontier_thickening ν {c p.1} (by linarith [ha p.2])
  choose r hr hn using hex
  refine ⟨fun n => ball (c (Nat.unpair n).1) (r (Nat.unpair n)),
    fun _ => isOpen_ball, fun n => hn (Nat.unpair n), ?_⟩
  intro x s hs hxs
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hs x hxs
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  have hak : 3 * a k < ε := by dsimp [a]; linarith
  obtain ⟨j, hj⟩ := hc.exists_dist_lt x (ha k)
  refine ⟨Nat.pair j k, ?_, ?_⟩
  · simpa only [Nat.unpair_pair, mem_ball] using hj.trans (hr (j, k)).1
  · simp only [Nat.unpair_pair]
    intro y hy
    apply hsub
    have hxy : dist y x ≤ dist y (c j) + dist (c j) x := dist_triangle _ _ _
    have hj' : dist (c j) x < a k := by simpa only [dist_comm] using hj
    have hy' : dist y (c j) < r (j, k) := hy
    have hr' := (hr (j, k)).2
    show dist y x < ε
    linarith

theorem exists_null_frontier_real_coding {X : Type*} [MetricSpace X] [PolishSpace X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    ∃ e : X → ℝ, MeasurableEmbedding e ∧ (∀ x, e x ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ x ∂ν, ContinuousAt e x) ∧
      ∀ (s : ℕ → X) (x : X), Tendsto (e ∘ s) atTop (𝓝 (e x)) →
        Tendsto s atTop (𝓝 x) := by
  classical
  obtain ⟨U, hUo, hUn, hUb⟩ := exists_null_frontier_basis ν
  let code : X → (ℕ → Bool) := fun x n => if x ∈ U n then true else false
  have hcm : Measurable code := by
    apply measurable_pi_iff.mpr
    intro n
    exact Measurable.ite (hUo n).measurableSet measurable_const measurable_const
  have hci : Function.Injective code := by
    intro x y hxy
    by_contra hne
    obtain ⟨n, hxn, hn⟩ := hUb x {y}ᶜ isOpen_compl_singleton hne
    have he := congrFun hxy n
    have hyn : y ∈ U n := by
      by_contra hny
      simp only [code, if_pos hxn, if_neg hny, Bool.true_eq_false] at he
    exact hn hyn rfl
  have hcc : ∀ᵐ x ∂ν, ContinuousAt code x := by
    have hx : ∀ n, ∀ᵐ x ∂ν, x ∉ frontier (U n) := fun n =>
      (by simpa only [ae_iff, not_not] using hUn n)
    filter_upwards [ae_all_iff.mpr hx] with x hx
    apply continuousAt_pi.mpr
    intro n
    by_cases hxn : x ∈ U n
    · apply (continuousAt_const (y := true)).congr
      filter_upwards [(hUo n).mem_nhds hxn] with y hy
      simp only [code, if_pos hy]
    · have hxcl : x ∉ closure (U n) := by
        intro hcl
        apply hx n
        exact ⟨hcl, fun hi => hxn (interior_subset hi)⟩
      apply (continuousAt_const (y := false)).congr
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy
      have hyn : y ∉ U n := fun h => hy (subset_closure h)
      simp only [code, if_neg hyn]
  let H := cantorSetHomeomorphNatToBool
  let e : X → ℝ := fun x => (H.symm (code x)).1
  have hem : Measurable e := measurable_subtype_coe.comp (H.symm.continuous.measurable.comp hcm)
  have hei : Function.Injective e := by
    intro x y hxy
    exact hci (H.symm.injective (Subtype.ext hxy))
  refine ⟨e, hem.measurableEmbedding hei,
    fun x => cantorSet_subset_unitInterval (H.symm (code x)).2, ?_, ?_⟩
  · filter_upwards [hcc] with x hx
    exact continuous_subtype_val.continuousAt.comp (H.symm.continuous.continuousAt.comp hx)
  · intro s x hs
    have ht : Tendsto (fun n => H.symm (code (s n))) atTop (𝓝 (H.symm (code x))) := by
      exact tendsto_subtype_rng.mpr hs
    have ht' : Tendsto (fun n => code (s n)) atTop (𝓝 (code x)) := by
      simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using H.continuous.continuousAt.tendsto.comp ht
    apply tendsto_def.mpr
    intro t ht
    obtain ⟨v, hvt, hv, hxv⟩ := _root_.mem_nhds_iff.mp ht
    obtain ⟨n, hxn, hnv⟩ := hUb x v hv hxv
    have hcoord := (tendsto_pi_nhds.mp ht') n
    have hcode : ∀ᶠ k in atTop, code (s k) n = code x n :=
      hcoord.eventually (isOpen_discrete {code x n} |>.mem_nhds rfl)
    filter_upwards [hcode] with k hk
    apply hvt
    apply hnv
    by_contra hkn
    simp only [code, if_neg hkn, if_pos hxn, Bool.false_eq_true] at hk

end SubdiffusiveProcess.Probability
