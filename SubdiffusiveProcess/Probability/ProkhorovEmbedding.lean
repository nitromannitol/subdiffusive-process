import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! A countable compact ambient space for a Polish space. Truncated distance functions
to a dense sequence define an embedding into `ℕ → unitInterval`. -/

open Filter Metric Set Topology TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess.Probability

/-- A Polish space embeds into the compact countable cube. -/
theorem exists_polish_embedding_cube (X : Type*) [TopologicalSpace X] [PolishSpace X] :
    ∃ e : X → (ℕ → unitInterval), IsEmbedding e := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h =>
    letI := h
    exact ⟨fun _ => 0, continuous_const.isClosedEmbedding
      (Function.injective_of_subsingleton _) |>.isEmbedding⟩
  | inr h =>
    letI := h
    letI := upgradeIsCompletelyMetrizable X
    let s := denseSeq X
    have hs : DenseRange s := denseRange_denseSeq X
    let e : X → (ℕ → unitInterval) := fun x n =>
      ⟨min (dist x (s n)) 1, le_min dist_nonneg zero_le_one, min_le_right _ _⟩
    have he : Continuous e := by
      apply continuous_pi
      intro n
      exact Continuous.subtype_mk ((continuous_id.dist continuous_const).min continuous_const) _
    have hind : IsInducing e := by
      apply isInducing_iff_nhds.mpr
      intro x
      apply le_antisymm
      · exact (he.tendsto x).le_comap
      · change Tendsto id (comap e (𝓝 (e x))) (𝓝 x)
        apply Metric.tendsto_nhds.mpr
        intro eps heps
        let r : ℝ := min eps 1 / 2
        have hr : 0 < r := by dsimp [r]; positivity
        have hr1 : r < 1 := by dsimp [r]; have := min_le_right eps (1 : ℝ); linarith
        obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp hs x (r / 2) (half_pos hr)
        have hxn : (e x n : ℝ) < r := by
          exact (min_le_left _ _).trans_lt (hn.trans (half_lt_self hr))
        have hcoord : Continuous (fun z : ℕ → unitInterval => (z n : ℝ)) := by fun_prop
        have hne : ∀ᶠ z in 𝓝 (e x), (z n : ℝ) < r :=
          hcoord.continuousAt.eventually (gt_mem_nhds hxn)
        filter_upwards [tendsto_comap.eventually hne] with y hy
        have hyn : dist y (s n) < r := by
          have hy' : min (dist y (s n)) 1 < r := hy
          rcases min_lt_iff.mp hy' with hlt | hlt
          · exact hlt
          · exact False.elim (not_lt_of_ge hr1.le hlt)
        calc
          dist y x ≤ dist y (s n) + dist (s n) x := dist_triangle _ _ _
          _ < r + r / 2 := add_lt_add hyn (by simpa [dist_comm] using hn)
          _ < eps := by dsimp [r]; have := min_le_left eps (1 : ℝ); linarith
    exact ⟨e, hind.isEmbedding⟩

end SubdiffusiveProcess.Probability
