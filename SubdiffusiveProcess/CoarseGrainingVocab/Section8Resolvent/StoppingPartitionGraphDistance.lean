import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTailSummability
import Mathlib.Combinatorics.SimpleGraph.Metric




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Omega I X : Type*}

/-- Distance from a vertex to a nonempty finite source family. -/
def stoppingGraphDistance (G : SimpleGraph I) (source : Finset I)
    (hsource : source.Nonempty) (q : I) : ℕ :=
  source.inf' hsource fun s ↦ G.dist q s

/-- A source vertex has distance zero from the source family. -/
@[simp]
theorem stoppingGraphDistance_eq_zero_of_mem (G : SimpleGraph I)
    {source : Finset I} (hsource : source.Nonempty) {q : I}
    (hq : q ∈ source) :
    stoppingGraphDistance G source hsource q = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Finset.inf'_le (fun s ↦ G.dist q s) hq).trans_eq G.dist_self

/-- Some source vertex realizes the finite-family graph distance. -/
theorem exists_source_dist_eq_stoppingGraphDistance (G : SimpleGraph I)
    {source : Finset I} (hsource : source.Nonempty) (q : I) :
    ∃ s ∈ source, G.dist q s = stoppingGraphDistance G source hsource q := by
  obtain ⟨s, hs, hmin⟩ := Finset.exists_mem_eq_inf' hsource fun s ↦ G.dist q s
  exact ⟨s, hs, hmin.symm⟩

/-- Along an edge, distance to the source can decrease by at most one.  This
is the level inequality `j ≤ p.1 + 1` consumed by the exterior row. -/
theorem stoppingGraphDistance_le_succ_of_adj (G : SimpleGraph I)
    (hconnected : G.Connected) {source : Finset I} (hsource : source.Nonempty)
    {q p : I} (hadj : G.Adj q p) :
    stoppingGraphDistance G source hsource q ≤
      stoppingGraphDistance G source hsource p + 1 := by
  obtain ⟨s, hs, hps⟩ :=
    exists_source_dist_eq_stoppingGraphDistance G hsource p
  refine (Finset.inf'_le (fun z ↦ G.dist q z) hs).trans ?_
  calc
    G.dist q s ≤ G.dist q p + G.dist p s := hconnected.dist_triangle
    _ = 1 + stoppingGraphDistance G source hsource p := by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, hps]
    _ = stoppingGraphDistance G source hsource p + 1 := Nat.add_comm _ _

/-- At scale `k`, a short crossing is a cell which meets the Euclidean
exterior but lies fewer than `ceil (epsilon * 3^k)` graph steps from the source.
The cells and graph may depend on the sample. -/
def stoppingShortCrossingEvent [PseudoMetricSpace X]
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X) (R epsilon : ℝ) (k : ℕ) : Set Omega :=
  {omega | ∃ q : I,
    (cell omega q ∩ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty ∧
      stoppingGraphDistance (G omega) (source omega) (hsource omega) q <
        ⌈epsilon * (3 : ℝ) ^ k⌉₊}

/-- Outside the short-crossing event, every cell meeting the scale-`k`
exterior has the required graph distance. -/
theorem natCeil_le_stoppingGraphDistance_of_not_mem_shortCrossing
    [PseudoMetricSpace X]
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X) (R epsilon : ℝ)
    {omega : Omega} {k : ℕ}
    (hgood : omega ∉ stoppingShortCrossingEvent G source hsource cell x0 R epsilon k)
    {q : I}
    (hmeet : (cell omega q ∩ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty) :
    ⌈epsilon * (3 : ℝ) ^ k⌉₊ ≤
      stoppingGraphDistance (G omega) (source omega) (hsource omega) q := by
  by_contra hnot
  apply hgood
  exact ⟨q, hmeet, Nat.lt_of_not_ge hnot⟩

/-- Real-valued form of the graph-distance estimate.  If `r` is below the
next triadic radius, the loss is exactly the factor three from the source. -/
theorem graphDistance_lower_bound_of_not_mem_shortCrossing
    [PseudoMetricSpace X]
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X)
    {R epsilon r : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon)
    {omega : Omega} {k : ℕ}
    (hlower : (3 : ℝ) ^ k * R ≤ r)
    (hupper : r ≤ 3 * ((3 : ℝ) ^ k * R))
    (hgood : omega ∉ stoppingShortCrossingEvent G source hsource cell x0 R epsilon k)
    {q : I} (hmeet : (cell omega q ∩ (Metric.ball x0 r)ᶜ).Nonempty) :
    epsilon * r / (3 * R) ≤
      stoppingGraphDistance (G omega) (source omega) (hsource omega) q := by
  have hR3 : 0 < 3 * R := mul_pos (by norm_num) hR
  have hsmallBall : Metric.ball x0 ((3 : ℝ) ^ k * R) ⊆ Metric.ball x0 r := by
    exact Metric.ball_subset_ball hlower
  obtain ⟨x, hxcell, hxoutside⟩ := hmeet
  have hmeetScale :
      (cell omega q ∩ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ).Nonempty :=
    ⟨x, hxcell, fun hx ↦ hxoutside (hsmallBall hx)⟩
  have hnat := natCeil_le_stoppingGraphDistance_of_not_mem_shortCrossing
    G source hsource cell x0 R epsilon hgood hmeetScale
  have hceil : epsilon * (3 : ℝ) ^ k ≤
      (⌈epsilon * (3 : ℝ) ^ k⌉₊ : ℝ) := Nat.le_ceil _
  calc
    epsilon * r / (3 * R) ≤ epsilon * (3 : ℝ) ^ k := by
      rw [div_le_iff₀ hR3]
      nlinarith [show (0 : ℝ) ≤ (3 : ℝ) ^ k by positivity]
    _ ≤ (⌈epsilon * (3 : ℝ) ^ k⌉₊ : ℕ) := hceil
    _ ≤ stoppingGraphDistance (G omega) (source omega) (hsource omega) q := by
      exact_mod_cast hnat

/-- The last short-crossing scale, with the same extended-height convention as
the Section 9 stopping construction. -/
def stoppingCrossingDepth [PseudoMetricSpace X]
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X) (R epsilon : ℝ)
    (omega : Omega) : ℕ :=
  (failureHeightAt
    (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega).untopD 0

/-- Finiteness of the crossing height excludes every short crossing at or
above the selected depth. -/
theorem not_mem_shortCrossing_of_depth_le [PseudoMetricSpace X]
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X) (R epsilon : ℝ)
    {omega : Omega}
    (hfinite : failureHeightAt
      (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega ≠
        (⊤ : WithTop ℕ))
    {k : ℕ}
    (hk : stoppingCrossingDepth G source hsource cell x0 R epsilon omega ≤ k) :
    omega ∉ stoppingShortCrossingEvent G source hsource cell x0 R epsilon k := by
  intro hbad
  have hcontribution : ((k + 1 : ℕ) : WithTop ℕ) ≤
      failureHeightAt
        (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega :=
    coe_succ_le_extendedFailureHeight hbad
  generalize hheight : failureHeightAt
    (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega =
      height at hcontribution
  cases height with
  | top => exact (hfinite hheight).elim
  | coe H =>
      have hnat : k + 1 ≤ H := WithTop.coe_le_coe.mp hcontribution
      have hkH : H ≤ k := by
        simpa only [stoppingCrossingDepth, hheight, WithTop.untopD_coe] using hk
      omega

variable [MeasurableSpace Omega]

/-- A geometric short-crossing bound makes the last bad crossing scale finite
almost surely. -/
theorem ae_stoppingCrossingHeight_ne_top_of_geometric
    [PseudoMetricSpace X] (mu : Measure Omega)
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X) (R epsilon : ℝ)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ k,
      mu (stoppingShortCrossingEvent G source hsource cell x0 R epsilon k) ≤
        C * q ^ k) :
    ∀ᵐ omega ∂mu,
      failureHeightAt
        (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega ≠
          (⊤ : WithTop ℕ) :=
  ae_failureHeightAt_ne_top_of_le_geometric mu
    (stoppingShortCrossingEvent G source hsource cell x0 R epsilon)
    C q hC hq hmeasure

/-- The selected finite depth inherits the geometric failure-height tail. -/
theorem measure_stoppingCrossingDepth_gt_le_geometric
    [PseudoMetricSpace X] (mu : Measure Omega)
    (G : Omega → SimpleGraph I) (source : Omega → Finset I)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → I → Set X) (x0 : X) (R epsilon : ℝ)
    (C q : ENNReal)
    (hmeasure : ∀ k,
      mu (stoppingShortCrossingEvent G source hsource cell x0 R epsilon k) ≤
        C * q ^ k) (N : ℕ) :
    mu {omega | N < stoppingCrossingDepth G source hsource cell x0 R epsilon omega} ≤
      C * q ^ N * (1 - q)⁻¹ := by
  refine le_trans (measure_mono ?_)
    (measure_failureHeightTail_le_geometric mu
      (stoppingShortCrossingEvent G source hsource cell x0 R epsilon)
      C q hmeasure N)
  intro omega homega
  have hcoe :
      ((stoppingCrossingDepth G source hsource cell x0 R epsilon omega : ℕ) :
          WithTop ℕ) ≤
        failureHeightAt
          (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega :=
    WithTop.coe_untopD_le _ 0
  exact (show (N : WithTop ℕ) <
      (stoppingCrossingDepth G source hsource cell x0 R epsilon omega : ℕ) by
        exact_mod_cast homega).trans_le hcoe

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
