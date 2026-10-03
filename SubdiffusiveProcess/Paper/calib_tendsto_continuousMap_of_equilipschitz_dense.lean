module

public import Mathlib
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

/-! Locally uniform convergence of locally equi-Lipschitz functions from convergence on a dense sequence of points. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology
noncomputable section
namespace Paper

/-- Pointwise convergence everywhere from equi-Lipschitz bounds on balls and convergence on a dense
sequence. -/
theorem aux_calib_tendsto_continuousMap_of_equilipschitz_dense_pointwise {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (h : ℕ → X → ℝ) (D : ℕ → X) (hD : DenseRange D) (x0 : X)
    (hconv : ∀ j, CauchySeq (fun n => h n (D j)))
    (hL : ∀ m : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ n, ∀ x ∈ Metric.closedBall x0 (m : ℝ),
      ∀ y ∈ Metric.closedBall x0 (m : ℝ), |h n x - h n y| ≤ L * dist x y) (x : X) :
    CauchySeq (fun n => h n x) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (dist x x0 + 1)
  obtain ⟨L, hL0, hLm⟩ := hL m
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set δ : ℝ := min 1 (ε / (4 * (L + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨j, hj⟩ := hD.exists_dist_lt x hδpos
  have hxm : x ∈ Metric.closedBall x0 (m : ℝ) := by
    rw [Metric.mem_closedBall]; linarith [dist_nonneg (x := x) (y := x0)]
  have hjm : D j ∈ Metric.closedBall x0 (m : ℝ) := by
    rw [Metric.mem_closedBall]
    have h1 : dist (D j) x0 ≤ dist (D j) x + dist x x0 := dist_triangle _ _ _
    have h2 : dist (D j) x < 1 := by rw [dist_comm]; exact hj.trans_le (min_le_left _ _)
    linarith
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 (hconv j) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hLδ : L * δ ≤ ε / 4 := by
    calc L * δ ≤ L * (ε / (4 * (L + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hL0
      _ = ε / 4 * (L / (L + 1)) := by field_simp
      _ ≤ ε / 4 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = ε / 4 := by ring
  have hdist : dist (D j) x ≤ δ := by rw [dist_comm]; exact hj.le
  have e1 : |h n x - h n (D j)| ≤ ε / 4 :=
    (hLm n x hxm (D j) hjm).trans
      ((mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact hdist) hL0).trans hLδ)
  have e2 : |h N x - h N (D j)| ≤ ε / 4 :=
    (hLm N x hxm (D j) hjm).trans
      ((mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact hdist) hL0).trans hLδ)
  have e3 : dist (h n (D j)) (h N (D j)) < ε / 2 := hN n hn
  rw [Real.dist_eq] at e3 ⊢
  have := abs_sub_abs_le_abs_sub (h n x - h n (D j)) (h N x - h N (D j))
  calc |h n x - h N x| = |(h n x - h n (D j)) + (h n (D j) - h N (D j)) - (h N x - h N (D j))| := by
        congr 1; ring
    _ ≤ |h n x - h n (D j)| + |h n (D j) - h N (D j)| + |h N x - h N (D j)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by linarith

/-- Locally uniform convergence (convergence in the compact-open topology of `C(X, ℝ)`). -/
theorem calib_tendsto_continuousMap_of_equilipschitz_dense
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (h : ℕ → C(X, ℝ)) (D : ℕ → X) (hD : DenseRange D) (x0 : X)
    (hconv : ∀ j, CauchySeq (fun n => h n (D j)))
    (hL : ∀ m : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ n, ∀ x ∈ Metric.closedBall x0 (m : ℝ),
      ∀ y ∈ Metric.closedBall x0 (m : ℝ), |h n x - h n y| ≤ L * dist x y) :
    ∃ f : C(X, ℝ), Tendsto h atTop (𝓝 f) := by
  have hcau := aux_calib_tendsto_continuousMap_of_equilipschitz_dense_pointwise (fun n x => h n x) D hD x0 hconv hL
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hgL : ∀ m : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.closedBall x0 (m : ℝ),
      ∀ y ∈ Metric.closedBall x0 (m : ℝ), |g x - g y| ≤ L * dist x y := by
    intro m
    obtain ⟨L, hL0, hLm⟩ := hL m
    refine ⟨L, hL0, fun x hx y hy => ?_⟩
    have ht : Tendsto (fun n => |h n x - h n y|) atTop (𝓝 |g x - g y|) :=
      ((hg x).sub (hg y)).abs
    exact le_of_tendsto ht (Eventually.of_forall fun n => hLm n x hx y hy)
  have hgcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨m, hm⟩ := exists_nat_gt (dist x x0)
    obtain ⟨L, hL0, hLm⟩ := hgL m
    have hlip : LipschitzOnWith (Real.toNNReal L) g (Metric.closedBall x0 (m : ℝ)) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      rw [Real.dist_eq, Real.coe_toNNReal _ hL0]
      exact hLm a ha b hb
    have hmem : Metric.closedBall x0 (m : ℝ) ∈ 𝓝 x :=
      mem_nhds_iff.2 ⟨Metric.ball x0 (m : ℝ), Metric.ball_subset_closedBall, Metric.isOpen_ball,
        Metric.mem_ball.2 hm⟩
    exact hlip.continuousOn.continuousAt hmem
  refine ⟨⟨g, hgcont⟩, ?_⟩
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m : ℕ, K ⊆ Metric.closedBall x0 (m : ℝ) := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall x0
    obtain ⟨m, hm⟩ := exists_nat_ge R
    exact ⟨m, hR.trans (Metric.closedBall_subset_closedBall hm)⟩
  obtain ⟨L, hL0, hLm⟩ := hL m
  obtain ⟨L', hL0', hLm'⟩ := hgL m
  set δ : ℝ := ε / (3 * (max L L' + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨t, htK, htfin, hcover⟩ := hK.finite_cover_balls hδpos
  have hev : ∀ᶠ n in atTop, ∀ y ∈ t, dist (h n y) (g y) < ε / 3 := by
    rw [eventually_all_finite htfin]
    intro y _
    exact (Metric.tendsto_nhds.1 (hg y)) (ε / 3) (by positivity)
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have hxm := hm hx
  have hym := hm (htK hy)
  have e1 : |h n x - h n y| ≤ ε / 3 := by
    refine (hLm n x hxm y hym).trans ?_
    have : L * dist x y ≤ max L L' * δ :=
      mul_le_mul (le_max_left _ _) (by rw [Metric.mem_ball] at hxy; exact hxy.le) dist_nonneg
        (le_trans hL0 (le_max_left _ _))
    refine this.trans ?_
    rw [hδ]
    have hpos : 0 < max L L' + 1 := by positivity
    calc max L L' * (ε / (3 * (max L L' + 1))) = ε / 3 * (max L L' / (max L L' + 1)) := by
          field_simp
      _ ≤ ε / 3 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one hpos]; linarith
      _ = ε / 3 := by ring
  have e2 : |g x - g y| ≤ ε / 3 := by
    have h1 := hLm' x hxm y hym
    refine h1.trans ?_
    have : L' * dist x y ≤ max L L' * δ :=
      mul_le_mul (le_max_right _ _) (by rw [Metric.mem_ball] at hxy; exact hxy.le)
        dist_nonneg (le_trans hL0 (le_max_left _ _))
    refine this.trans ?_
    rw [hδ]
    have hpos : 0 < max L L' + 1 := by positivity
    calc max L L' * (ε / (3 * (max L L' + 1))) = ε / 3 * (max L L' / (max L L' + 1)) := by
          field_simp
      _ ≤ ε / 3 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one hpos]; linarith
      _ = ε / 3 := by ring
  have e3 := hn y hy
  rw [Real.dist_eq] at e3 ⊢
  have e1' : |h n y - h n x| ≤ ε / 3 := by rw [abs_sub_comm]; exact e1
  have e3' : |g y - h n y| < ε / 3 := by rw [abs_sub_comm]; exact e3
  have hsum : g x - h n x = (g x - g y) + (g y - h n y) + (h n y - h n x) := by ring
  change |g x - h n x| < ε
  rw [hsum]
  calc |(g x - g y) + (g y - h n y) + (h n y - h n x)|
      ≤ |g x - g y| + |g y - h n y| + |h n y - h n x| := abs_add_three _ _ _
    _ < ε := by linarith

end Paper
