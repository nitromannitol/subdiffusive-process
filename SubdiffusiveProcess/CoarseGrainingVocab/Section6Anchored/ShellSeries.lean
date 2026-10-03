module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSet
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.UniformCalculus
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter SubdiffusiveProcess.Frozen.Assumptions Homogenization Topology
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Summable shell gauges on one closed ball. -/
structure ShellC11Bound (omega : PotentialSample d) (R : ℝ) (u v w : ℕ → ℝ) :
    Prop where
  u_nonneg : ∀ k, 0 ≤ u k
  v_nonneg : ∀ k, 0 ≤ v k
  w_nonneg : ∀ k, 0 ≤ w k
  u_summable : Summable u
  v_summable : Summable v
  w_summable : Summable w
  value_le : ∀ k : ℕ, ∀ x ∈ Metric.closedBall (0 : Vec d) R,
    |omega k x - omega k 0| ≤ u k
  deriv_le : ∀ k : ℕ, ∀ x ∈ Metric.closedBall (0 : Vec d) R,
    ‖PotentialField.deriv (omega k) x‖ ≤ v k
  deriv_lipschitz : ∀ k : ℕ, ∀ x ∈ Metric.closedBall (0 : Vec d) R,
    ∀ y ∈ Metric.closedBall (0 : Vec d) R,
      ‖PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y‖ ≤
        w k * ‖x - y‖

/-- The shell gauges are summable on every closed ball. -/
def ShellC11Summable (omega : PotentialSample d) : Prop :=
  ∀ R : ℝ, ∃ u v w : ℕ → ℝ, ShellC11Bound omega R u v w

/-! ### The derivative of a finite anchored sum -/

theorem deriv_anchoredPartialSumField (omega : PotentialSample d) (L : ℕ)
    (x : Vec d) :
    PotentialField.deriv (anchoredPartialSumField omega L) x =
      ∑ k ∈ Finset.range (L + 1), PotentialField.deriv (omega k) x := by
  induction L with
  | zero => simp [anchoredPartialSumField]
  | succ L ih =>
      rw [anchoredPartialSumField, PotentialField.add_deriv, ih,
        PotentialField.anchor_deriv]
      exact (Finset.sum_range_succ _ _).symm

/-! ### The limiting value and derivative -/

/-- The anchored shell series. -/
def shellAnchoredValue (omega : PotentialSample d) (x : Vec d) : ℝ :=
  ∑' k : ℕ, (omega k x - omega k 0)

/-- The shell derivative series. -/
def shellDerivSum (omega : PotentialSample d) (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑' k : ℕ, PotentialField.deriv (omega k) x

variable {omega : PotentialSample d}

theorem tendstoUniformlyOn_shellAnchoredValue {R : ℝ} {u v w : ℕ → ℝ}
    (h : ShellC11Bound omega R u v w) :
    TendstoUniformlyOn
      (fun N x => ∑ k ∈ Finset.range N, (omega k x - omega k 0))
      (shellAnchoredValue omega) atTop (Metric.closedBall (0 : Vec d) R) :=
  tendstoUniformlyOn_tsum_nat h.u_summable
    (fun k x hx => by simpa only [Real.norm_eq_abs] using h.value_le k x hx)

theorem tendstoUniformlyOn_shellDerivSum {R : ℝ} {u v w : ℕ → ℝ}
    (h : ShellC11Bound omega R u v w) :
    TendstoUniformlyOn
      (fun N x => ∑ k ∈ Finset.range N, PotentialField.deriv (omega k) x)
      (shellDerivSum omega) atTop (Metric.closedBall (0 : Vec d) R) :=
  tendstoUniformlyOn_tsum_nat h.v_summable (fun k x hx => h.deriv_le k x hx)

/-! ### Continuity of the two series -/

private theorem closedBall_mem_nhds_self (x : Vec d) :
    Metric.closedBall (0 : Vec d) (‖x‖ + 1) ∈ nhds x := by
  have hx : x ∈ Metric.ball (0 : Vec d) (‖x‖ + 1) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx)
    Metric.ball_subset_closedBall

theorem continuous_shellAnchoredValue (h : ShellC11Summable omega) :
    Continuous (shellAnchoredValue omega) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨u, v, w, hb⟩ := h (‖x‖ + 1)
  refine ContinuousOn.continuousAt ?_ (closedBall_mem_nhds_self x)
  refine (tendstoUniformlyOn_shellAnchoredValue hb).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun N => ?_))
  exact continuousOn_finset_sum _ fun k _ =>
    (((omega k).1.1.continuous.sub continuous_const)).continuousOn

theorem continuous_shellDerivSum (h : ShellC11Summable omega) :
    Continuous (shellDerivSum omega) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨u, v, w, hb⟩ := h (‖x‖ + 1)
  refine ContinuousOn.continuousAt ?_ (closedBall_mem_nhds_self x)
  refine (tendstoUniformlyOn_shellDerivSum hb).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun N => ?_))
  exact continuousOn_finset_sum _ fun k _ =>
    (PotentialField.deriv (omega k)).continuous.continuousOn

/-! ### Differentiability of the series -/

theorem hasFDerivAt_shellAnchoredValue (h : ShellC11Summable omega) (x : Vec d) :
    HasFDerivAt (shellAnchoredValue omega) (shellDerivSum omega x) x := by
  obtain ⟨u, v, w, hb⟩ := h (‖x‖ + 1)
  have hx : x ∈ Metric.ball (0 : Vec d) (‖x‖ + 1) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  refine hasFDerivAt_of_tendstoUniformlyOn
    (f := fun N y => ∑ k ∈ Finset.range N, (omega k y - omega k 0))
    (f' := fun N y => ∑ k ∈ Finset.range N, PotentialField.deriv (omega k) y)
    Metric.isOpen_ball
    ((tendstoUniformlyOn_shellDerivSum hb).mono Metric.ball_subset_closedBall)
    (fun N y _ => ?_) (fun y hy => ?_) hx
  · have hterm : ∀ k ∈ Finset.range N,
        HasFDerivAt (fun z => omega k z - omega k 0)
          (PotentialField.deriv (omega k) y) y :=
      fun k _ => ((omega k).hasFDerivAt y).sub_const (omega k 0)
    exact HasFDerivAt.fun_sum hterm
  · exact ((tendstoUniformlyOn_shellAnchoredValue hb).mono
      Metric.ball_subset_closedBall).tendsto_at hy

/-! ### The Lipschitz certificate -/

theorem summable_deriv_apply {R : ℝ} {u v w : ℕ → ℝ}
    (hb : ShellC11Bound omega R u v w) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) R) :
    Summable fun k => PotentialField.deriv (omega k) x :=
  Summable.of_norm_bounded hb.v_summable fun k => hb.deriv_le k x hx

theorem norm_shellDerivSum_sub_le {R : ℝ} {u v w : ℕ → ℝ}
    (hb : ShellC11Bound omega R u v w) {x y : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) R)
    (hy : y ∈ Metric.closedBall (0 : Vec d) R) :
    ‖shellDerivSum omega x - shellDerivSum omega y‖ ≤ (∑' k, w k) * ‖x - y‖ := by
  have hsx := summable_deriv_apply hb hx
  have hsy := summable_deriv_apply hb hy
  have hnorm : Summable fun k =>
      ‖PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => hb.deriv_lipschitz k x hx y hy) ?_
    exact hb.w_summable.mul_right _
  have hdiff : shellDerivSum omega x - shellDerivSum omega y =
      ∑' k, (PotentialField.deriv (omega k) x -
        PotentialField.deriv (omega k) y) := (hsx.tsum_sub hsy).symm
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm hnorm) ?_
  refine le_trans (Summable.tsum_mono hnorm (hb.w_summable.mul_right _)
    (fun k => hb.deriv_lipschitz k x hx y hy)) ?_
  exact le_of_eq tsum_mul_right

/-! ### The limiting potential field -/

theorem tsum_w_nonneg {R : ℝ} {u v w : ℕ → ℝ}
    (hb : ShellC11Bound omega R u v w) : 0 ≤ ∑' k, w k :=
  tsum_nonneg hb.w_nonneg

theorem lipschitzOnWith_shellDerivSum_closedBall {R : ℝ} {u v w : ℕ → ℝ}
    (hb : ShellC11Bound omega R u v w) :
    LipschitzOnWith (Real.toNNReal (∑' k, w k)) (shellDerivSum omega)
      (Metric.closedBall (0 : Vec d) R) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.coe_toNNReal _ (tsum_w_nonneg hb), dist_eq_norm, dist_eq_norm]
  exact norm_shellDerivSum_sub_le hb hx hy

theorem shellDerivSum_lipschitz_compact (h : ShellC11Summable omega) :
    ∀ K : Set (Vec d), IsCompact K →
      ∃ C : NNReal, LipschitzOnWith C (shellDerivSum omega) K := by
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨u, v, w, hb⟩ := h R
  exact ⟨Real.toNNReal (∑' k, w k),
    (lipschitzOnWith_shellDerivSum_closedBall hb).mono hR⟩

/-- The local `C¹ˑ¹` limit of the anchored shell sums. -/
def anchoredLimitField (h : ShellC11Summable omega) : PotentialField d :=
  ⟨(⟨shellAnchoredValue omega, continuous_shellAnchoredValue h⟩,
      ⟨shellDerivSum omega, continuous_shellDerivSum h⟩),
    hasFDerivAt_shellAnchoredValue h, shellDerivSum_lipschitz_compact h⟩

@[simp]
theorem anchoredLimitField_apply (h : ShellC11Summable omega) (x : Vec d) :
    anchoredLimitField h x = shellAnchoredValue omega x := rfl

@[simp]
theorem anchoredLimitField_deriv (h : ShellC11Summable omega) (x : Vec d) :
    PotentialField.deriv (anchoredLimitField h) x = shellDerivSum omega x := rfl

/-! ### The defining limit property -/

theorem shellAnchoredValue_origin : shellAnchoredValue omega 0 = 0 := by
  simp [shellAnchoredValue]

theorem anchoredLimitField_origin (h : ShellC11Summable omega) :
    anchoredLimitField h 0 = 0 :=
  shellAnchoredValue_origin

theorem isAnchoredC11Limit_anchoredLimitField (h : ShellC11Summable omega) :
    IsAnchoredC11Limit omega (anchoredLimitField h) := by
  refine ⟨fun K hK => ?_, fun K hK => ?_, fun K hK => ?_,
    anchoredLimitField_origin h⟩
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
    obtain ⟨u, v, w, hb⟩ := h R
    have hbase :=
      (tendstoUniformlyOn_natSucc
        (tendstoUniformlyOn_shellAnchoredValue hb)).mono hR
    exact (hbase.congr
      (Filter.Eventually.of_forall fun _ _ _ => rfl)).congr_right fun _ _ => rfl
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
    obtain ⟨u, v, w, hb⟩ := h R
    have hbase :=
      (tendstoUniformlyOn_natSucc (tendstoUniformlyOn_shellDerivSum hb)).mono hR
    exact (hbase.congr (Filter.Eventually.of_forall fun L x _ =>
      (deriv_anchoredPartialSumField omega L x).symm)).congr_right
      fun _ _ => rfl
  · intro eps heps
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
    obtain ⟨u, v, w, hb⟩ := h R
    have hcauchy : CauchySeq fun N => ∑ k ∈ Finset.range N, w k :=
      hb.w_summable.hasSum.tendsto_sum_nat.cauchySeq
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcauchy eps heps
    refine ⟨N, fun m n hm hn => ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hxR := hR hx
    have hyR := hR hy
    have hstep : ∀ p q : ℕ, q ≤ p → N ≤ q →
        ‖(PotentialField.deriv (anchoredPartialSumField omega p) x -
            PotentialField.deriv (anchoredPartialSumField omega q) x) -
          (PotentialField.deriv (anchoredPartialSumField omega p) y -
            PotentialField.deriv (anchoredPartialSumField omega q) y)‖ ≤
          eps * ‖x - y‖ := by
      intro p q hqp hNq
      have hIco : ∀ z : Vec d,
          PotentialField.deriv (anchoredPartialSumField omega p) z -
            PotentialField.deriv (anchoredPartialSumField omega q) z =
            ∑ k ∈ Finset.Ico (q + 1) (p + 1), PotentialField.deriv (omega k) z := by
        intro z
        rw [deriv_anchoredPartialSumField, deriv_anchoredPartialSumField,
          Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hqp)]
      rw [hIco x, hIco y, ← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ k ∈ Finset.Ico (q + 1) (p + 1),
          ‖PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y‖ ≤
            w k * ‖x - y‖ := fun k _ => hb.deriv_lipschitz k x hxR y hyR
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hsub : ∑ k ∈ Finset.Ico (q + 1) (p + 1), w k =
          (∑ k ∈ Finset.range (p + 1), w k) - ∑ k ∈ Finset.range (q + 1), w k :=
        Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hqp)
      have hd := hN (p + 1) (le_trans hNq (by omega)) (q + 1)
        (le_trans hNq (by omega))
      rw [Real.dist_eq] at hd
      rw [hsub]
      exact le_trans (le_abs_self _) hd.le
    have hcoe : ((Real.toNNReal eps : NNReal) : ℝ) = eps :=
      Real.coe_toNNReal eps heps.le
    rw [hcoe, dist_eq_norm, dist_eq_norm]
    rcases le_total n m with hmn | hmn
    · exact hstep m n hmn hn
    · have := hstep n m hmn hm
      rw [← norm_neg]
      convert this using 2
      abel

/-- Summable shell gauges put the sample in the canonical anchored good
event. -/
theorem mem_anchoredC11GoodSet_of_shellC11Summable (h : ShellC11Summable omega) :
    omega ∈ anchoredC11GoodSet d := by
  rw [anchoredC11GoodSet_eq]
  exact ⟨anchoredLimitField h, isAnchoredC11Limit_anchoredLimitField h⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
