module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.LipschitzLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries

@[expose] public section

/-!
# The anchored good event as a Cauchy condition

The canonical anchored event `anchoredC11GoodSet` asserts the *existence* of a
local `C¹ˑ¹` limit object.  This module replaces that existential by an
intrinsic Cauchy condition on the anchored partial sums themselves, which is
the first half of the reduction of the event to a countable Borel description.

The forward direction is immediate (a uniform limit is uniformly Cauchy).  The
converse builds the limit `PotentialField` outright: the values and the stored
derivatives converge pointwise because `ℝ` and `Vec d →L[ℝ] ℝ` are complete,
the convergence is uniform on every closed ball, continuity and the genuine
`HasFDerivAt` come from the uniform-limit calculus, and the compact Lipschitz
certificate of the limiting derivative is obtained from the Cauchy form of the
Lipschitz seminorm by the `LipschitzLimit` device.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter _root_.SubdiffusiveProcess.Model Homogenization Topology

noncomputable section

variable {d : ℕ} {omega : PotentialSample d}

/-! ### The Cauchy condition -/

/-- The intrinsic Cauchy form of anchored local `C¹ˑ¹` convergence: on every
closed ball centred at the origin the anchored partial sums and their stored
derivatives are uniformly Cauchy, and the derivatives are Cauchy in the
Lipschitz seminorm. -/
structure AnchoredC11Cauchy (omega : PotentialSample d) : Prop where
  value : ∀ R : ℝ, UniformCauchySeqOn
    (fun L x ↦ anchoredPartialSum omega L x) atTop (Metric.closedBall (0 : Vec d) R)
  gradient : ∀ R : ℝ, UniformCauchySeqOn
    (fun L x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L) x) atTop
    (Metric.closedBall (0 : Vec d) R)
  lipschitz : ∀ R : ℝ, LipschitzSeminormCauchyOn
    (fun L x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L) x)
    (Metric.closedBall (0 : Vec d) R)

/-! ### From a limit to the Cauchy condition -/

theorem anchoredC11Cauchy_of_isAnchoredC11Limit {g : PotentialField d}
    (h : IsAnchoredC11Limit omega g) : AnchoredC11Cauchy omega where
  value R := (h.value_tendsto _ (isCompact_closedBall (0 : Vec d) R)).uniformCauchySeqOn
  gradient R := (h.deriv_tendsto _ (isCompact_closedBall (0 : Vec d) R)).uniformCauchySeqOn
  lipschitz R := h.deriv_lipschitz_cauchy _ (isCompact_closedBall (0 : Vec d) R)

/-! ### The limiting value and derivative -/

/-- The pointwise limit of the anchored partial sums. -/
def cauchyLimitValue (omega : PotentialSample d) (x : Vec d) : ℝ :=
  limUnder atTop fun L ↦ anchoredPartialSum omega L x

/-- The pointwise limit of the stored derivatives of the anchored partial
sums. -/
def cauchyLimitDeriv (omega : PotentialSample d) (x : Vec d) : Vec d →L[ℝ] ℝ :=
  limUnder atTop fun L ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L) x

private theorem mem_closedBall_self_norm (x : Vec d) (R : ℝ) (hx : ‖x‖ ≤ R) :
    x ∈ Metric.closedBall (0 : Vec d) R := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx

private theorem closedBall_mem_nhds (x : Vec d) :
    Metric.closedBall (0 : Vec d) (‖x‖ + 1) ∈ nhds x := by
  have hx : x ∈ Metric.ball (0 : Vec d) (‖x‖ + 1) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx)
    Metric.ball_subset_closedBall

theorem tendsto_cauchyLimitValue (h : AnchoredC11Cauchy omega) (x : Vec d) :
    Tendsto (fun L ↦ anchoredPartialSum omega L x) atTop
      (nhds (cauchyLimitValue omega x)) :=
  ((h.value ‖x‖).cauchySeq (mem_closedBall_self_norm x ‖x‖ le_rfl)).tendsto_limUnder

theorem tendsto_cauchyLimitDeriv (h : AnchoredC11Cauchy omega) (x : Vec d) :
    Tendsto (fun L ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L) x) atTop
      (nhds (cauchyLimitDeriv omega x)) :=
  ((h.gradient ‖x‖).cauchySeq (mem_closedBall_self_norm x ‖x‖ le_rfl)).tendsto_limUnder

theorem tendstoUniformlyOn_cauchyLimitValue (h : AnchoredC11Cauchy omega) (R : ℝ) :
    TendstoUniformlyOn (fun L x ↦ anchoredPartialSum omega L x)
      (cauchyLimitValue omega) atTop (Metric.closedBall (0 : Vec d) R) :=
  (h.value R).tendstoUniformlyOn_of_tendsto fun x _ ↦ tendsto_cauchyLimitValue h x

theorem tendstoUniformlyOn_cauchyLimitDeriv (h : AnchoredC11Cauchy omega) (R : ℝ) :
    TendstoUniformlyOn
      (fun L x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L) x)
      (cauchyLimitDeriv omega) atTop (Metric.closedBall (0 : Vec d) R) :=
  (h.gradient R).tendstoUniformlyOn_of_tendsto fun x _ ↦ tendsto_cauchyLimitDeriv h x

/-! ### Continuity -/

theorem continuous_cauchyLimitValue (h : AnchoredC11Cauchy omega) :
    Continuous (cauchyLimitValue omega) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine ContinuousOn.continuousAt ?_ (closedBall_mem_nhds x)
  refine (tendstoUniformlyOn_cauchyLimitValue h (‖x‖ + 1)).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun L ↦ ?_))
  exact ((anchoredPartialSumField omega L).1.1.continuous.congr
    fun y ↦ anchoredPartialSumField_apply omega L y).continuousOn

theorem continuous_cauchyLimitDeriv (h : AnchoredC11Cauchy omega) :
    Continuous (cauchyLimitDeriv omega) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine ContinuousOn.continuousAt ?_ (closedBall_mem_nhds x)
  refine (tendstoUniformlyOn_cauchyLimitDeriv h (‖x‖ + 1)).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun L ↦ ?_))
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L)).continuous.continuousOn

/-! ### Differentiability -/

theorem hasFDerivAt_cauchyLimitValue (h : AnchoredC11Cauchy omega) (x : Vec d) :
    HasFDerivAt (cauchyLimitValue omega) (cauchyLimitDeriv omega x) x := by
  have hx : x ∈ Metric.ball (0 : Vec d) (‖x‖ + 1) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  refine hasFDerivAt_of_tendstoUniformlyOn
    (f := fun L y ↦ anchoredPartialSum omega L y)
    (f' := fun L y ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L) y)
    Metric.isOpen_ball
    ((tendstoUniformlyOn_cauchyLimitDeriv h (‖x‖ + 1)).mono
      Metric.ball_subset_closedBall)
    (fun L y _ ↦ ?_) (fun y hy ↦ ?_) hx
  · refine ((anchoredPartialSumField omega L).hasFDerivAt y).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun z ↦
      (anchoredPartialSumField_apply omega L z).symm
  · exact tendsto_cauchyLimitValue h y

/-! ### The compact Lipschitz certificate -/

theorem lipschitzOnWith_cauchyLimitDeriv (h : AnchoredC11Cauchy omega)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ C : NNReal, LipschitzOnWith C (cauchyLimitDeriv omega) K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨N, hN⟩ := h.lipschitz R 1 one_pos
  have hdiff : LipschitzOnWith (Real.toNNReal 1)
      (fun x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega N) x -
        cauchyLimitDeriv omega x) (Metric.closedBall (0 : Vec d) R) := by
    refine lipschitzOnWith_sub_limit (fun x _ ↦ tendsto_cauchyLimitDeriv h x) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN N n le_rfl hn
  obtain ⟨C, hC⟩ := (anchoredPartialSumField omega N).2.2
    (Metric.closedBall (0 : Vec d) R) (isCompact_closedBall (0 : Vec d) R)
  have hC' : LipschitzOnWith C
      (fun x ↦ _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega N) x)
      (Metric.closedBall (0 : Vec d) R) := hC
  refine ⟨C + Real.toNNReal 1, LipschitzOnWith.mono ?_ hR⟩
  simpa only [sub_sub_cancel] using hC'.sub hdiff

/-! ### The limit field -/

/-- The local `C¹ˑ¹` limit produced by the Cauchy condition. -/
def cauchyLimitField (h : AnchoredC11Cauchy omega) : PotentialField d :=
  ⟨(⟨cauchyLimitValue omega, continuous_cauchyLimitValue h⟩,
      ⟨cauchyLimitDeriv omega, continuous_cauchyLimitDeriv h⟩),
    hasFDerivAt_cauchyLimitValue h, fun _ hK ↦ lipschitzOnWith_cauchyLimitDeriv h hK⟩

@[simp]
theorem cauchyLimitField_apply (h : AnchoredC11Cauchy omega) (x : Vec d) :
    cauchyLimitField h x = cauchyLimitValue omega x := rfl

@[simp]
theorem cauchyLimitField_deriv (h : AnchoredC11Cauchy omega) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.deriv (cauchyLimitField h) x = cauchyLimitDeriv omega x := rfl

theorem cauchyLimitValue_origin (h : AnchoredC11Cauchy omega) :
    cauchyLimitValue omega 0 = 0 := by
  refine tendsto_nhds_unique (tendsto_cauchyLimitValue h 0) ?_
  have hzero : ∀ L : ℕ, anchoredPartialSum omega L (0 : Vec d) = 0 := by
    intro L
    simp [anchoredPartialSum]
  simpa only [hzero] using tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ))

theorem isAnchoredC11Limit_cauchyLimitField (h : AnchoredC11Cauchy omega) :
    IsAnchoredC11Limit omega (cauchyLimitField h) := by
  refine ⟨fun K hK ↦ ?_, fun K hK ↦ ?_, fun K hK ↦ ?_, cauchyLimitValue_origin h⟩
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
    exact (tendstoUniformlyOn_cauchyLimitValue h R).mono hR
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
    exact (tendstoUniformlyOn_cauchyLimitDeriv h R).mono hR
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
    intro eps heps
    obtain ⟨N, hN⟩ := h.lipschitz R eps heps
    exact ⟨N, fun m n hm hn ↦ (hN m n hm hn).mono hR⟩

/-! ### The characterisation -/

theorem exists_isAnchoredC11Limit_iff_anchoredC11Cauchy (omega : PotentialSample d) :
    (∃ g : PotentialField d, IsAnchoredC11Limit omega g) ↔ AnchoredC11Cauchy omega :=
  ⟨fun ⟨_, hg⟩ ↦ anchoredC11Cauchy_of_isAnchoredC11Limit hg,
    fun h ↦ ⟨cauchyLimitField h, isAnchoredC11Limit_cauchyLimitField h⟩⟩

/-- The canonical anchored good event is exactly the set of samples whose
anchored partial sums satisfy the intrinsic Cauchy condition. -/
theorem anchoredC11GoodSet_eq_setOf_anchoredC11Cauchy :
    anchoredC11GoodSet d = {omega : PotentialSample d | AnchoredC11Cauchy omega} := by
  rw [anchoredC11GoodSet_eq]
  ext omega
  exact exists_isAnchoredC11Limit_iff_anchoredC11Cauchy omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
