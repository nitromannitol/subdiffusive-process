import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.CauchyLimit
import Mathlib.Topology.Bases

/-!
# Measurability of the anchored good event

`SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet` is an existential over the
uncountable carrier `PotentialField d`, so its measurability is not immediate.
`CauchyLimit.lean` already replaced the existential by the intrinsic Cauchy
condition `AnchoredC11Cauchy`.  This module replaces that condition in turn by
a *countable* Borel condition: uniform Cauchyness of the anchored partial sums
and of their stored derivatives, together with Cauchyness of the derivative
Lipschitz seminorm, are tested only

* on the countably many closed balls of integer radius,
* at the countably many accuracies `(j+1)⁻¹`, and
* at the countably many points of a fixed dense sequence of `Vec d`,

the last reduction being legitimate because every function involved is
continuous in the space variable, so the defining inequalities cut out closed
sets.  Each atom of the resulting description is measurable because evaluation
of a potential and of its stored derivative at a point is continuous, hence
measurable, on the carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter SubdiffusiveProcess.Frozen.Assumptions Homogenization MeasureTheory Topology

noncomputable section

variable {d : ℕ}

/-! ### Continuity and measurability of the readouts -/

theorem continuous_anchoredPartialSum (omega : PotentialSample d) (L : ℕ) :
    Continuous fun x : Vec d ↦ anchoredPartialSum omega L x :=
  (anchoredPartialSumField omega L).1.1.continuous.congr fun x ↦
    anchoredPartialSumField_apply omega L x

/-- Evaluation of a finite anchored sum is measurable in the sample.  (This
repeats `MeasurableEnvelope.measurable_anchoredPartialSum`, kept private here so
that the measurability of the good event does not depend on the probabilistic
lanes.) -/
private theorem measurable_anchoredPartialSum (L : ℕ) (x : Vec d) :
    Measurable fun omega : PotentialSample d ↦ anchoredPartialSum omega L x := by
  unfold anchoredPartialSum
  exact Finset.measurable_sum _ fun k _ ↦
    ((PotentialField.measurable_eval x).comp (measurable_pi_apply k)).sub
      ((PotentialField.measurable_eval (0 : Vec d)).comp (measurable_pi_apply k))

theorem measurable_deriv_anchoredPartialSumField (L : ℕ) (x : Vec d) :
    Measurable fun omega : PotentialSample d ↦
      PotentialField.deriv (anchoredPartialSumField omega L) x := by
  have hrw : (fun omega : PotentialSample d ↦
      PotentialField.deriv (anchoredPartialSumField omega L) x) =
      fun omega : PotentialSample d ↦
        ∑ k ∈ Finset.range (L + 1), PotentialField.deriv (omega k) x :=
    funext fun omega ↦ deriv_anchoredPartialSumField omega L x
  rw [hrw]
  exact Finset.measurable_sum _ fun k _ ↦
    (PotentialField.continuous_eval_deriv x).measurable.comp (measurable_pi_apply k)

/-! ### The countable set of test points -/

/-- A fixed dense sequence of test points of `Vec d`. -/
def densePt (d : ℕ) : ℕ → Vec d := TopologicalSpace.denseSeq (Vec d)

theorem dense_range_densePt : Dense (Set.range (densePt d)) :=
  TopologicalSpace.denseRange_denseSeq (Vec d)

/-- A closed condition holding at all dense test points of norm `< r` holds on
every closed ball of strictly smaller radius. -/
theorem forall_mem_closedBall_of_forall_densePt {P : Vec d → Prop}
    (hP : IsClosed {x : Vec d | P x}) {r : ℕ} {R : ℝ} (hR : R < (r : ℝ))
    (h : ∀ i : ℕ, ‖densePt d i‖ < (r : ℝ) → P (densePt d i)) :
    ∀ x ∈ Metric.closedBall (0 : Vec d) R, P x := by
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx
  have hxr : x ∈ Metric.ball (0 : Vec d) (r : ℝ) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hsub : Metric.ball (0 : Vec d) (r : ℝ) ∩ Set.range (densePt d) ⊆
      {x : Vec d | P x} := by
    rintro y ⟨hy, i, rfl⟩
    simp only [Metric.mem_ball, dist_zero_right] at hy
    exact h i hy
  exact hP.closure_subset_iff.mpr hsub
    (dense_range_densePt.open_subset_closure_inter Metric.isOpen_ball hxr)

/-- The two-point version of `forall_mem_closedBall_of_forall_densePt`. -/
theorem forall_mem_closedBall_pair_of_forall_densePt
    {P : Vec d → Vec d → Prop}
    (hP : IsClosed {q : Vec d × Vec d | P q.1 q.2}) {r : ℕ} {R : ℝ}
    (hR : R < (r : ℝ))
    (h : ∀ i i' : ℕ, ‖densePt d i‖ < (r : ℝ) → ‖densePt d i'‖ < (r : ℝ) →
      P (densePt d i) (densePt d i')) :
    ∀ x ∈ Metric.closedBall (0 : Vec d) R, ∀ y ∈ Metric.closedBall (0 : Vec d) R,
      P x y := by
  intro x hx y hy
  simp only [Metric.mem_closedBall, dist_zero_right] at hx hy
  have hmem : (x, y) ∈ Metric.ball (0 : Vec d) (r : ℝ) ×ˢ
      Metric.ball (0 : Vec d) (r : ℝ) := by
    constructor <;> simp only [Metric.mem_ball, dist_zero_right] <;> linarith
  have hopen : IsOpen (Metric.ball (0 : Vec d) (r : ℝ) ×ˢ
      Metric.ball (0 : Vec d) (r : ℝ)) :=
    Metric.isOpen_ball.prod Metric.isOpen_ball
  have hdense : Dense (Set.range (densePt d) ×ˢ Set.range (densePt d)) :=
    dense_range_densePt.prod dense_range_densePt
  have hsub : (Metric.ball (0 : Vec d) (r : ℝ) ×ˢ Metric.ball (0 : Vec d) (r : ℝ)) ∩
      (Set.range (densePt d) ×ˢ Set.range (densePt d)) ⊆
      {q : Vec d × Vec d | P q.1 q.2} := by
    rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, ⟨i, rfl⟩, ⟨i', rfl⟩⟩
    simp only [Metric.mem_ball, dist_zero_right] at hu hv
    exact h i i' hu hv
  exact hP.closure_subset_iff.mpr hsub (hdense.open_subset_closure_inter hopen hmem)

/-! ### The countable description -/

/-- The value clause of the countable description. -/
def valueClauseSet (d r j m n : ℕ) : Set (PotentialSample d) :=
  ⋂ i : ℕ, ⋂ _ : ‖densePt d i‖ < (r : ℝ),
    {omega : PotentialSample d |
      |anchoredPartialSum omega m (densePt d i) -
        anchoredPartialSum omega n (densePt d i)| ≤ ((j : ℝ) + 1)⁻¹}

/-- The gradient clause of the countable description. -/
def gradClauseSet (d r j m n : ℕ) : Set (PotentialSample d) :=
  ⋂ i : ℕ, ⋂ _ : ‖densePt d i‖ < (r : ℝ),
    {omega : PotentialSample d |
      ‖PotentialField.deriv (anchoredPartialSumField omega m) (densePt d i) -
        PotentialField.deriv (anchoredPartialSumField omega n) (densePt d i)‖ ≤
        ((j : ℝ) + 1)⁻¹}

/-- The gradient-Lipschitz clause of the countable description. -/
def lipClauseSet (d r j m n : ℕ) : Set (PotentialSample d) :=
  ⋂ i : ℕ, ⋂ i' : ℕ, ⋂ _ : ‖densePt d i‖ < (r : ℝ),
    ⋂ _ : ‖densePt d i'‖ < (r : ℝ),
      {omega : PotentialSample d |
        ‖(PotentialField.deriv (anchoredPartialSumField omega m) (densePt d i) -
              PotentialField.deriv (anchoredPartialSumField omega n) (densePt d i)) -
            (PotentialField.deriv (anchoredPartialSumField omega m) (densePt d i') -
              PotentialField.deriv (anchoredPartialSumField omega n)
                (densePt d i'))‖ ≤
          ((j : ℝ) + 1)⁻¹ * ‖densePt d i - densePt d i'‖}

/-- The countable Borel description of the anchored good event. -/
def anchoredCauchySet (d : ℕ) : Set (PotentialSample d) :=
  ⋂ r : ℕ, ⋂ j : ℕ, ⋃ N : ℕ, ⋂ m : ℕ, ⋂ _ : N ≤ m, ⋂ n : ℕ, ⋂ _ : N ≤ n,
    valueClauseSet d r j m n ∩ gradClauseSet d r j m n ∩ lipClauseSet d r j m n

/-! ### Measurability of the countable description -/

theorem measurableSet_valueClauseSet (r j m n : ℕ) :
    MeasurableSet (valueClauseSet d r j m n) :=
  MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le
      (((measurable_anchoredPartialSum m (densePt d i)).sub
        (measurable_anchoredPartialSum n (densePt d i))).norm) measurable_const

theorem measurableSet_gradClauseSet (r j m n : ℕ) :
    MeasurableSet (gradClauseSet d r j m n) :=
  MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le
      (((measurable_deriv_anchoredPartialSumField m (densePt d i)).sub
        (measurable_deriv_anchoredPartialSumField n (densePt d i))).norm)
      measurable_const

theorem measurableSet_lipClauseSet (r j m n : ℕ) :
    MeasurableSet (lipClauseSet d r j m n) :=
  MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun i' ↦
    MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le
        (((((measurable_deriv_anchoredPartialSumField m (densePt d i)).sub
              (measurable_deriv_anchoredPartialSumField n (densePt d i))).sub
            ((measurable_deriv_anchoredPartialSumField m (densePt d i')).sub
              (measurable_deriv_anchoredPartialSumField n (densePt d i'))))).norm)
        measurable_const

theorem measurableSet_anchoredCauchySet (d : ℕ) :
    MeasurableSet (anchoredCauchySet d) :=
  MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iUnion fun _ ↦ MeasurableSet.iInter fun m ↦
      MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun n ↦
        MeasurableSet.iInter fun _ ↦
          ((measurableSet_valueClauseSet r j m n).inter
            (measurableSet_gradClauseSet r j m n)).inter
            (measurableSet_lipClauseSet r j m n)

/-! ### The countable description is the anchored good event -/

theorem mem_anchoredCauchySet_iff {omega : PotentialSample d} :
    omega ∈ anchoredCauchySet d ↔
      ∀ r j : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
        ((∀ i : ℕ, ‖densePt d i‖ < (r : ℝ) →
              |anchoredPartialSum omega m (densePt d i) -
                anchoredPartialSum omega n (densePt d i)| ≤ ((j : ℝ) + 1)⁻¹) ∧
            ∀ i : ℕ, ‖densePt d i‖ < (r : ℝ) →
              ‖PotentialField.deriv (anchoredPartialSumField omega m) (densePt d i) -
                  PotentialField.deriv (anchoredPartialSumField omega n)
                    (densePt d i)‖ ≤ ((j : ℝ) + 1)⁻¹) ∧
          ∀ i i' : ℕ, ‖densePt d i‖ < (r : ℝ) → ‖densePt d i'‖ < (r : ℝ) →
            ‖(PotentialField.deriv (anchoredPartialSumField omega m) (densePt d i) -
                  PotentialField.deriv (anchoredPartialSumField omega n)
                    (densePt d i)) -
                (PotentialField.deriv (anchoredPartialSumField omega m)
                    (densePt d i') -
                  PotentialField.deriv (anchoredPartialSumField omega n)
                    (densePt d i'))‖ ≤
              ((j : ℝ) + 1)⁻¹ * ‖densePt d i - densePt d i'‖ := by
  simp only [anchoredCauchySet, valueClauseSet, gradClauseSet, lipClauseSet,
    Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]

theorem mem_anchoredCauchySet_of_anchoredC11Cauchy {omega : PotentialSample d}
    (h : AnchoredC11Cauchy omega) : omega ∈ anchoredCauchySet d := by
  rw [mem_anchoredCauchySet_iff]
  intro r j
  have hpos : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.uniformCauchySeqOn_iff.1 (h.value (r : ℝ)) _ hpos
  obtain ⟨N₂, hN₂⟩ := Metric.uniformCauchySeqOn_iff.1 (h.gradient (r : ℝ)) _ hpos
  obtain ⟨N₃, hN₃⟩ := h.lipschitz (r : ℝ) _ hpos
  refine ⟨max N₁ (max N₂ N₃), fun m hm n hn ↦ ⟨⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩,
    fun i i' hi hi' ↦ ?_⟩⟩
  · have hmem : densePt d i ∈ Metric.closedBall (0 : Vec d) (r : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hi.le
    have := hN₁ m (le_trans (le_max_left _ _) hm) n
      (le_trans (le_max_left _ _) hn) _ hmem
    rw [Real.dist_eq] at this
    exact this.le
  · have hmem : densePt d i ∈ Metric.closedBall (0 : Vec d) (r : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hi.le
    have := hN₂ m (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm) n
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn) _ hmem
    rw [dist_eq_norm] at this
    exact this.le
  · have hmem : densePt d i ∈ Metric.closedBall (0 : Vec d) (r : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hi.le
    have hmem' : densePt d i' ∈ Metric.closedBall (0 : Vec d) (r : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hi'.le
    have hlip := hN₃ m n
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
    have := hlip.dist_le_mul _ hmem _ hmem'
    rwa [Real.coe_toNNReal _ hpos.le, dist_eq_norm, dist_eq_norm] at this

theorem anchoredC11Cauchy_of_mem_anchoredCauchySet {omega : PotentialSample d}
    (h : omega ∈ anchoredCauchySet d) : AnchoredC11Cauchy omega := by
  rw [mem_anchoredCauchySet_iff] at h
  refine ⟨fun R ↦ ?_, fun R ↦ ?_, fun R ↦ ?_⟩
  · rw [Metric.uniformCauchySeqOn_iff]
    intro eps heps
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt heps
    obtain ⟨r, hr⟩ := exists_nat_gt R
    obtain ⟨N, hN⟩ := h r j
    refine ⟨N, fun m hm n hn x hx ↦ ?_⟩
    have hcl : IsClosed {x : Vec d | |anchoredPartialSum omega m x -
        anchoredPartialSum omega n x| ≤ ((j : ℝ) + 1)⁻¹} :=
      isClosed_le (((continuous_anchoredPartialSum omega m).sub
        (continuous_anchoredPartialSum omega n)).norm) continuous_const
    have hball := forall_mem_closedBall_of_forall_densePt hcl hr
      (hN m hm n hn).1.1 x hx
    have hlt : ((j : ℝ) + 1)⁻¹ < eps := by rwa [← one_div]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hball hlt
  · rw [Metric.uniformCauchySeqOn_iff]
    intro eps heps
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt heps
    obtain ⟨r, hr⟩ := exists_nat_gt R
    obtain ⟨N, hN⟩ := h r j
    refine ⟨N, fun m hm n hn x hx ↦ ?_⟩
    have hcl : IsClosed {x : Vec d |
        ‖PotentialField.deriv (anchoredPartialSumField omega m) x -
          PotentialField.deriv (anchoredPartialSumField omega n) x‖ ≤
          ((j : ℝ) + 1)⁻¹} :=
      isClosed_le
        (((PotentialField.deriv (anchoredPartialSumField omega m)).continuous.sub
          (PotentialField.deriv
            (anchoredPartialSumField omega n)).continuous).norm) continuous_const
    have hball := forall_mem_closedBall_of_forall_densePt hcl hr
      (hN m hm n hn).1.2 x hx
    have hlt : ((j : ℝ) + 1)⁻¹ < eps := by rwa [← one_div]
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hball hlt
  · intro eps heps
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt heps
    obtain ⟨r, hr⟩ := exists_nat_gt R
    obtain ⟨N, hN⟩ := h r j
    refine ⟨N, fun m n hm hn ↦ ?_⟩
    have hcont : Continuous fun q : Vec d × Vec d ↦
        ‖(PotentialField.deriv (anchoredPartialSumField omega m) q.1 -
            PotentialField.deriv (anchoredPartialSumField omega n) q.1) -
          (PotentialField.deriv (anchoredPartialSumField omega m) q.2 -
            PotentialField.deriv (anchoredPartialSumField omega n) q.2)‖ := by
      have hm1 := (PotentialField.deriv
        (anchoredPartialSumField omega m)).continuous
      have hn1 := (PotentialField.deriv
        (anchoredPartialSumField omega n)).continuous
      exact (((hm1.comp continuous_fst).sub (hn1.comp continuous_fst)).sub
        ((hm1.comp continuous_snd).sub (hn1.comp continuous_snd))).norm
    have hcl : IsClosed {q : Vec d × Vec d |
        ‖(PotentialField.deriv (anchoredPartialSumField omega m) q.1 -
              PotentialField.deriv (anchoredPartialSumField omega n) q.1) -
            (PotentialField.deriv (anchoredPartialSumField omega m) q.2 -
              PotentialField.deriv (anchoredPartialSumField omega n) q.2)‖ ≤
          ((j : ℝ) + 1)⁻¹ * ‖q.1 - q.2‖} :=
      isClosed_le hcont
        (continuous_const.mul ((continuous_fst.sub continuous_snd).norm))
    have hball := forall_mem_closedBall_pair_of_forall_densePt
      (P := fun x y : Vec d ↦
        ‖(PotentialField.deriv (anchoredPartialSumField omega m) x -
              PotentialField.deriv (anchoredPartialSumField omega n) x) -
            (PotentialField.deriv (anchoredPartialSumField omega m) y -
              PotentialField.deriv (anchoredPartialSumField omega n) y)‖ ≤
          ((j : ℝ) + 1)⁻¹ * ‖x - y‖)
      hcl hr (hN m hm n hn).2
    have hlt : ((j : ℝ) + 1)⁻¹ < eps := by rwa [← one_div]
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    rw [Real.coe_toNNReal _ heps.le, dist_eq_norm, dist_eq_norm]
    exact le_trans (hball x hx y hy)
      (mul_le_mul_of_nonneg_right hlt.le (norm_nonneg _))

/-- The anchored good event coincides with its countable Borel description. -/
theorem anchoredC11GoodSet_eq_anchoredCauchySet :
    anchoredC11GoodSet d = anchoredCauchySet d := by
  rw [anchoredC11GoodSet_eq_setOf_anchoredC11Cauchy]
  ext omega
  exact ⟨mem_anchoredCauchySet_of_anchoredC11Cauchy,
    anchoredC11Cauchy_of_mem_anchoredCauchySet⟩

/-- The canonical anchored convergence event is measurable. -/
theorem measurableSet_anchoredC11GoodSet (d : ℕ) :
    MeasurableSet (anchoredC11GoodSet d) := by
  rw [anchoredC11GoodSet_eq_anchoredCauchySet]
  exact measurableSet_anchoredCauchySet d

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
