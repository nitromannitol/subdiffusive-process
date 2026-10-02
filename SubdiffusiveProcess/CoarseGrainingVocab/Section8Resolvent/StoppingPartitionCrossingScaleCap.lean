import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedGraphDistance
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedSource
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionSphereGrowth




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-! ## 1. The Euclidean length of one repaired-graph step -/

/-- **One repaired-graph edge moves the refined centre by at most `105`
neighbour side lengths.**  The three contributions are the half-grid offset of
each endpoint (`3/2` side lengths) and the nearness of the selected parent
cubes (`10` times the larger side); the scale window collapses the larger side
to nine times `p`'s. -/
theorem dist_refinedStoppingCenter_le_of_repairedStoppingGraph_adj
    {q p : RefinedStoppingCell failure omega base}
    (hadj : repairedStoppingGraph.Adj q p) :
    dist (refinedStoppingCenter q) (refinedStoppingCenter p) ≤
      105 * cubeScaleFactor (refinedStoppingFailureCube p) := by
  have hnear := ((repairedStoppingGraph_adj_iff q p).mp hadj).2
  rw [StoppingCubesNear] at hnear
  have hq9 := cubeScaleFactor_le_nine_mul_of_repairedStoppingGraph_adj hadj
  have hppos : 0 < cubeScaleFactor (refinedStoppingFailureCube p) := by
    rw [cubeScaleFactor]; positivity
  have hmax : max (cubeScaleFactor (refinedStoppingFailureCube q))
      (cubeScaleFactor (refinedStoppingFailureCube p)) ≤
      9 * cubeScaleFactor (refinedStoppingFailureCube p) :=
    max_le hq9 (by linarith)
  have h1 := dist_cubeCenter_refinedStoppingCenter_le q
  have h2 := dist_cubeCenter_refinedStoppingCenter_le p
  have h1' : dist (refinedStoppingCenter q)
      (cubeCenter (refinedStoppingFailureCube q)) ≤
      3 / 2 * cubeScaleFactor (refinedStoppingFailureCube q) := by
    rw [dist_comm]; exact h1
  have ht1 := dist_triangle (refinedStoppingCenter q)
    (cubeCenter (refinedStoppingFailureCube q)) (refinedStoppingCenter p)
  have ht2 := dist_triangle (cubeCenter (refinedStoppingFailureCube q))
    (cubeCenter (refinedStoppingFailureCube p)) (refinedStoppingCenter p)
  nlinarith [h1, h1', h2, hnear, hmax, hq9, hppos, ht1, ht2]

/-! ## 2. A deterministic scale cap on every ball -/

/-- **Every ball carries a scale cap.**  Only finitely many refined cells have
their centre in a fixed ball, because the centred enlargements form a locally
finite family, so their side lengths are bounded.  The cap is deterministic;
its *size* is what the multiscale failure estimate has to control. -/
theorem exists_refinedStoppingScaleCap
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) (rho : ℝ) :
    ∃ S : ℝ, 0 < S ∧ ∀ q : RefinedStoppingCell failure omega base,
      dist (refinedStoppingCenter q) x0 ≤ rho →
        cubeScaleFactor (refinedStoppingFailureCube q) ≤ S := by
  classical
  have hpos : ∀ p : RefinedStoppingCell failure omega base,
      0 ≤ cubeScaleFactor (refinedStoppingFailureCube p) := by
    intro p
    rw [cubeScaleFactor]
    positivity
  set T := repairedStoppingSourceCells hinitial hrepair x0 rho with hT
  refine ⟨1 + ∑ p ∈ T, cubeScaleFactor (refinedStoppingFailureCube p), ?_, ?_⟩
  · have hsum : 0 ≤ ∑ p ∈ T, cubeScaleFactor (refinedStoppingFailureCube p) :=
      Finset.sum_nonneg (fun p _ ↦ hpos p)
    linarith
  · intro q hq
    have hqT : q ∈ T := by
      apply (mem_repairedStoppingSourceCells_iff hinitial hrepair x0 rho q).mpr
      refine ⟨refinedStoppingCenter q, ?_, ?_⟩
      · rw [translatedCube_eq_metricBall]
        exact Metric.mem_ball_self (by positivity)
      · exact Metric.mem_closedBall.mpr hq
    have hle := Finset.single_le_sum
      (f := fun p ↦ cubeScaleFactor (refinedStoppingFailureCube p))
      (fun p _ ↦ hpos p) hqT
    linarith

/-! ## 3. The reach of `n` repaired-graph steps -/

/-- **The deterministic reach bound.**  Under a scale cap `S` valid on the ball
of radius `rho`, a cell at graph distance at most `n` from a source family
inside `B(x0, R + 3/2 S)` has its centre within `R + 3/2 S + 105 S n` of `x0`.

This is the deterministic content of `l.resolvent.multiscale.crossing`: to reach
Euclidean distance `3 ^ k R` one needs at least `(3 ^ k R - R - 3/2 S)/(105 S)`
repaired-graph steps.  A short crossing (fewer than `epsilon 3 ^ k` steps) is
therefore impossible unless `S ≳ R / epsilon`, i.e. unless a cell of side at
least `R / (105 epsilon)` meets the ball. -/
theorem dist_refinedStoppingCenter_le_of_stoppingGraphDistance_le
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (x0 : Vec d) {R S rho : ℝ} (hS : 0 ≤ S)
    (hsrc : ∀ s ∈ source, dist (refinedStoppingCenter s) x0 ≤ R + 3 / 2 * S)
    (hcap : ∀ p : RefinedStoppingCell failure omega base,
      dist (refinedStoppingCenter p) x0 ≤ rho →
        cubeScaleFactor (refinedStoppingFailureCube p) ≤ S) :
    ∀ n : ℕ, R + 3 / 2 * S + 105 * S * (n : ℝ) ≤ rho →
      ∀ q : RefinedStoppingCell failure omega base,
        stoppingGraphDistance repairedStoppingGraph source hsource q ≤ n →
          dist (refinedStoppingCenter q) x0 ≤
            R + 3 / 2 * S + 105 * S * (n : ℝ) := by
  have hconn := repairedStoppingGraph_connected failure omega hinitial hrepair
  intro n
  induction n with
  | zero =>
    intro _hguard q hq
    have hq0 : stoppingGraphDistance repairedStoppingGraph source hsource q = 0 := by
      omega
    obtain ⟨s, hs, hqs⟩ :=
      exists_source_dist_eq_stoppingGraphDistance repairedStoppingGraph hsource q
    have h0 : repairedStoppingGraph.dist q s = 0 := hqs.trans hq0
    have hqe : q = s := (hconn.dist_eq_zero_iff).mp h0
    subst hqe
    have hqs' := hsrc q hs
    simp only [Nat.cast_zero, mul_zero, add_zero] at hqs' ⊢
    linarith
  | succ n ih =>
    intro hguard q hq
    have hguard' : R + 3 / 2 * S + 105 * S * (n : ℝ) ≤ rho := by
      push_cast at hguard ⊢
      nlinarith [hS]
    by_cases hle : stoppingGraphDistance repairedStoppingGraph source hsource q ≤ n
    · have hrec := ih hguard' q hle
      push_cast
      nlinarith [hS]
    · have heq : stoppingGraphDistance repairedStoppingGraph source hsource q = n + 1 := by
        omega
      obtain ⟨p, hadj, hp⟩ := exists_adj_stoppingGraphDistance_eq_pred
        repairedStoppingGraph hconn hsource heq
      have hpd := ih hguard' p (le_of_eq hp)
      have hpcap := hcap p (le_trans hpd hguard')
      have hstep := dist_refinedStoppingCenter_le_of_repairedStoppingGraph_adj hadj
      have htri := dist_triangle (refinedStoppingCenter q) (refinedStoppingCenter p) x0
      push_cast
      nlinarith [hS, hpd, hpcap, hstep, htri]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
