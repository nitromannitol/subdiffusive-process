import SubdiffusiveProcess.KilledFeller.KilledResolventFubini
import SubdiffusiveProcess.Analysis.KilledOccupationResolvent
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- A norm-preserving extension of a continuous source from a compact closed
carrier. Only its restriction is ever read before exit. -/
def closedSourceExtension {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (f : C(closure Q, ℝ)) :
    BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
  (BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed
    (BoundedContinuousFunction.mkOfCompact f) isClosed_closure).choose

theorem closedSourceExtension_restrict {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (f : C(closure Q, ℝ)) (x : closure Q) :
    closedSourceExtension Q f x = f x := by
  have h := (BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed
    (BoundedContinuousFunction.mkOfCompact f) isClosed_closure).choose_spec.2
  exact congrFun (congrArg (fun g : BoundedContinuousFunction (closure Q) ℝ =>
    (g : closure Q → ℝ)) h) x

theorem norm_closedSourceExtension {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (f : C(closure Q, ℝ)) : ‖closedSourceExtension Q f‖ = ‖f‖ := by
  exact (BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed
    (BoundedContinuousFunction.mkOfCompact f) isClosed_closure).choose_spec.1

theorem killedTest_congr_on {d : ℕ} (Q : Set (SpatialCoordinates d))
    (f g : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hfg : Set.EqOn f g Q) (w : DiffusionPath d) (t : ℝ) :
    SubdiffusiveProcess.KilledFeller.killedTest Q f w t = SubdiffusiveProcess.KilledFeller.killedTest Q g w t := by
  classical
  unfold SubdiffusiveProcess.KilledFeller.killedTest
  split_ifs with ht
  · exact hfg (ContinuousPath.mem_of_lt_exitTime Q w (Real.toNNReal t) ht)
  · rfl

theorem killedResolventScalar_congr_on {d : ℕ} (Q : Set (SpatialCoordinates d))
    (f g : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hfg : Set.EqOn f g Q) (lam : ℝ) (mu : Measure (DiffusionPath d)) :
    SubdiffusiveProcess.KilledFeller.killedResolventScalar Q f lam mu =
      SubdiffusiveProcess.KilledFeller.killedResolventScalar Q g lam mu := by
  unfold SubdiffusiveProcess.KilledFeller.killedResolventScalar
  congr 1
  funext w
  congr 1
  funext t
  rw [killedTest_congr_on Q f g hfg]

theorem closedSourceExtension_scalar_eq {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (lam : ℝ) (mu : Measure (DiffusionPath d)) :
    SubdiffusiveProcess.KilledFeller.killedResolventScalar Q
      (closedSourceExtension Q (f.toContinuousMap.restrict (closure Q))) lam mu =
      SubdiffusiveProcess.KilledFeller.killedResolventScalar Q f lam mu := by
  apply killedResolventScalar_congr_on
  intro x hx
  exact closedSourceExtension_restrict Q _ ⟨x, subset_closure hx⟩

/-- Read the source on the closed carrier strictly before the original exit. -/
def closedKilledTest {d : ℕ} (Q : Set (SpatialCoordinates d))
    (f : C(closure Q, ℝ)) (w : DiffusionPath d) (t : ℝ) : ℝ :=
  if ht : ENNReal.ofReal t < ContinuousPath.exitTime Q w then
    f ⟨w (Real.toNNReal t), subset_closure
      (ContinuousPath.mem_of_lt_exitTime Q w (Real.toNNReal t) ht)⟩
  else 0

theorem closedKilledTest_eq {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (f : C(closure Q, ℝ)) (w : DiffusionPath d) (t : ℝ) :
    closedKilledTest Q f w t = SubdiffusiveProcess.KilledFeller.killedTest Q (closedSourceExtension Q f) w t := by
  classical
  unfold closedKilledTest SubdiffusiveProcess.KilledFeller.killedTest
  split_ifs with ht
  · exact (closedSourceExtension_restrict Q f _).symm
  · rfl

theorem abs_closedKilledTest_le {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (f : C(closure Q, ℝ)) (w : DiffusionPath d) (t : ℝ) :
    |closedKilledTest Q f w t| ≤ ‖f‖ := by
  classical
  unfold closedKilledTest
  split_ifs
  · simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm _
  · simpa only [abs_zero] using norm_nonneg f

theorem continuous_closedKilledTest_source {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace (closure Q)] (w : DiffusionPath d) (t : ℝ) :
    Continuous (fun f : C(closure Q, ℝ) => closedKilledTest Q f w t) := by
  classical
  unfold closedKilledTest
  split_ifs
  · exact continuous_eval_const _
  · exact continuous_const

/-- Joint shift/source continuity of the literal killed occupation integral.
No continuity of the exit-time map or extension operator is used. -/
theorem continuous_closedKilledResolventScalar {d : ℕ}
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) [CompactSpace (closure Q)]
    (mu : Measure (DiffusionPath d)) [IsFiniteMeasure mu] :
    Continuous (fun a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ) =>
      SubdiffusiveProcess.KilledFeller.killedResolventScalar Q (closedSourceExtension Q a.2) a.1.1 mu) := by
  let F := fun (a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ)) (p : DiffusionPath d × ℝ) =>
    Real.exp (-a.1.1 * p.2) * closedKilledTest Q a.2 p.1 p.2
  have hFmeas (a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ)) :
      AEStronglyMeasurable (F a) (mu.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    simp only [F, closedKilledTest_eq]
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (SubdiffusiveProcess.KilledFeller.measurable_killedTest Q hQ (closedSourceExtension Q a.2))).aestronglyMeasurable
  have hFeq (a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ)) :
      (∫ p, F a p ∂(mu.prod (volume.restrict (Ioi (0 : ℝ))))) =
        SubdiffusiveProcess.KilledFeller.killedResolventScalar Q (closedSourceExtension Q a.2) a.1.1 mu := by
    simp only [F, closedKilledTest_eq]
    rw [integral_prod _ (SubdiffusiveProcess.KilledFeller.integrable_killedLaplace_product Q hQ
      (closedSourceExtension Q a.2) a.1.1 a.1.2 mu)]
    rfl
  have hFc : Continuous (fun a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ) =>
      ∫ p, F a p ∂(mu.prod (volume.restrict (Ioi (0 : ℝ))))) := by
    apply continuous_iff_continuousAt.mpr
    intro a0
    let bound : DiffusionPath d × ℝ → ℝ := fun p =>
      Real.exp (-(a0.1.1 / 2) * p.2) * (‖a0.2‖ + 1)
    have hbound : Integrable bound (mu.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      ((exp_neg_integrableOn_Ioi 0 (half_pos a0.1.2)).mul_const (‖a0.2‖ + 1)).comp_snd mu
    have hnear : ∀ᶠ a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ) in 𝓝 a0,
        a0.1.1 / 2 < a.1.1 ∧ ‖a.2‖ < ‖a0.2‖ + 1 := by
      exact ((continuous_subtype_val.comp continuous_fst).continuousAt.eventually
        (eventually_gt_nhds (by
          change a0.1.1 / 2 < a0.1.1
          have hp : 0 < a0.1.1 := a0.1.2
          linarith))).and
        (continuous_snd.norm.continuousAt.eventually (eventually_lt_nhds (lt_add_one _)))
    refine continuousAt_of_dominated (Eventually.of_forall hFmeas) ?_ hbound ?_
    · filter_upwards [hnear] with a ha
      have ht : ∀ᵐ p : DiffusionPath d × ℝ ∂(mu.prod (volume.restrict (Ioi (0 : ℝ)))),
          0 < p.2 := by
        rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)]
        exact Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
      filter_upwards [ht] with p hp
      dsimp only [F, bound]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-a.1.1 * p.2) ≤ Real.exp (-(a0.1.1 / 2) * p.2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [ha.1, hp]
      exact mul_le_mul hexp ((abs_closedKilledTest_le Q a.2 p.1 p.2).trans ha.2.le)
        (abs_nonneg _) (Real.exp_pos _).le
    · exact Eventually.of_forall fun p =>
        ((Real.continuous_exp.comp
          ((continuous_subtype_val.comp continuous_fst).neg.mul continuous_const)).mul
          ((continuous_closedKilledTest_source Q p.1 p.2).comp continuous_snd)).continuousAt
  simpa only [hFeq] using hFc

theorem killedOccupationResolvent_eq_scalar {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    killedOccupationResolvent Q KN N omega lam f x =
      SubdiffusiveProcess.KilledFeller.killedResolventScalar Q f lam (KN N (omega, x)) := by
  simp only [killedOccupationResolvent, SubdiffusiveProcess.KilledFeller.killedResolventScalar,
    SubdiffusiveProcess.KilledFeller.indicator_exp_eq_exp_killedTest]

end SubdiffusiveProcess.Analysis
