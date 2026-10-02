import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import SubdiffusiveProcess.Frozen.Assumptions.PotentialSample
/-!
# Standard Borel structure of the frozen potential carrier

The derivative graph is closed by locally uniform convergence of derivatives.
Local Lipschitz continuity of the derivative is a countable intersection of
countable unions of closed Lipschitz conditions on integer-radius balls.
Thus the frozen carrier is a Borel subset of a Polish continuous-map pair.
Only a proposition-valued instance is added; its topology and sigma-field
are exactly the existing frozen vocabulary's structures.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open Homogenization Filter Topology Set MeasureTheory
noncomputable section

local instance (d : ℕ) : MeasurableSpace C(Vec d, ℝ) := borel _
local instance (d : ℕ) : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
local instance (d : ℕ) : MeasurableSpace C(Vec d, Vec d →L[ℝ] ℝ) := borel _
local instance (d : ℕ) : BorelSpace C(Vec d, Vec d →L[ℝ] ℝ) := ⟨rfl⟩

local instance restrictedDerivativeContinuousMapPolish (d : ℕ) :
    PolishSpace C(Vec d, Vec d →L[ℝ] ℝ) := by
  letI : TopologicalSpace.IsCompletelyMetrizableSpace C(Vec d, Vec d →L[ℝ] ℝ) :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
      (X := C(Vec d, Vec d →L[ℝ] ℝ))
  infer_instance

theorem restricted_derivative_limit (d : ℕ) (u : ℕ → C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) (p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) (hu : Tendsto u atTop (𝓝 p)) (hd : ∀ n x, HasFDerivAt (u n).1 ((u n).2 x) x) (x : Vec d) : HasFDerivAt p.1 (p.2 x) x := by
  have hdconv : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hu
  have hfconv : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hu
  have hconv : TendstoLocallyUniformly (fun n => (u n).2) p.2 atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hdconv
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
    hconv.tendstoLocallyUniformlyOn
    (fun n x _ => hd n x)
    (fun y _ => (continuous_eval_const y).tendsto p.1 |>.comp hfconv)
    (Set.mem_univ x)


theorem restricted_isClosed_lipschitzOn (X E : Type*) [PseudoMetricSpace X]
    [PseudoMetricSpace E] (K : Set X) (c : NNReal) :
    IsClosed {g : C(X, E) | LipschitzOnWith c g K} := by
  simp_rw [lipschitzOnWith_iff_dist_le_mul, Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _hx =>
    isClosed_iInter fun y => isClosed_iInter fun _hy =>
      isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const


theorem restricted_locallyLipschitz_iff (d : ℕ) (g : C(Vec d, Vec d →L[ℝ] ℝ)) : (∀ K : Set (Vec d), IsCompact K → ∃ c : NNReal, LipschitzOnWith c g K) ↔ ∀ n : ℕ, ∃ m : ℕ, LipschitzOnWith (m : NNReal) g (Metric.closedBall 0 (n : ℝ)) := by
  constructor
  · intro h n
    have hc := h (Metric.closedBall 0 (n : ℝ)) (isCompact_closedBall 0 (n : ℝ))
    obtain ⟨c, hc⟩ := hc
    obtain ⟨m, hm⟩ := exists_nat_ge (c : ℝ)
    refine ⟨m, ?_⟩
    rw [lipschitzOnWith_iff_dist_le_mul] at hc ⊢
    intro x hx y hy
    exact (hc x hx y hy).trans
      (mul_le_mul_of_nonneg_right hm (dist_nonneg))
  · intro h K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨n, hn⟩ := exists_nat_ge r
    obtain ⟨m, hm⟩ := h n
    refine ⟨m, hm.mono ?_⟩
    intro x hx
    exact Metric.closedBall_subset_closedBall hn (hr hx)


theorem restricted_locallyLipschitz_measurable (d : ℕ)
    (hclosed : ∀ n m : ℕ, IsClosed {g : C(Homogenization.Vec d,
      Homogenization.Vec d →L[ℝ] ℝ) |
      LipschitzOnWith (m : NNReal) g (Metric.closedBall 0 (n : ℝ))}) :
    MeasurableSet {g : C(Homogenization.Vec d,
      Homogenization.Vec d →L[ℝ] ℝ) |
      ∀ n : ℕ, ∃ m : ℕ, LipschitzOnWith (m : NNReal) g (Metric.closedBall 0 (n : ℝ))} := by
  simp_rw [Set.setOf_forall, Set.setOf_exists]
  exact MeasurableSet.iInter (fun n =>
    MeasurableSet.iUnion (fun m =>
      (hclosed n m).measurableSet))



open SubdiffusiveProcess.Frozen.Assumptions Homogenization

theorem restricted_potentialField_standardBorel (d : ℕ)
    [StandardBorelSpace (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ))]
    (h : MeasurableSet {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) |
      (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Vec d), IsCompact K → ∃ C : NNReal, LipschitzOnWith C p.2 K}) :
    StandardBorelSpace (PotentialField d) := by
  have heq : potentialFieldMeasurableSpace d =
      MeasurableSpace.comap (Subtype.val : PotentialField d →
        C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) inferInstance := by
    unfold potentialFieldMeasurableSpace potentialFieldTopologicalSpace
    rw [borel_comap, ← BorelSpace.measurable_eq]
  rw [heq]
  exact h.standardBorel


theorem restricted_derivativeGraph_isClosed (d : ℕ) :
    IsClosed {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) |
      ∀ x, HasFDerivAt p.1 (p.2 x) x} := by
  apply IsSeqClosed.isClosed
  intro u p hu hp
  exact restricted_derivative_limit d u p hp hu

theorem restricted_potentialField_measurable (d : ℕ) :
    MeasurableSet {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) |
      (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Vec d), IsCompact K → ∃ C : NNReal, LipschitzOnWith C p.2 K} := by
  have hlip := restricted_locallyLipschitz_measurable d
    (fun n m => restricted_isClosed_lipschitzOn _ _ (Metric.closedBall 0 (n : ℝ)) m)
  have hd := (restricted_derivativeGraph_isClosed d).measurableSet
  have heq : {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) |
      (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Vec d), IsCompact K → ∃ C : NNReal, LipschitzOnWith C p.2 K} =
    {p : C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) |
      ∀ x, HasFDerivAt p.1 (p.2 x) x} ∩
    Prod.snd ⁻¹' {g : C(Vec d, Vec d →L[ℝ] ℝ) |
      ∀ n : ℕ, ∃ m : ℕ, LipschitzOnWith (m : NNReal) g (Metric.closedBall 0 (n : ℝ))} := by
    ext p
    exact and_congr_right (fun _ => restricted_locallyLipschitz_iff d p.2)
  rw [heq]
  exact hd.inter (hlip.preimage measurable_snd)


/-- The frozen potential carrier is a Borel subspace of the continuous-map pair. -/
instance restrictedPotentialFieldStandardBorel (d : ℕ) :
    StandardBorelSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  restricted_potentialField_standardBorel d (restricted_potentialField_measurable d)

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
