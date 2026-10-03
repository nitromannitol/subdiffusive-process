module

public import SubdiffusiveProcess.Section10.PhysicalExitChaining

@[expose] public section

/-! The already proved successive-exit argument only needs two small-time
exit estimates. This qualitative version serves the finitely many head laws. -/
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalExitChaining

/-- Choose the number of successive exits after the first small-time bound,
then use any deterministic second time giving the short-gap probability. -/
theorem head_modulus_bound_of_two_exit_estimates {d : ℕ}
    (R r T h0 epsilon : ℝ) (hr : 0 < r) (hT : 0 < T)
    (hh0 : 0 < h0) (hepsilon : 0 < epsilon) :
    ∃ q : ℕ, ∀ delta : NNReal,
      ∀ law : Kernel (Vec d) (Path d), StrongMarkov law →
        (∀ x : Vec d, ∀ᵐ w ∂law x, w.lifetime = ⊤) →
        (∀ x ∈ Metric.ball (0 : Vec d) R,
          law x {w | LifetimePath.exitTime (Metric.ball x (r / 4)) w ≤ ENNReal.ofReal h0} ≤
            ENNReal.ofReal (1 / 8 : ℝ)) →
        (∀ x ∈ Metric.ball (0 : Vec d) R,
          law x {w | LifetimePath.exitTime (Metric.ball x (r / 4)) w ≤ (delta : ENNReal)} ≤
            ENNReal.ofReal (epsilon / (16 * ((q : ℝ) + 1)))) →
        ∀ x ∈ Metric.ball (0 : Vec d) R,
          (law x).map (LifetimePath.continuousPathExtension
            (ContinuousMap.const NNReal (0 : Vec d)))
            (ContinuousPath.modulusSet (Real.toNNReal T) (delta : ENNReal) (ENNReal.ofReal r))ᶜ ≤
              law x {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤ ENNReal.ofReal T} +
                ENNReal.ofReal epsilon := by
  let h : ℝ := h0 / 2
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt
    (16 * Real.exp (T / h) / epsilon) (by norm_num : (1 : ℝ) < 2)
  have hgeometric : ENNReal.ofReal (Real.exp (T / h)) * ENNReal.ofReal (1 / 2 : ℝ) ^ q ≤
      ENNReal.ofReal (epsilon / 16) := geometric_error_le hepsilon (Real.exp_pos _).le q hq
  have hgap : (q : ENNReal) * ENNReal.ofReal (epsilon / (16 * ((q : ℝ) + 1))) ≤
      ENNReal.ofReal (epsilon / 16) := short_gap_error_le hepsilon.le q
  refine ⟨q, ?_⟩
  intro delta law hSM hcons hfirst hsecond x hx
  let k := continuousKernel law
  letI : IsMarkovKernel k := continuousKernel_isMarkov law hSM
  have hgamma : ∀ y ∈ Metric.ball (0 : Vec d) R,
      (∫⁻ p, exitWeight h (ContinuousPath.exitTime (Metric.ball y (r / 4)) p) ∂k y) ≤
        ENNReal.ofReal (1 / 2) := by
    intro y hy
    apply exitWeight_integral_le_half k y _ Metric.isOpen_ball h0 hh0
    rw [continuousKernel_exit law hcons y _ Metric.isOpen_ball]
    exact hfirst y hy
  have hbeta : ∀ y ∈ Metric.ball (0 : Vec d) R,
      k y {p | ContinuousPath.exitTime (Metric.ball y (r / 4)) p ≤ (delta : ENNReal)} ≤
        ENNReal.ofReal (epsilon / (16 * ((q : ℝ) + 1))) := by
    intro y hy
    rw [continuousKernel_exit law hcons y _ Metric.isOpen_ball]
    exact hsecond y hy
  have hbound := modulus_bound_of_restart_estimates k law
    (continuousKernel_attachment law hcons) hSM (continuousKernel_start law hSM hcons)
    (Metric.ball (0 : Vec d) R) Metric.isOpen_ball.measurableSet
    (by positivity : 0 < r / 4) (Real.toNNReal T) delta hh
    (ENNReal.ofReal (1 / 2)) hgamma
    (ENNReal.ofReal (epsilon / (16 * ((q : ℝ) + 1)))) hbeta q x
  have hmod : ContinuousPath.modulusSet (alpha := Vec d) (Real.toNNReal T)
      (delta : ENNReal) (ENNReal.ofReal (3 * (r / 4))) ⊆
      ContinuousPath.modulusSet (Real.toNNReal T) (delta : ENNReal) (ENNReal.ofReal r) :=
    ContinuousPath.modulusSet_mono (ENNReal.ofReal_le_ofReal (by linarith))
  have hcontain := continuousKernel_containment_le law hcons x R T
  have herror : ENNReal.ofReal (Real.exp ((Real.toNNReal T : ℝ) / h)) *
        ENNReal.ofReal (1 / 2 : ℝ) ^ q +
        (q : ENNReal) * ENNReal.ofReal (epsilon / (16 * ((q : ℝ) + 1))) ≤
      ENNReal.ofReal epsilon := by
    rw [Real.coe_toNNReal T hT.le]
    calc
      _ ≤ ENNReal.ofReal (epsilon / 16) + ENNReal.ofReal (epsilon / 16) :=
        add_le_add hgeometric hgap
      _ ≤ ENNReal.ofReal epsilon := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [← continuousKernel_apply]
  calc
    _ ≤ k x (ContinuousPath.modulusSet (Real.toNNReal T) (delta : ENNReal)
        (ENNReal.ofReal (3 * (r / 4))))ᶜ := measure_mono (compl_subset_compl.mpr hmod)
    _ ≤ _ := hbound
    _ ≤ law x {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤ ENNReal.ofReal T} +
        ENNReal.ofReal epsilon := by
      rw [add_assoc]
      exact add_le_add hcontain herror

end SubdiffusiveProcess.Section10.PhysicalTightness
