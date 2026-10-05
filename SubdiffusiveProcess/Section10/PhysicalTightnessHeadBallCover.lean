module

public import SubdiffusiveProcess.Section10.PhysicalTightnessHeadExitDescent
public import SubdiffusiveProcess.Section10.PhysicalTightnessLocalCover

@[expose] public section

/-! Finite spatial cover of the qualitative compact killed-density estimate.
The time is deterministic and the exceptional event is genuinely measurable. -/
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- Every centered small ball inherits the finite-cover estimate at the same
positive time, outside one measurable event of small environment probability. -/
theorem measurable_uniform_local_exit {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (law : Kernel (Omega × Vec d) (Path d))
    (c rho : Omega → Vec d → ℝ)
    (hdata : ∀ᵐ omega ∂mu, LocalDiffusionData (c omega) (rho omega)
      (Kernel.comap law (fun x => (omega, x)) measurable_prodMk_left))
    (R r b e : ℝ) (hr : 0 < r) (hb : 0 < b) (he : 0 < e) :
    ∃ n : ℕ, ∃ S : Set Omega, MeasurableSet S ∧ mu S ≤ ENNReal.ofReal e ∧
      ∀ᵐ omega ∂mu, omega ∉ S → ∀ x ∈ Metric.ball (0 : Vec d) R,
        law (omega, x) {w | LifetimePath.exitTime (Metric.ball x (r / 4)) w ≤
          (headTime n : ENNReal)} ≤ ENNReal.ofReal b := by
  classical
  obtain ⟨centres, hcover⟩ := (isCompact_closedBall (0 : Vec d) R).elim_finite_subcover
    (fun y : Vec d => Metric.ball y (r / 32)) (fun _ => Metric.isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by positivity)⟩)
  let ei : ℝ := e / ((Fintype.card centres : ℝ) + 1)
  have hei : 0 < ei := by dsimp [ei]; positivity
  have hbank : ∀ i : centres, ∃ n : ℕ, ∃ S : Set Omega, MeasurableSet S ∧
      mu S ≤ ENNReal.ofReal ei ∧ ∀ᵐ omega ∂mu, omega ∉ S →
        ∀ x ∈ Metric.ball (i : Vec d) (r / 32),
          law (omega, x) {w | LifetimePath.exitTime (Metric.ball (i : Vec d) (r / 16)) w ≤
            (headTime n : ENNReal)} ≤ ENNReal.ofReal b := by
    intro i
    exact measurable_small_time_exit_on_open mu law c rho hdata Metric.isOpen_ball
      Metric.isBounded_ball Metric.isOpen_ball Metric.ball_subset_closedBall
      (isCompact_closedBall (i : Vec d) (r / 32))
      (Metric.closedBall_subset_ball (by linarith)) b ei hb hei
  choose ni Si hSi hSiMass hSiExit using hbank
  let n : ℕ := Finset.univ.sup ni
  let S : Set Omega := ⋃ i : centres, Si i
  have hS : MeasurableSet S := MeasurableSet.iUnion hSi
  have hSbound : mu S ≤ ENNReal.ofReal e := by
    calc
      mu S ≤ ∑ i : centres, mu (Si i) := measure_iUnion_fintype_le mu Si
      _ ≤ ∑ _i : centres, ENNReal.ofReal ei := Finset.sum_le_sum fun i _ => hSiMass i
      _ = ENNReal.ofReal ((Fintype.card centres : ℝ) * ei) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hei.le)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal (by
        dsimp only [ei]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (Fintype.card centres : ℝ) + 1)]
        nlinarith)
  refine ⟨n, S, hS, hSbound, ?_⟩
  filter_upwards [ae_all_iff.mpr hSiExit] with omega homega hgood
  intro x hx
  have hxclosed : x ∈ Metric.closedBall (0 : Vec d) R := Metric.ball_subset_closedBall hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hxclosed)
  let j : centres := ⟨i, hi⟩
  have hball : Metric.ball i (r / 16) ⊆ Metric.ball x (r / 4) := by
    intro y hy
    have hd := dist_triangle y i x
    have hdix : dist i x < r / 32 := by simpa only [dist_comm] using Metric.mem_ball.mp hxi
    have hdyi := Metric.mem_ball.mp hy
    exact Metric.mem_ball.mpr (by linarith)
  have hnot : omega ∉ Si j := fun hmem => hgood (mem_iUnion.mpr ⟨j, hmem⟩)
  have htime : (headTime n : ENNReal) ≤ (headTime (ni j) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (headTime_antitone (Finset.le_sup (f := ni) (Finset.mem_univ j)))
  exact (measure_mono fun w hw => ((exitTime_le_of_subset hball w).trans hw).trans htime).trans
    (homega j hnot x hxi)

end SubdiffusiveProcess.Section10.PhysicalTightness
