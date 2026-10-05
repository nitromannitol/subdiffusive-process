module

public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Main.MeasureTraceCharacterization
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

lemma aux_speed_trace_completion_finite_union
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → Set α) (hf : ∀ x ∈ s, μ (f x) < (⊤ : ℝ≥0∞)) :
    μ (⋃ x ∈ s, f x) < (⊤ : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha' : μ (f a) < (⊤ : ℝ≥0∞) := hf a (by simp)
      have hs' : ∀ x ∈ s, μ (f x) < (⊤ : ℝ≥0∞) := by
        intro x hx
        exact hf x (by simp [hx])
      have hi : μ (⋃ x ∈ s, f x) < (⊤ : ℝ≥0∞) := ih hs'
      simpa [Finset.mem_insert, ha] using
        (measure_union_lt_top ha' hi)



theorem speed_trace_completion {d : Nat} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Homogenization.TriadicCube d) (hr : 0 < cubeScaleFactor Q)
    (epsilon : ℝ) (_heps : 0 < epsilon) (heps1 : epsilon < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ),
      ∀ omega : BilateralField d,
      ∀ mu : Measure (SpatialCoordinates d),
      ∀ Kmu : ℝ,
      0 ≤ Kmu →
      mu (closure (openCubeSet Q)) < ∞ →
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) mu →
      (∀ x ∈ closure (openCubeSet Q), ∀ r : ℝ, 0 < r → r ≤ 1 →
        mu (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) ∧
        ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
          ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon))) →
      ∀ nu : Measure (SpatialCoordinates d),
      (nu = mu.restrict (closure (openCubeSet Q)) ∨
        ∃ N : Nat, nu = (cutoffSpeedMeasure M H omega N).restrict
          (closure (openCubeSet Q))) →
        ∃! T : CubeFractionalL2 (k := 1) hd (cubeCenter Q) (cubeScaleFactor Q)
          hr halfFractionalOrder → Lp ℝ 2 nu,
        MeasureTraceCharacterization hd Q hr nu Kmu C T := by
  have ht : (d : ℝ) - 1 < (d : ℝ) - epsilon := by
    linarith
  obtain ⟨C, hC, htrace⟩ :=
    SubdiffusiveProcess.exists_unique_measureTrace hd Q hr
      ((d : ℝ) - epsilon) ht
  refine ⟨C, hC, ?_⟩
  have hcompact : IsCompact (closure (openCubeSet Q)) := by
    rw [← SubdiffusiveProcess.centeredCube_eq_openCubeSet Q hr]
    exact (centeredCube_isBounded (cubeCenter Q) hr).isCompact_closure
  have hclosed : IsClosed (closure (openCubeSet Q)) := isClosed_closure
  have hcover : closure (openCubeSet Q) ⊆
      ⋃ x : closure (openCubeSet Q), Metric.ball (x : SpatialCoordinates d) 1 := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self one_pos⟩
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : closure (openCubeSet Q) => Metric.ball (x : SpatialCoordinates d) 1)
    (fun x => Metric.isOpen_ball) hcover
  intro M H omega mu Kmu hKmu hmu hconv hgrowth nu hnu
  rcases hnu with hnu | ⟨N, hnu⟩
  · subst nu
    have hfinite : mu.restrict (closure (openCubeSet Q)) Set.univ <
        (⊤ : ℝ≥0∞) := by
      rw [Measure.restrict_apply_univ]
      exact hmu
    have hsupp : (mu.restrict (closure (openCubeSet Q)))
        (closure (openCubeSet Q))ᶜ = 0 := by
      simp [Measure.restrict_apply' hclosed.measurableSet]
    have hgrowth' : ∀ x ∈ closure (openCubeSet Q), ∀ r : ℝ,
        0 < r → r ≤ 1 →
        (mu.restrict (closure (openCubeSet Q))) (Metric.ball x r) ≤
          ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) := by
      intro x hx r hr hr1
      exact (Measure.restrict_le_self (μ := mu)
        (s := closure (openCubeSet Q)) (Metric.ball x r)).trans
        (hgrowth x hx r hr hr1).1
    exact htrace (mu.restrict (closure (openCubeSet Q))) Kmu
      hfinite hsupp hKmu hgrowth'
  · subst nu
    have hfiniteCutoff :
        (cutoffSpeedMeasure M H omega N).restrict
          (closure (openCubeSet Q)) Set.univ < (⊤ : ℝ≥0∞) := by
      rw [Measure.restrict_apply_univ]
      have hmeasureUnion :
          cutoffSpeedMeasure M H omega N
            (⋃ x ∈ s, Metric.ball (x : SpatialCoordinates d) 1) <
            (⊤ : ℝ≥0∞) := by
        apply aux_speed_trace_completion_finite_union
        intro x hx
        exact lt_of_le_of_lt
          ((hgrowth (x : SpatialCoordinates d) x.property 1
            zero_lt_one le_rfl).2 N) ENNReal.ofReal_lt_top
      exact (measure_mono hs).trans_lt hmeasureUnion
    have hsupp :
        ((cutoffSpeedMeasure M H omega N).restrict
          (closure (openCubeSet Q))) (closure (openCubeSet Q))ᶜ = 0 := by
      simp [Measure.restrict_apply' hclosed.measurableSet]
    have hgrowth' : ∀ x ∈ closure (openCubeSet Q), ∀ r : ℝ,
        0 < r → r ≤ 1 →
        ((cutoffSpeedMeasure M H omega N).restrict
          (closure (openCubeSet Q))) (Metric.ball x r) ≤
          ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) := by
      intro x hx r hr hr1
      have hball :
          (cutoffSpeedMeasure M H omega N) (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)) :=
        (hgrowth x hx r hr hr1).2 N
      exact (Measure.restrict_le_self
        (μ := cutoffSpeedMeasure M H omega N)
        (s := closure (openCubeSet Q)) (Metric.ball x r)).trans
        hball
    exact htrace
      ((cutoffSpeedMeasure M H omega N).restrict
        (closure (openCubeSet Q))) Kmu
      hfiniteCutoff hsupp hKmu hgrowth'

end SubdiffusiveProcess.Paper
