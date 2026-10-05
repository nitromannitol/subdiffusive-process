module

public import SubdiffusiveProcess.Paper.tight_static
public import SubdiffusiveProcess.Paper.tight_static_estimates
public import SubdiffusiveProcess.Paper.tight_scale_covariance
public import SubdiffusiveProcess.Paper.tight_subharmonic
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_cutoff_fdd_start_continuity
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.MultiplicativeChaos.SpeedBasic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Path.ExitTime
public import MarkovProcess.Killed.Nested
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernelIntegral
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonFormOnH1Function
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.DomainMonotonicity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeWeakGenerator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerPointwise
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.MassiveTranslation

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonFormOnH1Function
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_tight_fast_exit_open_event_dense {α Ω : Type*} [TopologicalSpace α]
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω]
    (P : α → ProbabilityMeasure Ω) (hP : Continuous P) {S : Set α} (hS : Dense S)
    {G : Set Ω} (hG : IsOpen G) {b : ℝ≥0∞}
    (hb : ∀ z ∈ S, (P z : Measure Ω) G ≤ b) (x : α) :
    (P x : Measure Ω) G ≤ b := by
  have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (hS.closure_eq ▸ Set.mem_univ x)
  have hlim : Tendsto P (𝓝[S] x) (𝓝 (P x)) :=
    hP.continuousAt.mono_left nhdsWithin_le_nhds
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG).trans ?_
  exact liminf_le_of_frequently_le'
    (Eventually.frequently (eventually_nhdsWithin_of_forall hb))

variable {E : Type*} [NormedAddCommGroup E]

def aux_tight_fast_exit_gap (y : E) (R' T : ℝ) : Set (ContinuousPath E) :=
  {p | ∃ s : ℝ≥0, (s : ℝ) < T ∧ p s ∉ Metric.closedBall y R'}

theorem aux_tight_fast_exit_isOpen_gap (y : E) (R' T : ℝ) :
    IsOpen (aux_tight_fast_exit_gap y R' T) := by
  have hEq : aux_tight_fast_exit_gap y R' T = ⋃ s : {s : ℝ≥0 // (s : ℝ) < T},
      (fun p : ContinuousPath E ↦ p s) ⁻¹' (Metric.closedBall y R')ᶜ := by
    ext p
    simp [aux_tight_fast_exit_gap]
  rw [hEq]
  exact isOpen_iUnion fun s ↦ Metric.isClosed_closedBall.isOpen_compl.preimage
    (continuous_eval_const _)

theorem aux_tight_fast_exit_exit_subset_gap (y : E) {R R' t ε : ℝ}
    (hR' : R' < R) (hε : 0 < ε) (ht : 0 ≤ t) :
    {p : ContinuousPath E | ContinuousPath.exitTime (Metric.ball y R) p ≤ ENNReal.ofReal t} ⊆
      aux_tight_fast_exit_gap y R' (t + ε) := by
  intro p hp
  have h := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ Metric.isOpen_ball t.toNNReal p).1
    (by simpa [ENNReal.ofReal] using hp)
  obtain ⟨⟨s, hs⟩, hsU⟩ := h
  refine ⟨s, ?_, ?_⟩
  · have hs' : (s : ℝ) ≤ t := by
      have := (NNReal.coe_le_coe.2 hs)
      simpa [Real.coe_toNNReal _ ht] using this
    linarith
  · intro hmem
    apply hsU
    rw [Metric.mem_closedBall] at hmem
    exact Metric.mem_ball.2 (lt_of_le_of_lt hmem hR')

theorem aux_tight_fast_exit_gap_subset_exit (y : E) {R' T : ℝ} :
    aux_tight_fast_exit_gap y R' T ⊆
      {p : ContinuousPath E |
        ContinuousPath.exitTime (Metric.ball y R') p ≤ ENNReal.ofReal T} := by
  rintro p ⟨s, hsT, hs⟩
  refine (ContinuousPath.exitTime_le_of_notMem _ p s fun h ↦ hs
    (Metric.ball_subset_closedBall h)).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hsT.le

theorem aux_tight_fast_exit_exit_every_start {α : Type*} [TopologicalSpace α]
    [HasOuterApproxClosed (ContinuousPath E)]
    (P : α → ProbabilityMeasure (ContinuousPath E)) (hP : Continuous P)
    {S : Set α} (hS : Dense S) (y : E) {R R' : ℝ} (hR' : R' < R)
    (B : ℝ → ℝ≥0∞)
    (hB : ∀ z ∈ S, ∀ T : ℝ, 0 < T →
      (P z : Measure (ContinuousPath E))
        {p | ContinuousPath.exitTime (Metric.ball y R') p ≤ ENNReal.ofReal T} ≤ B T)
    (x : α) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    (P x : Measure (ContinuousPath E))
        {p | ContinuousPath.exitTime (Metric.ball y R) p ≤ ENNReal.ofReal t} ≤ B (t + ε) := by
  refine (measure_mono (aux_tight_fast_exit_exit_subset_gap y hR' hε ht)).trans ?_
  exact aux_tight_fast_exit_open_event_dense P hP hS
    (aux_tight_fast_exit_isOpen_gap y R' (t + ε))
      (fun z hz ↦ (measure_mono (aux_tight_fast_exit_gap_subset_exit y)).trans
      (hB z hz _ (by linarith))) x

theorem aux_tight_fast_exit_fdd_open_event_dense {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂((P x).map
          (ContinuousPath.finsetEvaluation I)).toMeasure))
    {S : Set (SpatialCoordinates d)} (hS : Dense S)
    (I : Finset ℝ≥0) {O : Set (I → SpatialCoordinates d)} (hO : IsOpen O)
    {b : ℝ≥0∞}
    (hb : ∀ z ∈ S,
      (P z : Measure (DiffusionPath d))
          (ContinuousPath.finsetEvaluation I ⁻¹' O) ≤ b)
    (x : SpatialCoordinates d) :
    (P x : Measure (DiffusionPath d))
        (ContinuousPath.finsetEvaluation I ⁻¹' O) ≤ b := by
  have hPI : Continuous (fun x =>
      (P x).map (ContinuousPath.finsetEvaluation I)) := by
    apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
    intro f
    exact hfd I f
  have hmap := aux_tight_fast_exit_open_event_dense
    (fun x => (P x).map (ContinuousPath.finsetEvaluation I))
      hPI hS hO
    (fun z hz => by
      change ((P z : Measure (DiffusionPath d)).map
        (ContinuousPath.finsetEvaluation I)) O ≤ b
      rw [Measure.map_apply_of_aemeasurable
        (ContinuousPath.measurable_finsetEvaluation I).aemeasurable
        hO.measurableSet]
      exact hb z hz) x
  change ((P x).map
      (ContinuousPath.finsetEvaluation I) :
        Measure (I → SpatialCoordinates d)) O ≤ b at hmap
  change ((P x : Measure (DiffusionPath d)).map
      (ContinuousPath.finsetEvaluation I)) O ≤ b at hmap
  rw [Measure.map_apply_of_aemeasurable
    (ContinuousPath.measurable_finsetEvaluation I).aemeasurable hO.measurableSet] at hmap
  exact hmap

theorem aux_tight_fast_exit_fdd_gap_dense {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂((P x).map
          (ContinuousPath.finsetEvaluation I)).toMeasure))
    {S : Set (SpatialCoordinates d)} (hS : Dense S)
    (y : SpatialCoordinates d) {R' T : ℝ} {b : ℝ≥0∞}
    (hB : ∀ z ∈ S,
      (P z : Measure (DiffusionPath d))
          {p | ContinuousPath.exitTime (Metric.ball y R') p ≤ ENNReal.ofReal T} ≤ b)
    (x : SpatialCoordinates d) :
    (P x : Measure (DiffusionPath d))
        (aux_tight_fast_exit_gap y R' T) ≤ b := by
  classical
  let J : Type := {s : ℝ≥0 // (s : ℝ) < T}
  let C : J → Set (DiffusionPath d) := fun s =>
    {p | p s.1 ∉ Metric.closedBall y R'}
  have hCopen : ∀ s : J, IsOpen (C s) := by
    intro s
    exact Metric.isClosed_closedBall.isOpen_compl.preimage
      (continuous_eval_const s.1)
  have hcover : aux_tight_fast_exit_gap y R' T ⊆ ⋃ s : J, C s := by
    intro p hp
    rcases hp with ⟨s, hsT, hs⟩
    exact Set.mem_iUnion.2 ⟨⟨s, hsT⟩, hs⟩
  by_contra hnot
  have hgt : b < (P x : Measure (DiffusionPath d))
      (aux_tight_fast_exit_gap y R' T) := lt_of_not_ge hnot
  obtain ⟨K, hKG, hKcompact, hKgt⟩ :=
    (aux_tight_fast_exit_isOpen_gap y R' T).exists_lt_isCompact hgt
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover C hCopen
    (hKG.trans hcover)
  let I : Finset ℝ≥0 := t.image (fun s : J => s.1)
  let O : Set (I → SpatialCoordinates d) :=
    {v | ∃ s : I, v s ∉ Metric.closedBall y R'}
  have hO : IsOpen O := by
    rw [show O = ⋃ s : I, {v : I → SpatialCoordinates d |
        v s ∉ Metric.closedBall y R'} by
      ext v
      simp [O]]
    exact isOpen_iUnion fun s : I => by
      change IsOpen ((fun v : I → SpatialCoordinates d => v s) ⁻¹'
        (Metric.closedBall y R')ᶜ)
      exact Metric.isClosed_closedBall.isOpen_compl.preimage (continuous_apply s)
  have hKI : K ⊆ ContinuousPath.finsetEvaluation I ⁻¹' O := by
    intro p hp
    rcases Set.mem_iUnion.1 (ht hp) with ⟨s, hs⟩
    rcases Set.mem_iUnion.1 hs with ⟨hst, hpC⟩
    have hi : s ∈ t := hst
    have himage : s.1 ∈ I := Finset.mem_image.2 ⟨s, hi, rfl⟩
    let i : I := ⟨s.1, himage⟩
    refine ⟨i, ?_⟩
    simpa [O, C, i, ContinuousPath.finsetEvaluation] using! hpC
  have hIH : ContinuousPath.finsetEvaluation I ⁻¹' O ⊆
      aux_tight_fast_exit_gap y R' T := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    rcases Finset.mem_image.1 i.2 with ⟨s, hst, his⟩
    refine ⟨s.1, s.2, ?_⟩
    simpa [O, C, his, ContinuousPath.finsetEvaluation] using! hi
  have hHbound : (P x : Measure (DiffusionPath d))
      (ContinuousPath.finsetEvaluation I ⁻¹' O) ≤ b := by
    apply aux_tight_fast_exit_fdd_open_event_dense P hfd hS I hO
    intro z hz
    exact (measure_mono hIH).trans
      ((measure_mono (aux_tight_fast_exit_gap_subset_exit y)).trans (hB z hz))
  exact (not_lt_of_ge ((measure_mono hKI).trans hHbound)) hKgt

theorem aux_tight_fast_exit_open_event_dense_local
    {α Ω : Type*} [TopologicalSpace α] [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω]
    (P : α → ProbabilityMeasure Ω) (hP : Continuous P)
    {S U : Set α} (hS : Dense S) (hU : IsOpen U)
    {G : Set Ω} (hG : IsOpen G) {b : ℝ≥0∞}
    (hb : ∀ z ∈ S, z ∈ U → (P z : Measure Ω) G ≤ b)
    (x : α) (hx : x ∈ U) :
    (P x : Measure Ω) G ≤ b := by
  have : (𝓝[S ∩ U] x).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [mem_closure_iff]
      intro V hV hxV
      rcases hS.inter_open_nonempty (V ∩ U) (hV.inter hU)
          ⟨x, ⟨hxV, hx⟩⟩ with ⟨z, ⟨hzV, hzU⟩, hzS⟩
      exact ⟨z, hzV, hzS, hzU⟩)
  have hlim : Tendsto P (𝓝[S ∩ U] x) (𝓝 (P x)) :=
    hP.continuousAt.mono_left nhdsWithin_le_nhds
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG).trans ?_
  exact liminf_le_of_frequently_le'
    (Eventually.frequently (eventually_nhdsWithin_of_forall
      (fun z hz => hb z hz.1 hz.2)))

theorem aux_tight_fast_exit_fdd_open_event_dense_local {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂((P x).map
          (ContinuousPath.finsetEvaluation I)).toMeasure))
    {S U : Set (SpatialCoordinates d)}
    (hS : Dense S)
    (hU : IsOpen U) (I : Finset ℝ≥0) {O : Set (I → SpatialCoordinates d)}
    (hO : IsOpen O) {b : ℝ≥0∞}
    (hb : ∀ z ∈ S, z ∈ U →
      (P z : Measure (DiffusionPath d))
        (ContinuousPath.finsetEvaluation I ⁻¹' O) ≤ b)
    (x : SpatialCoordinates d) (hx : x ∈ U) :
    (P x : Measure (DiffusionPath d))
        (ContinuousPath.finsetEvaluation I ⁻¹' O) ≤ b := by
  have hPI : Continuous (fun x =>
      (P x).map (ContinuousPath.finsetEvaluation I)) := by
    apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
    intro f
    exact hfd I f
  have hmap := aux_tight_fast_exit_open_event_dense_local
    (fun x => (P x).map (ContinuousPath.finsetEvaluation I))
      hPI hS hU hO
    (fun z hz hzu => by
      change ((P z : Measure (DiffusionPath d)).map
        (ContinuousPath.finsetEvaluation I)) O ≤ b
      rw [Measure.map_apply_of_aemeasurable
        (ContinuousPath.measurable_finsetEvaluation I).aemeasurable
        hO.measurableSet]
      exact hb z hz hzu) x hx
  change ((P x : Measure (DiffusionPath d)).map
      (ContinuousPath.finsetEvaluation I)) O ≤ b at hmap
  rw [Measure.map_apply_of_aemeasurable
    (ContinuousPath.measurable_finsetEvaluation I).aemeasurable hO.measurableSet] at hmap
  exact hmap

theorem aux_tight_fast_exit_fdd_gap_dense_local {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂((P x).map
          (ContinuousPath.finsetEvaluation I)).toMeasure))
    {S U : Set (SpatialCoordinates d)}
    (hS : Dense S) (hU : IsOpen U)
    (y : SpatialCoordinates d) {R' T : ℝ} {b : ℝ≥0∞}
    (hB : ∀ z ∈ S, z ∈ U →
      (P z : Measure (DiffusionPath d))
        {p | ContinuousPath.exitTime (Metric.ball y R') p ≤ ENNReal.ofReal T} ≤ b)
    (x : SpatialCoordinates d) (hx : x ∈ U) :
    (P x : Measure (DiffusionPath d))
        (aux_tight_fast_exit_gap y R' T) ≤ b := by
  classical
  let J : Type := {s : ℝ≥0 // (s : ℝ) < T}
  let C : J → Set (DiffusionPath d) := fun s =>
    {p | p s.1 ∉ Metric.closedBall y R'}
  have hCopen : ∀ s : J, IsOpen (C s) := by
    intro s
    exact Metric.isClosed_closedBall.isOpen_compl.preimage
      (continuous_eval_const s.1)
  have hcover : aux_tight_fast_exit_gap y R' T ⊆ ⋃ s : J, C s := by
    intro p hp
    rcases hp with ⟨s, hsT, hs⟩
    exact Set.mem_iUnion.2 ⟨⟨s, hsT⟩, hs⟩
  by_contra hnot
  have hgt : b < (P x : Measure (DiffusionPath d))
      (aux_tight_fast_exit_gap y R' T) := lt_of_not_ge hnot
  obtain ⟨K, hKG, hKcompact, hKgt⟩ :=
    (aux_tight_fast_exit_isOpen_gap y R' T).exists_lt_isCompact hgt
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover C hCopen
    (hKG.trans hcover)
  let I : Finset ℝ≥0 := t.image (fun s : J => s.1)
  let O : Set (I → SpatialCoordinates d) :=
    {v | ∃ s : I, v s ∉ Metric.closedBall y R'}
  have hO : IsOpen O := by
    rw [show O = ⋃ s : I, {v : I → SpatialCoordinates d |
        v s ∉ Metric.closedBall y R'} by
      ext v
      simp [O]]
    exact isOpen_iUnion fun s : I => by
      change IsOpen ((fun v : I → SpatialCoordinates d => v s) ⁻¹'
        (Metric.closedBall y R')ᶜ)
      exact Metric.isClosed_closedBall.isOpen_compl.preimage (continuous_apply s)
  have hKI : K ⊆ ContinuousPath.finsetEvaluation I ⁻¹' O := by
    intro p hp
    rcases Set.mem_iUnion.1 (ht hp) with ⟨s, hs⟩
    rcases Set.mem_iUnion.1 hs with ⟨hst, hpC⟩
    have hi : s ∈ t := hst
    have himage : s.1 ∈ I := Finset.mem_image.2 ⟨s, hi, rfl⟩
    let i : I := ⟨s.1, himage⟩
    refine ⟨i, ?_⟩
    simpa [O, C, i, ContinuousPath.finsetEvaluation] using! hpC
  have hIH : ContinuousPath.finsetEvaluation I ⁻¹' O ⊆
      aux_tight_fast_exit_gap y R' T := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    rcases Finset.mem_image.1 i.2 with ⟨s, hst, his⟩
    refine ⟨s.1, s.2, ?_⟩
    simpa [O, C, his, ContinuousPath.finsetEvaluation] using! hi
  have hHbound : (P x : Measure (DiffusionPath d))
      (ContinuousPath.finsetEvaluation I ⁻¹' O) ≤ b := by
    apply aux_tight_fast_exit_fdd_open_event_dense_local P hfd hS hU I hO
    intro z hz hzu
    exact (measure_mono hIH).trans
      ((measure_mono (aux_tight_fast_exit_gap_subset_exit y)).trans
        (hB z hz hzu))
    exact hx
  exact (not_lt_of_ge ((measure_mono hKI).trans hHbound)) hKgt

theorem aux_tight_fast_exit_weighted_lintegral {d : ℕ}
    {U : Set (Homogenization.Vec d)} (hU : MeasurableSet U)
    {b g : Homogenization.Vec d → ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict U))
    (hg : AEStronglyMeasurable g (volume.restrict U))
    (hb0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ b x)
    (hg0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ g x)
    (hi : Integrable (fun x => b x * g x) (volume.restrict U)) :
    (∫⁻ x in U, ENNReal.ofReal (g x * b x) ∂volume) =
      ENNReal.ofReal (∫ x in U, b x * g x ∂volume) := by
  have h := weighted_lintegral_ofReal_eq hU hb hg hb0 hg0 hi
  unfold weightedMeasure at h
  rw [restrict_withDensity hU,
    lintegral_withDensity_eq_lintegral_mul₀ hb.aemeasurable.ennreal_ofReal
      hg.aemeasurable.ennreal_ofReal] at h
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [hb0] with x hx
  change ENNReal.ofReal (g x * b x) =
    ENNReal.ofReal (b x) * ENNReal.ofReal (g x)
  rw [mul_comm, ENNReal.ofReal_mul hx]

theorem aux_tight_fast_exit_resolvent_bounds {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (f : Homogenization.Vec d → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : Homogenization.Vec d) :
    0 ≤ killedResolvent law U s f x ∧ killedResolvent law U s f x ≤ 1 := by
  let R := resolventKernel law U hU s hs
  let : IsSubMarkovKernel R := resolventKernel_subMarkov law U hU s hs
  let : IsFiniteKernel R := (resolventKernel_subMarkov law U hU s hs).isFiniteKernel
  have hfi : Integrable f (R x) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
        exact hf1 z)
  rw [← resolventKernel_integral_eq_of_integrable law U hU s hs f x hfi]
  change 0 ≤ (∫ z, f z ∂(R x)) ∧ (∫ z, f z ∂(R x)) ≤ 1
  refine ⟨integral_nonneg hf0, ?_⟩
  calc
    (∫ z, f z ∂(R x)) ≤ ∫ _z, (1 : ℝ) ∂(R x) :=
      integral_mono hfi (integrable_const 1) hf1
    _ = (R x Set.univ).toReal := by
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
    _ ≤ 1 := by
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
        ((resolventKernel_subMarkov law U hU s hs).measure_le_one x Set.univ)

theorem aux_tight_fast_exit_weak_resolvent {d : ℕ}
    {c rho : Homogenization.Vec d → ℝ} {law : Kernel (Homogenization.Vec d) (Path d)}
    [IsMarkovKernel law] (hD : LocalDiffusion c rho law) (U : Set (Homogenization.Vec d))
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s)
    (f : Homogenization.Vec d → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hf2 : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    ∃ u : H10Function U,
      u.toFun =ᵐ[(weightedMeasure rho).restrict U] killedResolvent law U s f ∧
      IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function (fun x => s⁻¹ * f x) ∧
      ∀ᵐ x ∂(weightedMeasure rho).restrict U, 0 ≤ u.toFun x ∧ u.toFun x ≤ 1 := by
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs f hf2
  refine ⟨u, hueq, hu, ?_⟩
  filter_upwards [hueq] with x hx
  rw [hx]
  exact aux_tight_fast_exit_resolvent_bounds law U hU s hs f hf hf0 hf1 x

theorem aux_tight_fast_exit_variational_algebra {r s eu euv ev : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ eu)
    (hdiff : 0 ≤ eu - 2 * euv + ev)
    (heq : r + s * (eu - euv) = 0) : r ≤ s * ev := by
  have h1 := mul_nonneg hs hdiff
  have h2 := mul_nonneg hs hu
  nlinarith only [hr, heq, h1, h2]

theorem aux_tight_fast_exit_variational_comparison {d : ℕ}
    {U : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d)}
    {c rho : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ} {lam Lam rhoMax s : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (hc : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x)
    (hrho : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict U))
    (hrhoBdd : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhoMax)
    (hs : 0 < s) (u eta : H10Function U)
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function
      (fun x => s⁻¹ * eta.toFun x)) :
    (∫ x in U, rho x * (u.toFun x - eta.toFun x) ^ 2) ≤
      s * energy c U eta.toH1Function := by
  let v := u.toH1Function
  let e := eta.toH1Function
  let r := ∫ x in U, rho x * (u.toFun x - eta.toFun x) ^ 2
  have hfun : (u - eta).toH1Function.toFun = fun x => u.toFun x - eta.toFun x := by
    change (u.toH1Function - eta.toH1Function).toFun = _
    exact H1Function.sub_toFun _ _
  have htest := resolvent_form_identity hEll hs hu (u - eta)
  have hi1 := integrableOn_mass_term hrhoMeas hrhoBdd
    u.toH1Function.memL2 (u - eta).toH1Function.memL2
  have hi2 := integrableOn_mass_term hrhoMeas hrhoBdd
    eta.toH1Function.memL2 (u - eta).toH1Function.memL2
  have hmass :
      (∫ x in U, rho x * u.toFun x * (u - eta).toH1Function.toFun x) -
        (∫ x in U, rho x * eta.toFun x * (u - eta).toH1Function.toFun x) = r := by
    rw [← integral_sub hi1 hi2]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    rw [hfun]
    ring
  have hgrad : (u - eta).toH1Function = v - e := rfl
  have htest' : r + s * (dirichletBilin hEll v v - dirichletBilin hEll v e) = 0 := by
    rw [hgrad, map_sub] at htest
    rw [H1Function.sub_toFun] at htest
    rw [hfun] at hmass
    dsimp only [v, e] at *
    linarith only [htest, hmass]
  have hr : 0 ≤ r := by
    apply integral_nonneg_of_ae
    filter_upwards [hrho] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hpos : ∀ w : H1Function U, 0 ≤ dirichletBilin hEll w w := by
    intro w
    rw [dirichletBilin_apply]
    apply integral_nonneg_of_ae
    filter_upwards [hc] with x hx
    exact mul_nonneg hx
      (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp.vecDot_self_nonneg _)
  have hdiff := hpos (v - e)
  simp only [map_sub, LinearMap.sub_apply] at hdiff
  rw [dirichletBilin_symm hEll e v] at hdiff
  have hdiff' : 0 ≤ dirichletBilin hEll v v - 2 * dirichletBilin hEll v e +
      dirichletBilin hEll e e := by linarith only [hdiff]
  have hbound := aux_tight_fast_exit_variational_algebra hr hs.le (hpos v) hdiff' htest'
  simpa only [dirichletBilin_self] using hbound

theorem aux_tight_fast_exit_moment_transfer {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {K0 : Ω → ℝ} {a p q C : ℝ}
    (hK0meas : Measurable K0) (hK0one : ∀ omega, 1 ≤ K0 omega)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hpq : p ≤ q)
    (hK0moment : ∫⁻ omega, ENNReal.ofReal (K0 omega ^ q) ∂μ ≤ ENNReal.ofReal C) :
    ∫⁻ omega, ENNReal.ofReal (a * K0 omega ^ p) ∂μ ≤ ENNReal.ofReal (a * C) := by
  have hpow : ∀ omega, K0 omega ^ p ≤ K0 omega ^ q := by
    intro omega
    exact Real.rpow_le_rpow_of_exponent_le (hK0one omega) hpq
  have hq : 0 ≤ q := hp.trans hpq
  have hmeas : Measurable (fun omega => ENNReal.ofReal (K0 omega ^ q)) := by
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hq).measurable.comp hK0meas)
  calc
    ∫⁻ omega, ENNReal.ofReal (a * K0 omega ^ p) ∂μ ≤
        ∫⁻ omega, ENNReal.ofReal (a * K0 omega ^ q) ∂μ := by
      apply lintegral_mono
      intro omega
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hpow omega) ha)
    _ = ENNReal.ofReal a * (∫⁻ omega, ENNReal.ofReal (K0 omega ^ q) ∂μ) := by
      rw [← lintegral_const_mul _ hmeas]
      apply lintegral_congr
      intro omega
      rw [ENNReal.ofReal_mul ha]
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal C :=
      mul_le_mul_right hK0moment _
    _ = ENNReal.ofReal (a * C) := by rw [ENNReal.ofReal_mul ha]

theorem aux_tight_fast_exit_probability_le_resolvent_defect {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (t : ℝ) (ht : 0 < t)
    (eta : Homogenization.Vec d → ℝ) (heta : Measurable eta)
    (heta0 : ∀ x, 0 ≤ eta x) (heta1 : ∀ x, eta x ≤ 1)
    (x : Homogenization.Vec d) :
    law x {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (4 * (1 - killedResolvent law U t eta x)) := by
  let := exponential_probability t ht
  let P : Measure (ℝ × Path d) := (expMeasure t⁻¹).prod (law x)
  let S : Set (ℝ × Path d) := {q | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2}
  let E : Set (Path d) := {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t}
  let R := resolventKernel law U hU t ht
  let : IsSubMarkovKernel R := resolventKernel_subMarkov law U hU t ht
  let : IsFiniteKernel R := (resolventKernel_subMarkov law U hU t ht).isFiniteKernel
  have hS : MeasurableSet S := survival_measurable U hU
  have hRmass : R x Set.univ = P S := by
    dsimp only [R, resolventKernel]
    rw [Kernel.map_apply' _ joint_position x MeasurableSet.univ,
      Set.preimage_univ, Kernel.restrict_apply' _ _ x MeasurableSet.univ,
      Set.univ_inter, Kernel.prod_apply, Kernel.const_apply]
  have hetaInt : Integrable eta (R x) :=
    Integrable.of_bound heta.aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (heta0 z)]
        exact heta1 z)
  have hres : killedResolvent law U t eta x ≤ (P S).toReal := by
    rw [← resolventKernel_integral_eq_of_integrable law U hU t ht eta x hetaInt]
    change (∫ z, eta z ∂(R x)) ≤ _
    calc
      (∫ z, eta z ∂(R x)) ≤ ∫ _z, (1 : ℝ) ∂(R x) :=
        integral_mono hetaInt (integrable_const 1) heta1
      _ = (R x Set.univ).toReal := by
        simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
      _ = (P S).toReal := congrArg ENNReal.toReal hRmass
  have hsub : Set.Ioi t ×ˢ E ⊆ Sᶜ := by
    rintro ⟨v, w⟩ ⟨hv, hw⟩
    exact not_lt_of_ge (hw.trans (ENNReal.ofReal_le_ofReal hv.le))
  have hmono : (1 / 4 : ℝ) * (law x E).toReal ≤ (P Sᶜ).toReal := by
    calc
      (1 / 4 : ℝ) * (law x E).toReal ≤
          ((expMeasure t⁻¹) (Set.Ioi t)).toReal * (law x E).toReal :=
        mul_le_mul_of_nonneg_right (expMeasure_Ioi_toReal_ge ht) ENNReal.toReal_nonneg
      _ = (P (Set.Ioi t ×ˢ E)).toReal := by
        rw [show P (Set.Ioi t ×ˢ E) =
          (expMeasure t⁻¹) (Set.Ioi t) * law x E from Measure.prod_prod _ _,
          ENNReal.toReal_mul]
      _ ≤ (P Sᶜ).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hsum : (P S).toReal + (P Sᶜ).toReal = 1 := by
    exact probReal_add_probReal_compl hS
  have hbound : (law x E).toReal ≤ 4 * (1 - killedResolvent law U t eta x) := by
    linarith only [hmono, hres, hsum]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (law x) E)]
  exact ENNReal.ofReal_le_ofReal hbound

theorem aux_tight_fast_exit_complement_subsolution {d : ℕ}
    {U : Set (Homogenization.Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {c rho : Homogenization.Vec d → ℝ} {rhoMax mu : ℝ}
    (hmu : 0 ≤ mu)
    (hrho : ∀ᵐ x ∂volume.restrict U, 0 ≤ rho x)
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict U))
    (hrhoBdd : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ rhoMax)
    (u : H1Function U)
    (hu : IsMassiveWeakSolutionOn c rho mu U u (fun _ => mu))
    (hu1 : ∀ᵐ x ∂volume.restrict U, u.toFun x ≤ 1) :
    IsWeakSubSolutionOn c U (H1Function.const 1 - u) := by
  intro psi hpsi
  have hi1 := integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 psi.toH1Function.memL2
  have hi2 := integrableOn_mass_term hrhoMeas hrhoBdd
    (H1Function.const (U := U) 1).memL2 psi.toH1Function.memL2
  have hmass : (∫ x in U, rho x * u.toFun x * psi.toH1Function.toFun x) ≤
      ∫ x in U, rho x * 1 * psi.toH1Function.toFun x := by
    apply integral_mono_ae hi1 hi2
    filter_upwards [hrho, hu1] with x hx hx1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx1 hx) (hpsi x)
  have htest := hu psi
  have hrhs : (∫ x in U, rho x * mu * psi.toH1Function.toFun x) =
      mu * ∫ x in U, rho x * 1 * psi.toH1Function.toFun x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hrhs] at htest
  have henergy : 0 ≤ ∫ x in U,
      vecDot (c x • u.grad x) (psi.toH1Function.grad x) := by
    have h := mul_le_mul_of_nonneg_left hmass hmu
    linarith only [htest, h]
  have hgrad : (H1Function.const (U := U) 1 - u).grad = fun x => -u.grad x := by
    rw [H1Function.sub_grad]
    funext x
    change (0 : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) - u.grad x = -u.grad x
    exact zero_sub _
  rw [hgrad]
  have heq : (∫ x in U,
      vecDot (c x • -u.grad x) (psi.toH1Function.grad x)) =
      -(∫ x in U, vecDot (c x • u.grad x) (psi.toH1Function.grad x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    simp only [smul_neg, vecDot_neg_left]
  rw [heq]
  exact neg_nonpos.mpr henergy

theorem aux_tight_fast_exit_of_resolvent_bound {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (t : ℝ) (ht : 0 < t)
    (eta : Homogenization.Vec d → ℝ) (heta : Measurable eta)
    (heta0 : ∀ x, 0 ≤ eta x) (heta1 : ∀ x, eta x ≤ 1)
    (x : Homogenization.Vec d) (K F : ℝ)
    (hmoser : 1 - killedResolvent law U t eta x ≤ K * Real.sqrt (t / F)) :
    law x {w | LifetimePath.exitTime U w ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal ((4 * K) * Real.sqrt (t / F)) := by
  refine (aux_tight_fast_exit_probability_le_resolvent_defect law U hU t ht eta heta
    heta0 heta1 x).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    4 * (1 - killedResolvent law U t eta x) ≤ 4 * (K * Real.sqrt (t / F)) :=
      mul_le_mul_of_nonneg_left hmoser (by norm_num)
    _ = (4 * K) * Real.sqrt (t / F) := (mul_assoc _ _ _).symm

theorem aux_tight_fast_exit_map_exit_event {d : ℕ}
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) {μ : Measure (DiffusionPath d)}
    {ν : Measure (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d)}
    (hμν : Measure.map MarkovProcess.LifetimePath.ofContinuousPath μ = ν) (t : ℝ) :
    μ {path : DiffusionPath d |
        ContinuousPath.exitTime U path ≤ ENNReal.ofReal t} =
      ν {path : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d |
        MarkovProcess.LifetimePath.exitTime U path ≤ ENNReal.ofReal t} := by
  have hmeas : MeasurableSet {path : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d |
      MarkovProcess.LifetimePath.exitTime U path ≤ ENNReal.ofReal t} := by
    exact measurableSet_le (MarkovProcess.LifetimePath.measurable_exitTime U hU)
      measurable_const
  rw [← hμν, Measure.map_apply MarkovProcess.LifetimePath.measurable_ofContinuousPath hmeas]
  congr 1
  ext path
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    MarkovProcess.LifetimePath.exitTime_ofContinuousPath]

theorem aux_tight_fast_exit_process_passage {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : IsMarkovKernel KN)
    (L : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hLMarkov : IsMarkovKernel L)
    (omega : BilateralField d) (y : SpatialCoordinates d)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    {R R' tA t0 F Kres : ℝ} (hR' : R' < R) (htA : 0 < tA)
    (ht0 : 0 < t0) (_hF : 0 < F) (hT : tA = t0 + t0)
    (hUeq : U = Metric.ball y R')
    (hL : ∀ z, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
        (KN (omega, z)) = L z)
    (eta : SpatialCoordinates d → ℝ) (heta : Measurable eta)
    (heta0 : ∀ z, 0 ≤ eta z) (heta1 : ∀ z, eta z ≤ 1)
    (hres : ∀ᵐ z ∂volume.restrict (Metric.ball y R'),
      1 - killedResolvent L U tA eta z ≤ Kres * Real.sqrt (tA / F))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂(KN.map
          (ContinuousPath.finsetEvaluation I) (omega, x))))
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball y R') :
    (KN (omega, x))
        {path : DiffusionPath d |
          ContinuousPath.exitTime (Metric.ball y R) path ≤ ENNReal.ofReal t0} ≤
      ENNReal.ofReal ((4 * Kres) * Real.sqrt (tA / F)) := by
  let P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d) :=
    fun z => jointPathProbabilityMeasure KN hKN omega z
  have hfdP : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂((P x).map
          (ContinuousPath.finsetEvaluation I)).toMeasure) := by
    intro I f
    have h := hfd I f
    simpa only [P, jointPathProbabilityMeasure,
      ProbabilityMeasure.toMeasure_map,
      Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] using! h
  let b : ℝ≥0∞ := ENNReal.ofReal ((4 * Kres) * Real.sqrt (tA / F))
  have hExitAE : ∀ᵐ z ∂volume.restrict (Metric.ball y R'),
      (L z) {w | MarkovProcess.LifetimePath.exitTime U w ≤ ENNReal.ofReal tA} ≤ b := by
    let : IsMarkovKernel L := hLMarkov
    filter_upwards [hres] with z hz
    exact aux_tight_fast_exit_of_resolvent_bound L U hU tA htA eta heta
      heta0 heta1 z Kres F hz
  have hExitKNAE : ∀ᵐ z ∂volume.restrict (Metric.ball y R'),
      (P z : Measure (DiffusionPath d))
        {path | ContinuousPath.exitTime (Metric.ball y R') path ≤ ENNReal.ofReal tA} ≤ b := by
    filter_upwards [hExitAE] with z hz
    have hm := aux_tight_fast_exit_map_exit_event hU (hL z) tA
    have hPz : (P z : Measure (DiffusionPath d)) = KN (omega, z) := by
      rfl
    rw [hPz]
    rw [← hUeq]
    change (KN (omega, z))
        {path : DiffusionPath d |
          ContinuousPath.exitTime U path ≤ ENNReal.ofReal tA} ≤ b
    rw [hm]
    simpa [hUeq] using hz
  let S : Set (SpatialCoordinates d) :=
    {z | z ∉ Metric.ball y R' ∨
      (P z : Measure (DiffusionPath d))
        {path | ContinuousPath.exitTime (Metric.ball y R') path ≤ ENNReal.ofReal tA} ≤ b}
  have hSae : ∀ᵐ z ∂volume, z ∈ S := by
    apply ae_of_ae_restrict_of_ae_restrict_compl (Metric.ball y R')
    · filter_upwards [hExitKNAE, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzmem
      exact Set.mem_ofPred_eq.mpr (Or.inr hz)
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with z hz
      exact Set.mem_ofPred_eq.mpr (Or.inl hz)
  have hSdense : Dense S := Measure.dense_of_ae hSae
  have hgap := aux_tight_fast_exit_fdd_gap_dense_local
    P hfdP hSdense Metric.isOpen_ball y
    (fun z hz hzmem => by
      change z ∉ Metric.ball y R' ∨
        (P z : Measure (DiffusionPath d))
          {path | ContinuousPath.exitTime (Metric.ball y R') path ≤ ENNReal.ofReal tA} ≤ b at hz
      rcases hz with hz | hz
      · exact False.elim (hz hzmem)
      · exact hz) x hx
  have hsub := aux_tight_fast_exit_exit_subset_gap y hR' ht0 ht0.le
  have hgap' : (P x : Measure (DiffusionPath d))
      (aux_tight_fast_exit_gap y R' (t0 + t0)) ≤ b := by
    simpa [hT] using hgap
  have hbound : (P x : Measure (DiffusionPath d))
      {path | ContinuousPath.exitTime (Metric.ball y R) path ≤ ENNReal.ofReal t0} ≤ b :=
    (measure_mono hsub).trans hgap'
  change (KN (omega, x))
      {path : DiffusionPath d |
        ContinuousPath.exitTime (Metric.ball y R) path ≤ ENNReal.ofReal t0} ≤ b at hbound
  simpa [b] using hbound

theorem aux_tight_fast_exit_h10_dilate {d : ℕ}
    {U : Set (Homogenization.Vec d)} {a : ℝ} (ha : 0 < a)
    (u : Homogenization.H10Function U) :
    ∃ v : Homogenization.H10Function (a • U),
      (∀ x, v.toFun x = u.toFun (a⁻¹ • x)) ∧
      (∀ x, v.grad x = a⁻¹ • u.grad (a⁻¹ • x)) := by
  let T : Homogenization.Vec d → Homogenization.Vec d := fun x => a⁻¹ • x
  let V : Set (Homogenization.Vec d) := a • U
  have ha0 : a ≠ 0 := ha.ne'
  have hpre : a⁻¹ • V = U := by
    ext x
    simp [V, ha0]
  have hmap := Homogenization.map_smul_volume_restrict
    (d := d) (a := a⁻¹) (inv_pos.mpr ha) V
  have hTmeas : AEMeasurable T (volume.restrict V) :=
    (measurable_const_smul a⁻¹).aemeasurable
  let v : Homogenization.H10Function V :=
    { toH1Function := a⁻¹ • u.toH1Function.dilate ha
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        simpa only [T, Function.comp_apply] using! (u.approx_smooth m).comp (contDiff_const_smul a⁻¹)
      approx_hasCompactSupport := by
        intro m
        show HasCompactSupport (u.approx m ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha0))
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph
            (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha0))
      approx_support_subset := by
        intro m x hx
        have hx' : a⁻¹ • x ∈ tsupport (u.approx m) := by
          rw [show (fun y => u.approx m (T y)) =
            u.approx m ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha0) by rfl,
            tsupport_comp_eq_preimage (u.approx m)
              (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha0))] at hx
          exact hx
        exact (Set.mem_smul_set_iff_inv_smul_mem₀ ha0 (A := U) (a := a) (x := x)).2
          (u.approx_support_subset m hx')
      tendsto_approx := by
        let C : ℝ≥0∞ :=
          ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)
        have hEq :
            (fun m =>
              eLpNorm
                (fun x => u.approx m (T x) -
                  (a⁻¹ • u.toH1Function.dilate ha).toFun x)
                2 (volume.restrict V)) =
              fun m => C * eLpNorm
                (fun x => u.approx m x - u.toH1Function.toFun x)
                2 (volume.restrict U) := by
          funext n
          let g : Homogenization.Vec d → ℝ :=
            fun x => u.approx n x - u.toH1Function.toFun x
          have hg_map : AEStronglyMeasurable g
              (Measure.map T (volume.restrict V)) := by
            rw [hpre] at hmap
            rw [hmap]
            exact ((u.approx_smooth n).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable).mono_ac
                Measure.smul_absolutelyContinuous
          have hmap_eLp : eLpNorm g 2 (Measure.map T (volume.restrict V)) =
              eLpNorm (fun x => g (T x)) 2 (volume.restrict V) := by
            exact MeasureTheory.eLpNorm_map_measure
              (g := g) (f := T) hg_map hTmeas
          have hfun :
              (fun x => u.approx n (T x) -
                (a⁻¹ • u.toH1Function.dilate ha).toFun x) =
                fun x => g (T x) := by
            funext x
            simp [g, T, Homogenization.H1Function.dilate_toFun, ha0]
          rw [hfun, ← hmap_eLp]
          have hmap' := hmap
          rw [hpre] at hmap'
          rw [hmap']
          rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
          · rfl
          · positivity
        rw [hEq]
        have hC_ne_top : C ≠ ⊤ := by simp [C]
        simpa using ENNReal.Tendsto.const_mul u.tendsto_approx (Or.inr hC_ne_top)
      tendsto_approx_grad := by
        intro i
        let C : ℝ≥0∞ :=
          ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)
        have hEq :
            (fun m =>
              eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec i) -
                    (a⁻¹ • u.toH1Function.dilate ha).grad x i)
                2 (volume.restrict V)) =
              fun m => (ENNReal.ofReal a⁻¹ * C) * eLpNorm
                (fun x =>
                  (fderiv ℝ (u.approx m) x) (basisVec i) -
                    u.toH1Function.grad x i)
                2 (volume.restrict U) := by
          funext m
          let g : Homogenization.Vec d → ℝ :=
            fun x => (fderiv ℝ (u.approx m) x) (basisVec i) -
              u.toH1Function.grad x i
          have hg_map : AEStronglyMeasurable g
              (Measure.map T (volume.restrict V)) := by
            have hmap' := hmap
            rw [hpre] at hmap'
            rw [hmap']
            exact (((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.aestronglyMeasurable.sub
                (u.toH1Function.gradMemL2 i).aestronglyMeasurable).mono_ac
                  Measure.smul_absolutelyContinuous
          have hmap_eLp : eLpNorm g 2 (Measure.map T (volume.restrict V)) =
              eLpNorm (fun x => g (T x)) 2 (volume.restrict V) := by
            exact MeasureTheory.eLpNorm_map_measure
              (g := g) (f := T) hg_map hTmeas
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec i) -
                  (a⁻¹ • u.toH1Function.dilate ha).grad x i) =
                fun x => a⁻¹ * g (T x) := by
            funext x
            have hderiv :
                fderiv ℝ (fun y : Homogenization.Vec d =>
                    u.approx m (a⁻¹ • y)) x =
                  a⁻¹ • fderiv ℝ (u.approx m) (a⁻¹ • x) := by
              simpa [T] using
                (fderiv_comp_smul (𝕜 := ℝ) (f := u.approx m)
                  (x := x) a⁻¹)
            simp [g, T, hderiv, Homogenization.H1Function.dilate_grad,
              Pi.smul_apply, smul_eq_mul]
            ring
          rw [hfun]
          change eLpNorm (a⁻¹ • fun x => g (T x)) 2 (volume.restrict V) =
            ENNReal.ofReal a⁻¹ * C * eLpNorm g 2 (volume.restrict U)
          rw [MeasureTheory.eLpNorm_const_smul]
          rw [Real.enorm_eq_ofReal (inv_nonneg.mpr ha.le)]
          rw [← hmap_eLp]
          have hmap' := hmap
          rw [hpre] at hmap'
          rw [hmap']
          rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
          · simp [C, smul_eq_mul, mul_assoc]
          · positivity
        rw [hEq]
        have hconst_ne_top : ENNReal.ofReal a⁻¹ * C ≠ ⊤ := by
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [C])
        simpa using
          ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i)
            (Or.inr hconst_ne_top) }
  refine ⟨v, ?_, ?_⟩
  · intro x
    simp [v, Homogenization.H1Function.dilate_toFun, ha0]
  · intro x
    simp [v, Homogenization.H1Function.dilate_grad]

theorem aux_tight_fast_exit_massive_dilate {d : ℕ}
    {U V : Set (Homogenization.Vec d)} {a mu : ℝ}
    (ha : 0 < a) (hV : V = a • U)
    {c rho f : Homogenization.Vec d → ℝ} (u : Homogenization.H1Function V)
    (hu : IsMassiveWeakSolutionOn c rho mu V u f) :
    IsMassiveWeakSolutionOn
      (fun x => c (a • x)) (fun x => rho (a • x)) (mu * a ^ 2) U
      (a • u.undilateSet ha hV) (fun x => a ^ 2 * f (a • x)) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hUV : a⁻¹ • V = U := by
    rw [hV]
    simp [ha0]
  subst U
  intro phi
  let psi : Homogenization.H10Function V :=
    Homogenization.H10Function.unscale (U := V) (a := a⁻¹)
      (inv_pos.mpr ha) phi
  have htest := hu psi
  have hmass :
      (∫ y in V, rho y * u.toFun y * psi.toH1Function.toFun y ∂volume) =
        a ^ d * ∫ x in a⁻¹ • V, rho (a • x) * u.toFun (a • x) *
          phi.toH1Function.toFun x ∂volume := by
    have hset : V = a • (a⁻¹ • V) := by
      ext x
      simp [ha0]
    calc
      (∫ y in V, rho y * u.toFun y * psi.toH1Function.toFun y ∂volume) =
          ∫ y in a • (a⁻¹ • V), rho y * u.toFun y *
            psi.toH1Function.toFun y ∂volume := by
            exact congrArg (fun S : Set (Homogenization.Vec d) =>
              ∫ y in S, rho y * u.toFun y * psi.toH1Function.toFun y ∂volume) hset
      _ = a ^ d * ∫ x in a⁻¹ • V, rho (a • x) * u.toFun (a • x) *
          phi.toH1Function.toFun x ∂volume := by
        rw [Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos ha
          (a⁻¹ • V)]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        simp [psi, Homogenization.H10Function.unscale_toH1Function,
          Homogenization.H1Function.unscale_toFun, ha0]
  have henergy :
      (∫ y in V, vecDot (c y • u.grad y) (psi.toH1Function.grad y) ∂volume) =
        a ^ d * a⁻¹ * ∫ x in a⁻¹ • V,
          vecDot (c (a • x) • u.grad (a • x))
            (phi.toH1Function.grad x) ∂volume := by
    have hset : V = a • (a⁻¹ • V) := by
      ext x
      simp [ha0]
    calc
      (∫ y in V, vecDot (c y • u.grad y) (psi.toH1Function.grad y) ∂volume) =
          ∫ y in a • (a⁻¹ • V), vecDot (c y • u.grad y)
            (psi.toH1Function.grad y) ∂volume := by
            exact congrArg (fun S : Set (Homogenization.Vec d) =>
              ∫ y in S, vecDot (c y • u.grad y) (psi.toH1Function.grad y) ∂volume) hset
      _ = a ^ d * (∫ x in a⁻¹ • V,
          vecDot (c (a • x) • u.grad (a • x)) (psi.grad (a • x)) ∂volume) := by
        rw [Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos ha
          (a⁻¹ • V)]
        rfl
      _ = (a ^ d * a⁻¹) * ∫ x in a⁻¹ • V,
          vecDot (c (a • x) • u.grad (a • x)) (phi.grad x) ∂volume := by
        have hi : (∫ x in a⁻¹ • V,
            vecDot (c (a • x) • u.grad (a • x)) (psi.grad (a • x)) ∂volume) =
            a⁻¹ * ∫ x in a⁻¹ • V,
              vecDot (c (a • x) • u.grad (a • x)) (phi.grad x) ∂volume := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          simp [psi, Homogenization.H10Function.unscale_toH1Function,
            Homogenization.H1Function.unscale_grad, ha0,
            Homogenization.vecDot_smul_right]
        rw [hi]
        ring
  have hforce :
      (∫ y in V, rho y * f y * psi.toH1Function.toFun y ∂volume) =
        a ^ d * ∫ x in a⁻¹ • V, rho (a • x) * f (a • x) *
          phi.toH1Function.toFun x ∂volume := by
    have hset : V = a • (a⁻¹ • V) := by
      ext x
      simp [ha0]
    calc
      (∫ y in V, rho y * f y * psi.toH1Function.toFun y ∂volume) =
          ∫ y in a • (a⁻¹ • V), rho y * f y *
            psi.toH1Function.toFun y ∂volume := by
            exact congrArg (fun S : Set (Homogenization.Vec d) =>
              ∫ y in S, rho y * f y * psi.toH1Function.toFun y ∂volume) hset
      _ = a ^ d * ∫ x in a⁻¹ • V, rho (a • x) * f (a • x) *
          phi.toH1Function.toFun x ∂volume := by
        rw [Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos ha
          (a⁻¹ • V)]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        simp [psi, Homogenization.H10Function.unscale_toH1Function,
          Homogenization.H1Function.unscale_toFun, ha0]
  rw [hmass, henergy, hforce] at htest
  have hufun : (a • u.undilateSet ha hV).toFun =
      fun x => u.toFun (a • x) := by
    funext x
    simp [Homogenization.H1Function.undilateSet_toFun, ha0]
  have hugrad : (a • u.undilateSet ha hV).grad =
      fun x => a • u.grad (a • x) := by
    funext x
    simp [Homogenization.H1Function.undilateSet_grad]
  rw [hufun, hugrad]
  simp only [Homogenization.vecDot_smul_left]
  simp only [Homogenization.vecDot_smul_left] at htest
  let I : ℝ := ∫ x in a⁻¹ • V,
    rho (a • x) * u.toFun (a • x) * phi.toFun x ∂volume
  let E : ℝ := ∫ x in a⁻¹ • V,
    c (a • x) * vecDot (u.grad (a • x)) (phi.grad x) ∂volume
  let F : ℝ := ∫ x in a⁻¹ • V,
    rho (a • x) * f (a • x) * phi.toFun x ∂volume
  have htest' : mu * (a ^ d * I) + a ^ d * a⁻¹ * E = a ^ d * F := by
    simpa only [I, E, F] using htest
  have hE :
      (∫ x in a⁻¹ • V, c (a • x) * (a *
        vecDot (u.grad (a • x)) (phi.grad x)) ∂volume) = a * E := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hE]
  have hzero : a ^ d * (mu * a ^ 2 * I + a * E - a ^ 2 * F) = 0 := by
    calc
      a ^ d * (mu * a ^ 2 * I + a * E - a ^ 2 * F) =
          a ^ 2 * (mu * (a ^ d * I) + a ^ d * a⁻¹ * E - a ^ d * F) := by
            field_simp [ha0]
      _ = 0 := by
        have hbracket :
            mu * (a ^ d * I) + a ^ d * a⁻¹ * E - a ^ d * F = 0 := by
          linarith [htest']
        rw [hbracket]
        ring
  have hz : mu * a ^ 2 * I + a * E - a ^ 2 * F = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero d ha0)
  have hF :
      (∫ x in a⁻¹ • V, rho (a • x) * (a ^ 2 * f (a • x)) * phi.toFun x ∂volume) =
        a ^ 2 * F := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hF]
  linarith

theorem aux_tight_fast_exit_massive_const_div {d : ℕ}
    {U : Set (Homogenization.Vec d)} {c rho f : Homogenization.Vec d → ℝ}
    {q mu : ℝ} (hq : q ≠ 0)
    {u : Homogenization.H1Function U}
    (hu : IsMassiveWeakSolutionOn (fun x => q * c x) (fun x => q * rho x)
      mu U u f) :
    IsMassiveWeakSolutionOn c rho mu U u f := by
  intro phi
  have h := hu phi
  have hmass :
      (∫ x in U, (q * rho x) * u.toFun x * phi.toH1Function.toFun x ∂volume) =
        q * ∫ x in U, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have henergy :
      (∫ x in U, vecDot ((q * c x) • u.grad x) (phi.toH1Function.grad x) ∂volume) =
        q * ∫ x in U, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [mul_smul, Homogenization.vecDot_smul_left]
  have hforce :
      (∫ x in U, (q * rho x) * f x * phi.toH1Function.toFun x ∂volume) =
        q * ∫ x in U, rho x * f x * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hmass, henergy, hforce] at h
  field_simp [hq] at h
  exact h

theorem aux_tight_fast_exit_massive_two_const_div {d : ℕ}
    {U : Set (Homogenization.Vec d)} {c rho eta : Homogenization.Vec d → ℝ}
    {qc qr mu : ℝ} (hqc : qc ≠ 0) (hqr : qr ≠ 0)
    {u : Homogenization.H1Function U}
    (hu : IsMassiveWeakSolutionOn (fun x => qc * c x) (fun x => qr * rho x)
      mu U u (fun x => mu * eta x)) :
    IsMassiveWeakSolutionOn c rho ((qr / qc) * mu) U u
      (fun x => (qr / qc) * mu * eta x) := by
  intro phi
  have h := hu phi
  have hmass :
      (∫ x in U, (qr * rho x) * u.toFun x * phi.toH1Function.toFun x ∂volume) =
        qr * ∫ x in U, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have henergy :
      (∫ x in U, vecDot ((qc * c x) • u.grad x) (phi.toH1Function.grad x) ∂volume) =
        qc * ∫ x in U, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [mul_smul, Homogenization.vecDot_smul_left]
  have hforce :
      (∫ x in U, (qr * rho x) * (mu * eta x) * phi.toH1Function.toFun x ∂volume) =
        qr * ∫ x in U, rho x * (mu * eta x) * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hmass, henergy, hforce] at h
  have hqc' : qc ≠ 0 := hqc
  field_simp [hqc', hqr] at h
  have hratio : qr / qc * mu = qr * mu / qc := by ring
  rw [hratio]
  have hsource :
      (∫ x in U, rho x * (qr * mu / qc * eta x) * phi.toH1Function.toFun x ∂volume) =
        (qr / qc) * ∫ x in U, rho x * (mu * eta x) * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    field_simp [hqc']
  rw [hsource]
  field_simp [hqc']
  nlinarith [h]

theorem aux_tight_fast_exit_subsolution_const_div {d : ℕ}
    {U : Set (Homogenization.Vec d)} {a : Homogenization.Vec d → ℝ}
    {q : ℝ} (hq : 0 < q) {w : Homogenization.H1Function U}
    (hw : IsWeakSubSolutionOn (fun x => q * a x) U w) :
    IsWeakSubSolutionOn a U w := by
  intro psi hpsi
  have h := hw psi hpsi
  have heq :
      (∫ x in U, vecDot ((q * a x) • w.grad x) (psi.toH1Function.grad x) ∂volume) =
        q * ∫ x in U, vecDot (a x • w.grad x) (psi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [mul_smul, Homogenization.vecDot_smul_left]
  rw [heq] at h
  nlinarith

theorem aux_tight_fast_exit_source_ae {d : ℕ}
    {U : Set (Homogenization.Vec d)} {c rho : Homogenization.Vec d → ℝ}
    {mu : ℝ} {u : Homogenization.H1Function U}
    {f g : Homogenization.Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g)
    (hu : IsMassiveWeakSolutionOn c rho mu U u f) :
    IsMassiveWeakSolutionOn c rho mu U u g := by
  intro phi
  have h := hu phi
  have hsrc : (∫ x in U, rho x * f x * phi.toH1Function.toFun x) =
      ∫ x in U, rho x * g x * phi.toH1Function.toFun x := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [hsrc] at h
  exact h

theorem aux_tight_fast_exit_scaled_nonneg {t a b r k B : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 < b)
    (hk : 0 ≤ k) :
    0 ≤ t * (a / b) * (r⁻¹) ^ 2 * (k * (3 : ℝ) ^ B) := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg ht (div_nonneg ha hb.le)) (sq_nonneg _))
    (mul_nonneg hk (Real.rpow_nonneg (by norm_num) _))

theorem aux_tight_fast_exit_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x := by
  linarith

theorem aux_tight_fast_exit_mul_four_rpow_nonneg {x B : ℝ}
    (hx : 0 ≤ x) : 0 ≤ x * (4 : ℝ) ^ B := by
  exact mul_nonneg hx (Real.rpow_nonneg (by norm_num) _)

theorem aux_tight_fast_exit_scaled4_nonneg {t a b r k B : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 < b) (hk : 0 ≤ k) :
    0 ≤ t * (a / b) * (r⁻¹) ^ 2 * (k * (4 : ℝ) ^ B) := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg ht (div_nonneg ha hb.le)) (sq_nonneg _))
    (mul_nonneg hk (Real.rpow_nonneg (by norm_num) _))

theorem aux_tight_fast_exit_moser_product_nonneg {c x p z : ℝ}
    (hc : 0 ≤ c) (hx : 0 ≤ x) (_hz : 0 ≤ z) :
    0 ≤ c * x ^ p * Real.sqrt z := by
  exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hx p)) (Real.sqrt_nonneg z)

def aux_tight_fast_exit_moser_rhs (c x p z : ℝ) : ℝ :=
  c * x ^ p * Real.sqrt z

theorem aux_tight_fast_exit_moser_rhs_nonneg {c x p z : ℝ}
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    0 ≤ aux_tight_fast_exit_moser_rhs c x p z := by
  exact aux_tight_fast_exit_moser_product_nonneg hc hx hz

theorem aux_tight_fast_exit_sqrt_rescale {t a b r k B : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hk : 0 ≤ k) :
    Real.sqrt (t * (a / b) * (r⁻¹) ^ 2 * (k * (4 : ℝ) ^ B)) =
      (4 : ℝ) ^ (B / 2) * (k ^ (1 / 2 : ℝ)) *
        Real.sqrt (t / (r ^ 2 * b / a)) := by
  have hX : t * (a / b) * (r⁻¹) ^ 2 * (k * (4 : ℝ) ^ B) =
      (t / (r ^ 2 * b / a)) * (k * (4 : ℝ) ^ B) := by
    field_simp [ne_of_gt ht, ne_of_gt ha, ne_of_gt hb, ne_of_gt hr]
  rw [hX, Real.sqrt_mul (by positivity), Real.sqrt_mul hk]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show B * (1 / 2 : ℝ) = B / 2 by ring]
  ring

theorem aux_tight_fast_exit_ofReal_sqrt_rpow {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x) := by
  calc
    (ENNReal.ofReal x) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (x ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow]

theorem aux_tight_fast_exit_ofReal_mul_sqrt {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    ENNReal.ofReal a * (ENNReal.ofReal x) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (a * Real.sqrt x) := by
  rw [aux_tight_fast_exit_ofReal_sqrt_rpow hx]
  exact (ENNReal.ofReal_mul ha).symm

theorem aux_tight_fast_exit_moser_to_real {d : ℕ}
    {S : Set (Homogenization.Vec d)}
    {f g : Homogenization.Vec d → ℝ} {C k p A : ℝ}
    (hC : 0 ≤ C) (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ᵐ z ∂volume.restrict S,
      ENNReal.ofReal (g z) ≤ ENNReal.ofReal (C * k ^ p) *
        (ENNReal.ofReal A) ^ (1 / 2 : ℝ))
    (hfg : ∀ᵐ z ∂volume.restrict S, g z = 1 - f z) :
    ∀ᵐ z ∂volume.restrict S, 1 - f z ≤ C * k ^ p * Real.sqrt A := by
  have hright : 0 ≤ C * k ^ p * Real.sqrt A := by
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hk p))
      (Real.sqrt_nonneg _)
  filter_upwards [hbound, hfg] with z hz hzg
  have hcoeff : 0 ≤ C * k ^ p :=
    mul_nonneg hC (Real.rpow_nonneg hk p)
  have hz' : ENNReal.ofReal (g z) ≤
      ENNReal.ofReal (C * k ^ p * Real.sqrt A) := by
    calc
      ENNReal.ofReal (g z) ≤ ENNReal.ofReal (C * k ^ p) *
          (ENNReal.ofReal A) ^ (1 / 2 : ℝ) := hz
      _ = ENNReal.ofReal (C * k ^ p * Real.sqrt A) :=
        aux_tight_fast_exit_ofReal_mul_sqrt hcoeff hA
  rw [← hzg]
  exact (ENNReal.ofReal_le_ofReal_iff hright).mp hz'

theorem aux_tight_fast_exit_moser_h1_to_real {d : ℕ}
    {U V S : Set (Homogenization.Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (u : Homogenization.H1Function U) (v : Homogenization.H1Function V)
    {C k p A : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ᵐ z ∂volume.restrict S,
      ENNReal.ofReal ((Homogenization.H1Function.const (U := U) 1 - u).toFun z) ≤
        ENNReal.ofReal (C * k ^ p) * (ENNReal.ofReal A) ^ (1 / 2 : ℝ))
    (hEq : u.toFun =ᵐ[volume.restrict S] v.toFun) :
    ∀ᵐ z ∂volume.restrict S, 1 - v.toFun z ≤ C * k ^ p * Real.sqrt A := by
  have hfg : ∀ᵐ z ∂volume.restrict S,
      (Homogenization.H1Function.const (U := U) 1 - u).toFun z =
        1 - v.toFun z := by
    filter_upwards [hEq] with z hz
    have hz' := congrArg (fun q : ℝ => 1 - q) hz
    simpa only [Homogenization.H1Function.sub_toFun,
      Homogenization.H1Function.const_apply] using hz'
  exact aux_tight_fast_exit_moser_to_real hC hk hA hbound hfg

theorem aux_tight_fast_exit_sub_const_toFun {d : ℕ} {U : Set (Homogenization.Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (u v : Homogenization.H1Function U) (x : Homogenization.Vec d)
    (h : u.toFun x = v.toFun x) :
    (Homogenization.H1Function.const 1 - u).toFun x = 1 - v.toFun x := by
  simp only [Homogenization.H1Function.sub_toFun,
    Homogenization.H1Function.const_apply, h]

theorem aux_tight_fast_exit_sub_const_toFun_cross {d : ℕ}
    {U V : Set (Homogenization.Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    [IsFiniteMeasure (volumeMeasureOn V)]
    (u : Homogenization.H1Function U) (v : Homogenization.H1Function V)
    (x : Homogenization.Vec d) (h : u.toFun x = v.toFun x) :
    (Homogenization.H1Function.const (U := U) 1 - u).toFun x = 1 - v.toFun x := by
  simp only [Homogenization.H1Function.sub_toFun,
    Homogenization.H1Function.const_apply, h]

theorem aux_tight_fast_exit_sub_const_toFun_ae {d : ℕ}
    {U V S : Set (Homogenization.Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    [IsFiniteMeasure (volumeMeasureOn V)]
    (u : Homogenization.H1Function U) (v : Homogenization.H1Function V)
    (h : u.toFun =ᵐ[volume.restrict S] v.toFun) :
    (Homogenization.H1Function.const (U := U) 1 - u).toFun =ᵐ[volume.restrict S]
      (fun z => 1 - v.toFun z) := by
  filter_upwards [h] with z hz
  exact aux_tight_fast_exit_sub_const_toFun_cross (U := U) (V := V) u v z hz

/-- Displays `tight:eq-fast-exit` / `tight:eq-physical-exit`: for the cube of physical side `3^m`
at cutoff `N`, centred at `y` (rescaled side `s = 3^{m-N}`, local time `F = T_m/T_N =
3^{2(m-N)} ahom_N / ahom_m` in the time units of the rescaled process), one random `K` with
`E K ≤ C` (uniform in `N, m, y`) satisfies, for every `t > 0` and every start in the inner
ninth, `P_x(τ_Q ≤ t) ≤ K √(t/F)`.  The process input is the heat-kernel-free `LocalDiffusion`
package (strong Markov + killed resolvent = H¹₀ weak solution: the paper's stopped Itô formula),
not `LocalDiffusionData`. -/
theorem aux_tight_fast_exit_factor_rearrange
    (a b c d e f : ℝ) (h : b * c = d) :
    a * b * (e * c * f) = a * e * d * f := by
  rw [← h]
  ring

theorem aux_tight_fast_exit_sqrt_double_le {a : ℝ} (_ha : 0 ≤ a) :
    Real.sqrt (2 * a) ≤ 2 * Real.sqrt a := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg a)

theorem aux_tight_fast_exit_zpow_square (m N : ℕ) :
    ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ))) ^ 2 =
      (3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) := by
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem aux_tight_fast_exit_process_passage_inner {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : IsMarkovKernel KN)
    (L : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hLMarkov : IsMarkovKernel L)
    (omega : BilateralField d) (y : SpatialCoordinates d)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    {R R' S tA t0 F Kres : ℝ} (hR' : R' < R) (_hS : 0 < S)
    (htA : 0 < tA) (ht0 : 0 < t0) (hT : tA = t0 + t0)
    (hUeq : U = Metric.ball y R')
    (hL : ∀ z, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
        (KN (omega, z)) = L z)
    (eta : SpatialCoordinates d → ℝ) (heta : Measurable eta)
    (heta0 : ∀ z, 0 ≤ eta z) (heta1 : ∀ z, eta z ≤ 1)
    (hres : ∀ᵐ z ∂volume.restrict (Metric.ball y S),
      1 - killedResolvent L U tA eta z ≤ Kres * Real.sqrt (tA / F))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂(KN.map
          (ContinuousPath.finsetEvaluation I) (omega, x))))
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball y S) :
    (KN (omega, x))
        {path : DiffusionPath d |
          ContinuousPath.exitTime (Metric.ball y R) path ≤ ENNReal.ofReal t0} ≤
      ENNReal.ofReal ((4 * Kres) * Real.sqrt (tA / F)) := by
  let P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d) :=
    fun z => jointPathProbabilityMeasure KN hKN omega z
  have hfdP : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂((P x).map
          (ContinuousPath.finsetEvaluation I)).toMeasure) := by
    intro I f
    have h := hfd I f
    simpa only [P, jointPathProbabilityMeasure,
      ProbabilityMeasure.toMeasure_map,
      Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] using! h
  let b : ℝ≥0∞ := ENNReal.ofReal ((4 * Kres) * Real.sqrt (tA / F))
  have hExitAE : ∀ᵐ z ∂volume.restrict (Metric.ball y S),
      (L z) {w | MarkovProcess.LifetimePath.exitTime U w ≤ ENNReal.ofReal tA} ≤ b := by
    let : IsMarkovKernel L := hLMarkov
    filter_upwards [hres] with z hz
    exact aux_tight_fast_exit_of_resolvent_bound L U hU tA htA eta heta
      heta0 heta1 z Kres F hz
  have hExitKNAE : ∀ᵐ z ∂volume.restrict (Metric.ball y S),
      (P z : Measure (DiffusionPath d))
        {path | ContinuousPath.exitTime (Metric.ball y R') path ≤ ENNReal.ofReal tA} ≤ b := by
    filter_upwards [hExitAE] with z hz
    have hm := aux_tight_fast_exit_map_exit_event hU (hL z) tA
    have hPz : (P z : Measure (DiffusionPath d)) = KN (omega, z) := by
      rfl
    rw [hPz]
    rw [← hUeq]
    change (KN (omega, z))
        {path : DiffusionPath d |
          ContinuousPath.exitTime U path ≤ ENNReal.ofReal tA} ≤ b
    rw [hm]
    simpa [hUeq] using hz
  let Sset : Set (SpatialCoordinates d) :=
    {z | z ∉ Metric.ball y S ∨
      (P z : Measure (DiffusionPath d))
        {path | ContinuousPath.exitTime (Metric.ball y R') path ≤ ENNReal.ofReal tA} ≤ b}
  have hSae : ∀ᵐ z ∂volume, z ∈ Sset := by
    apply ae_of_ae_restrict_of_ae_restrict_compl (Metric.ball y S)
    · filter_upwards [hExitKNAE, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hzmem
      exact Set.mem_ofPred_eq.mpr (Or.inr hz)
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with z hz
      exact Set.mem_ofPred_eq.mpr (Or.inl hz)
  have hSdense : Dense Sset := Measure.dense_of_ae hSae
  have hgap := aux_tight_fast_exit_fdd_gap_dense_local
    P hfdP hSdense (U := Metric.ball y S) Metric.isOpen_ball y
    (fun z hz hzmem => by
      change z ∉ Metric.ball y S ∨
        (P z : Measure (DiffusionPath d))
          {path | ContinuousPath.exitTime (Metric.ball y R') path ≤ ENNReal.ofReal tA} ≤ b at hz
      rcases hz with hz | hz
      · exact False.elim (hz hzmem)
      · exact hz) x hx
  have hsub := aux_tight_fast_exit_exit_subset_gap y hR' ht0 ht0.le
  have hgap' : (P x : Measure (DiffusionPath d))
      (aux_tight_fast_exit_gap y R' (t0 + t0)) ≤ b := by
    simpa [hT] using hgap
  have hbound : (P x : Measure (DiffusionPath d))
      {path | ContinuousPath.exitTime (Metric.ball y R) path ≤ ENNReal.ofReal t0} ≤ b :=
    (measure_mono hsub).trans hgap'
  change (KN (omega, x))
      {path : DiffusionPath d |
        ContinuousPath.exitTime (Metric.ball y R) path ≤ ENNReal.ofReal t0} ≤ b at hbound
  simpa [b] using hbound



theorem aux_tight_fast_exit_post_moser
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ j, IsMarkovKernel (KN j))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ j omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN j (omega, x)) =
        L j omega x)
    (N m : ℕ) (y : SpatialCoordinates d) (omega : BilateralField d)
    (B Cmos Bm Btot : ℝ) (hCmos : 0 < Cmos)
    (hBtot : Btot = Bm + (1 / 2 : ℝ))
    (Kbase : BilateralField d → ℝ)
    (T : BilateralField d → BilateralField d)
    (hKbaseone : ∀ omega, 1 ≤ Kbase omega)
    (r t t0 : ℝ) (hr : 0 < r) (ht : 0 < t) (ht0 : 0 < t0)
    (hT : t = 2 * t0)
    (U : Set (SpatialCoordinates d)) (hUopen : IsOpen U)
    (hUV : U = Metric.ball y (5 * r / 12))
    (V V1 : Set (Homogenization.Vec d))
    [IsFiniteMeasure (volume.restrict V1)]
    (etaM : SpatialCoordinates d → ℝ)
    (u : H10Function U) (uDil : H1Function V) (uCap1 : H1Function V1)
    (hueq : u.toFun =ᵐ[(weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U]
      (killedResolvent (L N omega) U t etaM))
    (hrhoCoeffMeas : AEStronglyMeasurable
      (cutoffSpeedDensity M H omega N) (volume.restrict U))
    (rhoLo rhoMax : ℝ) (hrhoLo : 0 < rhoLo)
    (hrhoHi : ∀ᵐ z ∂volume.restrict U,
      rhoLo ≤ cutoffSpeedDensity M H omega N z ∧
        cutoffSpeedDensity M H omega N z ≤ rhoMax)
    (huDilfun : ∀ z : Homogenization.Vec d,
      uDil.toFun z = u.toFun (r • z + y))
    (hmoserBound : ∀ᵐ z ∂volume.restrict
        (Metric.ball (0 : Homogenization.Vec d) (3 * (1 / 27 : ℚ) / 2)),
        ENNReal.ofReal ((H1Function.const 1 - uCap1).toFun z) ≤
          ENNReal.ofReal (Cmos * Kbase (T omega) ^ Bm) *
            (ENNReal.ofReal (t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
              (Kbase (T omega) * (4 : ℝ) ^ B))) ^ (1 / 2 : ℝ))
    (huCap1DilSmall : uCap1.toFun =ᵐ[volume.restrict
        (Metric.ball (0 : Homogenization.Vec d)
          (3 * ((1 / 27 : ℚ) : ℝ) / 2))] uDil.toFun)
    (hetaMmeas : Measurable etaM)
    (hetaM0 : ∀ z, 0 ≤ etaM z) (hetaM1 : ∀ z, etaM z ≤ 1)
    (hmk : ∀ j, IsMarkovKernel (L j omega))
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂(KN N).map
          (ContinuousPath.finsetEvaluation I) (omega, x)))
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball y (r / 18)) :
    (KN N (omega, x))
        {path : DiffusionPath d |
          ContinuousPath.exitTime (Metric.ball y (r / 2)) path ≤ ENNReal.ofReal t0} ≤
      ENNReal.ofReal (8 * Cmos * (4 : ℝ) ^ (B / 2) *
        Kbase (T omega) ^ Btot * Real.sqrt (t0 /
          (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))) := by

  let Ares : ℝ := t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
    (Kbase (T omega) * (4 : ℝ) ^ B)
  have hAres : 0 ≤ Ares := by
    have hampos : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M m :=
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m
    have hanpos : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    have hk0 : 0 ≤ Kbase (T omega) :=
      aux_tight_fast_exit_nonneg_of_one_le (hKbaseone (T omega))
    change 0 ≤ t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
        (Kbase (T omega) * (4 : ℝ) ^ B)
    exact aux_tight_fast_exit_scaled4_nonneg
      (t := t) (a := SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)
      (b := SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) (r := r)
      (k := Kbase (T omega)) (B := B) ht.le
      hampos.le hanpos hk0
  have hlocalMoser := aux_tight_fast_exit_moser_h1_to_real
    (U := V1) (V := V)
    (S := Metric.ball (0 : Homogenization.Vec d)
      (3 * ((1 / 27 : ℚ) : ℝ) / 2))
    uCap1 uDil
    (C := Cmos) (k := Kbase (T omega)) (p := Bm) (A := Ares)
    hCmos.le (aux_tight_fast_exit_nonneg_of_one_le (hKbaseone (T omega))) hAres
    hmoserBound huCap1DilSmall
  let Wsmall : Set (Homogenization.Vec d) :=
    Metric.ball (0 : Homogenization.Vec d) (1 / 18 : ℝ)
  have hlocalMoser' : ∀ᵐ z ∂volume.restrict Wsmall,
      1 - u.toFun (r • z + y) ≤
        Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
    have hm : ∀ᵐ z ∂volume.restrict Wsmall,
        1 - uDil.toFun z ≤
          Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
      convert hlocalMoser using 1 ; norm_num [Wsmall]
    filter_upwards [hm] with z hz
    rw [huDilfun z] at hz
    exact hz
  have hMoserScaled : ∀ᵐ z ∂volume.restrict (r • Wsmall),
      1 - u.toFun (z + y) ≤
        Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
    have hm : ∀ᵐ z ∂Measure.map (fun z : Homogenization.Vec d => r • z)
        (volume.restrict Wsmall),
      1 - u.toFun (z + y) ≤
        Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
      apply (measurableEmbedding_const_smul₀ hr.ne').ae_map_iff.mpr
      exact hlocalMoser'
    rw [map_smul_volume_restrict hr Wsmall] at hm
    exact (Measure.absolutelyContinuous_smul (by positivity)).ae_le hm
  have hMoserTranslated : ∀ᵐ z ∂volume.restrict (translateSet y (r • Wsmall)),
      1 - u.toFun z ≤
        Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
    have hm : ∀ᵐ z ∂Measure.map (fun z : Homogenization.Vec d => z + y)
        (volume.restrict (r • Wsmall)),
      1 - u.toFun z ≤
        Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
      apply (measurableEmbedding_addRight y).ae_map_iff.mpr
      exact hMoserScaled
    rw [(measurePreserving_addRight_restrict_translateSet y (r • Wsmall)).map_eq] at hm
    exact hm
  have hWphys : translateSet y (r • Wsmall) =
      Metric.ball y (r / 18) := by
    dsimp [Wsmall]
    rw [_root_.smul_ball hr.ne' 0 (1 / 18 : ℝ)]
    ext z
    rw [mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball, dist_eq_norm, smul_zero, sub_zero]
    have hrnorm : ‖r‖ = r := by
      rw [Real.norm_eq_abs, abs_of_pos hr]
    rw [hrnorm]
    simp only [div_eq_mul_inv, one_mul]
  rw [hWphys] at hMoserTranslated
  have hsmallU : Metric.ball y (r / 18) ⊆ U := by
    rw [hUV]
    exact Metric.ball_subset_ball (by linarith only [hr])
  have hueqVol : u.toFun =ᵐ[volume.restrict U]
      killedResolvent (L N omega) U t etaM :=
    (volume_restrict_absolutelyContinuous_weightedMeasure_restrict
      hUopen.measurableSet
      ⟨hrhoCoeffMeas, ⟨rhoLo, rhoMax, hrhoLo, hrhoHi⟩⟩).ae_le hueq
  have hueqSmall : u.toFun =ᵐ[volume.restrict (Metric.ball y (r / 18))]
      killedResolvent (L N omega) U t etaM :=
    ae_restrict_of_ae_restrict_of_subset hsmallU hueqVol
  have hMoserResolvent : ∀ᵐ z ∂volume.restrict (Metric.ball y (r / 18)),
      1 - killedResolvent (L N omega) U t etaM z ≤
        Cmos * Kbase (T omega) ^ Bm * Real.sqrt Ares := by
    filter_upwards [hMoserTranslated, hueqSmall] with z hz heq
    rw [← heq]
    exact hz
  let Kres : ℝ := Cmos * (Kbase (T omega) ^ Bm) *
    ((4 : ℝ) ^ (B / 2) * (Kbase (T omega) ^ (1 / 2 : ℝ)))
  have hKresnonneg : 0 ≤ Kres := by
    dsimp [Kres]
    exact mul_nonneg
      (mul_nonneg hCmos.le (Real.rpow_nonneg (zero_le_one.trans
        (hKbaseone (T omega))) _))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (zero_le_one.trans (hKbaseone (T omega))) _))
  have hresolventBound : ∀ᵐ z ∂volume.restrict (Metric.ball y (r / 18)),
      1 - killedResolvent (L N omega) U t etaM z ≤
        Kres * Real.sqrt (t /
          (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) := by
    filter_upwards [hMoserResolvent] with z hz
    have hsq : Real.sqrt Ares =
        (4 : ℝ) ^ (B / 2) * (Kbase (T omega) ^ (1 / 2 : ℝ)) *
          Real.sqrt (t /
            (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) := by
      exact aux_tight_fast_exit_sqrt_rescale ht
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m)
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N) hr
        (aux_tight_fast_exit_nonneg_of_one_le (hKbaseone (T omega)))
    rw [hsq] at hz
    let q : ℝ := Real.sqrt (t /
      (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))
    have hz' : 1 - killedResolvent (L N omega) U t etaM z ≤
        Cmos * Kbase (T omega) ^ Bm *
          ((4 : ℝ) ^ (B / 2) * (Kbase (T omega) ^ (1 / 2 : ℝ)) * q) := by
      simpa only [q] using hz
    simpa only [Kres, q, mul_assoc] using hz'
  let F : ℝ := r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M m
  have hresF : ∀ᵐ z ∂volume.restrict (Metric.ball y (r / 18)),
      1 - killedResolvent (L N omega) U t etaM z ≤ Kres * Real.sqrt (t / F) := by
    exact hresolventBound
  have hpass := aux_tight_fast_exit_process_passage_inner
    (KN := KN N) (hKN := hKN N) (L := L N omega)
    (hLMarkov := hmk N) (omega := omega) (y := y) (U := U)
    (hU := hUopen) (R := r / 2) (R' := 5 * r / 12) (S := r / 18)
    (tA := t) (t0 := t0) (F := F) (Kres := Kres)
    (by linarith only [hr]) (div_pos hr (by norm_num)) ht ht0
    (by rw [hT]; ring) hUV (fun z => hL N omega z)
    etaM hetaMmeas hetaM0 hetaM1 hresF hfd x hx
  have hpow : Kbase (T omega) ^ Bm * Kbase (T omega) ^ (1 / 2 : ℝ) =
      Kbase (T omega) ^ Btot := by
    have hkpos : 0 < Kbase (T omega) :=
      lt_of_lt_of_le zero_lt_one (hKbaseone (T omega))
    rw [hBtot, ← Real.rpow_add hkpos]
  have hKresEq : Kres = Cmos * (4 : ℝ) ^ (B / 2) *
      Kbase (T omega) ^ Btot := by
    dsimp [Kres]
    calc
      Cmos * Kbase (T omega) ^ Bm *
          ((4 : ℝ) ^ (B / 2) * Kbase (T omega) ^ (1 / 2 : ℝ)) =
          Cmos * (4 : ℝ) ^ (B / 2) *
            (Kbase (T omega) ^ Bm * Kbase (T omega) ^ (1 / 2 : ℝ)) := by ring
      _ = Cmos * (4 : ℝ) ^ (B / 2) * Kbase (T omega) ^ Btot := by rw [hpow]
  have hF : 0 < F := by
    dsimp [F]
    exact div_pos
      (mul_pos (pow_pos hr 2) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m)
  have hsqtime : Real.sqrt (t / F) ≤ 2 * Real.sqrt (t0 / F) := by
    have harg : t / F = 2 * (t0 / F) := by
      rw [hT]
      ring
    rw [harg]
    exact aux_tight_fast_exit_sqrt_double_le (div_nonneg ht0.le hF.le)
  have hreal : (4 * Kres) * Real.sqrt (t / F) ≤
      8 * Cmos * (4 : ℝ) ^ (B / 2) * Kbase (T omega) ^ Btot *
        Real.sqrt (t0 / F) := by
    calc
      (4 * Kres) * Real.sqrt (t / F) ≤
          (4 * Kres) * (2 * Real.sqrt (t0 / F)) :=
        mul_le_mul_of_nonneg_left hsqtime
          (mul_nonneg (by norm_num) hKresnonneg)
      _ = 8 * Cmos * (4 : ℝ) ^ (B / 2) * Kbase (T omega) ^ Btot *
          Real.sqrt (t0 / F) := by
        rw [hKresEq]
        ring
  have hpass' := hpass.trans (ENNReal.ofReal_le_ofReal hreal)
  simpa only [F] using hpass'

theorem aux_tight_fast_exit_scaled_resolvent_and_moser_pointwise

    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (_hin : in_crossing M H PN KN)
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
        L N omega x)
    (N m : ℕ) (y : SpatialCoordinates d)
    (B Cmos Bm Btot : ℝ) (hCmos : 0 < Cmos)
    (hBtot : Btot = Bm + (1 / 2 : ℝ))
    (hmos : ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ),
      Continuous b → Continuous A → (∀ x, 0 < b x) → (∀ x, 0 < A x) → 1 ≤ K →
      tight_static_estimates b A 3 K B →
      ∀ w : Homogenization.H1Function
          (Metric.ball (0 : SpatialCoordinates d) (3 * ((1 / 9 : ℚ) : ℝ) / 2)),
        (∀ x, 0 ≤ w.toFun x) → (∃ Mw : ℝ, ∀ x, w.toFun x ≤ Mw) →
        SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn
          A (Metric.ball (0 : SpatialCoordinates d) (3 * ((1 / 9 : ℚ) : ℝ) / 2)) w →
        ∀ᵐ x ∂(volume.restrict
            (Metric.ball (0 : SpatialCoordinates d) (3 * ((1 / 27 : ℚ) : ℝ) / 2))),
          ENNReal.ofReal (w.toFun x) ≤
            ENNReal.ofReal (Cmos * K ^ Bm) *
              (∫⁻ z in Metric.ball (0 : SpatialCoordinates d)
                  (3 * ((1 / 9 : ℚ) : ℝ) / 2),
                ENNReal.ofReal (w.toFun z ^ 2 * b z)) ^ (1 / 2 : ℝ))
    (Kbase : BilateralField d → ℝ)
    (hKbaseone : ∀ omega, 1 ≤ Kbase omega)
    (T : BilateralField d → BilateralField d)
    (_hK0 : ∀ omega, 1 ≤ Kbase (T omega))
    (omega : BilateralField d)
    (hmk : ∀ j, IsMarkovKernel (L j omega))
    (hfin : ∀ j, (weightedMeasure (cutoffSpeedDensity M H omega j))
      (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) ≠ ∞)
    (hD : ∀ j,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega j) (cutoffSpeedDensity M H omega j) (L j omega))
    (hsc : ∃ c : ℝ, 0 < c ∧ ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H omega N (y + (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) • x) =
        c * cutoffSpeedDensity M H (T omega) m x)
    (hest : tight_static_estimates (cutoffSpeedDensity M H (T omega) m)
      (cutoffCoefficient M H (T omega) m) 3 (Kbase (T omega)) B)
    (hfd : ∀ I : Finset ℝ≥0,
      ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
        Continuous (fun x => ∫ z, f z ∂(KN N).map
          (ContinuousPath.finsetEvaluation I) (omega, x))) :
    ∀ t0 : ℝ, 0 < t0 →
      ∀ x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 18),
        (KN N (omega, x))
            {path : DiffusionPath d |
              ContinuousPath.exitTime
                (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) path ≤
                ENNReal.ofReal t0} ≤
          ENNReal.ofReal (8 * Cmos * (4 : ℝ) ^ (B / 2) *
            (Kbase (T omega)) ^ Btot * Real.sqrt (t0 /
            ((3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))) := by
  rcases hsc with ⟨cscale, hcscale, hscale'⟩
  intro t0 ht0 x hx
  let t : ℝ := 2 * t0
  have ht : 0 < t := by
    dsimp [t]
    linarith
  let r : ℝ := (3 : ℝ) ^ ((m : ℤ) - (N : ℤ))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hcut := hest.2.2 (1 / 9 : ℚ) (5 / 18 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  rcases hcut with ⟨chi, hchi01, hchi1, hchisupp, hchiE⟩
  have hbcont : Continuous (cutoffSpeedDensity M H (T omega) m) := by
    have hrel : cutoffSpeedDensity M H (T omega) m =
        fun z => SubdiffusiveProcess.CoarseGrainingVocab.ahom M m *
          cutoffCoefficient M H (T omega) m z := by
      funext z
      rw [cutoffCoefficient_eq_smul_cutoffSpeedDensity]
      rw [← mul_assoc, mul_inv_cancel₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m).ne',
        one_mul]
    rw [hrel]
    exact continuous_const.mul
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (T omega) m)
  have hbpos : ∀ z, 0 < cutoffSpeedDensity M H (T omega) m z := by
    intro z
    unfold cutoffSpeedDensity
    exact Real.exp_pos _
  have hAcont : Continuous (cutoffCoefficient M H omega N) :=
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N
  have hApos : ∀ z, 0 < cutoffCoefficient M H omega N z :=
    fun z => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H omega N z
  have hD0 := hD N
  have hmk0 := hmk N
  have hfin0 := hfin N
  let V : Set (Homogenization.Vec d) :=
    Metric.ball (0 : Homogenization.Vec d) (3 * ((5 / 18 : ℚ) : ℝ) / 2)
  let U : Set (SpatialCoordinates d) := translateSet y (r • V)
  have hUVphys : Metric.ball y (5 * r / 12) = U := by
    dsimp [U]
    have hVeq : V = Metric.ball (0 : Homogenization.Vec d) (5 / 12 : ℝ) := by
      dsimp [V]
      norm_num
    rw [hVeq]
    ext z
    rw [mem_translateSet_iff_sub_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hform : r⁻¹ * ‖z - y‖ = ‖z - y‖ / r := by
      rw [div_eq_mul_inv]
      ring
    rw [hform]
    constructor
    · intro hz
      apply (div_lt_iff₀ hr).2
      nlinarith
    · intro hz
      have hz' := (div_lt_iff₀ hr).1 hz
      nlinarith
  have hUV : U = Metric.ball y (5 * r / 12) := hUVphys.symm
  have hUopen : IsOpen U := by
    rw [hUV]
    exact Metric.isOpen_ball
  have hUbd : Bornology.IsBounded U := by
    rw [hUV]
    exact Metric.isBounded_ball
  let : IsMarkovKernel (L N omega) := hmk0
  obtain ⟨chiDil, hchiDilFun, hchiDilGrad⟩ :=
    aux_tight_fast_exit_h10_dilate hr chi
  let etaH0 : H10Function (translateSet y (r • V)) := chiDil.translate y
  let etaH : H10Function U := etaH0
  have hetaHfun : ∀ z, etaH.toFun z =
      chi.toFun (r⁻¹ • (z - y)) := by
    intro z
    simp [etaH, etaH0, H10Function.translate_toH1Function,
      H1Function.translate_toFun, hchiDilFun]
  have hetaH0 : ∀ z, 0 ≤ etaH.toFun z := by
    intro z
    rw [hetaHfun]
    exact (hchi01 _).1
  have hetaH1 : ∀ z, etaH.toFun z ≤ 1 := by
    intro z
    rw [hetaHfun]
    exact (hchi01 _).2
  have hetaHAE : AEMeasurable etaH.toFun (volume.restrict U) :=
    etaH.toH1Function.memL2.aestronglyMeasurable.aemeasurable
  let etaRaw : SpatialCoordinates d → ℝ :=
    AEMeasurable.mk etaH.toFun hetaHAE
  let etaM : SpatialCoordinates d → ℝ := fun z => max 0 (min 1 (etaRaw z))
  have hetaMmeas : Measurable etaM := by
    exact measurable_const.max (measurable_const.min hetaHAE.measurable_mk)
  have hetaM0 : ∀ z, 0 ≤ etaM z := by
    intro z
    exact le_max_left _ _
  have hetaM1 : ∀ z, etaM z ≤ 1 := by
    intro z
    exact max_le (by norm_num) (min_le_left _ _)
  have hetaMae : etaM =ᵐ[volume.restrict U] etaH.toFun := by
    filter_upwards [hetaHAE.ae_eq_mk.symm] with z hz
    change max 0 (min 1 ((AEMeasurable.mk etaH.toFun hetaHAE) z)) = etaH.toFun z
    rw [hz]
    rw [min_eq_right (hetaH1 z), max_eq_right (hetaH0 z)]
  have hrhoCoeff : CoefficientOn U (cutoffSpeedDensity M H omega N) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower.coefficientOn_of_localDiffusion
      hD0 hUbd
  obtain ⟨hrhoCoeffMeas, rhoLo, rhoMax, hrhoLo, hrhoHi⟩ := hrhoCoeff
  have hetaMem : MemLp etaH.toFun 2
      ((weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U) :=
    memLp_weighted_of_volume_restrict hUopen.measurableSet
      ⟨hrhoCoeffMeas, ⟨rhoLo, rhoMax, hrhoLo, hrhoHi⟩⟩
      etaH.toH1Function.memL2
  have hetaMaeW : etaM =ᵐ[(weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U]
      etaH.toFun := by
    apply ae_iff.mpr
    exact (weightedMeasure_restrict_absolutelyContinuous_volume_restrict
      (rho := cutoffSpeedDensity M H omega N) hUopen.measurableSet)
      (ae_iff.mp hetaMae)
  have hetaMMem : MemLp etaM 2
      ((weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U) :=
    (memLp_congr_ae hetaMaeW).mpr hetaMem
  obtain ⟨u, hueq, hu, hu01⟩ :=
    aux_tight_fast_exit_weak_resolvent hD0 U hUopen hUbd t ht etaM hetaMmeas
      hetaM0 hetaM1 hetaMMem
  have hsourceAE : (fun z => t⁻¹ * etaM z) =ᵐ[volume.restrict U]
      (fun z => t⁻¹ * etaH.toFun z) := by
    filter_upwards [hetaMae] with z hz
    rw [hz]
  have huChi : IsMassiveWeakSolutionOn (cutoffCoefficient M H omega N)
      (cutoffSpeedDensity M H omega N) t⁻¹ U u.toH1Function
      (fun z => t⁻¹ * etaH.toFun z) :=
    aux_tight_fast_exit_source_ae hsourceAE hu
  obtain ⟨lam, Lam, hEll, _⟩ :=
    exists_isEllipticFieldOn_ball_of_continuous_pos hAcont hApos y
      (r := 5 * r / 12) (by positivity)
  have hEll' : IsEllipticFieldOn lam Lam U
      (scalarCoeffField (cutoffCoefficient M H omega N)) := by
    simpa [hUV] using hEll
  have hvar := aux_tight_fast_exit_variational_comparison
    (U := U) (c := cutoffCoefficient M H omega N)
    (rho := cutoffSpeedDensity M H omega N) (s := t)
    (rhoMax := rhoMax)
    hEll'
    (by filter_upwards with z; exact (hApos z).le)
    (by
      filter_upwards with z
      exact (by unfold cutoffSpeedDensity; positivity :
        0 ≤ cutoffSpeedDensity M H omega N z))
    (by
      have hrhoCont : Continuous (cutoffSpeedDensity M H omega N) := by
        have hrel : cutoffSpeedDensity M H omega N =
            fun z => SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              cutoffCoefficient M H omega N z := by
          funext z
          rw [cutoffCoefficient_eq_smul_cutoffSpeedDensity]
          rw [← mul_assoc, mul_inv_cancel₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne',
            one_mul]
        rw [hrel]
        exact continuous_const.mul
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N)
      exact hrhoCont.aestronglyMeasurable)
    (by
      filter_upwards [hrhoHi] with z hz
      rw [abs_of_pos (by unfold cutoffSpeedDensity; positivity)]
      exact hz.2)
    ht u etaH huChi
  have hcoefscale : ∀ z : Homogenization.Vec d,
      cutoffCoefficient M H omega N (r • z + y) =
        (cscale * SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
          cutoffCoefficient M H (T omega) m z := by
    intro z
    rw [cutoffCoefficient_eq_smul_cutoffSpeedDensity,
      cutoffCoefficient_eq_smul_cutoffSpeedDensity]
    have hs := hscale' z
    rw [add_comm] at hs
    rw [hs]
    field_simp [SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N |>.ne',
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m |>.ne']
  have hrhoscale : ∀ z : Homogenization.Vec d,
      cutoffSpeedDensity M H omega N (r • z + y) =
        cscale * cutoffSpeedDensity M H (T omega) m z := by
    intro z
    have hs := hscale' z
    rw [add_comm] at hs
    exact hs
  have hetaHscale : ∀ z : Homogenization.Vec d,
      etaH.toFun (r • z + y) = chi.toFun z := by
    intro z
    rw [hetaHfun]
    have hz : r⁻¹ • (r • z + y - y) = z := by
      rw [add_sub_cancel_right]
      simp [smul_smul, hr.ne']
    exact congrArg chi.toFun hz
  let uT : H1Function (r • V) := H1Function.untranslate y u.toH1Function
  have huT : IsMassiveWeakSolutionOn
      (fun z => cutoffCoefficient M H omega N (z + y))
      (fun z => cutoffSpeedDensity M H omega N (z + y)) t⁻¹
      (r • V) uT (fun z => t⁻¹ * etaH.toFun (z + y)) := by
    simpa [uT, U] using
      (isMassiveWeakSolutionOn_untranslate y u.toH1Function huChi)
  let uDil : H1Function V := r • uT.undilateSet hr (by rfl)
  have huDil : IsMassiveWeakSolutionOn
      (fun z => cutoffCoefficient M H omega N (r • z + y))
      (fun z => cutoffSpeedDensity M H omega N (r • z + y))
      (t⁻¹ * r ^ 2) V uDil
      (fun z => r ^ 2 * (t⁻¹ * etaH.toFun (r • z + y))) := by
    simpa [uDil, uT, add_comm] using
      (aux_tight_fast_exit_massive_dilate (U := V) (V := r • V)
        hr (by rfl) uT huT)
  have huDil' : IsMassiveWeakSolutionOn
      (fun z => (cscale * SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
          cutoffCoefficient M H (T omega) m z)
      (fun z => cscale * cutoffSpeedDensity M H (T omega) m z)
      (t⁻¹ * r ^ 2) V uDil
      (fun z => (t⁻¹ * r ^ 2) * chi.toFun z) := by
    rw [show (fun z => cutoffCoefficient M H omega N (r • z + y)) = _ from
      funext (fun z => hcoefscale z)] at huDil
    rw [show (fun z => cutoffSpeedDensity M H omega N (r • z + y)) = _ from
      funext (fun z => hrhoscale z)] at huDil
    simpa [hetaHscale, mul_assoc, mul_comm, mul_left_comm] using huDil
  let qc : ℝ := cscale * SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
  let qr : ℝ := cscale
  have hqc : qc ≠ 0 := by
    dsimp [qc]
    exact div_ne_zero
      (mul_ne_zero hcscale.ne'
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m).ne')
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'
  have hqr : qr ≠ 0 := by
    dsimp [qr]
    exact hcscale.ne'
  have huNorm0 := aux_tight_fast_exit_massive_two_const_div
    (u := uDil) (eta := chi.toFun) hqc hqr huDil'
  have hmu : (qr / qc) * (t⁻¹ * r ^ 2) =
      t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) := by
    dsimp [qc, qr]
    field_simp [hcscale.ne',
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N |>.ne',
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m |>.ne']
  have huNorm : IsMassiveWeakSolutionOn
      (cutoffCoefficient M H (T omega) m)
      (cutoffSpeedDensity M H (T omega) m)
      (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) V uDil
      (fun z => (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) * chi.toFun z) := by
    simpa [qc, qr, hmu] using huNorm0
  have hu01vol : ∀ᵐ z ∂volume.restrict U,
      0 ≤ u.toFun z ∧ u.toFun z ≤ 1 :=
    (volume_restrict_absolutelyContinuous_weightedMeasure_restrict
      hUopen.measurableSet
      ⟨hrhoCoeffMeas, ⟨rhoLo, rhoMax, hrhoLo, hrhoHi⟩⟩).ae_le hu01
  have hgoodScaled : ∀ᵐ z ∂volume.restrict (r • V),
      0 ≤ u.toFun (z + y) ∧ u.toFun (z + y) ≤ 1 := by
    have hmapgood : ∀ᵐ z ∂Measure.map (fun z : Homogenization.Vec d => z + y)
        (volume.restrict (r • V)),
        0 ≤ u.toFun z ∧ u.toFun z ≤ 1 := by
      rw [(measurePreserving_addRight_restrict_translateSet y (r • V)).map_eq]
      simpa [U] using hu01vol
    exact ae_of_ae_map (measurable_add_const y).aemeasurable hmapgood
  have hgoodLocal : ∀ᵐ z ∂volume.restrict V,
      0 ≤ u.toFun (r • z + y) ∧ u.toFun (r • z + y) ≤ 1 := by
    have hmapgood : ∀ᵐ z ∂Measure.map (fun z : Homogenization.Vec d => r • z)
        (volume.restrict V),
        0 ≤ u.toFun (z + y) ∧ u.toFun (z + y) ≤ 1 := by
      rw [map_smul_volume_restrict hr V]
      exact Measure.smul_absolutelyContinuous.ae_le hgoodScaled
    exact ae_of_ae_map (measurable_const_smul r).aemeasurable hmapgood
  have huDil01 : ∀ᵐ z ∂volume.restrict V,
      0 ≤ uDil.toFun z ∧ uDil.toFun z ≤ 1 := by
    filter_upwards [hgoodLocal] with z hz
    rw [show uDil.toFun z = u.toFun (r • z + y) by
      simp [uDil, uT, Homogenization.H1Function.undilateSet_toFun,
        Homogenization.H1Function.untranslate_toFun, hr.ne']]
    exact hz
  have hVopen : IsOpen V := by
    dsimp [V]
    exact Metric.isOpen_ball
  have hVdom : IsOpenBoundedConvexDomain V := by
    dsimp [V]
    apply isOpenBoundedConvexDomain_ball
    norm_num
  obtain ⟨n, hnfun, hngrad⟩ :=
    exists_h1_max_sub_const hVdom (-uDil) 0
  let uNonneg : H1Function V := uDil + n
  have hnzero : n.toFun =ᵐ[volume.restrict V] 0 := by
    filter_upwards [huDil01] with z hz
    rw [hnfun]
    simp [max_eq_right (neg_nonpos.mpr hz.1)]
  have hngradzero : n.grad =ᵐ[volume.restrict V] 0 := by
    exact Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (u := n) (v := (0 : H1Function V)) hVopen (by simpa using hnzero)
  have huNonnegfun : uNonneg.toFun =ᵐ[volume.restrict V] uDil.toFun := by
    filter_upwards [huDil01] with z hz
    simp only [uNonneg, H1Function.add_toFun]
    rw [hnfun]
    simp [max_eq_right (neg_nonpos.mpr hz.1)]
  have huNonneggrad : uNonneg.grad =ᵐ[volume.restrict V] uDil.grad := by
    change (uDil + n).grad =ᵐ[volume.restrict V] uDil.grad
    rw [H1Function.add_grad]
    filter_upwards [hngradzero] with z hz
    simp [hz]
  have huNonneg : IsMassiveWeakSolutionOn
      (cutoffCoefficient M H (T omega) m)
      (cutoffSpeedDensity M H (T omega) m)
      (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) V uNonneg
      (fun z => (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) * chi.toFun z) := by
    exact IsMassiveWeakSolutionOn.congr huNonnegfun.symm huNonneggrad.symm huNorm
  have huNonneg0 : ∀ z, 0 ≤ uNonneg.toFun z := by
    intro z
    simp only [uNonneg, H1Function.add_toFun]
    rw [hnfun]
    simp only [H1Function.neg_toFun, sub_zero]
    linarith [le_max_left (-uDil.toFun z) 0]
  have huNonneg1 : ∀ᵐ z ∂volume.restrict V, uNonneg.toFun z ≤ 1 := by
    filter_upwards [huDil01, huNonnegfun] with z hz heq
    rw [heq]
    exact hz.2
  obtain ⟨p, hpfun, hpgrad⟩ :=
    exists_h1_max_sub_const hVdom uNonneg 1
  let uCap : H1Function V := uNonneg - p
  have hpzero : p.toFun =ᵐ[volume.restrict V] 0 := by
    filter_upwards [huNonneg1] with z hz
    rw [hpfun]
    change max (uNonneg.toFun z - 1) 0 = 0
    simp [max_eq_right (sub_nonpos.mpr hz)]
  have hpgradzero : p.grad =ᵐ[volume.restrict V] 0 := by
    exact Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (u := p) (v := (0 : H1Function V)) hVopen (by simpa using hpzero)
  have huCapfun : uCap.toFun =ᵐ[volume.restrict V] uNonneg.toFun := by
    filter_upwards [huNonneg1] with z hz
    simp only [uCap, H1Function.sub_toFun]
    rw [hpfun]
    change uNonneg.toFun z - max (uNonneg.toFun z - 1) 0 = uNonneg.toFun z
    simp [max_eq_right (sub_nonpos.mpr hz)]
  have huCapgrad : uCap.grad =ᵐ[volume.restrict V] uNonneg.grad := by
    change (uNonneg - p).grad =ᵐ[volume.restrict V] uNonneg.grad
    rw [H1Function.sub_grad]
    filter_upwards [hpgradzero] with z hz
    simp [hz]
  have huCap : IsMassiveWeakSolutionOn
      (cutoffCoefficient M H (T omega) m)
      (cutoffSpeedDensity M H (T omega) m)
      (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) V uCap
      (fun z => (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) * chi.toFun z) := by
    exact IsMassiveWeakSolutionOn.congr huCapfun.symm huCapgrad.symm huNonneg
  let V1 : Set (Homogenization.Vec d) :=
    Metric.ball (0 : Homogenization.Vec d) (3 * ((1 / 9 : ℚ) : ℝ) / 2)
  have hV1open : IsOpen V1 := by
    dsimp [V1]
    exact Metric.isOpen_ball
  have hV1sub : V1 ⊆ V := by
    dsimp [V1, V]
    apply Metric.ball_subset_ball
    norm_num
  have hV1bd : Bornology.IsBounded V1 := by
    dsimp [V1]
    exact Metric.isBounded_ball
  let uCap1 : H1Function V1 := uCap.restrict hV1open hV1sub
  have huCap1 := IsMassiveWeakSolutionOn.restrict hV1open hVopen hV1sub huCap
  have huCap1upper : ∀ z, uCap1.toFun z ≤ 1 := by
    intro z
    change uCap.toFun z ≤ 1
    simp only [uCap, H1Function.sub_toFun]
    rw [hpfun]
    change uNonneg.toFun z - max (uNonneg.toFun z - 1) 0 ≤ 1
    by_cases hz : uNonneg.toFun z ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr hz), sub_zero]
      exact hz
    · simp [max_eq_left (sub_nonneg.mpr (le_of_not_ge hz))]
  have huCap1lower : ∀ z, 0 ≤ uCap1.toFun z := by
    intro z
    change 0 ≤ uCap.toFun z
    simp only [uCap, H1Function.sub_toFun]
    rw [hpfun]
    change 0 ≤ uNonneg.toFun z - max (uNonneg.toFun z - 1) 0
    by_cases hz : uNonneg.toFun z ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr hz), sub_zero]
      exact huNonneg0 z
    · simp [max_eq_left (sub_nonneg.mpr (le_of_not_ge hz))]
  let rhoMMax : ℝ := rhoMax / cscale
  have hphysicalBound : ∀ᵐ z ∂volume.restrict (r • V),
      |cutoffSpeedDensity M H omega N (z + y)| ≤ rhoMax := by
    have hmapgood : ∀ᵐ z ∂Measure.map (fun z : Homogenization.Vec d => z + y)
        (volume.restrict (r • V)),
        |cutoffSpeedDensity M H omega N z| ≤ rhoMax := by
      rw [(measurePreserving_addRight_restrict_translateSet y (r • V)).map_eq]
      filter_upwards [hrhoHi] with z hz
      rw [abs_of_pos (by unfold cutoffSpeedDensity; positivity)]
      exact hz.2
    exact ae_of_ae_map (measurable_add_const y).aemeasurable hmapgood
  have hlocalBound : ∀ᵐ z ∂volume.restrict V,
      |cutoffSpeedDensity M H omega N (r • z + y)| ≤ rhoMax := by
    have hmapgood : ∀ᵐ z ∂Measure.map (fun z : Homogenization.Vec d => r • z)
        (volume.restrict V),
        |cutoffSpeedDensity M H omega N (z + y)| ≤ rhoMax := by
      rw [map_smul_volume_restrict hr V]
      exact Measure.smul_absolutelyContinuous.ae_le hphysicalBound
    exact ae_of_ae_map (measurable_const_smul r).aemeasurable hmapgood
  have hlocalBound1 : ∀ᵐ z ∂volume.restrict V1,
      |cutoffSpeedDensity M H (T omega) m z| ≤ rhoMMax := by
    have hrestrict := ae_restrict_of_ae_restrict_of_subset hV1sub hlocalBound
    filter_upwards [hrestrict] with z hz
    rw [hrhoscale z, abs_mul, abs_of_pos hcscale, abs_of_pos (hbpos z)] at hz
    rw [abs_of_pos (hbpos z)]
    dsimp [rhoMMax]
    exact (le_div_iff₀ hcscale).2 (by simpa [mul_comm] using hz)
  let : IsFiniteMeasure (volume.restrict V1) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_ball (0 : Homogenization.Vec d) (by norm_num)).isFiniteMeasure_restrict_volume
  have hsub1 : IsWeakSubSolutionOn
      (cutoffCoefficient M H (T omega) m) V1
      (H1Function.const 1 - uCap1) := by
    have hchiV1 : ∀ z ∈ V1, chi.toFun z = 1 := by
      intro z hz
      apply hchi1 z
      exact hz
    have hsource1 : (fun z =>
        (t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) * chi.toFun z) =ᵐ[volume.restrict V1]
        (fun _ => t⁻¹ * (r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) := by
      filter_upwards [ae_restrict_mem hV1open.measurableSet] with z hz
      rw [hchiV1 z hz]
      ring
    have huCap1const := aux_tight_fast_exit_source_ae hsource1 huCap1
    exact aux_tight_fast_exit_complement_subsolution
      (u := uCap1) (rhoMax := rhoMMax)
      (by
        exact mul_nonneg (inv_pos.mpr ht).le
          (div_nonneg
            (mul_nonneg (sq_nonneg r)
              (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le)
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m).le))
      (by filter_upwards with z; exact (hbpos z).le)
      hbcont.aestronglyMeasurable
      hlocalBound1
      huCap1const (Filter.Eventually.of_forall huCap1upper)
  have hw0 : ∀ z, 0 ≤ (H1Function.const 1 - uCap1).toFun z := by
    intro z
    simp only [H1Function.sub_toFun, H1Function.const_apply]
    linarith [huCap1upper z]
  have hw1 : ∀ z, (H1Function.const 1 - uCap1).toFun z ≤ 1 := by
    intro z
    simp only [H1Function.sub_toFun, H1Function.const_apply]
    linarith [huCap1lower z]
  have hmoser := hmos
    (cutoffSpeedDensity M H (T omega) m)
    (cutoffCoefficient M H (T omega) m) (Kbase (T omega)) hbcont
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (T omega) m)
    hbpos
    (fun z => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (T omega) m z)
    (hKbaseone (T omega)) hest (H1Function.const 1 - uCap1)
    hw0
    ⟨1, hw1⟩
    hsub1
  obtain ⟨lamm, Lamm, hEllm0, _⟩ :=
    exists_isEllipticFieldOn_ball_of_continuous_pos
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (T omega) m)
      (fun z => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (T omega) m z)
      0 (r := (1 / 2 : ℝ)) (by norm_num)
  have hEllm : IsEllipticFieldOn lamm Lamm V
      (scalarCoeffField (cutoffCoefficient M H (T omega) m)) := by
    apply IsEllipticFieldOn.mono hEllm0
    · exact Metric.isOpen_ball.measurableSet
    · dsimp [V]
      exact Metric.ball_subset_ball (by norm_num)
  have hchiEnergyInt : IntegrableOn
      (fun z => cutoffCoefficient M H (T omega) m z *
        Homogenization.vecDot (chi.grad z) (chi.grad z)) V := by
    simpa only [Homogenization.vecDot_smul_left, smul_eq_mul, one_mul] using
      (integrableOn_energy_term hEllm chi.grad_memVectorL2 chi.grad_memVectorL2)
  have hchiEnergyNonneg : ∀ᵐ z ∂volume.restrict V,
      0 ≤ cutoffCoefficient M H (T omega) m z *
        Homogenization.vecDot (chi.grad z) (chi.grad z) := by
    filter_upwards with z
    exact mul_nonneg (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (T omega) m z).le
      (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp.vecDot_self_nonneg _)
  have hchiEnergyBound :
      ∫ z in V, cutoffCoefficient M H (T omega) m z *
        Homogenization.vecDot (chi.grad z) (chi.grad z) ∂volume ≤
        Kbase (T omega) * (4 : ℝ) ^ B := by
    have hE := hchiE (0 : Homogenization.Vec d) 1 (by norm_num) (by norm_num)
    have hVset : Metric.ball (0 : Homogenization.Vec d) 1 ∩ V = V := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        have hz' : ‖z‖ < (5 / 12 : ℝ) := by
          norm_num [V, Metric.mem_ball, dist_eq_norm] at hz ⊢
          exact hz
        exact ⟨Metric.mem_ball.mpr (by
            simpa [dist_eq_norm] using
            (lt_trans hz' (show (5 / 12 : ℝ) < 1 by norm_num))), hz⟩
    rw [hVset] at hE
    have hE' := (ofReal_integral_eq_lintegral_ofReal hchiEnergyInt
      hchiEnergyNonneg).symm
    rw [hE'] at hE
    have hfactor :
        3 * (((5 / 18 : ℚ) : ℝ) - ((1 / 9 : ℚ) : ℝ)) / 2 = (1 / 4 : ℝ) := by
      norm_num
    have hRhs : Kbase (T omega) *
        (3 * (((5 / 18 : ℚ) : ℝ) - ((1 / 9 : ℚ) : ℝ)) / 2) ^ (-B) *
          (1 : ℝ) ^ ((d : ℝ) - 1 / 2) = Kbase (T omega) * (4 : ℝ) ^ B := by
      rw [hfactor, Real.one_rpow, mul_one]
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      simp
    rw [hRhs] at hE
    have hRnonneg : 0 ≤ Kbase (T omega) * (4 : ℝ) ^ B := by
      exact mul_nonneg (by linarith [hKbaseone (T omega)])
        (Real.rpow_nonneg (by norm_num) _)
    exact (ENNReal.ofReal_le_ofReal_iff hRnonneg).mp hE
  have huDilfun : ∀ z : Homogenization.Vec d,
      uDil.toFun z = u.toFun (r • z + y) := by
    intro z
    simp [uDil, uT, Homogenization.H1Function.undilateSet_toFun,
      Homogenization.H1Function.untranslate_toFun, hr.ne']
  have huDilgrad : ∀ z : Homogenization.Vec d,
      uDil.grad z = r • u.grad (r • z + y) := by
    intro z
    simp [uDil, uT, Homogenization.H1Function.undilateSet_grad,
      Homogenization.H1Function.untranslate_grad]
  have hetaHgradscale : ∀ z : Homogenization.Vec d,
      etaH.grad (r • z + y) = r⁻¹ • chi.grad z := by
    intro z
    simp [etaH, etaH0, H1Function.translate_grad, hchiDilGrad,
      smul_smul, hr.ne']
  have hleftscale :
      (∫ z in U, cutoffSpeedDensity M H omega N z *
          (u.toFun z - etaH.toFun z) ^ 2 ∂volume) =
        cscale * r ^ d *
          (∫ z in V, cutoffSpeedDensity M H (T omega) m z *
            (uDil.toFun z - chi.toFun z) ^ 2 ∂volume) := by
    have htrans := setIntegral_comp_addRight_translateSet (d := d) y (r • V)
      (fun z => cutoffSpeedDensity M H omega N z *
        (u.toFun z - etaH.toFun z) ^ 2)
    have hscaleint :=
      Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
        hr V (fun z => cutoffSpeedDensity M H omega N (z + y) *
          (u.toFun (z + y) - etaH.toFun (z + y)) ^ 2)
    change (∫ z in translateSet y (r • V), cutoffSpeedDensity M H omega N z *
        (u.toFun z - etaH.toFun z) ^ 2 ∂volume) = _
    rw [← htrans]
    rw [hscaleint]
    rw [smul_eq_mul]
    calc
      r ^ d * (∫ z in V, cutoffSpeedDensity M H omega N (r • z + y) *
            (u.toFun (r • z + y) - etaH.toFun (r • z + y)) ^ 2) =
          ∫ z in V, r ^ d *
            (cutoffSpeedDensity M H omega N (r • z + y) *
              (u.toFun (r • z + y) - etaH.toFun (r • z + y)) ^ 2) := by
        rw [integral_const_mul]
      _ = ∫ z in V, cscale * r ^ d *
          (cutoffSpeedDensity M H (T omega) m z *
            (uDil.toFun z - chi.toFun z) ^ 2) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hrhoscale z, huDilfun z, hetaHscale z]
        ring
      _ = cscale * r ^ d *
          ∫ z in V, cutoffSpeedDensity M H (T omega) m z *
            (uDil.toFun z - chi.toFun z) ^ 2 := by
        rw [integral_const_mul]
  have henergyscale :
      energy (cutoffCoefficient M H omega N) U etaH.toH1Function =
        cscale * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * r ^ d * (r⁻¹) ^ 2 *
          energy (cutoffCoefficient M H (T omega) m) V chi.toH1Function := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy
    have htransE := setIntegral_comp_addRight_translateSet (d := d) y (r • V)
      (fun z => cutoffCoefficient M H omega N z *
        Homogenization.vecDot (etaH.grad z) (etaH.grad z))
    have hscaleE :=
      Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos
        hr V (fun z => cutoffCoefficient M H omega N (z + y) *
          Homogenization.vecDot (etaH.grad (z + y)) (etaH.grad (z + y)))
    change (∫ z in translateSet y (r • V), cutoffCoefficient M H omega N z *
        Homogenization.vecDot (etaH.grad z) (etaH.grad z) ∂volume) = _
    rw [← htransE]
    rw [hscaleE]
    rw [smul_eq_mul]
    calc
      r ^ d * (∫ z in V, cutoffCoefficient M H omega N (r • z + y) *
            Homogenization.vecDot (etaH.grad (r • z + y))
              (etaH.grad (r • z + y)) ∂volume) =
          ∫ z in V, r ^ d * (cutoffCoefficient M H omega N (r • z + y) *
            Homogenization.vecDot (etaH.grad (r • z + y))
              (etaH.grad (r • z + y))) ∂volume := by
        rw [integral_const_mul]
      _ = ∫ z in V, cscale *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * r ^ d * (r⁻¹) ^ 2 *
            (cutoffCoefficient M H (T omega) m z *
              Homogenization.vecDot (chi.grad z) (chi.grad z)) ∂volume := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hcoefscale z, hetaHgradscale z]
        simp only [Homogenization.vecDot_smul_left,
          Homogenization.vecDot_smul_right]
        ring
      _ = cscale * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * r ^ d * (r⁻¹) ^ 2 *
          (∫ z in V, cutoffCoefficient M H (T omega) m z *
            Homogenization.vecDot (chi.grad z) (chi.grad z) ∂volume) := by
        rw [integral_const_mul]
  have hvar2 := hvar
  rw [hleftscale, henergyscale] at hvar2
  have hresid :
      (∫ z in V, cutoffSpeedDensity M H (T omega) m z *
          (uDil.toFun z - chi.toFun z) ^ 2 ∂volume) ≤
        t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
          (∫ z in V, cutoffCoefficient M H (T omega) m z *
            Homogenization.vecDot (chi.grad z) (chi.grad z) ∂volume) := by
    refine le_of_mul_le_mul_left ?_ (mul_pos hcscale (pow_pos hr d))
    calc
      cscale * r ^ d *
            (∫ z in V, cutoffSpeedDensity M H (T omega) m z *
              (uDil.toFun z - chi.toFun z) ^ 2 ∂volume) ≤
          t * (cscale * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * r ^ d * (r⁻¹) ^ 2 *
            (∫ z in V, cutoffCoefficient M H (T omega) m z *
              Homogenization.vecDot (chi.grad z) (chi.grad z) ∂volume)) := by
        simpa only [energy, mul_assoc] using! hvar2
      _ = cscale * r ^ d *
          (t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
            (∫ z in V, cutoffCoefficient M H (T omega) m z *
              Homogenization.vecDot (chi.grad z) (chi.grad z) ∂volume)) := by
        ring
  have hresidBound :
      (∫ z in V, cutoffSpeedDensity M H (T omega) m z *
          (uDil.toFun z - chi.toFun z) ^ 2 ∂volume) ≤
        t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
          (Kbase (T omega) * (4 : ℝ) ^ B) := by
    calc
      _ ≤ t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
          (∫ z in V, cutoffCoefficient M H (T omega) m z *
            Homogenization.vecDot (chi.grad z) (chi.grad z) ∂volume) := hresid
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hchiEnergyBound
        have ham : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M m :=
          SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M m
        have han : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
          SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
        positivity
  have hlocalBoundM : ∀ᵐ z ∂volume.restrict V,
      |cutoffSpeedDensity M H (T omega) m z| ≤ rhoMMax := by
    filter_upwards [hlocalBound] with z hz
    rw [hrhoscale z, abs_mul, abs_of_pos hcscale] at hz
    exact (le_div_iff₀ hcscale).2 (by simpa [mul_comm] using hz)
  have hresidInt : IntegrableOn
      (fun z => cutoffSpeedDensity M H (T omega) m z *
        (uDil.toFun z - chi.toFun z) ^ 2) V := by
    have h := integrableOn_mass_term hbcont.aestronglyMeasurable hlocalBoundM
      (uDil - chi.toH1Function).memL2 (uDil - chi.toH1Function).memL2
    simpa [H1Function.sub_toFun, pow_two, mul_assoc] using h
  have hresidNonneg : ∀ᵐ z ∂volume.restrict V,
      0 ≤ cutoffSpeedDensity M H (T omega) m z *
        (uDil.toFun z - chi.toFun z) ^ 2 := by
    filter_upwards with z
    exact mul_nonneg (hbpos z).le (sq_nonneg _)
  have huCapDil : uCap.toFun =ᵐ[volume.restrict V] uDil.toFun :=
    huCapfun.trans huNonnegfun
  have huCap1Dil : uCap1.toFun =ᵐ[volume.restrict V1] uDil.toFun := by
    have hrestrict := ae_restrict_of_ae_restrict_of_subset hV1sub huCapDil
    filter_upwards [hrestrict] with z hz
    simpa only [uCap1] using! hz
  have hwmInt : IntegrableOn
      (fun z => cutoffSpeedDensity M H (T omega) m z *
        (H1Function.const 1 - uCap1).toFun z ^ 2) V1 := by
    have h := integrableOn_mass_term hbcont.aestronglyMeasurable hlocalBound1
      (H1Function.const 1 - uCap1).memL2
      (H1Function.const 1 - uCap1).memL2
    simpa [H1Function.sub_toFun, pow_two, mul_assoc] using h
  have hwmEq : ∀ᵐ z ∂volume.restrict V1,
      (H1Function.const 1 - uCap1).toFun z ^ 2 *
          cutoffSpeedDensity M H (T omega) m z =
        cutoffSpeedDensity M H (T omega) m z *
          (uDil.toFun z - chi.toFun z) ^ 2 := by
    filter_upwards [huCap1Dil,
      ae_restrict_mem hV1open.measurableSet] with z hz hzmem
    simp only [H1Function.sub_toFun, H1Function.const_apply]
    rw [hz, hchi1 z hzmem]
    ring
  have hwmRealBound :
      (∫ z in V1, cutoffSpeedDensity M H (T omega) m z *
        (H1Function.const 1 - uCap1).toFun z ^ 2 ∂volume) ≤
      t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
        (Kbase (T omega) * (4 : ℝ) ^ B) := by
    calc
      (∫ z in V1, cutoffSpeedDensity M H (T omega) m z *
        (H1Function.const 1 - uCap1).toFun z ^ 2 ∂volume) =
        ∫ z in V1, cutoffSpeedDensity M H (T omega) m z *
          (uDil.toFun z - chi.toFun z) ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards [hwmEq] with z hz
        simpa [mul_comm] using hz
      _ ≤ _ := (setIntegral_mono_set hresidInt hresidNonneg
        (Filter.Eventually.of_forall (fun z hz => hV1sub hz))).trans hresidBound
  have hweightedEq :
      (∫⁻ z in V1, ENNReal.ofReal ((H1Function.const 1 - uCap1).toFun z ^ 2 *
        cutoffSpeedDensity M H (T omega) m z) ∂volume) =
      ENNReal.ofReal (∫ z in V1, cutoffSpeedDensity M H (T omega) m z *
        (H1Function.const 1 - uCap1).toFun z ^ 2 ∂volume) := by
    exact aux_tight_fast_exit_weighted_lintegral
      hV1open.measurableSet hbcont.aestronglyMeasurable
      ((H1Function.const 1 - uCap1).memL2.aestronglyMeasurable.pow 2)
      (by filter_upwards with z; exact (hbpos z).le)
      (by filter_upwards with z; positivity)
      hwmInt
  have hweightedBound :
      (∫⁻ z in V1, ENNReal.ofReal ((H1Function.const 1 - uCap1).toFun z ^ 2 *
        cutoffSpeedDensity M H (T omega) m z) ∂volume) ≤
      ENNReal.ofReal (t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
        (Kbase (T omega) * (4 : ℝ) ^ B)) := by
    rw [hweightedEq]
    exact ENNReal.ofReal_le_ofReal hwmRealBound
  have hmoserBound : ∀ᵐ z ∂volume.restrict
      (Metric.ball (0 : Homogenization.Vec d) (3 * (1 / 27 : ℚ) / 2)),
      ENNReal.ofReal ((H1Function.const 1 - uCap1).toFun z) ≤
        ENNReal.ofReal (Cmos * Kbase (T omega) ^ Bm) *
          (ENNReal.ofReal (t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
            (Kbase (T omega) * (4 : ℝ) ^ B))) ^ (1 / 2 : ℝ) := by
    have hweightedBound' :
        (∫⁻ q in Metric.ball (0 : Homogenization.Vec d)
            (3 * (1 / 9 : ℚ) / 2),
            ENNReal.ofReal ((H1Function.const 1 - uCap1).toFun q ^ 2 *
              cutoffSpeedDensity M H (T omega) m q)) ≤
          ENNReal.ofReal (t * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (r⁻¹) ^ 2 *
            (Kbase (T omega) * (4 : ℝ) ^ B)) := by
      change (∫⁻ q in V1, ENNReal.ofReal ((H1Function.const 1 - uCap1).toFun q ^ 2 *
        cutoffSpeedDensity M H (T omega) m q)) ≤ _
      exact hweightedBound
    exact hmoser.mono fun z hz =>
      hz.trans (mul_le_mul_of_nonneg_left
        (ENNReal.rpow_le_rpow hweightedBound' (by norm_num))
        (by positivity))
  have hsmallsub : Metric.ball (0 : Homogenization.Vec d)
      (3 * ((1 / 27 : ℚ) : ℝ) / 2) ⊆ V1 := by
    dsimp [V1]
    apply Metric.ball_subset_ball
    norm_num
  have huCap1DilSmall : uCap1.toFun =ᵐ[volume.restrict
      (Metric.ball (0 : Homogenization.Vec d)
        (3 * ((1 / 27 : ℚ) : ℝ) / 2))] uDil.toFun := by
    exact ae_restrict_of_ae_restrict_of_subset hsmallsub huCap1Dil


  have hpost := aux_tight_fast_exit_post_moser
    M H KN hKN L hL N m y omega B Cmos Bm Btot hCmos hBtot Kbase T hKbaseone
    r t t0 hr ht ht0 (by rfl) U hUopen hUV V V1 etaM u uDil uCap1 hueq
    hrhoCoeffMeas rhoLo rhoMax hrhoLo hrhoHi huDilfun hmoserBound
    huCap1DilSmall hetaMmeas hetaM0 hetaM1 hmk hfd x
    (by simpa [r] using hx)
  have hradius : r / 2 = (3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2 := by
    rfl
  have hF_eq : r ^ 2 * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M m =
      (3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m := by
    dsimp [r]
    rw [aux_tight_fast_exit_zpow_square]
  rw [hradius, hF_eq] at hpost
  exact hpost

theorem tight_fast_exit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 → ∃ C : ℝ, 0 < C ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (_hKN : ∀ N, IsMarkovKernel (KN N))
        (_hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (_hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (_hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
        (N m : ℕ) (y : SpatialCoordinates d),
        ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ omega, 0 ≤ K omega) ∧
          ∫⁻ omega, ENNReal.ofReal (K omega) ∂(chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal C ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
            ∀ x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 18),
              (KN N (omega, x))
                  {path : DiffusionPath d |
                    ContinuousPath.exitTime
                      (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) path ≤
                      ENNReal.ofReal t} ≤
                ENNReal.ofReal (K omega * Real.sqrt (t /
                  ((3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))) := by
  obtain ⟨B, hB, hstatic⟩ := tight_static hd Jc Pc Xc Sf W Cp
  obtain ⟨Cmos, Bm, hCmos, hBm, hmos⟩ :=
    tight_subharmonic hd B 3 hB (by norm_num) (1 / 27 : ℚ) (1 / 9 : ℚ)
      (by norm_num) (by norm_num) (by norm_num)
  let Btot : ℝ := Bm + (1 / 2 : ℝ)
  have hBtot : 0 < Btot := by
    dsimp only [Btot]
    linarith
  obtain ⟨delta0, hdelta0, hstaticBm⟩ :=
    hstatic (max 1 Btot) (le_max_left _ _)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It hMd
  obtain ⟨Cstat, hCstat, hCdata⟩ := hstaticBm M Rm Sreg It hMd 3 (by norm_num)
  refine ⟨8 * Cmos * (4 : ℝ) ^ (B / 2) * Cstat, by positivity, ?_⟩
  intro H hH PN KN hKN hin L hL hLloc N m y
  obtain ⟨Kbase, hKbasemeas, hKbaseone, hKbasemoment, hKbaseest⟩ := hCdata H hH m
  obtain ⟨T, hTpres, hscale⟩ := tight_scale_covariance hd M H hH N m y
  let K0 : BilateralField d → ℝ := fun omega => Kbase (T omega)
  have hKbaseestT : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      tight_static_estimates (cutoffSpeedDensity M H (T omega) m)
        (cutoffCoefficient M H (T omega) m) 3 (Kbase (T omega)) B := by
    have hmap : ∀ᵐ z ∂Measure.map T (chaosSampleLaw M).toMeasure,
        tight_static_estimates (cutoffSpeedDensity M H z m)
          (cutoffCoefficient M H z m) 3 (Kbase z) B := by
      rw [hTpres.map_eq]
      exact hKbaseest
    exact ae_of_ae_map hTpres.measurable.aemeasurable hmap
  have hK0meas : Measurable K0 := hKbasemeas.comp hTpres.measurable
  have hK0one : ∀ omega, 1 ≤ K0 omega := fun omega => hKbaseone (T omega)
  have hK0moment :
      ∫⁻ omega, ENNReal.ofReal (K0 omega ^ max 1 Btot)
          ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cstat := by
    calc
      ∫⁻ omega, ENNReal.ofReal (K0 omega ^ max 1 Btot)
          ∂(chaosSampleLaw M).toMeasure =
          ∫⁻ omega, ENNReal.ofReal (Kbase omega ^ max 1 Btot)
            ∂Measure.map T (chaosSampleLaw M).toMeasure := by
        symm
        exact MeasureTheory.lintegral_map
          ((Real.continuous_rpow_const (by positivity)).measurable.ennreal_ofReal.comp
            hKbasemeas) hTpres.measurable
      _ = ∫⁻ omega, ENNReal.ofReal (Kbase omega ^ max 1 Btot)
          ∂(chaosSampleLaw M).toMeasure := by rw [hTpres.map_eq]
      _ ≤ ENNReal.ofReal Cstat := hKbasemoment


  have hKbaseoneT : ∀ omega, 1 ≤ Kbase (T omega) := by
    intro omega
    exact hKbaseone (T omega)
  have hscaled_resolvent_and_moser :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
        ∀ x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 18),
          (KN N (omega, x))
              {path : DiffusionPath d |
                ContinuousPath.exitTime
                  (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) path ≤
                  ENNReal.ofReal t} ≤
            ENNReal.ofReal (8 * Cmos * (4 : ℝ) ^ (B / 2) * (K0 omega) ^ Btot * Real.sqrt (t /
              ((3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))) := by
    have hlocalMarkov :
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ j,
          IsMarkovKernel (L j omega) := by
      filter_upwards [hLloc] with omega hD
      intro j
      exact isMarkovKernel_of_localDiffusion (hD j)
    have hlocalFinite :
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ j,
          (weightedMeasure (cutoffSpeedDensity M H omega j))
              (Metric.ball y
                ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) ≠ ∞ := by
      filter_upwards [hLloc] with omega hD
      intro j
      exact weightedMeasure_ne_top_of_localDiffusion (hD j) Metric.isOpen_ball
        (Metric.isBounded_ball)
    have hfdd := in_cutoff_fdd_start_continuity hd M H hH PN KN hin
    filter_upwards [hlocalMarkov, hlocalFinite, hLloc, hscale, hKbaseestT, hfdd] with
      omega hmk hfin hD hsc hest hfd
    exact aux_tight_fast_exit_scaled_resolvent_and_moser_pointwise
      hd M H hH PN KN hKN hin L hL N m y
      B Cmos Bm Btot hCmos (by rfl) hmos Kbase hKbaseone T hKbaseoneT
      omega hmk hfin hD hsc hest (hfd N)

  have hmoment_and_measurability :
      ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ omega, 0 ≤ K omega) ∧
        ∫⁻ omega, ENNReal.ofReal (K omega) ∂(chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (8 * Cmos * (4 : ℝ) ^ (B / 2) * Cstat) ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
          ∀ x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 18),
            (KN N (omega, x))
                {path : DiffusionPath d |
                  ContinuousPath.exitTime
                    (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - (N : ℤ)) / 2)) path ≤
                    ENNReal.ofReal t} ≤
              ENNReal.ofReal (K omega * Real.sqrt (t /
                ((3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N /
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))) := by
    refine ⟨fun omega => 8 * Cmos * (4 : ℝ) ^ (B / 2) * (K0 omega) ^ Btot,
      ?_, ?_, ?_, ?_⟩
    · exact (measurable_const.mul
        ((Real.continuous_rpow_const hBtot.le).measurable.comp hK0meas))
    · intro omega
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCmos.le)
          (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg (zero_le_one.trans (hK0one omega)) _)
    · exact aux_tight_fast_exit_moment_transfer hK0meas hK0one
        (by positivity) hBtot.le (le_max_right _ _) hK0moment
    · filter_upwards [hscaled_resolvent_and_moser] with omega homega
      simpa only using homega
  exact hmoment_and_measurability

end SubdiffusiveProcess.Paper
