module

public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.lem_killing
public import SubdiffusiveProcess.Paper.cube_exhaustion
public import SubdiffusiveProcess.Paper.limit_kernel
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
public import SubdiffusiveProcess.Paper.cor_as_resolvent
public import SubdiffusiveProcess.Paper.lem_determining
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Probability.PathLawMetricSeparation
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import MarkovProcess.Trajectory.CylinderAlgebra
public import MarkovProcess.Trajectory.WeakContinuity
public import MarkovProcess.Continuity.PathModulus
public import MarkovProcess.Continuity.PathTightness
public import MarkovProcess.Path.ClosedSetDetection
public import Mathlib.MeasureTheory.Measure.Tight
public import SubdiffusiveProcess.Model.LifetimeProcess
public import MarkovProcess.Path.ExitTimeShift
public import MarkovProcess.Path.RandomShiftMeasurability
public import MarkovProcess.Lifetime.ExitTimeStopping


@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators
open scoped BoundedContinuousFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ### RtpBase -/

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- The `StrongMarkov` identity of the lifetime-path law, transported to continuous paths
(copied from `finite_cutoff_local_path_bounds`, `aux_soft_sm_transport`). -/
theorem aux_lem_resolvents_to_paths_sm_transport {d : ℕ}
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (hSM : StrongMarkov L)
    (x : SpatialCoordinates d) (T : Path d → ℝ≥0∞)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B)
    (g : Path d → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w | T w < w.lifetime}),
        g (LifetimePath.ofContinuousPath
          (ContinuousPath.shift (T (LifetimePath.ofContinuousPath p)).toNNReal p)) ∂K x =
      ∫⁻ p in LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w | T w < w.lifetime}),
        (∫⁻ q, g (LifetimePath.ofContinuousPath q)
          ∂K (p (T (LifetimePath.ofContinuousPath p)).toNNReal)) ∂K x := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hemb := LifetimePath.measurableEmbedding_ofContinuousPath (α := SpatialCoordinates d)
  have hTm : Measurable T := hT.measurable'
  have hS : MeasurableSet (B ∩ {w : Path d | T w < w.lifetime}) :=
    (hT.measurableSpace_le _ hB).inter
      (measurableSet_lt hTm LifetimePath.measurable_lifetime)
  have h := hSM.2.2 x T hT B hB g hg
  rw [← hL x, Measure.restrict_map hemb.measurable hS, hemb.lintegral_map,
    hemb.lintegral_map] at h
  simp only [SubdiffusiveProcess.Model.LifetimeProcess.shift_ofContinuousPath,
    SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath] at h
  rw [h]
  refine setLIntegral_congr_fun_ae (hemb.measurable hS) (ae_of_all _ fun p _ => ?_)
  rw [← hL, hemb.lintegral_map]

/-- Random time shift by a measurable time is measurable on path space. -/
theorem aux_lem_resolvents_to_paths_measurable_shift {d : ℕ}
    (τ : ContinuousPath (SpatialCoordinates d) → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun p : ContinuousPath (SpatialCoordinates d) => ContinuousPath.shift (τ p) p) :=
  ContinuousPath.continuous_shift.measurable.comp (hτ.prodMk measurable_id)

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Weighted strong Markov identity at the exit time of an open set.**  The identity of
`hSM`, which holds with indicator weights of the stopped σ-algebra, extends to every weight
measurable for (the continuous-path trace of) the stopped σ-algebra: both sides are integrals
of the weight against two measures that agree on that σ-algebra (compare their trims). -/
theorem aux_lem_resolvents_to_paths_sm_weighted {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (x : SpatialCoordinates d)
    (W : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞)
    (hW : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace] W)
    (g : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        W p * g (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p) ∂k x =
      ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        W p * ∫⁻ q, g q ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k x := by
  classical
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hemb := LifetimePath.measurableEmbedding_ofContinuousPath (α := SpatialCoordinates d)
  set hT := LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU with hTdef
  set f := LifetimePath.ofContinuousPath (α := SpatialCoordinates d) with hfdef
  set τ : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞ := ContinuousPath.exitTime U with hτdef
  set S : Set (ContinuousPath (SpatialCoordinates d)) := {p | τ p < ⊤} with hSdef
  have hm : MeasurableSpace.comap f hT.measurableSpace ≤
      (inferInstance : MeasurableSpace (ContinuousPath (SpatialCoordinates d))) :=
    (MeasurableSpace.comap_mono hT.measurableSpace_le).trans hemb.measurable.comap_le
  set g' : Path d → ℝ≥0∞ := Function.extend f g (fun _ => 0) with hg'def
  have hg' : Measurable g' := hemb.measurable_extend hg measurable_const
  have hg'f : ∀ p, g' (LifetimePath.ofContinuousPath p) = g p := fun p =>
    hemb.injective.extend_apply _ _ p
  have hτmeas : Measurable τ := ContinuousPath.measurable_exitTime U hU
  have hτnn : Measurable fun p => (τ p).toNNReal := ENNReal.measurable_toNNReal.comp hτmeas
  set F : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞ :=
    fun p => g (ContinuousPath.shift (τ p).toNNReal p) with hFdef
  set G : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞ :=
    fun p => ∫⁻ q, g q ∂k (p (τ p).toNNReal) with hGdef
  have hF : Measurable F := hg.comp (aux_lem_resolvents_to_paths_measurable_shift _ hτnn)
  have hG : Measurable G :=
    (hg.lintegral_kernel (κ := k)).comp (ContinuousPath.measurable_eval_of_measurable _ hτnn)
  have hSm : MeasurableSet S := measurableSet_lt hτmeas measurable_const
  have hid : ∀ A, MeasurableSet[MeasurableSpace.comap f hT.measurableSpace] A → ∫⁻ p in A ∩ S, F p ∂k x = ∫⁻ p in A ∩ S, G p ∂k x := by
    rintro A ⟨B, hB, rfl⟩
    have h := aux_lem_resolvents_to_paths_sm_transport (fun z => k z) L hL hSM x _ hT B hB g' hg'
    have hpre : f ⁻¹' (B ∩ {w | LifetimePath.exitTime U w < w.lifetime}) = f ⁻¹' B ∩ S := by
      ext p
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, hfdef, hSdef, hτdef,
        LifetimePath.exitTime_ofContinuousPath, LifetimePath.lifetime_ofContinuousPath]
    rw [hpre] at h
    simp only [hfdef, LifetimePath.exitTime_ofContinuousPath] at h
    simp only [hg'f] at h
    exact h
  have hWm : Measurable W := hW.mono hm le_rfl
  have e1 : ∫⁻ p in S, W p * F p ∂k x = ∫⁻ p, W p ∂(((k x).restrict S).withDensity F) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hF hWm]
    refine lintegral_congr fun p => ?_
    simp only [Pi.mul_apply]
    ring
  have e2 : ∫⁻ p in S, W p * G p ∂k x = ∫⁻ p, W p ∂(((k x).restrict S).withDensity G) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hG hWm]
    refine lintegral_congr fun p => ?_
    simp only [Pi.mul_apply]
    ring
  have htrim : (((k x).restrict S).withDensity F).trim hm =
      (((k x).restrict S).withDensity G).trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap f hT.measurableSpace) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA,
      withDensity_apply _ (hm _ hA), withDensity_apply _ (hm _ hA),
      Measure.restrict_restrict (hm _ hA)]
    exact hid A hA
  change ∫⁻ p in S, W p * F p ∂k x = ∫⁻ p in S, W p * G p ∂k x
  rw [e1, e2, ← lintegral_trim hm hW, ← lintegral_trim hm hW, htrim]


/-! ### RtpLimit -/

/-- The time-zero finite-dimensional attachment pins the starting point. -/
theorem aux_lem_resolvents_to_paths_start_pinned_of {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    ∀ y, K (omega, y) {z : DiffusionPath d | z 0 ≠ y} = 0 := by
  intro y
  have hev : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) :=
    Measurable.of_eval fun t => (continuous_eval_const ((t : ℝ≥0))).measurable
  have hfdd0 : (K (omega, y)).map (ContinuousPath.finsetEvaluation ({0} : Finset ℝ≥0))
      = SubMarkovKernelSemigroup.finiteSetKernel P ({0} : Finset ℝ≥0) y := by
    rw [← Kernel.map_apply K hev (omega, y)]
    exact hfdd ({0} : Finset ℝ≥0) y
  have heval := map_eval_eq_of_finsetEvaluation P (K (omega, y)) y 0 hfdd0
  have hev0 : Measurable (fun path : DiffusionPath d => path 0) :=
    (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0).measurable
  have hset : {z : DiffusionPath d | z 0 ≠ y}
      = (fun path : DiffusionPath d => path 0) ⁻¹' ({y}ᶜ) := rfl
  rw [hset, ← Measure.map_apply hev0 (measurableSet_singleton y).compl, heval,
    P.kernel_zero, Kernel.id_apply]
  simp

/-- One-time marginals from the finite-dimensional attachment. -/
theorem aux_lem_resolvents_to_paths_map_eval_of {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) (t : ℝ≥0) (y : SpatialCoordinates d) :
    (K (omega, y)).map (fun path : DiffusionPath d => path t) = P t y := by
  have hev : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) ({t} : Finset ℝ≥0)) :=
    Measurable.of_eval fun s => (continuous_eval_const ((s : ℝ≥0))).measurable
  have hfdd0 : (K (omega, y)).map (ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0))
      = SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) y := by
    rw [← Kernel.map_apply K hev (omega, y)]
    exact hfdd ({t} : Finset ℝ≥0) y
  exact map_eval_eq_of_finsetEvaluation P (K (omega, y)) y t hfdd0

/-- Closedness of "some time `s ≤ T` has `c ≤ Φ p s`" for a jointly continuous `Φ`. -/
theorem aux_lem_resolvents_to_paths_isClosed_exists_le {d : ℕ} (T : ℝ≥0)
    (Φ : DiffusionPath d → ℝ≥0 → ℝ)
    (hΦ : Continuous (fun q : DiffusionPath d × ℝ≥0 => Φ q.1 q.2)) (c : ℝ) :
    IsClosed {p : DiffusionPath d | ∃ s : ℝ≥0, s ≤ T ∧ c ≤ Φ p s} := by
  have hIic : IsCompact (Set.Iic T) := by
    have hIcc : IsCompact (Set.Icc (⊥ : ℝ≥0) T) := isCompact_Icc
    exact (Set.Icc_bot (α := ℝ≥0) (a := T)) ▸ hIcc
  have : CompactSpace (Set.Iic T) := isCompact_iff_compactSpace.mp hIic
  have hcont : Continuous (fun q : DiffusionPath d × Set.Iic T => Φ q.1 (q.2 : ℝ≥0)) :=
    hΦ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hC : IsClosed {q : DiffusionPath d × Set.Iic T | c ≤ Φ q.1 (q.2 : ℝ≥0)} :=
    isClosed_le continuous_const hcont
  have heq : {p : DiffusionPath d | ∃ s : ℝ≥0, s ≤ T ∧ c ≤ Φ p s}
      = Prod.fst '' {q : DiffusionPath d × Set.Iic T | c ≤ Φ q.1 (q.2 : ℝ≥0)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hc⟩
      exact ⟨(z, ⟨s, hs⟩), hc, rfl⟩
    · rintro ⟨⟨z', s⟩, hs, rfl⟩
      exact ⟨s, s.2, hs⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace (X := DiffusionPath d) (Y := Set.Iic T) _ hC

/-- **Dini-type uniformity.**  For a weakly continuous family of laws, a decreasing sequence
of closed events with empty intersection has uniformly small mass over a compact set. -/
theorem aux_lem_resolvents_to_paths_dini {X Ω : Type*} [TopologicalSpace X]
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (μ : X → ProbabilityMeasure Ω) (hμ : Continuous μ)
    (F : ℕ → Set Ω) (hFc : ∀ j, IsClosed (F j)) (hFa : Antitone F) (hF0 : ⋂ j, F j = ∅)
    (C : Set X) (hC : IsCompact C) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ j, ∀ y ∈ C, (μ y : Measure Ω) (F j) < ε := by
  classical
  have hj : ∀ y, ∃ j, (μ y : Measure Ω) (F j) < ε := by
    intro y
    have h := tendsto_measure_iInter_atTop (μ := (μ y : Measure Ω))
      (fun j => (hFc j).measurableSet.nullMeasurableSet) hFa ⟨0, measure_ne_top _ _⟩
    rw [hF0, measure_empty] at h
    exact (h.eventually (gt_mem_nhds hε)).exists
  choose J hJ using hj
  have hnhds : ∀ y, {y' | (μ y' : Measure Ω) (F (J y)) < ε} ∈ 𝓝 y := by
    intro y
    have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hμ.tendsto y)
      (hFc (J y))
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim (hJ y))
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover
    (fun y => {y' | (μ y' : Measure Ω) (F (J y)) < ε}) (fun y _ => hnhds y)
  refine ⟨t.sup J, fun y hy => ?_⟩
  obtain ⟨y0, hy0t, hy'⟩ := Set.mem_iUnion₂.mp (hcover hy)
  exact lt_of_le_of_lt (measure_mono (hFa (Finset.le_sup hy0t))) hy'

/-- **Short exits of a weakly continuous family started at its point**, uniformly over a
compact set of starting points (`mfd:prop-as-forms`: continuity in the start and continuity of
paths at time zero). -/
theorem aux_lem_resolvents_to_paths_limit_short_exit {d : ℕ}
    (μ : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d)) (hμ : Continuous μ)
    (hstart : ∀ y, (μ y : Measure (DiffusionPath d)) {p | p 0 ≠ y} = 0)
    (C : Set (SpatialCoordinates d)) (hC : IsCompact C) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ h : ℝ≥0, 0 < h ∧ ∀ y ∈ C,
      (μ y : Measure (DiffusionPath d))
        {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ (h : ℝ≥0∞)} < ε := by
  set F : ℕ → Set (DiffusionPath d) := fun j =>
    {p | ∃ s : ℝ≥0, s ≤ ((j : ℝ≥0) + 1)⁻¹ ∧ ρ ≤ dist (p s) (p 0)} with hFdef
  have hFc : ∀ j, IsClosed (F j) := fun j =>
    aux_lem_resolvents_to_paths_isClosed_exists_le _ (fun p s => dist (p s) (p 0))
      (continuous_eval.dist ((ContinuousPath.continuous_eval 0).comp continuous_fst)) ρ
  have hFa : Antitone F := by
    intro i j hij p hp
    obtain ⟨s, hs, hd⟩ := hp
    refine ⟨s, hs.trans ?_, hd⟩
    gcongr
  have hF0 : ⋂ j, F j = ∅ := by
    ext p
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    have hc : ContinuousAt p 0 := p.continuous.continuousAt
    obtain ⟨δ, hδ, hδp⟩ := Metric.continuousAt_iff.mp hc ρ hρ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    refine ⟨j, ?_⟩
    rintro ⟨s, hs, hd⟩
    have hs' : dist s 0 < δ := by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq]
      have : (s : ℝ) ≤ ((j : ℝ) + 1)⁻¹ := by
        have := NNReal.coe_le_coe.mpr hs
        simpa using this
      calc (s : ℝ) ≤ ((j : ℝ) + 1)⁻¹ := this
        _ = 1 / ((j : ℝ) + 1) := by rw [one_div]
        _ < δ := hj
    exact absurd (hδp hs') (not_lt.mpr hd)
  obtain ⟨j, hj⟩ := aux_lem_resolvents_to_paths_dini μ hμ F hFc hFa hF0 C hC ε hε
  refine ⟨((j : ℝ≥0) + 1)⁻¹, by positivity, fun y hy => ?_⟩
  refine lt_of_le_of_lt ?_ (hj y hy)
  calc (μ y : Measure (DiffusionPath d))
        {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ ((((j : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)}
      ≤ (μ y : Measure (DiffusionPath d)) (F j ∪ {p | p 0 ≠ y}) := by
        refine measure_mono fun p hp => ?_
        simp only [Set.mem_ofPred_eq] at hp
        by_cases h0 : p 0 = y
        · left
          obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _ Metric.isOpen_ball
            _ p).mp hp
          refine ⟨s, s.2, ?_⟩
          have hs' : p s ∉ Metric.ball y ρ := hs
          rw [Metric.mem_ball, not_lt] at hs'
          rw [h0]
          exact hs'
        · right
          exact h0
    _ ≤ (μ y : Measure (DiffusionPath d)) (F j) + (μ y : Measure (DiffusionPath d)) {p | p 0 ≠ y} :=
        measure_union_le _ _
    _ = (μ y : Measure (DiffusionPath d)) (F j) := by rw [hstart y, add_zero]

/-- **Compact containment for a weakly continuous family**, uniformly over a compact set of
starting points (`mfd:prop-as-forms`: conservativeness and continuity of the limiting kernel). -/
theorem aux_lem_resolvents_to_paths_limit_containment {d : ℕ}
    (μ : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d)) (hμ : Continuous μ)
    (C : Set (SpatialCoordinates d)) (hC : IsCompact C) (S : ℝ≥0)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ C,
      (μ y : Measure (DiffusionPath d)) {p | ∃ s : ℝ≥0, s ≤ S ∧ R ≤ ‖p s‖} < ε := by
  set F : ℕ → Set (DiffusionPath d) := fun j =>
    {p | ∃ s : ℝ≥0, s ≤ S ∧ (j : ℝ) + 1 ≤ ‖p s‖} with hFdef
  have hFc : ∀ j, IsClosed (F j) := fun j =>
    aux_lem_resolvents_to_paths_isClosed_exists_le _ (fun p s => ‖p s‖)
      continuous_eval.norm _
  have hFa : Antitone F := by
    intro i j hij p hp
    obtain ⟨s, hs, hd⟩ := hp
    refine ⟨s, hs, le_trans ?_ hd⟩
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hF0 : ⋂ j, F j = ∅ := by
    ext p
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    have hIcc : IsCompact (Set.Icc (0 : ℝ≥0) S) := isCompact_Icc
    obtain ⟨M, hM⟩ := (hIcc.image p.continuous).isBounded.exists_norm_le
    obtain ⟨j, hj⟩ := exists_nat_gt M
    refine ⟨j, ?_⟩
    rintro ⟨s, hs, hd⟩
    have := hM (p s) ⟨s, ⟨bot_le, hs⟩, rfl⟩
    linarith
  obtain ⟨j, hj⟩ := aux_lem_resolvents_to_paths_dini μ hμ F hFc hFa hF0 C hC ε hε
  exact ⟨(j : ℝ) + 1, by positivity, hj⟩


/-! ### RtpKilled -/

/-- The killed discounted occupation functional appearing in `hkilled`. -/
def aux_lem_resolvents_to_paths_kf {d : ℕ} (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (path : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Set.indicator
    {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
    (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t

/-- The whole-space discounted occupation functional. -/
def aux_lem_resolvents_to_paths_wf {d : ℕ} (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (path : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) * f (path (Real.toNNReal t))

theorem aux_lem_resolvents_to_paths_integral_exp_Ioi {lam : ℝ} (hlam : 0 < lam) (T : ℝ) :
    ∫ t in Set.Ioi T, Real.exp (-lam * t) = Real.exp (-lam * T) / lam := by
  rw [integral_exp_mul_Ioi (by linarith) T]
  field_simp

theorem aux_lem_resolvents_to_paths_integral_exp_Ioc {lam : ℝ} (hlam : 0 < lam) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ t in Set.Ioc 0 T, Real.exp (-lam * t) = (1 - Real.exp (-lam * T)) / lam := by
  have hU : Set.Ioc (0 : ℝ) T ∪ Set.Ioi T = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hT
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) T) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hlam
  have h := setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set (by rw [← hU]; exact Set.subset_union_left))
    (hint.mono_set (by rw [← hU]; exact Set.subset_union_right))
  rw [hU, aux_lem_resolvents_to_paths_integral_exp_Ioi hlam 0,
    aux_lem_resolvents_to_paths_integral_exp_Ioi hlam T] at h
  simp only [mul_zero, Real.exp_zero] at h
  rw [sub_div]
  linarith

/-- Joint measurability of the killed integrand. -/
theorem aux_lem_resolvents_to_paths_kf_integrand_measurable {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (fun q : DiffusionPath d × ℝ => Set.indicator
      {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U q.1}
      (fun s => Real.exp (-lam * s) * f (q.1 (Real.toNNReal s))) q.2) := by
  have hset : MeasurableSet {q : DiffusionPath d × ℝ |
      ENNReal.ofReal q.2 < ContinuousPath.exitTime U q.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_fst)
  have hev : Continuous (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hg : Measurable (fun q : DiffusionPath d × ℝ =>
      Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (hf.comp hev.measurable)
  have heq : (fun q : DiffusionPath d × ℝ => Set.indicator
      {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U q.1}
      (fun s => Real.exp (-lam * s) * f (q.1 (Real.toNNReal s))) q.2) =
      Set.indicator {q : DiffusionPath d × ℝ |
        ENNReal.ofReal q.2 < ContinuousPath.exitTime U q.1}
        (fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))) := by
    funext q
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [heq]
  exact hg.indicator hset

theorem aux_lem_resolvents_to_paths_measurable_kf {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (aux_lem_resolvents_to_paths_kf U lam f) := by
  have h := (aux_lem_resolvents_to_paths_kf_integrand_measurable U hU lam f hf).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

theorem aux_lem_resolvents_to_paths_measurable_wf {d : ℕ} (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (aux_lem_resolvents_to_paths_wf (d := d) lam f) := by
  have hev : Continuous (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hg : Measurable (fun q : DiffusionPath d × ℝ =>
      Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (hf.comp hev.measurable)
  exact (hg.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

/-- Bound of the killed functional by `‖f‖ / λ` (general form). -/
theorem aux_lem_resolvents_to_paths_abs_kf_le {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) (path : DiffusionPath d) :
    |aux_lem_resolvents_to_paths_kf U lam f path| ≤ M / lam := by
  unfold aux_lem_resolvents_to_paths_kf
  rw [← Real.norm_eq_abs]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (path 0))
  have hg : Integrable (fun t : ℝ => M * Real.exp (-lam * t)) (volume.restrict (Set.Ioi (0:ℝ))) :=
    (exp_neg_integrableOn_Ioi 0 hlam).const_mul M
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ‖Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖
        ≤ M * Real.exp (-lam * t) := by
    refine Eventually.of_forall (fun t => ?_)
    calc ‖Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖
        ≤ ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ := norm_indicator_le_norm_self _ t
      _ = Real.exp (-lam * t) * |f (path (Real.toNNReal t))| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-lam * t) * M := mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le
      _ = M * Real.exp (-lam * t) := by ring
  calc _ ≤ ∫ t in Set.Ioi (0:ℝ), M * Real.exp (-lam * t) := norm_integral_le_of_norm_le hg hpt
    _ = M / lam := by
        rw [integral_const_mul, aux_lem_resolvents_to_paths_integral_exp_Ioi hlam 0]
        simp only [mul_zero, Real.exp_zero]
        ring

theorem aux_lem_resolvents_to_paths_kf_nonneg {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z) (path : DiffusionPath d) :
    0 ≤ aux_lem_resolvents_to_paths_kf U lam f path := by
  unfold aux_lem_resolvents_to_paths_kf
  refine integral_nonneg fun t => ?_
  exact Set.indicator_nonneg (fun s _ => mul_nonneg (Real.exp_pos _).le (hf0 _)) t

/-- Upper bound: if `f ∈ [0, 1]` vanishes along the path on `(0, T0]` (while alive), the
killed functional is at most `e^{-λ T0} / λ`. -/
theorem aux_lem_resolvents_to_paths_kf_le_of_vanish {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hf1 : ∀ z, f z ≤ 1) (hf : Measurable f) (path : DiffusionPath d) {T0 : ℝ} (hT0 : 0 ≤ T0)
    (hvan : ∀ s : ℝ, 0 < s → s ≤ T0 → f (path (Real.toNNReal s)) = 0) :
    aux_lem_resolvents_to_paths_kf U lam f path ≤ Real.exp (-lam * T0) / lam := by
  unfold aux_lem_resolvents_to_paths_kf
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hlam
  have hle : ∀ t ∈ Set.Ioi (0 : ℝ), Set.indicator
      {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t ≤
      Set.indicator (Set.Ioi T0) (fun t => Real.exp (-lam * t)) t := by
    intro t ht
    by_cases htT : T0 < t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioi T0 from htT)]
      have hb : Real.exp (-lam * t) * f (path (Real.toNNReal t)) ≤ Real.exp (-lam * t) := by
        calc _ ≤ Real.exp (-lam * t) * 1 :=
              mul_le_mul_of_nonneg_left (hf1 _) (Real.exp_pos _).le
          _ = _ := mul_one _
      by_cases hA : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      · rw [Set.indicator_of_mem hA]; exact hb
      · rw [Set.indicator_of_notMem hA]; exact (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi T0 from htT)]
      have h0 : f (path (Real.toNNReal t)) = 0 := hvan t ht (not_lt.mp htT)
      simp only [Set.indicator, h0, mul_zero, ite_self, le_refl]
  have hint2 : IntegrableOn (fun t => Set.indicator (Set.Ioi T0)
      (fun t => Real.exp (-lam * t)) t) (Set.Ioi 0) :=
    hint.indicator measurableSet_Ioi
  have hint1 : IntegrableOn (fun t => Set.indicator
      {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) (Set.Ioi 0) := by
    refine Integrable.mono' hint ?_ ?_
    · have hm : Measurable (fun t : ℝ => Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) := by
        refine Measurable.indicator ?_ (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
        exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
          (hf.comp (path.continuous.comp continuous_real_toNNReal).measurable)
      exact hm.aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      calc ‖Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
            (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖
          ≤ ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ := norm_indicator_le_norm_self _ t
        _ ≤ Real.exp (-lam * t) := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            abs_of_nonneg (hf0 _)]
          calc Real.exp (-lam * t) * f (path (Real.toNNReal t)) ≤ Real.exp (-lam * t) * 1 :=
                mul_le_mul_of_nonneg_left (hf1 _) (Real.exp_pos _).le
            _ = Real.exp (-lam * t) := mul_one _
  calc _ ≤ ∫ t in Set.Ioi (0:ℝ), Set.indicator (Set.Ioi T0) (fun t => Real.exp (-lam * t)) t :=
        setIntegral_mono_on hint1 hint2 measurableSet_Ioi hle
    _ = ∫ t in Set.Ioi T0, Real.exp (-lam * t) := by
        rw [setIntegral_indicator measurableSet_Ioi,
          Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hT0)]
    _ = Real.exp (-lam * T0) / lam := aux_lem_resolvents_to_paths_integral_exp_Ioi hlam T0

theorem aux_lem_resolvents_to_paths_kf_integrand_integrableOn {d : ℕ}
    (U : Set (SpatialCoordinates d)) {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (path : DiffusionPath d) :
    IntegrableOn (fun t => Set.indicator
      {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) (Set.Ioi 0) := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-lam * t)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam).const_mul M
  refine Integrable.mono' hint ?_ ?_
  · have hm : Measurable (fun t : ℝ => Set.indicator
        {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) := by
      refine Measurable.indicator ?_ (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
      exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
        (hf.comp (path.continuous.comp continuous_real_toNNReal).measurable)
    exact hm.aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    calc ‖Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖
        ≤ ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ := norm_indicator_le_norm_self _ t
      _ = Real.exp (-lam * t) * |f (path (Real.toNNReal t))| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-lam * t) * M := mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le
      _ = M * Real.exp (-lam * t) := by ring

/-- Lower bound: if the path is alive with `f ≥ 1` on `(0, T1]`, the killed functional is at
least `(1 - e^{-λ T1}) / λ`. -/
theorem aux_lem_resolvents_to_paths_kf_ge_of_one {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (path : DiffusionPath d) {T1 : ℝ}
    (hT1 : 0 ≤ T1)
    (hone : ∀ s : ℝ, 0 < s → s ≤ T1 →
      ENNReal.ofReal s < ContinuousPath.exitTime U path ∧ 1 ≤ f (path (Real.toNNReal s))) :
    (1 - Real.exp (-lam * T1)) / lam ≤ aux_lem_resolvents_to_paths_kf U lam f path := by
  unfold aux_lem_resolvents_to_paths_kf
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hlam
  have hle : ∀ t ∈ Set.Ioi (0 : ℝ),
      Set.indicator (Set.Ioc 0 T1) (fun t => Real.exp (-lam * t)) t ≤
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t := by
    intro t ht
    by_cases htT : t ≤ T1
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 T1 from ⟨ht, htT⟩)]
      obtain ⟨hA, h1⟩ := hone t ht htT
      rw [Set.indicator_of_mem (show t ∈ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime U path} from hA)]
      calc Real.exp (-lam * t) = Real.exp (-lam * t) * 1 := (mul_one _).symm
        _ ≤ Real.exp (-lam * t) * f (path (Real.toNNReal t)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioc 0 T1 from fun h => htT h.2)]
      exact Set.indicator_nonneg (fun s _ => mul_nonneg (Real.exp_pos _).le (hf0 _)) t
  calc (1 - Real.exp (-lam * T1)) / lam = ∫ t in Set.Ioc 0 T1, Real.exp (-lam * t) :=
        (aux_lem_resolvents_to_paths_integral_exp_Ioc hlam hT1).symm
    _ = ∫ t in Set.Ioi (0:ℝ), Set.indicator (Set.Ioc 0 T1) (fun t => Real.exp (-lam * t)) t := by
        rw [setIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
    _ ≤ _ := setIntegral_mono_on (hint.indicator measurableSet_Ioc)
        (aux_lem_resolvents_to_paths_kf_integrand_integrableOn U hlam f hf M hM path)
        measurableSet_Ioi hle

/-- With `f = 1`, an exit by time `S` caps the killed functional by `(1 - e^{-λ S}) / λ`. -/
theorem aux_lem_resolvents_to_paths_kf_one_le_of_exit {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (path : DiffusionPath d) {S : ℝ} (hS : 0 ≤ S)
    (hτ : ContinuousPath.exitTime U path ≤ ENNReal.ofReal S) :
    aux_lem_resolvents_to_paths_kf U lam (fun _ => (1 : ℝ)) path ≤
      (1 - Real.exp (-lam * S)) / lam := by
  unfold aux_lem_resolvents_to_paths_kf
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hlam
  have hle : ∀ t ∈ Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s => Real.exp (-lam * s) * (fun _ => (1 : ℝ)) (path (Real.toNNReal s))) t ≤
      Set.indicator (Set.Ioc 0 S) (fun t => Real.exp (-lam * t)) t := by
    intro t ht
    by_cases hA : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
    · rw [Set.indicator_of_mem hA]
      have htS : t ≤ S := by
        have h1 : ENNReal.ofReal t < ENNReal.ofReal S := lt_of_lt_of_le hA hτ
        exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).mp h1).le
      rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 S from ⟨ht, htS⟩), mul_one]
    · rw [Set.indicator_of_notMem hA]
      exact Set.indicator_nonneg (fun s _ => (Real.exp_pos _).le) t
  calc _ ≤ ∫ t in Set.Ioi (0:ℝ), Set.indicator (Set.Ioc 0 S) (fun t => Real.exp (-lam * t)) t :=
        setIntegral_mono_on
          (aux_lem_resolvents_to_paths_kf_integrand_integrableOn U hlam _ measurable_const 1
            (fun _ => by simp) path)
          (hint.indicator measurableSet_Ioc) measurableSet_Ioi hle
    _ = ∫ t in Set.Ioc 0 S, Real.exp (-lam * t) := by
        rw [setIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
    _ = (1 - Real.exp (-lam * S)) / lam := aux_lem_resolvents_to_paths_integral_exp_Ioc hlam hS

/-- **Whole versus killed.**  The whole-space and killed functionals differ by at most
`M / λ` on an exit by time `S`, and by at most `M e^{-λ S} / λ` otherwise. -/
theorem aux_lem_resolvents_to_paths_abs_wf_sub_kf_le {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) (path : DiffusionPath d) {S : ℝ} (hS : 0 ≤ S) :
    |aux_lem_resolvents_to_paths_wf lam f path - aux_lem_resolvents_to_paths_kf U lam f path| ≤
      M / lam * (Set.indicator {p : DiffusionPath d |
        ContinuousPath.exitTime U p ≤ ENNReal.ofReal S} (fun _ => (1 : ℝ)) path +
        Real.exp (-lam * S)) := by
  unfold aux_lem_resolvents_to_paths_wf aux_lem_resolvents_to_paths_kf
  set A : Set ℝ := {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path} with hAdef
  set g : ℝ → ℝ := fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s)) with hgdef
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (path 0))
  have hAm : MeasurableSet A := measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hgm : Measurable g := (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    (hf.comp (path.continuous.comp continuous_real_toNNReal).measurable)
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-lam * t)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam).const_mul M
  have hgb : ∀ t, ‖g t‖ ≤ M * Real.exp (-lam * t) := by
    intro t
    rw [hgdef, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-lam * t) * |f (path (Real.toNNReal t))| ≤ Real.exp (-lam * t) * M :=
          mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le
      _ = M * Real.exp (-lam * t) := by ring
  have hgi : IntegrableOn g (Set.Ioi 0) :=
    Integrable.mono' hint hgm.aestronglyMeasurable (Eventually.of_forall hgb)
  have hdiff : (∫ t in Set.Ioi (0:ℝ), g t) - ∫ t in Set.Ioi (0:ℝ), A.indicator g t =
      ∫ t in Set.Ioi (0:ℝ), Aᶜ.indicator g t := by
    rw [← integral_sub hgi (hgi.indicator hAm)]
    congr 1
    funext t
    by_cases ht : t ∈ A
    · simp [Set.indicator_of_mem ht, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ht)]
    · simp [Set.indicator_of_notMem ht, Set.indicator_of_mem (Set.mem_compl ht)]
  change |(∫ t in Set.Ioi (0:ℝ), g t) - ∫ t in Set.Ioi (0:ℝ), A.indicator g t| ≤ _
  rw [hdiff]
  by_cases hτ : ContinuousPath.exitTime U path ≤ ENNReal.ofReal S
  · rw [Set.indicator_of_mem (show path ∈ {p : DiffusionPath d |
      ContinuousPath.exitTime U p ≤ ENNReal.ofReal S} from hτ)]
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in Set.Ioi (0:ℝ), Aᶜ.indicator g t‖ ≤ ∫ t in Set.Ioi (0:ℝ), M * Real.exp (-lam * t) :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall fun t =>
            (norm_indicator_le_norm_self _ t).trans (hgb t))
      _ = M / lam := by
          rw [integral_const_mul, aux_lem_resolvents_to_paths_integral_exp_Ioi hlam 0]
          simp only [mul_zero, Real.exp_zero]
          ring
      _ ≤ M / lam * (1 + Real.exp (-lam * S)) := by
          have : 0 ≤ M / lam := div_nonneg hM0 hlam.le
          nlinarith [Real.exp_pos (-lam * S)]
  · rw [Set.indicator_of_notMem (show path ∉ {p : DiffusionPath d |
      ContinuousPath.exitTime U p ≤ ENNReal.ofReal S} from hτ), zero_add]
    rw [not_le] at hτ
    have hsub : ∀ t ∈ Set.Ioi (0:ℝ), ‖Aᶜ.indicator g t‖ ≤
        Set.indicator (Set.Ioi S) (fun t => M * Real.exp (-lam * t)) t := by
      intro t ht
      by_cases htA : t ∈ Aᶜ
      · rw [Set.indicator_of_mem htA]
        have htS : S < t := by
          have h1 : ContinuousPath.exitTime U path ≤ ENNReal.ofReal t := by
            simpa [hAdef] using htA
          have h2 : ENNReal.ofReal S < ENNReal.ofReal t := lt_of_lt_of_le hτ h1
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS).mp h2
        rw [Set.indicator_of_mem (show t ∈ Set.Ioi S from htS)]
        exact hgb t
      · rw [Set.indicator_of_notMem htA, norm_zero]
        exact Set.indicator_nonneg (fun s _ => mul_nonneg hM0 (Real.exp_pos _).le) t
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in Set.Ioi (0:ℝ), Aᶜ.indicator g t‖
        ≤ ∫ t in Set.Ioi (0:ℝ), ‖Aᶜ.indicator g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioi (0:ℝ), Set.indicator (Set.Ioi S) (fun t => M * Real.exp (-lam * t)) t :=
          setIntegral_mono_on ((hgi.indicator hAm.compl).norm) (hint.indicator measurableSet_Ioi)
            measurableSet_Ioi hsub
      _ = ∫ t in Set.Ioi S, M * Real.exp (-lam * t) := by
          rw [setIntegral_indicator measurableSet_Ioi,
            Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hS)]
      _ = M / lam * Real.exp (-lam * S) := by
          rw [integral_const_mul, aux_lem_resolvents_to_paths_integral_exp_Ioi hlam S]
          ring

/-- **The resolvent Dynkin inequality, pathwise.**  Before the exit time from `Q`, restarting
at a time `σ` loses at most the discount factor: `e^{-λσ} kf(θ_σ p) ≤ kf(p)` for `f ≥ 0`. -/
theorem aux_lem_resolvents_to_paths_kf_shift_le {d : ℕ} (Q : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (path : DiffusionPath d) (σ : ℝ≥0)
    (hσ : (σ : ℝ≥0∞) < ContinuousPath.exitTime Q path) :
    Real.exp (-lam * σ) *
        aux_lem_resolvents_to_paths_kf Q lam f (ContinuousPath.shift σ path) ≤
      aux_lem_resolvents_to_paths_kf Q lam f path := by
  unfold aux_lem_resolvents_to_paths_kf
  set G : ℝ → ℝ := Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
    (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) with hGdef
  have hpt : ∀ u ∈ Set.Ioi (0:ℝ), Real.exp (-lam * σ) *
      Set.indicator {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime Q (ContinuousPath.shift σ path)}
        (fun s => Real.exp (-lam * s) * f ((ContinuousPath.shift σ path) (Real.toNNReal s))) u =
      G (u + σ) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hnn : Real.toNNReal (u + σ) = σ + Real.toNNReal u := by
      rw [Real.toNNReal_add hu0 σ.coe_nonneg, Real.toNNReal_coe, add_comm]
    have hiff : ENNReal.ofReal u < ContinuousPath.exitTime Q (ContinuousPath.shift σ path) ↔
        ENNReal.ofReal (u + σ) < ContinuousPath.exitTime Q path := by
      have h := ContinuousPath.coe_add_lt_exitTime_iff Q path σ (Real.toNNReal u)
      have e1 : ENNReal.ofReal (u + σ) = ((σ + Real.toNNReal u : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal, hnn]
      rw [e1, h]
      exact ⟨fun h' => ⟨hσ, h'⟩, fun h' => h'.2⟩
    simp only [hGdef, Set.indicator, Set.mem_ofPred_eq]
    by_cases hA : ENNReal.ofReal u < ContinuousPath.exitTime Q (ContinuousPath.shift σ path)
    · rw [ite_eq_left hA, ite_eq_left (hiff.mp hA), ContinuousPath.shift_apply, hnn, ← mul_assoc,
        ← Real.exp_add]
      congr 2
      ring
    · rw [ite_eq_right hA, ite_eq_right (fun h => hA (hiff.mpr h)), mul_zero]
  have hGi : IntegrableOn G (Set.Ioi 0) :=
    aux_lem_resolvents_to_paths_kf_integrand_integrableOn Q hlam f hf M hM path
  calc Real.exp (-lam * σ) * ∫ u in Set.Ioi (0:ℝ), Set.indicator {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime Q (ContinuousPath.shift σ path)}
        (fun s => Real.exp (-lam * s) * f ((ContinuousPath.shift σ path) (Real.toNNReal s))) u
      = ∫ u in Set.Ioi (0:ℝ), G (u + σ) := by
        rw [← integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Ioi hpt
    _ = ∫ s in Set.Ioi (σ : ℝ), G s := by
        have h := (measurePreserving_add_right (volume : Measure ℝ) (σ : ℝ)).setIntegral_preimage_emb
          (measurableEmbedding_addRight (σ : ℝ)) G (Set.Ioi (σ : ℝ))
        have hpre : (fun x : ℝ => x + (σ : ℝ)) ⁻¹' Set.Ioi (σ : ℝ) = Set.Ioi 0 := by
          ext x; simp
        rw [hpre] at h
        exact h
    _ ≤ ∫ s in Set.Ioi (0:ℝ), G s := by
        refine setIntegral_mono_set hGi ?_ (Eventually.of_forall
          (Set.Ioi_subset_Ioi σ.coe_nonneg))
        exact Eventually.of_forall fun t =>
          Set.indicator_nonneg (fun s _ => mul_nonneg (Real.exp_pos _).le (hf0 _)) t


/-! ### RtpContain -/

theorem aux_lem_resolvents_to_paths_integrable_kf {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsFiniteMeasure μ] (U : Set (SpatialCoordinates d)) (hU : IsOpen U) {lam : ℝ}
    (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) :
    Integrable (aux_lem_resolvents_to_paths_kf U lam f) μ :=
  Integrable.of_bound (aux_lem_resolvents_to_paths_measurable_kf U hU lam f hf).aestronglyMeasurable
    (M / lam) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact aux_lem_resolvents_to_paths_abs_kf_le U hlam f M hM p)

theorem aux_lem_resolvents_to_paths_bcf_one {d : ℕ} :
    (⇑(1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ)) = fun _ => (1 : ℝ) := by
  funext z; simp

/-- **Compact containment of the finite-cutoff laws** (`mfd:prop-as-forms`, removing the
killing).  With `f = 1`, `λ = 1` the killed functional is `1 - e^{-τ_Q}`; its uniform
convergence (`hkilled`) transfers the containment of the limit laws (continuity and
conservativeness, `aux_lem_resolvents_to_paths_limit_containment`) to all large cutoffs. -/
theorem aux_lem_resolvents_to_paths_cutoff_containment
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)))
    (hkilled : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ (closure (centeredCube (Qc n) (Qr n) (hQr n) :
              Set (SpatialCoordinates d))),
              |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(KN N (omega, x)))
                - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(K (omega, x)))| < eps)
    (hcontK : Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ S : ℝ≥0, ∀ eps : ℝ, 0 < eps →
      ∃ n N0 : ℕ, B ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) ∧
        ∀ N, N0 ≤ N → ∀ y ∈ B,
          KN N (omega, y) {p | ContinuousPath.exitTime
            (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) p ≤ (S : ℝ≥0∞)}
            ≤ ENNReal.ofReal eps := by
  intro B hB S eps heps
  set a : ℝ := eps / 3 with hadef
  have ha : 0 < a := by positivity
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / a)
  have hLexp : Real.exp (-(L : ℝ)) < a := by
    have h1 : (L : ℝ) + 1 ≤ Real.exp L := by
      have := Real.add_one_le_exp (L : ℝ); linarith
    rw [Real.exp_neg]
    have hLpos : 0 < (L : ℝ) := lt_trans (by positivity) hL
    rw [inv_lt_comm₀ (Real.exp_pos _) ha]
    have : 1 / a < Real.exp L := lt_of_lt_of_le (by linarith) h1
    simpa [one_div] using this
  set S' : ℝ := (S : ℝ) + L with hS'def
  have hS'0 : 0 ≤ S' := by positivity
  set b : ℝ := a * Real.exp (-(S : ℝ)) with hbdef
  have hb : 0 < b := by positivity
  obtain ⟨R, hR, hRcont⟩ := aux_lem_resolvents_to_paths_limit_containment
    (fun x => jointPathProbabilityMeasure K hK omega x) hcontK B hB (Real.toNNReal S')
    (ENNReal.ofReal b) (ENNReal.ofReal_pos.mpr hb)
  obtain ⟨n, hn⟩ := hQ (Metric.closedBall 0 R ∪ B)
    (Metric.isBounded_closedBall.union hB.isBounded)
  set Q : Set (SpatialCoordinates d) := (centeredCube (Qc n) (Qr n) (hQr n) :
    Set (SpatialCoordinates d)) with hQdef
  have hQo : IsOpen Q := (centeredCube (Qc n) (Qr n) (hQr n)).isOpen
  obtain ⟨N0, hN0⟩ := hkilled n 1 one_pos (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    b hb
  refine ⟨n, N0, fun y hy => hn (Or.inr hy), fun N hN y hy => ?_⟩
  have : IsProbabilityMeasure (KN N (omega, y)) := (hKN N).isProbabilityMeasure _
  have : IsProbabilityMeasure (K (omega, y)) := hK.isProbabilityMeasure _
  set kf := aux_lem_resolvents_to_paths_kf Q 1 (fun _ => (1 : ℝ)) with hkfdef
  have hconv : |(∫ p, kf p ∂(KN N (omega, y))) - ∫ p, kf p ∂(K (omega, y))| < b := by
    have h := hN0 N hN y (subset_closure (hn (Or.inr hy)))
    rw [aux_lem_resolvents_to_paths_bcf_one] at h
    exact h
  have hkfm : Measurable kf :=
    aux_lem_resolvents_to_paths_measurable_kf Q hQo 1 _ measurable_const
  have hkfi : ∀ μ : Measure (DiffusionPath d), IsFiniteMeasure μ → Integrable kf μ :=
    fun μ _ => aux_lem_resolvents_to_paths_integrable_kf μ Q hQo one_pos _ measurable_const 1
      (fun _ => by simp)
  have hkf1 : ∀ p, kf p ≤ 1 := by
    intro p
    have h := aux_lem_resolvents_to_paths_abs_kf_le Q one_pos (fun _ => (1 : ℝ)) 1
      (fun _ => by simp) p
    rw [div_one] at h
    exact (le_abs_self _).trans h
  have hkf0 : ∀ p, 0 ≤ kf p := fun p =>
    aux_lem_resolvents_to_paths_kf_nonneg Q 1 _ (fun _ => zero_le_one) p
  set E : Set (DiffusionPath d) := {p | ContinuousPath.exitTime Q p ≤ (S : ℝ≥0∞)} with hEdef
  set E' : Set (DiffusionPath d) := {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S'}
    with hE'def
  have hEm : MeasurableSet E :=
    measurableSet_le (ContinuousPath.measurable_exitTime Q hQo) measurable_const
  have hE'm : MeasurableSet E' :=
    measurableSet_le (ContinuousPath.measurable_exitTime Q hQo) measurable_const
  -- (i) lower pointwise bound
  have hlow : ∀ p, Real.exp (-(S : ℝ)) * E.indicator (fun _ => (1 : ℝ)) p ≤ 1 - kf p := by
    intro p
    by_cases hp : p ∈ E
    · rw [Set.indicator_of_mem hp, mul_one]
      have h := aux_lem_resolvents_to_paths_kf_one_le_of_exit Q one_pos p S.coe_nonneg
        (by simpa [hEdef, ENNReal.ofReal_coe_nnreal] using hp)
      simp only [one_mul, div_one, neg_mul] at h
      linarith
    · rw [Set.indicator_of_notMem hp, mul_zero]
      linarith [hkf1 p]
  -- (ii) upper pointwise bound
  have hup : ∀ p, 1 - kf p ≤ E'.indicator (fun _ => (1 : ℝ)) p + Real.exp (-S') := by
    intro p
    by_cases hp : p ∈ E'
    · rw [Set.indicator_of_mem hp]
      linarith [hkf0 p, Real.exp_pos (-S')]
    · rw [Set.indicator_of_notMem hp, zero_add]
      have hτ : ENNReal.ofReal S' < ContinuousPath.exitTime Q p := not_le.mp hp
      have h := aux_lem_resolvents_to_paths_kf_ge_of_one Q one_pos (fun _ => (1 : ℝ))
        (fun _ => zero_le_one) measurable_const 1 (fun _ => by simp) p hS'0
        (fun s hs hsS => ⟨lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsS) hτ, le_refl _⟩)
      simp only [one_mul, div_one, neg_mul] at h
      linarith
  -- integrate
  have hIndInt : ∀ (μ : Measure (DiffusionPath d)) [IsProbabilityMeasure μ]
      (A : Set (DiffusionPath d)), MeasurableSet A →
      ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂μ = μ.real A := by
    intro μ _ A hA
    change ∫ p, A.indicator 1 p ∂μ = μ.real A
    rw [integral_indicator_one hA]
  have h1 : Real.exp (-(S : ℝ)) * (KN N (omega, y)).real E ≤
      1 - ∫ p, kf p ∂(KN N (omega, y)) := by
    have hmono := integral_mono (μ := KN N (omega, y))
      (f := fun p => Real.exp (-(S : ℝ)) * E.indicator (fun _ => (1 : ℝ)) p)
      (g := fun p => 1 - kf p)
      (((integrable_const (μ := KN N (omega, y)) (1:ℝ)).indicator hEm).const_mul
        (Real.exp (-(S : ℝ))))
      ((integrable_const (μ := KN N (omega, y)) (1:ℝ)).sub (hkfi _ inferInstance)) hlow
    have eA : ∫ p, (1 - kf p) ∂(KN N (omega, y)) = 1 - ∫ p, kf p ∂(KN N (omega, y)) := by
      rw [integral_sub (integrable_const _) (hkfi _ inferInstance), integral_const,
        probReal_univ, one_smul]
    have eB : ∫ p, Real.exp (-(S : ℝ)) * E.indicator (fun _ => (1 : ℝ)) p ∂(KN N (omega, y)) =
        Real.exp (-(S : ℝ)) * (KN N (omega, y)).real E := by
      rw [integral_const_mul, hIndInt _ E hEm]
    rw [eA, eB] at hmono
    exact hmono
  have h2 : 1 - ∫ p, kf p ∂(K (omega, y)) ≤ (K (omega, y)).real E' + Real.exp (-S') := by
    have hmono := integral_mono (μ := K (omega, y))
      (f := fun p => 1 - kf p)
      (g := fun p => E'.indicator (fun _ => (1 : ℝ)) p + Real.exp (-S'))
      ((integrable_const (μ := K (omega, y)) (1:ℝ)).sub (hkfi _ inferInstance))
      (((integrable_const (μ := K (omega, y)) (1:ℝ)).indicator hE'm).add
        (integrable_const _)) hup
    have eA : ∫ p, (1 - kf p) ∂(K (omega, y)) = 1 - ∫ p, kf p ∂(K (omega, y)) := by
      rw [integral_sub (integrable_const _) (hkfi _ inferInstance), integral_const,
        probReal_univ, one_smul]
    have eB : ∫ p, (E'.indicator (fun _ => (1 : ℝ)) p + Real.exp (-S')) ∂(K (omega, y)) =
        (K (omega, y)).real E' + Real.exp (-S') := by
      rw [integral_add ((integrable_const (1:ℝ)).indicator hE'm) (integrable_const _),
        hIndInt _ E' hE'm, integral_const, probReal_univ, one_smul]
    rw [eA, eB] at hmono
    exact hmono
  -- the limit containment
  have h3 : (K (omega, y)).real E' ≤ b := by
    have hsub : E' ⊆ {p | ∃ s : ℝ≥0, s ≤ Real.toNNReal S' ∧ R ≤ ‖p s‖} := by
      intro p hp
      have hp' : ContinuousPath.exitTime Q p ≤ ((Real.toNNReal S' : ℝ≥0) : ℝ≥0∞) := by
        simpa [hE'def, ENNReal.ofReal] using hp
      obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy Q hQo _ p).mp hp'
      refine ⟨s, s.2, ?_⟩
      have hsQ : p s ∉ Q := hs
      by_contra hlt
      rw [not_le] at hlt
      exact hsQ (hn (Or.inl (by rw [Metric.mem_closedBall, dist_zero_right]; exact hlt.le)))
    have hle := (measure_mono hsub).trans (hRcont y hy).le
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hb.le hle
  have hfinal : (KN N (omega, y)).real E ≤ eps := by
    have hexp : Real.exp (-(S : ℝ)) * Real.exp (S : ℝ) = 1 := by
      rw [← Real.exp_add]; simp
    have hkey : Real.exp (-(S : ℝ)) * (KN N (omega, y)).real E ≤ 2 * b + Real.exp (-S') := by
      have := abs_lt.mp hconv
      linarith
    have hS'e : Real.exp (-S') = Real.exp (-(S : ℝ)) * Real.exp (-(L : ℝ)) := by
      rw [← Real.exp_add]; congr 1; rw [hS'def]; ring
    rw [hS'e, hbdef] at hkey
    have hpos : 0 < Real.exp (-(S : ℝ)) := Real.exp_pos _
    have hkey' : (KN N (omega, y)).real E ≤ 2 * a + Real.exp (-(L : ℝ)) := by
      have : Real.exp (-(S : ℝ)) * (KN N (omega, y)).real E ≤
          Real.exp (-(S : ℝ)) * (2 * a + Real.exp (-(L : ℝ))) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hfinal


/-! ### RtpExit -/

/-- The separator of `mfd:prop-as-forms`: `0` on the ball of radius `ρ/4` about `c`, `1` outside
the ball of radius `3ρ/8`, continuous, with values in `[0, 1]`. -/
def aux_lem_resolvents_to_paths_sep {d : ℕ} (c : SpatialCoordinates d) (ρ : ℝ) :
    BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => min 1 (max 0 ((dist z c - ρ / 4) * (8 / ρ))), by fun_prop⟩ 1 (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : ∀ w : ℝ, 0 ≤ min 1 (max 0 w) ∧ min 1 (max 0 w) ≤ 1 := fun w =>
        ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
      obtain ⟨a0, a1⟩ := h1 ((dist x c - ρ / 4) * (8 / ρ))
      obtain ⟨b0, b1⟩ := h1 ((dist y c - ρ / 4) * (8 / ρ))
      rw [abs_le]; constructor <;> linarith)

theorem aux_lem_resolvents_to_paths_sep_apply {d : ℕ} (c : SpatialCoordinates d) (ρ : ℝ)
    (z : SpatialCoordinates d) :
    aux_lem_resolvents_to_paths_sep c ρ z = min 1 (max 0 ((dist z c - ρ / 4) * (8 / ρ))) := rfl

theorem aux_lem_resolvents_to_paths_sep_nonneg {d : ℕ} (c : SpatialCoordinates d) (ρ : ℝ)
    (z : SpatialCoordinates d) : 0 ≤ aux_lem_resolvents_to_paths_sep c ρ z := by
  rw [aux_lem_resolvents_to_paths_sep_apply]
  exact le_min zero_le_one (le_max_left _ _)

theorem aux_lem_resolvents_to_paths_sep_le_one {d : ℕ} (c : SpatialCoordinates d) (ρ : ℝ)
    (z : SpatialCoordinates d) : aux_lem_resolvents_to_paths_sep c ρ z ≤ 1 := by
  rw [aux_lem_resolvents_to_paths_sep_apply]
  exact min_le_left _ _

theorem aux_lem_resolvents_to_paths_abs_sep_le {d : ℕ} (c : SpatialCoordinates d) (ρ : ℝ)
    (z : SpatialCoordinates d) : |aux_lem_resolvents_to_paths_sep c ρ z| ≤ 1 := by
  rw [abs_of_nonneg (aux_lem_resolvents_to_paths_sep_nonneg c ρ z)]
  exact aux_lem_resolvents_to_paths_sep_le_one c ρ z

theorem aux_lem_resolvents_to_paths_sep_eq_zero {d : ℕ} (c : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) (z : SpatialCoordinates d) (hz : dist z c ≤ ρ / 4) :
    aux_lem_resolvents_to_paths_sep c ρ z = 0 := by
  rw [aux_lem_resolvents_to_paths_sep_apply]
  have : (dist z c - ρ / 4) * (8 / ρ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [max_eq_left this, min_eq_right zero_le_one]

theorem aux_lem_resolvents_to_paths_sep_eq_one {d : ℕ} (c : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) (z : SpatialCoordinates d) (hz : 3 * ρ / 8 ≤ dist z c) :
    aux_lem_resolvents_to_paths_sep c ρ z = 1 := by
  rw [aux_lem_resolvents_to_paths_sep_apply]
  have h : 1 ≤ (dist z c - ρ / 4) * (8 / ρ) := by
    rw [show (dist z c - ρ / 4) * (8 / ρ) = (dist z c - ρ / 4) * 8 / ρ by ring,
      le_div_iff₀ hρ]
    linarith
  rw [max_eq_right (by linarith), min_eq_left h]

/-- The exit time of `U` precedes that of `Q` when `closure U ⊆ Q` and the path starts in `U`. -/
theorem aux_lem_resolvents_to_paths_exitTime_lt {d : ℕ} (U Q : Set (SpatialCoordinates d))
    (hU : IsOpen U) (hQ : IsOpen Q) (hUQ : closure U ⊆ Q) (p : DiffusionPath d)
    (hp0 : p 0 ∈ U) (hfin : ContinuousPath.exitTime U p ≠ ⊤) :
    ContinuousPath.exitTime U p < ContinuousPath.exitTime Q p := by
  by_contra hcon
  rw [not_lt] at hcon
  set σ : ℝ≥0 := (ContinuousPath.exitTime U p).toNNReal with hσdef
  have hσ : (σ : ℝ≥0∞) = ContinuousPath.exitTime U p := ENNReal.coe_toNNReal hfin
  rw [← hσ] at hcon
  obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy Q hQ σ p).mp hcon
  have hsQ : p s ∉ Q := hs
  apply hsQ
  apply hUQ
  rcases lt_or_eq_of_le (show (s : ℝ≥0) ≤ σ from s.2) with hlt | heq
  · exact subset_closure (ContinuousPath.mem_of_lt_exitTime U p s (by
      rw [← hσ]; exact_mod_cast hlt))
  · rw [heq]
    exact frontier_subset_closure
      (ContinuousPath.coordinate_exitTime_mem_frontier U hU p hp0 hfin)

/-- Lower bound on the restart side of the resolvent Dynkin identity. -/
theorem aux_lem_resolvents_to_paths_dynkin_low {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k] (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (U Q : Set (SpatialCoordinates d)) (hU : IsOpen U) (hQ : IsOpen Q)
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (m : ℝ)
    (hm : ∀ z ∈ frontier U, m ≤ ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k z)
    (x : SpatialCoordinates d) (hx : x ∈ U) (h : ℝ≥0) :
    ENNReal.ofReal m * k x {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} ≤
      ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}.indicator 1 p *
          ∫⁻ q, ENNReal.ofReal (aux_lem_resolvents_to_paths_kf Q lam f q)
            ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k x := by
  have hτm : Measurable (ContinuousPath.exitTime U : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime U hU
  have hEm : MeasurableSet {p : ContinuousPath (SpatialCoordinates d) |
      ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} := measurableSet_le hτm measurable_const
  have hES : {p : ContinuousPath (SpatialCoordinates d) |
      ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} ⊆ {p | ContinuousPath.exitTime U p < ⊤} :=
    fun p hp => lt_of_le_of_lt hp ENNReal.coe_lt_top
  have hkf0 : ∀ p, 0 ≤ aux_lem_resolvents_to_paths_kf Q lam f p :=
    aux_lem_resolvents_to_paths_kf_nonneg Q lam f hf0
  have hkfi : ∀ z, Integrable (aux_lem_resolvents_to_paths_kf Q lam f) (k z) := fun z =>
    aux_lem_resolvents_to_paths_integrable_kf (k z) Q hQ hlam f hf M hM
  rw [show ENNReal.ofReal m * k x {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} =
      ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}.indicator
          (fun _ => ENNReal.ofReal m) p ∂k x by
    rw [lintegral_indicator_const hEm, Measure.restrict_apply hEm, Set.inter_eq_left.mpr hES]]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae (h0 x)] with p hp0
  by_cases hpE : p ∈ {p : ContinuousPath (SpatialCoordinates d) |
      ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}
  · rw [Set.indicator_of_mem hpE, Set.indicator_of_mem hpE, Pi.one_apply, one_mul]
    have hfin : ContinuousPath.exitTime U p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hpE
    have hfr : p (ContinuousPath.exitTime U p).toNNReal ∈ frontier U :=
      ContinuousPath.coordinate_exitTime_mem_frontier U hU p (hp0 ▸ hx) hfin
    rw [← ofReal_integral_eq_lintegral_ofReal (hkfi _) (Eventually.of_forall fun q => hkf0 q)]
    exact ENNReal.ofReal_le_ofReal (hm _ hfr)
  · rw [Set.indicator_of_notMem hpE]
    exact bot_le

/-- Upper bound on the shifted side of the resolvent Dynkin identity. -/
theorem aux_lem_resolvents_to_paths_dynkin_up {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k] (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (U Q : Set (SpatialCoordinates d)) (hU : IsOpen U) (hQ : IsOpen Q) (hUQ : closure U ⊆ Q)
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    (x : SpatialCoordinates d) (hx : x ∈ U) (h : ℝ≥0) :
    ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}.indicator 1 p *
          ENNReal.ofReal (aux_lem_resolvents_to_paths_kf Q lam f
            (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p)) ∂k x ≤
      ENNReal.ofReal (Real.exp (lam * h) *
        ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k x) := by
  have hkf0 : ∀ p, 0 ≤ aux_lem_resolvents_to_paths_kf Q lam f p :=
    aux_lem_resolvents_to_paths_kf_nonneg Q lam f hf0
  have hkfi : ∀ z, Integrable (aux_lem_resolvents_to_paths_kf Q lam f) (k z) := fun z =>
    aux_lem_resolvents_to_paths_integrable_kf (k z) Q hQ hlam f hf M hM
  have hint : Integrable (fun p => Real.exp (lam * h) *
      aux_lem_resolvents_to_paths_kf Q lam f p) (k x) := (hkfi x).const_mul _
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun q => mul_nonneg (Real.exp_pos _).le (hkf0 q))]
  refine (setLIntegral_le_lintegral _ _).trans ?_
  refine lintegral_mono_ae ?_
  filter_upwards [h0 x] with p hp0
  by_cases hpE : p ∈ {p : ContinuousPath (SpatialCoordinates d) |
      ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}
  · rw [Set.indicator_of_mem hpE, Pi.one_apply, one_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hfin : ContinuousPath.exitTime U p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hpE
    have hσ : ((ContinuousPath.exitTime U p).toNNReal : ℝ≥0∞) = ContinuousPath.exitTime U p :=
      ENNReal.coe_toNNReal hfin
    have hσQ : ((ContinuousPath.exitTime U p).toNNReal : ℝ≥0∞) <
        ContinuousPath.exitTime Q p := by
      rw [hσ]
      exact aux_lem_resolvents_to_paths_exitTime_lt U Q hU hQ hUQ p (hp0 ▸ hx) hfin
    have hsh := aux_lem_resolvents_to_paths_kf_shift_le Q hlam f hf0 hf M hM p _ hσQ
    have hσh : ((ContinuousPath.exitTime U p).toNNReal : ℝ) ≤ h := by
      have : ((ContinuousPath.exitTime U p).toNNReal : ℝ≥0∞) ≤ h := by rw [hσ]; exact hpE
      exact_mod_cast this
    set σ : ℝ := ((ContinuousPath.exitTime U p).toNNReal : ℝ) with hσdef
    have hexp : Real.exp (-lam * σ) * Real.exp (lam * σ) = 1 := by
      rw [← Real.exp_add]; simp
    have h1 : aux_lem_resolvents_to_paths_kf Q lam f
        (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p) ≤
        Real.exp (lam * σ) * aux_lem_resolvents_to_paths_kf Q lam f p := by
      have := mul_le_mul_of_nonneg_left hsh (Real.exp_pos (lam * σ)).le
      rw [← mul_assoc, mul_comm (Real.exp (lam * σ)), hexp, one_mul] at this
      exact this
    calc _ ≤ Real.exp (lam * σ) * aux_lem_resolvents_to_paths_kf Q lam f p := h1
      _ ≤ Real.exp (lam * h) * aux_lem_resolvents_to_paths_kf Q lam f p :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hσh hlam.le)) (hkf0 p)
  · rw [Set.indicator_of_notMem hpE, zero_mul]
    exact bot_le

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Optional stopping in resolvent form** (`mfd:prop-as-forms`).  With `f ≥ 0` and
`m ≤ E_z kf` on the frontier of `U`, strong Markov at the exit from `U` and the pathwise
restart inequality give `m · P_x(τ_U ≤ h) ≤ e^{λh} E_x kf`. -/
theorem aux_lem_resolvents_to_paths_dynkin {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (U Q : Set (SpatialCoordinates d)) (hU : IsOpen U) (hQ : IsOpen Q) (hUQ : closure U ⊆ Q)
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hf : Measurable f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (m : ℝ)
    (hm : ∀ z ∈ frontier U, m ≤ ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k z)
    (x : SpatialCoordinates d) (hx : x ∈ U) (h : ℝ≥0) :
    ENNReal.ofReal m * k x {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * h) * ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k x) := by
  have hEc : MeasurableSet[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      {p : ContinuousPath (SpatialCoordinates d) | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} := by
    refine ⟨{w | LifetimePath.exitTime U w ≤ (h : ℝ≥0∞)},
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSet_le' h,
      ?_⟩
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath]
  have hW : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      ({p : ContinuousPath (SpatialCoordinates d) |
        ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}.indicator 1) :=
    show Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      ({p : ContinuousPath (SpatialCoordinates d) |
        ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)}.indicator (fun _ => (1 : ℝ≥0∞))) from
    (measurable_const (a := (1 : ℝ≥0∞))).indicator hEc
  have hg : Measurable (fun p => ENNReal.ofReal (aux_lem_resolvents_to_paths_kf Q lam f p)) :=
    ENNReal.measurable_ofReal.comp (aux_lem_resolvents_to_paths_measurable_kf Q hQ lam f hf)
  have hSMid := aux_lem_resolvents_to_paths_sm_weighted k L hL hSM U hU x _ hW _ hg
  refine (aux_lem_resolvents_to_paths_dynkin_low k h0 U Q hU hQ hlam f hf0 hf M hM m hm x hx h).trans
    ?_
  rw [← hSMid]
  exact aux_lem_resolvents_to_paths_dynkin_up k h0 U Q hU hQ hUQ hlam f hf0 hf M hM x hx h


/-! ### RtpExit2 -/

theorem aux_lem_resolvents_to_paths_integral_indicator_one {d : ℕ}
    (μ : Measure (DiffusionPath d)) [IsFiniteMeasure μ] (A : Set (DiffusionPath d))
    (hA : MeasurableSet A) :
    ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂μ = μ.real A := by
  change ∫ p, A.indicator 1 p ∂μ = μ.real A
  rw [integral_indicator_one hA]

/-- Lower bound for the killed resolvent of a law started at `z`, when `f ≥ 1` near `z`. -/
theorem aux_lem_resolvents_to_paths_kf_integral_ge {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsProbabilityMeasure μ] (z : SpatialCoordinates d) (hz0 : ∀ᵐ p ∂μ, p 0 = z)
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) {r : ℝ} (hball : Metric.ball z r ⊆ Q)
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ w, 0 ≤ f w)
    (hf : Measurable f) (M : ℝ) (hM : ∀ w, |f w| ≤ M)
    (hone : ∀ w ∈ Metric.ball z r, 1 ≤ f w) {h' : ℝ} (hh' : 0 ≤ h') {δ : ℝ}
    (hδ : μ {p | ContinuousPath.exitTime (Metric.ball z r) p ≤ ENNReal.ofReal h'} ≤
      ENNReal.ofReal δ) (hδ0 : 0 ≤ δ) :
    (1 - Real.exp (-lam * h')) * (1 - δ) / lam ≤
      ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂μ := by
  set B := Metric.ball z r with hBdef
  have hBo : IsOpen B := Metric.isOpen_ball
  set E : Set (DiffusionPath d) := {p | ContinuousPath.exitTime B p ≤ ENNReal.ofReal h'}
    with hEdef
  have hEm : MeasurableSet E :=
    measurableSet_le (ContinuousPath.measurable_exitTime B hBo) measurable_const
  have hkfi := aux_lem_resolvents_to_paths_integrable_kf μ Q hQ hlam f hf M hM
  set c : ℝ := (1 - Real.exp (-lam * h')) / lam with hcdef
  have hc0 : 0 ≤ c := by
    have : Real.exp (-lam * h') ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact div_nonneg (by linarith) hlam.le
  have hpt : ∀ᵐ p ∂μ, c * Eᶜ.indicator (fun _ => (1 : ℝ)) p ≤
      aux_lem_resolvents_to_paths_kf Q lam f p := by
    filter_upwards [hz0] with p hp0
    by_cases hpE : p ∈ E
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hpE), mul_zero]
      exact aux_lem_resolvents_to_paths_kf_nonneg Q lam f hf0 p
    · rw [Set.indicator_of_mem (Set.mem_compl hpE), mul_one]
      have hτ : ENNReal.ofReal h' < ContinuousPath.exitTime B p := not_le.mp hpE
      refine aux_lem_resolvents_to_paths_kf_ge_of_one Q hlam f hf0 hf M hM p hh' ?_
      intro s hs hsh
      have hsB : ENNReal.ofReal s < ContinuousPath.exitTime B p :=
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsh) hτ
      have hmem : p (Real.toNNReal s) ∈ B :=
        ContinuousPath.mem_of_lt_exitTime B p _ (by simpa [ENNReal.ofReal] using hsB)
      refine ⟨lt_of_lt_of_le hsB (ContinuousPath.exitTime_mono hball p), hone _ hmem⟩
  have hint := integral_mono_ae (((integrable_const (μ := μ) (1:ℝ)).indicator
    hEm.compl).const_mul c) hkfi hpt
  rw [integral_const_mul, aux_lem_resolvents_to_paths_integral_indicator_one μ _ hEm.compl,
    probReal_compl_eq_one_sub hEm] at hint
  have hμE : μ.real E ≤ δ := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hδ0 hδ
  calc (1 - Real.exp (-lam * h')) * (1 - δ) / lam = c * (1 - δ) := by rw [hcdef]; ring
    _ ≤ c * (1 - μ.real E) := mul_le_mul_of_nonneg_left (by linarith) hc0
    _ ≤ _ := hint

/-- Upper bound for the killed resolvent of a law started at `x`, when `f ∈ [0,1]` vanishes
near `x`. -/
theorem aux_lem_resolvents_to_paths_kf_integral_le {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsProbabilityMeasure μ] (x : SpatialCoordinates d) (hx0 : ∀ᵐ p ∂μ, p 0 = x)
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) {r : ℝ}
    {lam : ℝ} (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf0 : ∀ w, 0 ≤ f w)
    (hf1 : ∀ w, f w ≤ 1) (hf : Measurable f)
    (hzero : ∀ w ∈ Metric.ball x r, f w = 0) {h' : ℝ} (hh' : 0 ≤ h') {δ : ℝ}
    (hδ : μ {p | ContinuousPath.exitTime (Metric.ball x r) p ≤ ENNReal.ofReal h'} ≤
      ENNReal.ofReal δ) (hδ0 : 0 ≤ δ) :
    ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂μ ≤ (δ + Real.exp (-lam * h')) / lam := by
  set B := Metric.ball x r with hBdef
  have hBo : IsOpen B := Metric.isOpen_ball
  set E : Set (DiffusionPath d) := {p | ContinuousPath.exitTime B p ≤ ENNReal.ofReal h'}
    with hEdef
  have hEm : MeasurableSet E :=
    measurableSet_le (ContinuousPath.measurable_exitTime B hBo) measurable_const
  have hM : ∀ w, |f w| ≤ 1 := fun w => by rw [abs_of_nonneg (hf0 w)]; exact hf1 w
  have hkfi := aux_lem_resolvents_to_paths_integrable_kf μ Q hQ hlam f hf 1 hM
  have hpt : ∀ᵐ p ∂μ, aux_lem_resolvents_to_paths_kf Q lam f p ≤
      (1 / lam) * (E.indicator (fun _ => (1 : ℝ)) p + Real.exp (-lam * h')) := by
    filter_upwards [hx0] with p hp0
    by_cases hpE : p ∈ E
    · rw [Set.indicator_of_mem hpE]
      have h1 := aux_lem_resolvents_to_paths_abs_kf_le Q hlam f 1 hM p
      have h2 : (1 / lam) * 1 ≤ (1 / lam) * (1 + Real.exp (-lam * h')) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.exp_pos (-lam * h')]) (by positivity)
      calc _ ≤ |aux_lem_resolvents_to_paths_kf Q lam f p| := le_abs_self _
        _ ≤ 1 / lam := h1
        _ = (1 / lam) * 1 := (mul_one _).symm
        _ ≤ _ := h2
    · rw [Set.indicator_of_notMem hpE, zero_add]
      have hτ : ENNReal.ofReal h' < ContinuousPath.exitTime B p := not_le.mp hpE
      have := aux_lem_resolvents_to_paths_kf_le_of_vanish Q hlam f hf0 hf1 hf p hh' (by
        intro s hs hsh
        have hsB : ENNReal.ofReal s < ContinuousPath.exitTime B p :=
          lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsh) hτ
        exact hzero _ (ContinuousPath.mem_of_lt_exitTime B p _ (by simpa [ENNReal.ofReal] using hsB)))
      calc _ ≤ Real.exp (-lam * h') / lam := this
        _ = _ := by ring
  have hint := integral_mono_ae (μ := μ) (f := fun p => aux_lem_resolvents_to_paths_kf Q lam f p)
    (g := fun p => (1 / lam) * (E.indicator (fun _ => (1 : ℝ)) p + Real.exp (-lam * h')))
    hkfi ((((integrable_const (μ := μ) (1:ℝ)).indicator hEm).add
    (integrable_const _)).const_mul (1 / lam)) hpt
  have eB : ∫ p, (1 / lam) * (E.indicator (fun _ => (1 : ℝ)) p + Real.exp (-lam * h')) ∂μ =
      1 / lam * (μ.real E + Real.exp (-lam * h')) := by
    rw [integral_const_mul, integral_add ((integrable_const (1:ℝ)).indicator hEm)
      (integrable_const _), aux_lem_resolvents_to_paths_integral_indicator_one μ _ hEm,
      integral_const, probReal_univ, one_smul]
  rw [eB] at hint
  have hμE : μ.real E ≤ δ := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hδ0 hδ
  calc _ ≤ 1 / lam * (μ.real E + Real.exp (-lam * h')) := hint
    _ ≤ 1 / lam * (δ + Real.exp (-lam * h')) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring


/-! ### RtpExit3 -/

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Short exits for one finite cutoff at one centre** (`mfd:prop-as-forms`): the separator
`sep c ρ`, the resolvent Dynkin inequality at the exit from `ball c (ρ/2)`, the limit bounds
and the closeness of the killed resolvents give `P_y(τ_{ball y ρ} ≤ 1/λ) ≤ 18 η`. -/
theorem aux_lem_resolvents_to_paths_short_exit_core {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (klim : SpatialCoordinates d → Measure (DiffusionPath d))
    (hklim : ∀ z, IsProbabilityMeasure (klim z)) (hlim0 : ∀ z, ∀ᵐ p ∂klim z, p 0 = z)
    (Q : Set (SpatialCoordinates d)) (hQo : IsOpen Q) (c : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) (hball : Metric.ball c ρ ⊆ Q) {lam : ℝ} (hlam : 0 < lam) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 10) {h' : ℝ} (hh' : 0 ≤ h') (hexp : Real.exp (-lam * h') ≤ η)
    (hshort : ∀ z, dist z c ≤ ρ / 2 →
      klim z {p | ContinuousPath.exitTime (Metric.ball z (ρ / 8)) p ≤ ENNReal.ofReal h'} ≤
        ENNReal.ofReal η)
    (hclose : ∀ x, dist x c ≤ ρ / 2 →
      |(∫ p, aux_lem_resolvents_to_paths_kf Q lam (aux_lem_resolvents_to_paths_sep c ρ) p ∂k x) -
        ∫ p, aux_lem_resolvents_to_paths_kf Q lam (aux_lem_resolvents_to_paths_sep c ρ) p ∂klim x|
        < η / lam)
    (y : SpatialCoordinates d) (hy : dist y c < ρ / 8) :
    k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ ((Real.toNNReal (1 / lam) : ℝ≥0) : ℝ≥0∞)}
      ≤ ENNReal.ofReal (18 * η) := by
  set f := aux_lem_resolvents_to_paths_sep c ρ with hfdef
  have hf0 : ∀ w, 0 ≤ f w := aux_lem_resolvents_to_paths_sep_nonneg c ρ
  have hf1 : ∀ w, f w ≤ 1 := aux_lem_resolvents_to_paths_sep_le_one c ρ
  have hfM : ∀ w, |f w| ≤ 1 := aux_lem_resolvents_to_paths_abs_sep_le c ρ
  have hfm : Measurable f := f.continuous.measurable
  set U : Set (SpatialCoordinates d) := Metric.ball c (ρ / 2) with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUQ : closure U ⊆ Q := by
    refine (Metric.closure_ball_subset_closedBall).trans (fun w hw => hball ?_)
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith
  set m : ℝ := ((1 - η) * (1 - η) - η) / lam with hmdef
  have hm : ∀ z ∈ frontier U, m ≤ ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k z := by
    intro z hz
    have hzc : dist z c = ρ / 2 := Metric.frontier_ball_subset_sphere hz
    have := hklim z
    have hball' : Metric.ball z (ρ / 8) ⊆ Q := by
      intro w hw
      apply hball
      rw [Metric.mem_ball] at hw ⊢
      linarith [dist_triangle w z c]
    have hone : ∀ w ∈ Metric.ball z (ρ / 8), 1 ≤ f w := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [hfdef, aux_lem_resolvents_to_paths_sep_eq_one c hρ w (by
        linarith [dist_triangle z w c, dist_comm w z])]
    have hlow := aux_lem_resolvents_to_paths_kf_integral_ge (klim z) z (hlim0 z) Q hQo hball'
      hlam f hf0 hfm 1 hfM hone hh' (hshort z hzc.le) hη.le
    have hc := hclose z hzc.le
    have h1 : (1 - η) * (1 - η) / lam ≤ (1 - Real.exp (-lam * h')) * (1 - η) / lam := by
      apply div_le_div_of_nonneg_right _ hlam.le
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 := (abs_lt.mp hc).1
    rw [hmdef, sub_div]
    have : η / lam = η / lam := rfl
    linarith
  have := hklim y
  have hyU : y ∈ U := by rw [Metric.mem_ball]; linarith
  have hup : ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k y ≤ 3 * η / lam := by
    have hzero : ∀ w ∈ Metric.ball y (ρ / 8), f w = 0 := by
      intro w hw
      rw [Metric.mem_ball] at hw
      exact aux_lem_resolvents_to_paths_sep_eq_zero c hρ w (by linarith [dist_triangle w y c])
    have hl := aux_lem_resolvents_to_paths_kf_integral_le (klim y) y (hlim0 y) Q hQo hlam f hf0 hf1
      hfm hzero hh' (hshort y (by linarith)) hη.le
    have hc := (abs_lt.mp (hclose y (by linarith))).2
    have : (η + Real.exp (-lam * h')) / lam ≤ 2 * η / lam :=
      div_le_div_of_nonneg_right (by linarith) hlam.le
    have e3 : 3 * η / lam = 2 * η / lam + η / lam := by ring
    linarith
  set h : ℝ≥0 := Real.toNNReal (1 / lam) with hhdef
  have hlamh : lam * (h : ℝ) = 1 := by
    rw [hhdef, Real.coe_toNNReal _ (by positivity)]
    field_simp
  have hD := aux_lem_resolvents_to_paths_dynkin k L hL hSM h0 U Q hUo hQo hUQ hlam f hf0 hfm 1
    hfM m hm y hyU h
  rw [hlamh] at hD
  set E : Set (ContinuousPath (SpatialCoordinates d)) :=
    {p | ContinuousPath.exitTime U p ≤ (h : ℝ≥0∞)} with hEdef
  have hsub : {p : ContinuousPath (SpatialCoordinates d) |
      ContinuousPath.exitTime (Metric.ball y ρ) p ≤ (h : ℝ≥0∞)} ⊆ E := by
    intro p hp
    refine le_trans (ContinuousPath.exitTime_mono ?_ p) hp
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    linarith [dist_triangle w c y, dist_comm y c]
  refine (measure_mono hsub).trans ?_
  have hEfin : k y E ≠ ⊤ := measure_ne_top _ _
  set x : ℝ := (k y E).toReal with hxdef
  have hxE : k y E = ENNReal.ofReal x := (ENNReal.ofReal_toReal hEfin).symm
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  rw [hxE] at hD ⊢
  have hmpos : 0.7 / lam ≤ m := by
    rw [hmdef]
    apply div_le_div_of_nonneg_right _ hlam.le
    nlinarith
  have hB0 : 0 ≤ Real.exp 1 * ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂k y :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun p =>
      aux_lem_resolvents_to_paths_kf_nonneg Q lam f hf0 p)
  rw [← ENNReal.ofReal_mul (by
    have : 0 < 0.7 / lam := by positivity
    linarith), ENNReal.ofReal_le_ofReal_iff hB0] at hD
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hkey : 0.7 / lam * x ≤ Real.exp 1 * (3 * η / lam) := by
    calc 0.7 / lam * x ≤ m * x := mul_le_mul_of_nonneg_right hmpos hx0
      _ ≤ _ := hD
      _ ≤ Real.exp 1 * (3 * η / lam) := mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le
  have hkey' : 0.7 * x ≤ Real.exp 1 * (3 * η) := by
    have := mul_le_mul_of_nonneg_left hkey hlam.le
    field_simp at this
    linarith
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith


/-! ### RtpExit4 -/

theorem aux_lem_resolvents_to_paths_ae_start {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) (y : SpatialCoordinates d) :
    ∀ᵐ p ∂(K (omega, y)), p 0 = y := by
  rw [ae_iff]
  exact aux_lem_resolvents_to_paths_start_pinned_of P K omega hfdd y

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Uniform short exits of the finite-cutoff laws** (`mfd:prop-as-forms`): for every compact
set of starting points and radius, the probability of leaving the ball of radius `ρ` about
the start before a small time is uniformly small for all large cutoffs.  Finite cover of the
compact set by centres, one separator per centre, `hkilled` at one `λ`. -/
theorem aux_lem_resolvents_to_paths_cutoff_short_exit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)))
    (omega : BilateralField d)
    (hfdd : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (L : ℕ → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N x, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
      (KN N (omega, x)) = L N x)
    (hLstrong : ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N))
    (hlimAt : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hkilled : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ (closure (centeredCube (Qc n) (Qr n) (hQr n) :
              Set (SpatialCoordinates d))),
              |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(KN N (omega, x)))
                - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(K (omega, x)))| < eps)
    (hcontK : Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) :
    ∀ C : Set (SpatialCoordinates d), IsCompact C → ∀ ρ : ℝ, 0 < ρ → ∀ eps : ℝ, 0 < eps →
      ∃ h : ℝ≥0, 0 < h ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ y ∈ C,
        KN N (omega, y) {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ (h : ℝ≥0∞)} ≤
          ENNReal.ofReal eps := by
  intro C hC ρ hρ eps heps
  set η : ℝ := min (1 / 10) (eps / 18) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 10 := min_le_left _ _
  have hη2 : η ≤ eps / 18 := min_le_right _ _
  have hC' : IsCompact (Metric.cthickening ρ C) := hC.cthickening
  obtain ⟨m, hm⟩ := hQ (Metric.cthickening (2 * ρ) C) (hC.cthickening).isBounded
  set Q : Set (SpatialCoordinates d) :=
    (centeredCube (Qc m) (Qr m) (hQr m) : Set (SpatialCoordinates d)) with hQdef
  have hQo : IsOpen Q := (centeredCube (Qc m) (Qr m) (hQr m)).isOpen
  have hKstart : ∀ y, (jointPathProbabilityMeasure K hK omega y : Measure (DiffusionPath d))
      {p | p 0 ≠ y} = 0 := fun y =>
    aux_lem_resolvents_to_paths_start_pinned_of (P omega) K omega hlimAt y
  obtain ⟨h', hh'pos, hh'⟩ := aux_lem_resolvents_to_paths_limit_short_exit
    (fun x => jointPathProbabilityMeasure K hK omega x) hcontK hKstart
    (Metric.cthickening ρ C) hC' (ρ / 8) (by positivity) (ENNReal.ofReal η)
    (ENNReal.ofReal_pos.mpr hη)
  have hh'r : (0 : ℝ) < h' := by exact_mod_cast hh'pos
  obtain ⟨L0, hL0⟩ := exists_nat_gt (1 / η)
  have hL0pos : (0 : ℝ) < L0 := lt_trans (by positivity) hL0
  set lam : ℝ := L0 / h' with hlamdef
  have hlam : 0 < lam := div_pos hL0pos hh'r
  have hexp : Real.exp (-lam * h') ≤ η := by
    have e1 : -lam * h' = -(L0 : ℝ) := by rw [hlamdef]; field_simp
    rw [e1, Real.exp_neg]
    have h1 : (L0 : ℝ) + 1 ≤ Real.exp L0 := by
      have := Real.add_one_le_exp (L0 : ℝ); linarith
    have h2 : 1 / η < Real.exp L0 := lt_of_lt_of_le (by linarith) h1
    rw [inv_le_comm₀ (Real.exp_pos _) hη]
    rw [one_div] at h2
    exact h2.le
  obtain ⟨T, hTC, hTfin, hcover⟩ := finite_cover_balls_of_compact hC
    (show (0 : ℝ) < ρ / 8 by positivity)
  have hkc : ∀ c : SpatialCoordinates d, ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ closure Q,
      |(∫ p, aux_lem_resolvents_to_paths_kf Q lam (aux_lem_resolvents_to_paths_sep c ρ) p
          ∂(KN N (omega, x))) -
        ∫ p, aux_lem_resolvents_to_paths_kf Q lam (aux_lem_resolvents_to_paths_sep c ρ) p
          ∂(K (omega, x))| < η / lam :=
    fun c => hkilled m lam hlam (aux_lem_resolvents_to_paths_sep c ρ) (η / lam) (by positivity)
  choose N0f hN0f using hkc
  refine ⟨Real.toNNReal (1 / lam), by simp [hlam], hTfin.toFinset.sup N0f, fun N hN y hy => ?_⟩
  obtain ⟨c, hcT, hyc⟩ := Set.mem_iUnion₂.mp (hcover hy)
  have hNc : N0f c ≤ N := le_trans (Finset.le_sup (hTfin.mem_toFinset.mpr hcT)) hN
  have hcC : c ∈ C := hTC hcT
  have hball : Metric.ball c ρ ⊆ Q := by
    intro w hw
    apply hm
    exact Metric.mem_cthickening_of_dist_le w c (2 * ρ) C hcC
      (by rw [Metric.mem_ball] at hw; linarith)
  have : IsMarkovKernel (KN N) := hKN N
  set k := (KN N).comap (fun x => (omega, x)) measurable_prodMk_left with hkdef
  have hkapp : ∀ z, k z = KN N (omega, z) := fun z => rfl
  have : IsMarkovKernel k := by rw [hkdef]; infer_instance
  have hLk : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L N z := fun z => hL N z
  have h0k : ∀ z, ∀ᵐ p ∂k z, p 0 = z := fun z =>
    aux_lem_resolvents_to_paths_ae_start (PN N omega) (KN N) omega (hfdd N) z
  have hklim : ∀ z, IsProbabilityMeasure (K (omega, z)) := fun z => hK.isProbabilityMeasure _
  have hlim0 : ∀ z, ∀ᵐ p ∂(K (omega, z)), p 0 = z := fun z =>
    aux_lem_resolvents_to_paths_ae_start (P omega) K omega hlimAt z
  have hshort : ∀ z, dist z c ≤ ρ / 2 →
      K (omega, z) {p | ContinuousPath.exitTime (Metric.ball z (ρ / 8)) p ≤
        ENNReal.ofReal (h' : ℝ)} ≤ ENNReal.ofReal η := by
    intro z hz
    have hzC : z ∈ Metric.cthickening ρ C :=
      Metric.mem_cthickening_of_dist_le z c ρ C hcC (by linarith)
    have := hh' z hzC
    rw [ENNReal.ofReal_coe_nnreal]
    exact this.le
  have hclose : ∀ x, dist x c ≤ ρ / 2 →
      |(∫ p, aux_lem_resolvents_to_paths_kf Q lam (aux_lem_resolvents_to_paths_sep c ρ) p ∂k x) -
        ∫ p, aux_lem_resolvents_to_paths_kf Q lam (aux_lem_resolvents_to_paths_sep c ρ) p
          ∂(K (omega, x))| < η / lam := by
    intro x hx
    exact hN0f c N hNc x (subset_closure (hball (by rw [Metric.mem_ball]; linarith)))
  have hcore := aux_lem_resolvents_to_paths_short_exit_core k (L N) hLk (hLstrong N) h0k
    (fun z => K (omega, z)) hklim hlim0 Q hQo c hρ hball hlam hη hη1 hh'r.le hexp hshort hclose
    y (by rw [← Metric.mem_ball]; exact hyc)
  calc KN N (omega, y) {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤
        ((Real.toNNReal (1 / lam) : ℝ≥0) : ℝ≥0∞)} ≤ ENNReal.ofReal (18 * η) := hcore
    _ ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal (by linarith)


/-! ### RtpCount -/

/-- Exit time from the ball of radius `ρ` about the starting point. -/
def aux_lem_resolvents_to_paths_ex {d : ℕ} (ρ : ℝ) (p : DiffusionPath d) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (p 0) ρ) p

open Classical in
/-- The exit time from the ball about the start, set to `⊤` when the start is outside `C`. -/
def aux_lem_resolvents_to_paths_tex {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) : ℝ≥0∞ :=
  if p 0 ∈ C then aux_lem_resolvents_to_paths_ex ρ p else ⊤

/-- Successive exit epochs: `σ₀ = 0`, `σ_{j+1} = σ_j + τ̃ ∘ θ_{σ_j}` (`⊤` absorbs). -/
def aux_lem_resolvents_to_paths_sig {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ) :
    ℕ → DiffusionPath d → ℝ≥0∞
  | 0, _ => 0
  | j + 1, p => aux_lem_resolvents_to_paths_sig C ρ j p + aux_lem_resolvents_to_paths_tex C ρ
        (ContinuousPath.shift (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal p)

theorem aux_lem_resolvents_to_paths_ex_eq {d : ℕ} (ρ : ℝ) (p : DiffusionPath d) :
    aux_lem_resolvents_to_paths_ex ρ p = ContinuousPath.exitTime (Metric.ball 0 ρ)
      (p - ContinuousMap.const ℝ≥0 (p 0)) := by
  unfold aux_lem_resolvents_to_paths_ex ContinuousPath.exitTime
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, dist_eq_norm, sub_zero]

theorem aux_lem_resolvents_to_paths_measurable_ex {d : ℕ} (ρ : ℝ) :
    Measurable (aux_lem_resolvents_to_paths_ex (d := d) ρ) := by
  have hΔ : Continuous (fun p : DiffusionPath d => p - ContinuousMap.const ℝ≥0 (p 0)) :=
    continuous_id.sub (ContinuousMap.continuous_const'.comp (ContinuousPath.continuous_eval 0))
  have h := (ContinuousPath.measurable_exitTime (Metric.ball (0 : SpatialCoordinates d) ρ)
    Metric.isOpen_ball).comp hΔ.measurable
  have heq : aux_lem_resolvents_to_paths_ex (d := d) ρ =
      (ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) ρ)) ∘
        (fun p : DiffusionPath d => p - ContinuousMap.const ℝ≥0 (p 0)) := by
    funext p; exact aux_lem_resolvents_to_paths_ex_eq ρ p
  rw [heq]; exact h

theorem aux_lem_resolvents_to_paths_measurable_tex {d : ℕ} (C : Set (SpatialCoordinates d))
    (hC : MeasurableSet C) (ρ : ℝ) :
    Measurable (aux_lem_resolvents_to_paths_tex C ρ) := by
  classical
  unfold aux_lem_resolvents_to_paths_tex
  exact Measurable.ite (hC.preimage (ContinuousPath.continuous_eval 0).measurable)
    (aux_lem_resolvents_to_paths_measurable_ex ρ) measurable_const

theorem aux_lem_resolvents_to_paths_measurable_sig {d : ℕ} (C : Set (SpatialCoordinates d))
    (hC : MeasurableSet C) (ρ : ℝ) (j : ℕ) :
    Measurable (aux_lem_resolvents_to_paths_sig C ρ j) := by
  classical
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hs : Measurable (fun p : DiffusionPath d => ContinuousPath.shift
        (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal p) :=
      aux_lem_resolvents_to_paths_measurable_shift _ (ENNReal.measurable_toNNReal.comp ih)
    exact ih.add ((aux_lem_resolvents_to_paths_measurable_tex C hC ρ).comp hs)

theorem aux_lem_resolvents_to_paths_sig_zero {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) : aux_lem_resolvents_to_paths_sig C ρ 0 p = 0 := rfl

theorem aux_lem_resolvents_to_paths_sig_succ {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (j : ℕ) (p : DiffusionPath d) :
    aux_lem_resolvents_to_paths_sig C ρ (j + 1) p = aux_lem_resolvents_to_paths_sig C ρ j p +
      aux_lem_resolvents_to_paths_tex C ρ
        (ContinuousPath.shift (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal p) := rfl

theorem aux_lem_resolvents_to_paths_sig_succ_top {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) (hj : aux_lem_resolvents_to_paths_sig C ρ j p = ⊤) :
    aux_lem_resolvents_to_paths_sig C ρ (j + 1) p = ⊤ := by
  rw [aux_lem_resolvents_to_paths_sig_succ, hj, top_add]

theorem aux_lem_resolvents_to_paths_sig_mono_succ {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) :
    aux_lem_resolvents_to_paths_sig C ρ j p ≤ aux_lem_resolvents_to_paths_sig C ρ (j + 1) p := by
  rw [aux_lem_resolvents_to_paths_sig_succ]; exact le_self_add

/-- **Front recursion** for the successive exit epochs. -/
theorem aux_lem_resolvents_to_paths_sig_front {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) (ha : aux_lem_resolvents_to_paths_tex C ρ p ≠ ⊤) :
    aux_lem_resolvents_to_paths_sig C ρ (j + 1) p = aux_lem_resolvents_to_paths_tex C ρ p +
      aux_lem_resolvents_to_paths_sig C ρ j
        (ContinuousPath.shift (aux_lem_resolvents_to_paths_tex C ρ p).toNNReal p) := by
  induction j generalizing p with
  | zero =>
    rw [aux_lem_resolvents_to_paths_sig_succ]
    simp [aux_lem_resolvents_to_paths_sig_zero, ContinuousPath.shift_zero]
  | succ j ih =>
    set a := aux_lem_resolvents_to_paths_tex C ρ p with hadef
    set q := ContinuousPath.shift a.toNNReal p with hqdef
    have hIH := ih p ha
    by_cases hb : aux_lem_resolvents_to_paths_sig C ρ j q = ⊤
    · have h1 : aux_lem_resolvents_to_paths_sig C ρ (j + 1) p = ⊤ := by
        rw [hIH, hb, add_top]
      rw [aux_lem_resolvents_to_paths_sig_succ_top C ρ (j + 1) p h1,
        aux_lem_resolvents_to_paths_sig_succ_top C ρ j q hb, add_top]
    · have hne : aux_lem_resolvents_to_paths_sig C ρ (j + 1) p ≠ ⊤ := by
        rw [hIH]; exact ENNReal.add_ne_top.mpr ⟨ha, hb⟩
      rw [aux_lem_resolvents_to_paths_sig_succ C ρ (j + 1) p,
        aux_lem_resolvents_to_paths_sig_succ C ρ j q, hIH, add_assoc]
      congr 2
      rw [hqdef, ContinuousPath.shift_add, ENNReal.toNNReal_add ha hb]

theorem aux_lem_resolvents_to_paths_sig_one {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) :
    aux_lem_resolvents_to_paths_sig C ρ 1 p = aux_lem_resolvents_to_paths_tex C ρ p := by
  rw [aux_lem_resolvents_to_paths_sig_succ, aux_lem_resolvents_to_paths_sig_zero, zero_add]
  simp [ContinuousPath.shift_zero]

theorem aux_lem_resolvents_to_paths_sig_mono {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) : Monotone (fun j => aux_lem_resolvents_to_paths_sig C ρ j p) :=
  monotone_nat_of_le_succ fun j => aux_lem_resolvents_to_paths_sig_mono_succ C ρ j p

theorem aux_lem_resolvents_to_paths_sig_succ_eq_top {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) (ha : aux_lem_resolvents_to_paths_tex C ρ p = ⊤) :
    aux_lem_resolvents_to_paths_sig C ρ (j + 1) p = ⊤ := by
  have h1 : aux_lem_resolvents_to_paths_sig C ρ 1 p ≤ aux_lem_resolvents_to_paths_sig C ρ (j + 1) p :=
    aux_lem_resolvents_to_paths_sig_mono C ρ p (by omega)
  rw [aux_lem_resolvents_to_paths_sig_one, ha] at h1
  exact top_le_iff.mp h1

/-- Exponential weight `e^{-s/h}` of an extended time, `0` at `⊤`. -/
def aux_lem_resolvents_to_paths_wt (h : ℝ) (s : ℝ≥0∞) : ℝ≥0∞ :=
  if s = ⊤ then 0 else ENNReal.ofReal (Real.exp (-s.toReal / h))

theorem aux_lem_resolvents_to_paths_wt_top (h : ℝ) : aux_lem_resolvents_to_paths_wt h ⊤ = 0 := by
  simp [aux_lem_resolvents_to_paths_wt]

theorem aux_lem_resolvents_to_paths_wt_zero (h : ℝ) : aux_lem_resolvents_to_paths_wt h 0 = 1 := by
  simp [aux_lem_resolvents_to_paths_wt]

theorem aux_lem_resolvents_to_paths_wt_add (h : ℝ) (a b : ℝ≥0∞) :
    aux_lem_resolvents_to_paths_wt h (a + b) =
      aux_lem_resolvents_to_paths_wt h a * aux_lem_resolvents_to_paths_wt h b := by
  by_cases ha : a = ⊤
  · simp [ha, aux_lem_resolvents_to_paths_wt_top]
  by_cases hb : b = ⊤
  · simp [hb, aux_lem_resolvents_to_paths_wt_top]
  have hab : a + b ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha, hb⟩
  simp only [aux_lem_resolvents_to_paths_wt, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab]
  rw [ENNReal.toReal_add ha hb, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem aux_lem_resolvents_to_paths_measurable_wt (h : ℝ) :
    Measurable (aux_lem_resolvents_to_paths_wt h) := by
  unfold aux_lem_resolvents_to_paths_wt
  exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (ENNReal.measurable_toReal.neg.div_const h)))

theorem aux_lem_resolvents_to_paths_wt_le_one {h : ℝ} (hh : 0 < h) (s : ℝ≥0∞) :
    aux_lem_resolvents_to_paths_wt h s ≤ 1 := by
  unfold aux_lem_resolvents_to_paths_wt
  split_ifs
  · exact zero_le_one
  · rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr ?_)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ENNReal.toReal_nonneg) hh.le

theorem aux_lem_resolvents_to_paths_wt_le_split {h : ℝ} (hh : 0 < h) {h1 : ℝ} (hh1 : 0 ≤ h1)
    (s : ℝ≥0∞) :
    aux_lem_resolvents_to_paths_wt h s ≤
      {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator 1 s + ENNReal.ofReal (Real.exp (-h1 / h)) := by
  by_cases hs : s ≤ ENNReal.ofReal h1
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} from hs), Pi.one_apply]
    exact (aux_lem_resolvents_to_paths_wt_le_one hh s).trans le_self_add
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} from hs), zero_add]
    unfold aux_lem_resolvents_to_paths_wt
    split_ifs with htop
    · exact bot_le
    · refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      rw [not_le] at hs
      have : h1 < s.toReal := by
        rw [← ENNReal.ofReal_lt_iff_lt_toReal hh1 htop]; exact hs
      exact div_le_div_of_nonneg_right (by linarith) hh.le

theorem aux_lem_resolvents_to_paths_wt_ge {h : ℝ} (hh : 0 < h) {T : ℝ} (hT : 0 ≤ T) {s : ℝ≥0∞}
    (hs : s ≤ ENNReal.ofReal T) :
    ENNReal.ofReal (Real.exp (-T / h)) ≤ aux_lem_resolvents_to_paths_wt h s := by
  have htop : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  unfold aux_lem_resolvents_to_paths_wt
  rw [ite_eq_right htop]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have : s.toReal ≤ T := ENNReal.toReal_le_of_le_ofReal hT hs
  exact div_le_div_of_nonneg_right (by linarith) hh.le

theorem aux_lem_resolvents_to_paths_exitTime_measurable_stopped {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) :
    Measurable[(LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      (LifetimePath.exitTime U : LifetimePath (SpatialCoordinates d) → ℝ≥0∞) := by
  refine measurable_of_Iic fun x => ?_
  induction x with
  | top =>
    have : (LifetimePath.exitTime U : LifetimePath (SpatialCoordinates d) → ℝ≥0∞) ⁻¹'
        Set.Iic ⊤ = Set.univ := by ext w; simp
    rw [this]; exact MeasurableSet.univ
  | coe t =>
    exact (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSet_le' t

/-- Weights read off the exit time are measurable for the stopped σ-algebra trace. -/
theorem aux_lem_resolvents_to_paths_measurable_stopped_comp {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (F : ℝ≥0∞ → ℝ≥0∞) (hF : Measurable F) :
    Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      (fun p : ContinuousPath (SpatialCoordinates d) => F (ContinuousPath.exitTime U p)) := by
  have hc : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace,
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      (LifetimePath.ofContinuousPath (α := SpatialCoordinates d)) := fun s hs => ⟨s, hs, rfl⟩
  have h := hF.comp ((aux_lem_resolvents_to_paths_exitTime_measurable_stopped U hU).comp hc)
  have heq : (fun p : ContinuousPath (SpatialCoordinates d) => F (ContinuousPath.exitTime U p)) =
      F ∘ (LifetimePath.exitTime U ∘ LifetimePath.ofContinuousPath) := by
    funext p; simp [LifetimePath.exitTime_ofContinuousPath]
  rw [heq]; exact h

open Classical in
theorem aux_lem_resolvents_to_paths_tex_of_start {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (p : DiffusionPath d) (z : SpatialCoordinates d) (hp0 : p 0 = z) :
    aux_lem_resolvents_to_paths_tex C ρ p =
      if z ∈ C then ContinuousPath.exitTime (Metric.ball z ρ) p else ⊤ := by
  classical
  unfold aux_lem_resolvents_to_paths_tex aux_lem_resolvents_to_paths_ex
  subst hp0
  rfl

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Geometric decay of the exponential moments of the successive exit epochs**
(`mfd:prop-as-forms`): `E_z e^{-σ_j/h} ≤ γ^j` when `E_y e^{-τ_ρ/h} ≤ γ` for starts in `C`. -/
theorem aux_lem_resolvents_to_paths_sig_moment {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) (ρ : ℝ) {h : ℝ}
    (γ : ℝ≥0∞)
    (hγ : ∀ y ∈ C, ∫⁻ p, aux_lem_resolvents_to_paths_wt h
      (ContinuousPath.exitTime (Metric.ball y ρ) p) ∂k y ≤ γ) :
    ∀ j z, ∫⁻ p, aux_lem_resolvents_to_paths_wt h (aux_lem_resolvents_to_paths_sig C ρ j p) ∂k z
      ≤ γ ^ j := by
  classical
  intro j
  induction j with
  | zero =>
    intro z
    simp only [aux_lem_resolvents_to_paths_sig_zero, aux_lem_resolvents_to_paths_wt_zero,
      lintegral_const, measure_univ, mul_one, pow_zero, le_refl]
  | succ j ih =>
    intro z
    by_cases hz : z ∈ C
    · set U := Metric.ball z ρ with hUdef
      have hU : IsOpen U := Metric.isOpen_ball
      set S : Set (ContinuousPath (SpatialCoordinates d)) :=
        {p | ContinuousPath.exitTime U p < ⊤} with hSdef
      have hSm : MeasurableSet S :=
        measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
      have hae : ∀ᵐ p ∂k z, aux_lem_resolvents_to_paths_wt h
          (aux_lem_resolvents_to_paths_sig C ρ (j + 1) p) =
          S.indicator (fun p => aux_lem_resolvents_to_paths_wt h (ContinuousPath.exitTime U p) *
            aux_lem_resolvents_to_paths_wt h (aux_lem_resolvents_to_paths_sig C ρ j
              (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p))) p := by
        filter_upwards [h0 z] with p hp0
        have htex := aux_lem_resolvents_to_paths_tex_of_start C ρ p z hp0
        rw [ite_eq_left hz] at htex
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS]
          have hne : aux_lem_resolvents_to_paths_tex C ρ p ≠ ⊤ := by
            rw [htex]; exact ne_of_lt hpS
          rw [aux_lem_resolvents_to_paths_sig_front C ρ j p hne, aux_lem_resolvents_to_paths_wt_add,
            htex]
        · rw [Set.indicator_of_notMem hpS]
          have htop : aux_lem_resolvents_to_paths_tex C ρ p = ⊤ := by
            rw [htex]; exact not_lt_top_iff.mp hpS
          rw [aux_lem_resolvents_to_paths_sig_succ_eq_top C ρ j p htop,
            aux_lem_resolvents_to_paths_wt_top]
      rw [lintegral_congr_ae hae, lintegral_indicator hSm]
      have hW := aux_lem_resolvents_to_paths_measurable_stopped_comp U hU _
        (aux_lem_resolvents_to_paths_measurable_wt h)
      have hg : Measurable (fun p => aux_lem_resolvents_to_paths_wt h
          (aux_lem_resolvents_to_paths_sig C ρ j p)) :=
        (aux_lem_resolvents_to_paths_measurable_wt h).comp
          (aux_lem_resolvents_to_paths_measurable_sig C hC ρ j)
      have hSMid := aux_lem_resolvents_to_paths_sm_weighted k L hL hSM U hU z _ hW _ hg
      rw [hSMid]
      calc ∫⁻ p in S, aux_lem_resolvents_to_paths_wt h (ContinuousPath.exitTime U p) *
            ∫⁻ q, aux_lem_resolvents_to_paths_wt h (aux_lem_resolvents_to_paths_sig C ρ j q)
              ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k z
          ≤ ∫⁻ p in S, aux_lem_resolvents_to_paths_wt h (ContinuousPath.exitTime U p) * γ ^ j
              ∂k z := lintegral_mono fun p => by gcongr; exact ih _
        _ ≤ ∫⁻ p, aux_lem_resolvents_to_paths_wt h (ContinuousPath.exitTime U p) * γ ^ j ∂k z :=
            setLIntegral_le_lintegral _ _
        _ = (∫⁻ p, aux_lem_resolvents_to_paths_wt h (ContinuousPath.exitTime U p) ∂k z) * γ ^ j :=
            lintegral_mul_const _ ((aux_lem_resolvents_to_paths_measurable_wt h).comp
              (ContinuousPath.measurable_exitTime U hU))
        _ ≤ γ * γ ^ j := by gcongr; exact hγ z hz
        _ = γ ^ (j + 1) := by rw [pow_succ, mul_comm]
    · have hae : ∀ᵐ p ∂k z, aux_lem_resolvents_to_paths_wt h
          (aux_lem_resolvents_to_paths_sig C ρ (j + 1) p) = 0 := by
        filter_upwards [h0 z] with p hp0
        have htex := aux_lem_resolvents_to_paths_tex_of_start C ρ p z hp0
        rw [ite_eq_right hz] at htex
        rw [aux_lem_resolvents_to_paths_sig_succ_eq_top C ρ j p htex,
          aux_lem_resolvents_to_paths_wt_top]
      rw [lintegral_congr_ae hae, lintegral_zero]
      exact bot_le


/-! ### RtpCount2 -/

/-- The `j`-th epoch is finite and the following gap is at most `δ`. -/
def aux_lem_resolvents_to_paths_gapEv {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (δ : ℝ≥0∞) (j : ℕ) : Set (DiffusionPath d) :=
  {p | aux_lem_resolvents_to_paths_sig C ρ j p ≠ ⊤ ∧ aux_lem_resolvents_to_paths_tex C ρ
    (ContinuousPath.shift (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal p) ≤ δ}

theorem aux_lem_resolvents_to_paths_measurableSet_gapEv {d : ℕ} (C : Set (SpatialCoordinates d))
    (hC : MeasurableSet C) (ρ : ℝ) (δ : ℝ≥0∞) (j : ℕ) :
    MeasurableSet (aux_lem_resolvents_to_paths_gapEv (d := d) C ρ δ j) := by
  have hs := aux_lem_resolvents_to_paths_measurable_sig (d := d) C hC ρ j
  have hsh : Measurable (fun p : DiffusionPath d => ContinuousPath.shift
      (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal p) :=
    aux_lem_resolvents_to_paths_measurable_shift _ (ENNReal.measurable_toNNReal.comp hs)
  exact (hs (measurableSet_singleton ⊤).compl).inter
    (measurableSet_le ((aux_lem_resolvents_to_paths_measurable_tex C hC ρ).comp hsh)
      measurable_const)

theorem aux_lem_resolvents_to_paths_gapEv_front {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (δ : ℝ≥0∞) (j : ℕ) (p : DiffusionPath d)
    (ha : aux_lem_resolvents_to_paths_tex C ρ p ≠ ⊤) :
    p ∈ aux_lem_resolvents_to_paths_gapEv C ρ δ (j + 1) ↔
      ContinuousPath.shift (aux_lem_resolvents_to_paths_tex C ρ p).toNNReal p ∈
        aux_lem_resolvents_to_paths_gapEv C ρ δ j := by
  set q := ContinuousPath.shift (aux_lem_resolvents_to_paths_tex C ρ p).toNNReal p with hqdef
  have hf := aux_lem_resolvents_to_paths_sig_front C ρ j p ha
  simp only [aux_lem_resolvents_to_paths_gapEv, Set.mem_ofPred_eq, hf]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : aux_lem_resolvents_to_paths_sig C ρ j q ≠ ⊤ := fun hb => h1 (by rw [hb, add_top])
    refine ⟨hb, ?_⟩
    rw [ENNReal.toNNReal_add ha hb, ← ContinuousPath.shift_add] at h2
    exact h2
  · rintro ⟨hb, h2⟩
    refine ⟨ENNReal.add_ne_top.mpr ⟨ha, hb⟩, ?_⟩
    rw [ENNReal.toNNReal_add ha hb, ← ContinuousPath.shift_add]
    exact h2

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Each gap is short with small probability** (`mfd:prop-as-forms`): by strong Markov at the
first exit, the probability that the `j`-th gap is at most `δ` is at most the short-exit bound. -/
theorem aux_lem_resolvents_to_paths_gap_prob {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) (ρ : ℝ) (δ : ℝ≥0∞) (hδ : δ ≠ ⊤)
    (β : ℝ≥0∞)
    (hβ : ∀ y ∈ C, k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ δ} ≤ β) :
    ∀ j z, k z (aux_lem_resolvents_to_paths_gapEv C ρ δ j) ≤ β := by
  classical
  intro j
  induction j with
  | zero =>
    intro z
    by_cases hz : z ∈ C
    · refine le_trans (measure_mono_ae ?_) (hβ z hz)
      filter_upwards [h0 z] with p hp0 hp
      have htex := aux_lem_resolvents_to_paths_tex_of_start C ρ p z hp0
      rw [ite_eq_left hz] at htex
      have hp' : aux_lem_resolvents_to_paths_tex C ρ p ≤ δ := by
        have := hp.2
        simpa [aux_lem_resolvents_to_paths_sig_zero, ContinuousPath.shift_zero] using this
      rw [htex] at hp'
      exact hp'
    · have h0' : k z (aux_lem_resolvents_to_paths_gapEv C ρ δ 0) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h0 z] with p hp0 hp
        have htex := aux_lem_resolvents_to_paths_tex_of_start C ρ p z hp0
        rw [ite_eq_right hz] at htex
        have hp' : aux_lem_resolvents_to_paths_tex C ρ p ≤ δ := by
          have := hp.2
          simpa [aux_lem_resolvents_to_paths_sig_zero, ContinuousPath.shift_zero] using this
        rw [htex, top_le_iff] at hp'
        exact hδ hp'
      rw [h0']; exact bot_le
  | succ j ih =>
    intro z
    have hGm := aux_lem_resolvents_to_paths_measurableSet_gapEv (d := d) C hC ρ δ j
    by_cases hz : z ∈ C
    · set U := Metric.ball z ρ with hUdef
      have hU : IsOpen U := Metric.isOpen_ball
      set S : Set (ContinuousPath (SpatialCoordinates d)) :=
        {p | ContinuousPath.exitTime U p < ⊤} with hSdef
      have hSm : MeasurableSet S :=
        measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
      have hae : ∀ᵐ p ∂k z,
          (aux_lem_resolvents_to_paths_gapEv C ρ δ (j + 1)).indicator (1 : DiffusionPath d → ℝ≥0∞) p =
          S.indicator (fun p => (1 : ℝ≥0∞) * (aux_lem_resolvents_to_paths_gapEv C ρ δ j).indicator 1
            (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p)) p := by
        filter_upwards [h0 z] with p hp0
        have htex := aux_lem_resolvents_to_paths_tex_of_start C ρ p z hp0
        rw [ite_eq_left hz] at htex
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS, one_mul]
          have hne : aux_lem_resolvents_to_paths_tex C ρ p ≠ ⊤ := by
            rw [htex]; exact ne_of_lt hpS
          have hiff := aux_lem_resolvents_to_paths_gapEv_front C ρ δ j p hne
          rw [htex] at hiff
          by_cases hq : ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p ∈
              aux_lem_resolvents_to_paths_gapEv C ρ δ j
          · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (hiff.mpr hq)]
            rfl
          · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq (hiff.mp h))]
        · rw [Set.indicator_of_notMem hpS]
          have htop : aux_lem_resolvents_to_paths_tex C ρ p = ⊤ := by
            rw [htex]; exact not_lt_top_iff.mp hpS
          have hnot : p ∉ aux_lem_resolvents_to_paths_gapEv C ρ δ (j + 1) := by
            intro hp
            exact hp.1 (aux_lem_resolvents_to_paths_sig_succ_eq_top C ρ j p htop)
          rw [Set.indicator_of_notMem hnot]
      rw [← lintegral_indicator_one (aux_lem_resolvents_to_paths_measurableSet_gapEv C hC ρ δ _),
        lintegral_congr_ae hae, lintegral_indicator hSm]
      have hW : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
          (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
          (fun _ : ContinuousPath (SpatialCoordinates d) => (1 : ℝ≥0∞)) := measurable_const
      have hg : Measurable ((aux_lem_resolvents_to_paths_gapEv C ρ δ j).indicator
          (1 : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞)) := measurable_one.indicator hGm
      have hSMid := aux_lem_resolvents_to_paths_sm_weighted k L hL hSM U hU z _ hW _ hg
      rw [hSMid]
      calc ∫⁻ p in S, 1 * ∫⁻ q, (aux_lem_resolvents_to_paths_gapEv C ρ δ j).indicator 1 q
            ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k z
          ≤ ∫⁻ p in S, β ∂k z := by
            refine lintegral_mono fun p => ?_
            rw [one_mul, lintegral_indicator_one hGm]
            exact ih _
        _ ≤ ∫⁻ _p, β ∂k z := setLIntegral_le_lintegral _ _
        _ = β := by rw [lintegral_const, measure_univ, mul_one]
    · have h0' : k z (aux_lem_resolvents_to_paths_gapEv C ρ δ (j + 1)) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h0 z] with p hp0 hp
        have htex := aux_lem_resolvents_to_paths_tex_of_start C ρ p z hp0
        rw [ite_eq_right hz] at htex
        exact hp.1 (aux_lem_resolvents_to_paths_sig_succ_eq_top C ρ j p htex)
      rw [h0']; exact bot_le


/-! ### RtpCount3 -/

/-- Between two successive epochs the path stays within `ρ` of its value at the first one. -/
theorem aux_lem_resolvents_to_paths_dist_le_on_interval {d : ℕ} (C : Set (SpatialCoordinates d))
    {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) (p : DiffusionPath d)
    (hfin : aux_lem_resolvents_to_paths_sig C ρ j p ≠ ⊤)
    (hC : p (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal ∈ C) (t : ℝ≥0)
    (ht1 : aux_lem_resolvents_to_paths_sig C ρ j p ≤ t)
    (ht2 : (t : ℝ≥0∞) ≤ aux_lem_resolvents_to_paths_sig C ρ (j + 1) p) :
    dist (p t) (p (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal) ≤ ρ := by
  classical
  set a : ℝ≥0 := (aux_lem_resolvents_to_paths_sig C ρ j p).toNNReal with hadef
  have ha : (a : ℝ≥0∞) = aux_lem_resolvents_to_paths_sig C ρ j p := ENNReal.coe_toNNReal hfin
  set q := ContinuousPath.shift a p with hqdef
  have hq0 : q 0 = p a := by simp [hqdef, ContinuousPath.shift_apply]
  have htexq : aux_lem_resolvents_to_paths_tex C ρ q =
      ContinuousPath.exitTime (Metric.ball (q 0) ρ) q := by
    unfold aux_lem_resolvents_to_paths_tex aux_lem_resolvents_to_paths_ex
    rw [ite_eq_left (hq0 ▸ hC)]
  have hsucc : aux_lem_resolvents_to_paths_sig C ρ (j + 1) p =
      aux_lem_resolvents_to_paths_sig C ρ j p + aux_lem_resolvents_to_paths_tex C ρ q :=
    aux_lem_resolvents_to_paths_sig_succ C ρ j p
  have hat : a ≤ t := by
    have : (a : ℝ≥0∞) ≤ t := ha ▸ ht1
    exact_mod_cast this
  set u : ℝ≥0 := t - a with hudef
  have htu : t = a + u := (add_tsub_cancel_of_le hat).symm
  have hu : (u : ℝ≥0∞) ≤ aux_lem_resolvents_to_paths_tex C ρ q := by
    rw [hsucc, ← ha, htu, ENNReal.coe_add] at ht2
    exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).mp ht2
  have hqu : q u = p t := by rw [hqdef, ContinuousPath.shift_apply, ← htu]
  rw [← hqu, ← hq0]
  rcases lt_or_eq_of_le hu with hlt | heq
  · rw [htexq] at hlt
    have := ContinuousPath.mem_of_lt_exitTime _ q u hlt
    rw [Metric.mem_ball] at this
    exact this.le
  · rw [htexq] at heq
    have hne : ContinuousPath.exitTime (Metric.ball (q 0) ρ) q ≠ ⊤ := by
      rw [← heq]; exact ENNReal.coe_ne_top
    have hfr := ContinuousPath.coordinate_exitTime_mem_frontier (Metric.ball (q 0) ρ)
      Metric.isOpen_ball q (Metric.mem_ball_self hρ) hne
    rw [← heq, ENNReal.toNNReal_coe] at hfr
    exact le_of_eq (Metric.frontier_ball_subset_sphere hfr)

/-- **Epochs control the modulus** (`mfd:prop-as-forms`).  If the path stays in `C` up to `T`, the
`n`-th epoch is after `T`, and every gap starting by `T` is longer than `δ`, then the
oscillation over `[0, T]` at scale `δ` is at most `3ρ`. -/
theorem aux_lem_resolvents_to_paths_modulus_of_epochs {d : ℕ} (C : Set (SpatialCoordinates d))
    {ρ : ℝ} (hρ : 0 < ρ) (T δ : ℝ≥0) (n : ℕ) (p : DiffusionPath d)
    (hstay : ∀ s : ℝ≥0, s ≤ T → p s ∈ C)
    (hn : (T : ℝ≥0∞) < aux_lem_resolvents_to_paths_sig C ρ n p)
    (hgap : ∀ j < n, aux_lem_resolvents_to_paths_sig C ρ j p ≤ T →
      p ∉ aux_lem_resolvents_to_paths_gapEv C ρ (δ : ℝ≥0∞) j) :
    p ∈ ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)) := by
  classical
  set σ := fun j => aux_lem_resolvents_to_paths_sig C ρ j p with hσdef
  -- the key two-point bound for `s ≤ t`
  have key : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) ≤ s + δ → dist (p s) (p t) ≤ 3 * ρ := by
    intro s t hst htT htsδ
    have hsT : s ≤ T := hst.trans htT
    have hex : ∃ i, (s : ℝ≥0∞) < σ (i + 1) := by
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [aux_lem_resolvents_to_paths_sig_zero] at hn
      refine ⟨n - 1, ?_⟩
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
      exact lt_of_le_of_lt (by exact_mod_cast hsT) hn
    set i := Nat.find hex with hidef
    have hi1 : (s : ℝ≥0∞) < σ (i + 1) := Nat.find_spec hex
    have hi0 : σ i ≤ s := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]; simp [hσdef, aux_lem_resolvents_to_paths_sig_zero]
      · obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hlt : i' < Nat.find hex := by rw [← hidef]; omega
        have := Nat.find_min hex hlt
        rw [hi']
        exact not_lt.mp this
    have hin : i + 1 ≤ n := by
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [aux_lem_resolvents_to_paths_sig_zero] at hn
      have : i ≤ n - 1 := Nat.find_min' hex (by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
        exact lt_of_le_of_lt (by exact_mod_cast hsT) hn)
      omega
    have hfin_i : σ i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hi0
    have hσi_le : (σ i).toNNReal ≤ s := by
      have : ((σ i).toNNReal : ℝ≥0∞) ≤ s := by rw [ENNReal.coe_toNNReal hfin_i]; exact hi0
      exact_mod_cast this
    have hCi : p (σ i).toNNReal ∈ C := hstay _ (hσi_le.trans hsT)
    have hds : dist (p s) (p (σ i).toNNReal) ≤ ρ :=
      aux_lem_resolvents_to_paths_dist_le_on_interval C hρ i p hfin_i hCi s hi0 hi1.le
    by_cases hti : (t : ℝ≥0∞) ≤ σ (i + 1)
    · have hdt : dist (p t) (p (σ i).toNNReal) ≤ ρ :=
        aux_lem_resolvents_to_paths_dist_le_on_interval C hρ i p hfin_i hCi t
          (hi0.trans (by exact_mod_cast hst)) hti
      calc dist (p s) (p t) ≤ dist (p s) (p (σ i).toNNReal) + dist (p t) (p (σ i).toNNReal) :=
            dist_triangle_right _ _ _
        _ ≤ 3 * ρ := by linarith
    · rw [not_le] at hti
      have hfin1 : σ (i + 1) ≠ ⊤ := ne_top_of_lt hti
      have hσ1t : (σ (i + 1)).toNNReal ≤ t := by
        have : ((σ (i + 1)).toNNReal : ℝ≥0∞) ≤ t := by
          rw [ENNReal.coe_toNNReal hfin1]; exact hti.le
        exact_mod_cast this
      have hC1 : p (σ (i + 1)).toNNReal ∈ C := hstay _ (hσ1t.trans htT)
      have hin' : i + 1 < n := by
        rcases lt_or_eq_of_le hin with h | h
        · exact h
        · exfalso
          have : σ n < (T : ℝ≥0∞) + 1 := by
            rw [← h]
            exact lt_of_lt_of_le hti (by exact_mod_cast htT.trans (le_add_of_nonneg_right zero_le_one) |>.trans le_rfl)
          have h2 : σ n ≤ T := by rw [← h]; exact hti.le.trans (by exact_mod_cast htT)
          exact absurd hn (not_lt.mpr h2)
      have hg := hgap (i + 1) hin' (hti.le.trans (by exact_mod_cast htT))
      have hlong : (δ : ℝ≥0∞) < aux_lem_resolvents_to_paths_tex C ρ
          (ContinuousPath.shift (σ (i + 1)).toNNReal p) := by
        by_contra hcon
        exact hg ⟨hfin1, not_lt.mp hcon⟩
      have hσ2 : σ (i + 2) = σ (i + 1) + aux_lem_resolvents_to_paths_tex C ρ
          (ContinuousPath.shift (σ (i + 1)).toNNReal p) :=
        aux_lem_resolvents_to_paths_sig_succ C ρ (i + 1) p
      have ht2 : (t : ℝ≥0∞) ≤ σ (i + 2) := by
        rw [hσ2]
        have htsδ' : (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) + δ := by
          have : t ≤ s + δ := by
            rw [← NNReal.coe_le_coe, NNReal.coe_add]; exact htsδ
          exact_mod_cast this
        calc (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) + δ := htsδ'
          _ ≤ σ (i + 1) + aux_lem_resolvents_to_paths_tex C ρ
              (ContinuousPath.shift (σ (i + 1)).toNNReal p) := add_le_add hi1.le hlong.le
      have hdt : dist (p t) (p (σ (i + 1)).toNNReal) ≤ ρ :=
        aux_lem_resolvents_to_paths_dist_le_on_interval C hρ (i + 1) p hfin1 hC1 t hti.le ht2
      have hd1 : dist (p (σ (i + 1)).toNNReal) (p (σ i).toNNReal) ≤ ρ :=
        aux_lem_resolvents_to_paths_dist_le_on_interval C hρ i p hfin_i hCi _
          (by rw [ENNReal.coe_toNNReal hfin1]; exact aux_lem_resolvents_to_paths_sig_mono_succ C ρ i p)
          (by rw [ENNReal.coe_toNNReal hfin1])
      calc dist (p s) (p t) ≤ dist (p s) (p (σ i).toNNReal) +
            dist (p (σ i).toNNReal) (p (σ (i + 1)).toNNReal) +
            dist (p (σ (i + 1)).toNNReal) (p t) := dist_triangle4 _ _ _ _
        _ ≤ 3 * ρ := by
          rw [dist_comm (p (σ i).toNNReal), dist_comm (p (σ (i + 1)).toNNReal) (p t)]
          linarith
  intro s t hs ht hst
  have hst' : dist s t ≤ δ := by
    rw [edist_dist] at hst
    have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp hst
    simpa using this
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total s t with h | h
  · refine key s t h ht ?_
    rw [NNReal.dist_eq] at hst'
    have := le_abs_self ((t : ℝ) - s)
    rw [abs_sub_comm] at this
    linarith
  · rw [dist_comm]
    refine key t s h hs ?_
    rw [NNReal.dist_eq] at hst'
    have := le_abs_self ((s : ℝ) - t)
    linarith


/-! ### RtpCount4 -/

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Modulus bound for one strong Markov family** (`mfd:prop-as-forms`): the modulus fails only
if the path leaves `C`, or `n` exits happen by time `T`, or some gap is short. -/
theorem aux_lem_resolvents_to_paths_modulus_bound {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) {ρ : ℝ} (hρ : 0 < ρ)
    (T δ : ℝ≥0) {h : ℝ} (hh : 0 < h) (γ : ℝ≥0∞)
    (hγ : ∀ y ∈ C, ∫⁻ p, aux_lem_resolvents_to_paths_wt h
      (ContinuousPath.exitTime (Metric.ball y ρ) p) ∂k y ≤ γ)
    (β : ℝ≥0∞)
    (hβ : ∀ y ∈ C, k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ (δ : ℝ≥0∞)} ≤ β)
    (n : ℕ) (z : SpatialCoordinates d) :
    k z (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ ≤
      k z {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ C} +
        ENNReal.ofReal (Real.exp (T / h)) * γ ^ n + n * β := by
  set A : Set (DiffusionPath d) := {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ C} with hAdef
  set B : Set (DiffusionPath d) := {p | aux_lem_resolvents_to_paths_sig C ρ n p ≤ (T : ℝ≥0∞)}
    with hBdef
  have hBm : MeasurableSet B :=
    measurableSet_le (aux_lem_resolvents_to_paths_measurable_sig C hC ρ n) measurable_const
  have hsub : (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ ⊆
      A ∪ B ∪ ⋃ j ∈ Finset.range n, aux_lem_resolvents_to_paths_gapEv C ρ (δ : ℝ≥0∞) j := by
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨⟨hA, hB⟩, hG⟩ := hcon
    apply hp
    refine aux_lem_resolvents_to_paths_modulus_of_epochs C hρ T δ n p ?_ ?_ ?_
    · intro s hs
      by_contra hsC
      exact hA ⟨s, hs, hsC⟩
    · exact not_le.mp hB
    · intro j hj _
      exact hG j hj
  have hBbound : k z B ≤ ENNReal.ofReal (Real.exp (T / h)) * γ ^ n := by
    have hmom := aux_lem_resolvents_to_paths_sig_moment k L hL hSM h0 C hC ρ γ hγ n z
    calc k z B = ∫⁻ p, B.indicator 1 p ∂k z := (lintegral_indicator_one hBm).symm
      _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (T / h)) *
            aux_lem_resolvents_to_paths_wt h (aux_lem_resolvents_to_paths_sig C ρ n p) ∂k z := by
          refine lintegral_mono fun p => ?_
          by_cases hpB : p ∈ B
          · rw [Set.indicator_of_mem hpB, Pi.one_apply]
            have hw := aux_lem_resolvents_to_paths_wt_ge hh (T := (T : ℝ)) T.coe_nonneg
              (s := aux_lem_resolvents_to_paths_sig C ρ n p) (by
                rw [ENNReal.ofReal_coe_nnreal]; exact hpB)
            calc (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (T / h)) *
                  ENNReal.ofReal (Real.exp (-(T : ℝ) / h)) := by
                  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
                  simp [neg_div]
              _ ≤ _ := by gcongr
          · rw [Set.indicator_of_notMem hpB]; exact bot_le
      _ = ENNReal.ofReal (Real.exp (T / h)) * ∫⁻ p,
            aux_lem_resolvents_to_paths_wt h (aux_lem_resolvents_to_paths_sig C ρ n p) ∂k z :=
          lintegral_const_mul _ ((aux_lem_resolvents_to_paths_measurable_wt h).comp
            (aux_lem_resolvents_to_paths_measurable_sig C hC ρ n))
      _ ≤ _ := by gcongr
  have hgap := aux_lem_resolvents_to_paths_gap_prob k L hL hSM h0 C hC ρ (δ : ℝ≥0∞)
    ENNReal.coe_ne_top β hβ
  calc k z (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ
      ≤ k z (A ∪ B ∪ ⋃ j ∈ Finset.range n, aux_lem_resolvents_to_paths_gapEv C ρ (δ : ℝ≥0∞) j) :=
        measure_mono hsub
    _ ≤ k z (A ∪ B) + k z (⋃ j ∈ Finset.range n,
          aux_lem_resolvents_to_paths_gapEv C ρ (δ : ℝ≥0∞) j) := measure_union_le _ _
    _ ≤ (k z A + k z B) + ∑ j ∈ Finset.range n,
          k z (aux_lem_resolvents_to_paths_gapEv C ρ (δ : ℝ≥0∞) j) :=
        add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ (k z A + ENNReal.ofReal (Real.exp (T / h)) * γ ^ n) + ∑ _j ∈ Finset.range n, β :=
        add_le_add (add_le_add le_rfl hBbound) (Finset.sum_le_sum fun j _ => hgap j z)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-! ### RtpModulus -/

theorem aux_lem_resolvents_to_paths_exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h4

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **The modulus bound for the finite-cutoff laws** (`mfd:prop-as-forms`), uniform over every
compact set of starting points for all large cutoffs: containment, short exits and the
successive-exit counting. -/
theorem aux_lem_resolvents_to_paths_uniform_modulus_core
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)))
    (omega : BilateralField d)
    (hfdd : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (L : ℕ → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N x, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
      (KN N (omega, x)) = L N x)
    (hLstrong : ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N))
    (hlimAt : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hkilled : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ (closure (centeredCube (Qc n) (Qr n) (hQr n) :
              Set (SpatialCoordinates d))),
              |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(KN N (omega, x)))
                - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(K (omega, x)))| < eps)
    (hcontK : Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
        ∃ delta : ℝ≥0∞, 0 < delta ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ y ∈ B,
          KN N (omega, y) (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
  intro B hB T r hr eps heps
  by_cases hepsT : eps = ⊤
  · exact ⟨1, one_pos, 0, fun _ _ _ _ => by rw [hepsT]; exact le_top⟩
  by_cases hrT : r = ⊤
  · refine ⟨1, one_pos, 0, fun N _ y _ => ?_⟩
    have huniv : (ContinuousPath.modulusSet (alpha := SpatialCoordinates d) T 1 r) = Set.univ := by
      ext p; simp only [Set.mem_univ, iff_true]
      intro s t _ _ _; rw [hrT]; exact le_top
    rw [huniv, Set.compl_univ, measure_empty]; exact bot_le
  set ε : ℝ := eps.toReal with hεdef
  have hε : 0 < ε := ENNReal.toReal_pos (ne_of_gt heps) hepsT
  have hεeq : ENNReal.ofReal ε = eps := ENNReal.ofReal_toReal hepsT
  set ρ : ℝ := min (r.toReal / 3) 1 with hρdef
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr) hrT
  have hρ : 0 < ρ := lt_min (by positivity) one_pos
  have h3ρ : ENNReal.ofReal (3 * ρ) ≤ r := by
    rw [← ENNReal.ofReal_toReal hrT]
    refine ENNReal.ofReal_le_ofReal ?_
    have := min_le_left (r.toReal / 3) 1
    linarith
  -- containment
  obtain ⟨n0, N1, hBQ, hN1⟩ := aux_lem_resolvents_to_paths_cutoff_containment KN hKN K hK omega
    Qc Qr hQr hQ hkilled hcontK B hB T (ε / 3) (by positivity)
  set Q : Set (SpatialCoordinates d) :=
    (centeredCube (Qc n0) (Qr n0) (hQr n0) : Set (SpatialCoordinates d)) with hQdef
  set CR := closure Q with hCRdef
  have hCRc : IsCompact CR := (centeredCube_isBounded (Qc n0) (hQr n0)).isCompact_closure
  have hCRm : MeasurableSet CR := isClosed_closure.measurableSet
  -- short exits with probability 1/4 give the exponential moment 1/2
  obtain ⟨h1, hh1, N2, hN2⟩ := aux_lem_resolvents_to_paths_cutoff_short_exit PN KN hKN K hK P
    Qc Qr hQr hQ omega hfdd L hL hLstrong hlimAt hkilled hcontK CR hCRc ρ hρ (1 / 4)
    (by norm_num)
  have hh1r : (0 : ℝ) < h1 := by exact_mod_cast hh1
  set hh : ℝ := (h1 : ℝ) / 2 with hhhdef
  have hhpos : 0 < hh := by positivity
  -- the number of exits
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 * Real.exp (T / hh) / ε) (by norm_num : (1:ℝ) < 2)
  -- short exits at the final scale
  obtain ⟨h2, hh2, N3, hN3⟩ := aux_lem_resolvents_to_paths_cutoff_short_exit PN KN hKN K hK P
    Qc Qr hQr hQ omega hfdd L hL hLstrong hlimAt hkilled hcontK CR hCRc ρ hρ
    (ε / (3 * ((n : ℝ) + 1))) (by positivity)
  refine ⟨(h2 : ℝ≥0∞), ENNReal.coe_pos.mpr hh2, max N1 (max N2 N3), fun N hN y hy => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3' : N3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have : IsMarkovKernel (KN N) := hKN N
  set k := (KN N).comap (fun x => (omega, x)) measurable_prodMk_left with hkdef
  have : IsMarkovKernel k := by rw [hkdef]; infer_instance
  have hLk : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L N z := fun z => hL N z
  have h0k : ∀ z, ∀ᵐ p ∂k z, p 0 = z := fun z =>
    aux_lem_resolvents_to_paths_ae_start (PN N omega) (KN N) omega (hfdd N) z
  have hγ : ∀ z ∈ CR, ∫⁻ p, aux_lem_resolvents_to_paths_wt hh
      (ContinuousPath.exitTime (Metric.ball z ρ) p) ∂k z ≤ ENNReal.ofReal (1 / 2) := by
    intro z hz
    have hτm : Measurable (ContinuousPath.exitTime (Metric.ball z ρ) :
        ContinuousPath (SpatialCoordinates d) → ℝ≥0∞) :=
      ContinuousPath.measurable_exitTime _ Metric.isOpen_ball
    have hEm : MeasurableSet {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} := measurableSet_Iic
    calc ∫⁻ p, aux_lem_resolvents_to_paths_wt hh (ContinuousPath.exitTime (Metric.ball z ρ) p) ∂k z
        ≤ ∫⁻ p, ({s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator (1 : ℝ≥0∞ → ℝ≥0∞)
            (ContinuousPath.exitTime (Metric.ball z ρ) p) +
            ENNReal.ofReal (Real.exp (-(h1 : ℝ) / hh))) ∂k z :=
          lintegral_mono fun p => aux_lem_resolvents_to_paths_wt_le_split hhpos h1.coe_nonneg _
      _ = k z {p | ContinuousPath.exitTime (Metric.ball z ρ) p ≤ (h1 : ℝ≥0∞)} +
            ENNReal.ofReal (Real.exp (-(h1 : ℝ) / hh)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
          congr 1
          have : (fun p => {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator (1 : ℝ≥0∞ → ℝ≥0∞)
              (ContinuousPath.exitTime (Metric.ball z ρ) p)) =
              {p : ContinuousPath (SpatialCoordinates d) |
                ContinuousPath.exitTime (Metric.ball z ρ) p ≤ (h1 : ℝ≥0∞)}.indicator
                  (1 : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞) := by
            funext p
            simp only [Set.indicator, Set.mem_ofPred_eq, ENNReal.ofReal_coe_nnreal, Pi.one_apply]
          rw [this, lintegral_indicator_one (measurableSet_le hτm measurable_const)]
      _ ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
          refine add_le_add (hN2 N hN2' z hz) (ENNReal.ofReal_le_ofReal ?_)
          have : -(h1 : ℝ) / hh = -2 := by rw [hhhdef]; field_simp
          rw [this]; exact aux_lem_resolvents_to_paths_exp_neg_two_le
      _ = ENNReal.ofReal (1 / 2) := by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hβ : ∀ z ∈ CR, k z {p | ContinuousPath.exitTime (Metric.ball z ρ) p ≤ (h2 : ℝ≥0∞)} ≤
      ENNReal.ofReal (ε / (3 * ((n : ℝ) + 1))) := fun z hz => hN3 N hN3' z hz
  have hbound := aux_lem_resolvents_to_paths_modulus_bound k (L N) hLk (hLstrong N) h0k CR hCRm
    hρ T h2 hhpos (ENNReal.ofReal (1 / 2)) hγ _ hβ n y
  have hA : k y {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ CR} ≤ ENNReal.ofReal (ε / 3) := by
    refine le_trans (measure_mono ?_) (hN1 N hN1' y hy)
    rintro p ⟨s, hs, hsC⟩
    have hsQ : p s ∉ Q := fun h => hsC (subset_closure h)
    exact (ContinuousPath.exitTime_le_of_notMem Q p s hsQ).trans (by exact_mod_cast hs)
  have hpow : ENNReal.ofReal (Real.exp (T / hh)) * ENNReal.ofReal (1 / 2) ^ n ≤
      ENNReal.ofReal (ε / 3) := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ h2n]
    rw [div_lt_iff₀ hε] at hn
    nlinarith
  have hsum : (n : ℝ≥0∞) * ENNReal.ofReal (ε / (3 * ((n : ℝ) + 1))) ≤ ENNReal.ofReal (ε / 3) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc KN N (omega, y) (ContinuousPath.modulusSet T (h2 : ℝ≥0∞) r)ᶜ
      ≤ k y (ContinuousPath.modulusSet T (h2 : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ :=
        measure_mono (Set.compl_subset_compl.mpr (ContinuousPath.modulusSet_mono h3ρ))
    _ ≤ _ := hbound
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
        add_le_add (add_le_add hA hpow) hsum
    _ = eps := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← hεeq]
        congr 1; ring


/-! ### RtpResolvent -/

/-- A single finite law of continuous paths has an arbitrarily good modulus. -/
theorem aux_lem_resolvents_to_paths_single_modulus {d : ℕ}
    (nu : Measure (DiffusionPath d)) [IsFiniteMeasure nu]
    (T : ℝ≥0) (r : ℝ≥0∞) (hr : 0 < r) (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧ nu (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
  obtain ⟨r', hr', hr'r⟩ : ∃ r' : ℝ, 0 < r' ∧ ENNReal.ofReal r' ≤ r := by
    by_cases hrT : r = ⊤
    · exact ⟨1, one_pos, by rw [hrT]; exact le_top⟩
    · exact ⟨r.toReal, ENNReal.toReal_pos (ne_of_gt hr) hrT, (ENNReal.ofReal_toReal hrT).le⟩
  set F : ℕ → Set (DiffusionPath d) := fun n => (ContinuousPath.modulusSet T
      (ENNReal.ofReal (1 / ((n : ℝ) + 1))) (ENNReal.ofReal r'))ᶜ with hFdef
  have hFm : ∀ n, MeasurableSet (F n) := fun n =>
    (ContinuousPath.measurableSet_modulusSet _ _ _).compl
  have hFanti : Antitone F := by
    intro i j hij p hp
    simp only [hFdef, Set.mem_compl_iff] at hp ⊢
    intro hpi
    apply hp
    intro s t hs ht hst
    refine hpi s t hs ht (hst.trans (ENNReal.ofReal_le_ofReal ?_))
    have hi : (i : ℝ) ≤ j := by exact_mod_cast hij
    gcongr
  have hF0 : ⋂ n, F n = ∅ := by
    ext p
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, hFdef,
      Set.mem_compl_iff, not_not]
    have huc : UniformContinuousOn p (Set.Icc (0 : ℝ≥0) T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous p.continuous.continuousOn
    obtain ⟨ε, hε, hδ⟩ := Metric.uniformContinuousOn_iff.1 huc r' hr'
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, fun s t hs ht hst => ?_⟩
    rw [edist_dist] at hst
    have hst' : dist s t ≤ 1 / ((n : ℝ) + 1) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hst
    have hlt := hδ s ⟨bot_le, hs⟩ t ⟨bot_le, ht⟩ (lt_of_le_of_lt hst' hn)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hlt.le
  have h := tendsto_measure_iInter_atTop (μ := nu) (fun n => (hFm n).nullMeasurableSet)
    hFanti ⟨0, measure_ne_top _ _⟩
  rw [hF0, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds heps)).exists
  refine ⟨ENNReal.ofReal (1 / ((n : ℝ) + 1)), ENNReal.ofReal_pos.mpr (by positivity), ?_⟩
  refine le_trans (measure_mono ?_) hn.le
  exact Set.compl_subset_compl.mpr (ContinuousPath.modulusSet_mono hr'r)

/-- The whole-space discounted functional of a bounded continuous `f` is continuous. -/
theorem aux_lem_resolvents_to_paths_continuous_wf {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (aux_lem_resolvents_to_paths_wf (d := d) lam f) := by
  unfold aux_lem_resolvents_to_paths_wf
  refine continuous_of_dominated (bound := fun t => ‖f‖ * Real.exp (-lam * t)) ?_ ?_ ?_ ?_
  · intro p
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (f.continuous.comp (p.continuous.comp continuous_real_toNNReal))).aestronglyMeasurable
  · intro p
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le
  · exact (exp_neg_integrableOn_Ioi 0 hlam).const_mul _
  · refine Eventually.of_forall fun t => ?_
    exact continuous_const.mul (f.continuous.comp (continuous_eval_const _))

/-- The whole-space functional as a bounded continuous function on path space. -/
def aux_lem_resolvents_to_paths_wfBCF {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    BoundedContinuousFunction (DiffusionPath d) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨aux_lem_resolvents_to_paths_wf lam f, aux_lem_resolvents_to_paths_continuous_wf hlam f⟩
    (2 * (‖f‖ / lam)) (by
      intro p q
      have hb : ∀ p : DiffusionPath d, |aux_lem_resolvents_to_paths_wf lam f p| ≤ ‖f‖ / lam := by
        intro p
        unfold aux_lem_resolvents_to_paths_wf
        rw [← Real.norm_eq_abs]
        calc ‖∫ t in Set.Ioi (0:ℝ), Real.exp (-lam * t) * f (p (Real.toNNReal t))‖
            ≤ ∫ t in Set.Ioi (0:ℝ), ‖f‖ * Real.exp (-lam * t) :=
              norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).const_mul _)
                (Eventually.of_forall fun t => by
                  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
                  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le)
          _ = ‖f‖ / lam := by
              rw [integral_const_mul, aux_lem_resolvents_to_paths_integral_exp_Ioi hlam 0]
              simp only [mul_zero, Real.exp_zero]; ring
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := hb p; have h2 := hb q
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith)

theorem aux_lem_resolvents_to_paths_wfBCF_apply {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (p : DiffusionPath d) :
    aux_lem_resolvents_to_paths_wfBCF hlam f p = aux_lem_resolvents_to_paths_wf lam f p := rfl

/-- Integrated whole-versus-killed comparison. -/
theorem aux_lem_resolvents_to_paths_abs_integral_wf_sub_kf {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsProbabilityMeasure μ] (U : Set (SpatialCoordinates d)) (hU : IsOpen U) {lam : ℝ}
    (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) {S : ℝ}
    (hS : 0 ≤ S) :
    |(∫ p, aux_lem_resolvents_to_paths_wf lam f p ∂μ) -
        ∫ p, aux_lem_resolvents_to_paths_kf U lam f p ∂μ| ≤
      ‖f‖ / lam * (μ.real {p | ContinuousPath.exitTime U p ≤ ENNReal.ofReal S} +
        Real.exp (-lam * S)) := by
  have hM : ∀ z, |f z| ≤ ‖f‖ := fun z => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm z
  have hwfi : Integrable (aux_lem_resolvents_to_paths_wf lam f) μ :=
    (aux_lem_resolvents_to_paths_wfBCF hlam f).integrable μ
  have hkfi := aux_lem_resolvents_to_paths_integrable_kf μ U hU hlam f f.continuous.measurable
    ‖f‖ hM
  set E : Set (DiffusionPath d) := {p | ContinuousPath.exitTime U p ≤ ENNReal.ofReal S} with hEdef
  have hEm : MeasurableSet E :=
    measurableSet_le (ContinuousPath.measurable_exitTime U hU) measurable_const
  rw [← integral_sub hwfi hkfi]
  calc |∫ p, (aux_lem_resolvents_to_paths_wf lam f p - aux_lem_resolvents_to_paths_kf U lam f p) ∂μ|
      ≤ ∫ p, |aux_lem_resolvents_to_paths_wf lam f p - aux_lem_resolvents_to_paths_kf U lam f p| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, ‖f‖ / lam * (E.indicator (fun _ => (1 : ℝ)) p + Real.exp (-lam * S)) ∂μ := by
        refine integral_mono ((hwfi.sub hkfi).abs)
          ((((integrable_const (μ := μ) (1 : ℝ)).indicator hEm).add (integrable_const _)).const_mul _)
          fun p => ?_
        exact aux_lem_resolvents_to_paths_abs_wf_sub_kf_le U hlam f f.continuous.measurable ‖f‖ hM p hS
    _ = ‖f‖ / lam * (μ.real E + Real.exp (-lam * S)) := by
        rw [integral_const_mul, integral_add ((integrable_const (1:ℝ)).indicator hEm)
          (integrable_const _), aux_lem_resolvents_to_paths_integral_indicator_one μ _ hEm,
          integral_const, probReal_univ, one_smul]


/-! ### RtpResolvent2 -/

/-- **Removing the killing at moving starts** (`mfd:prop-as-forms`): the whole-space resolvent
functionals of the finite-cutoff laws started at `u n → x` converge to those of the limit law
at `x`.  Localisation on a large cube with small exit probability (finite-cutoff and limit
containment), `hkilled` on that cube, and weak continuity of the limit in the start. -/
theorem aux_lem_resolvents_to_paths_resolvent_moving'
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)))
    (hkilled : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ (closure (centeredCube (Qc n) (Qr n) (hQr n) :
              Set (SpatialCoordinates d))),
              |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(KN N (omega, x)))
                - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(K (omega, x)))| < eps)
    (hcontK : Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) :
    ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Tendsto (fun n ↦ ∫ path, aux_lem_resolvents_to_paths_wf lam f path
            ∂(KN (φ n) (omega, u n)))
          atTop (𝓝 (∫ path, aux_lem_resolvents_to_paths_wf lam f path ∂(K (omega, x)))) := by
  intro u x φ hφ hu lam hlam f
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M := ‖f‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  set B' : Set (SpatialCoordinates d) := insert x (Set.range u) with hB'def
  have hB' : IsCompact B' := hu.isCompact_insert_range
  -- the horizon
  obtain ⟨L0, hL0⟩ := exists_nat_gt (8 * (M / lam + 1) / ε)
  set S : ℝ := (L0 : ℝ) / lam with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hSexp : M / lam * Real.exp (-lam * S) ≤ ε / 8 := by
    have e1 : -lam * S = -(L0 : ℝ) := by rw [hSdef]; field_simp
    rw [e1]
    have h1 : (L0 : ℝ) + 1 ≤ Real.exp L0 := by linarith [Real.add_one_le_exp (L0 : ℝ)]
    have hpos : 0 < Real.exp (L0 : ℝ) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have hL0' : 8 * (M / lam + 1) < ε * L0 := by
      rw [div_lt_iff₀ hε] at hL0; linarith
    have : M / lam ≤ ε / 8 * (L0 : ℝ) := by nlinarith [div_nonneg hM0 hlam.le]
    nlinarith
  set ε1 : ℝ := ε / (8 * (M / lam + 1)) with hε1def
  have hε1 : 0 < ε1 := by positivity
  have hε1b : M / lam * ε1 ≤ ε / 8 := by
    rw [hε1def, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ M / lam := div_nonneg hM0 hlam.le
    nlinarith
  -- limit containment on `B'`
  obtain ⟨R, hR, hRc⟩ := aux_lem_resolvents_to_paths_limit_containment
    (fun y => jointPathProbabilityMeasure K hK omega y) hcontK B' hB' (Real.toNNReal S)
    (ENNReal.ofReal ε1) (ENNReal.ofReal_pos.mpr hε1)
  -- finite-cutoff containment on the larger compact set
  have hB'' : IsCompact (Metric.closedBall (0 : SpatialCoordinates d) R ∪ B') :=
    (isCompact_closedBall 0 R).union hB'
  obtain ⟨n1, N1, hsubQ, hN1⟩ := aux_lem_resolvents_to_paths_cutoff_containment KN hKN K hK omega
    Qc Qr hQr hQ hkilled hcontK _ hB'' (Real.toNNReal S) ε1 hε1
  set Q : Set (SpatialCoordinates d) :=
    (centeredCube (Qc n1) (Qr n1) (hQr n1) : Set (SpatialCoordinates d)) with hQdef
  have hQo : IsOpen Q := (centeredCube (Qc n1) (Qr n1) (hQr n1)).isOpen
  -- killed convergence on `Q`
  obtain ⟨N2, hN2⟩ := hkilled n1 lam hlam f (ε / 8) (by positivity)
  -- weak convergence of the limit laws
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    ((hcontK.tendsto x).comp hu)) (aux_lem_resolvents_to_paths_wfBCF hlam f)
  obtain ⟨n3, hn3⟩ := Metric.tendsto_atTop.mp hweak (ε / 8) (by positivity)
  refine ⟨max n3 (max N1 N2), fun n hn => ?_⟩
  have hn3' : n3 ≤ n := le_trans (le_max_left _ _) hn
  have hφn : max N1 N2 ≤ φ n := le_trans (le_trans (le_max_right _ _) hn) (hφ.id_le n)
  have hN1' : N1 ≤ φ n := le_trans (le_max_left _ _) hφn
  have hN2' : N2 ≤ φ n := le_trans (le_max_right _ _) hφn
  have hun : u n ∈ B' := Set.mem_insert_of_mem x ⟨n, rfl⟩
  have : IsProbabilityMeasure (KN (φ n) (omega, u n)) := (hKN _).isProbabilityMeasure _
  have : IsProbabilityMeasure (K (omega, u n)) := hK.isProbabilityMeasure _
  have hEeq : {p : DiffusionPath d | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S} =
      {p | ContinuousPath.exitTime Q p ≤ ((Real.toNNReal S : ℝ≥0) : ℝ≥0∞)} := rfl
  -- term 1: finite cutoff, whole vs killed
  have t1 := aux_lem_resolvents_to_paths_abs_integral_wf_sub_kf (KN (φ n) (omega, u n)) Q hQo hlam
    f hS0
  have hE1 : (KN (φ n) (omega, u n)).real
      {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S} ≤ ε1 := by
    rw [hEeq, measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hε1.le (hN1 (φ n) hN1' (u n) (Or.inr hun))
  -- term 3: limit at `u n`, whole vs killed
  have t3 := aux_lem_resolvents_to_paths_abs_integral_wf_sub_kf (K (omega, u n)) Q hQo hlam f hS0
  have hE3 : (K (omega, u n)).real {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S} ≤ ε1 := by
    have hsub : {p : DiffusionPath d | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S} ⊆
        {p | ∃ s : ℝ≥0, s ≤ Real.toNNReal S ∧ R ≤ ‖p s‖} := by
      intro p hp
      have hp' : ContinuousPath.exitTime Q p ≤ ((Real.toNNReal S : ℝ≥0) : ℝ≥0∞) := hp
      obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy Q hQo _ p).mp hp'
      refine ⟨s, s.2, ?_⟩
      have hsQ : p s ∉ Q := hs
      by_contra hlt
      rw [not_le] at hlt
      exact hsQ (hsubQ (Or.inl (by rw [Metric.mem_closedBall, dist_zero_right]; exact hlt.le)))
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hε1.le ((measure_mono hsub).trans (hRc (u n) hun).le)
  -- term 2: killed convergence
  have t2 := hN2 (φ n) hN2' (u n) (subset_closure (hsubQ (Or.inr hun)))
  -- term 4: weak convergence
  have t4 := hn3 n hn3'
  rw [Real.dist_eq] at t4 ⊢
  simp only [Function.comp, aux_lem_resolvents_to_paths_wfBCF_apply] at t4
  change |(∫ p, aux_lem_resolvents_to_paths_wf lam f p ∂(K (omega, u n))) -
    ∫ p, aux_lem_resolvents_to_paths_wf lam f p ∂(K (omega, x))| < ε / 8 at t4
  change |(∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂(KN (φ n) (omega, u n))) -
    ∫ p, aux_lem_resolvents_to_paths_kf Q lam f p ∂(K (omega, u n))| < ε / 8 at t2
  have b1 : ‖f‖ / lam * ((KN (φ n) (omega, u n)).real
      {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S} + Real.exp (-lam * S)) ≤ ε / 4 := by
    have : ‖f‖ / lam * ((KN (φ n) (omega, u n)).real
        {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S}) ≤ M / lam * ε1 :=
      mul_le_mul_of_nonneg_left hE1 (div_nonneg hM0 hlam.le)
    rw [mul_add]; linarith
  have b3 : ‖f‖ / lam * ((K (omega, u n)).real
      {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S} + Real.exp (-lam * S)) ≤ ε / 4 := by
    have : ‖f‖ / lam * ((K (omega, u n)).real
        {p | ContinuousPath.exitTime Q p ≤ ENNReal.ofReal S}) ≤ M / lam * ε1 :=
      mul_le_mul_of_nonneg_left hE3 (div_nonneg hM0 hlam.le)
    rw [mul_add]; linarith
  have a1 := abs_le.mp (t1.trans b1)
  have a3 := abs_le.mp (t3.trans b3)
  have a2 := abs_sub_lt_iff.mp t2
  have a4 := abs_sub_lt_iff.mp t4
  rw [abs_sub_lt_iff]
  constructor <;> linarith [a1.1, a1.2, a3.1, a3.2, a2.1, a2.2, a4.1, a4.2]


/-! ### RtpLaplace -/

/-- The bump `κ(t) = max 0 ((t - t₀)(t₀ + δ - t))`, supported in `[t₀, t₀ + δ]`. -/
def aux_lem_resolvents_to_paths_bump (t0 δ t : ℝ) : ℝ := max 0 ((t - t0) * (t0 + δ - t))

theorem aux_lem_resolvents_to_paths_bump_nonneg (t0 δ t : ℝ) :
    0 ≤ aux_lem_resolvents_to_paths_bump t0 δ t := le_max_left _ _

theorem aux_lem_resolvents_to_paths_bump_continuous (t0 δ : ℝ) :
    Continuous (aux_lem_resolvents_to_paths_bump t0 δ) := by
  unfold aux_lem_resolvents_to_paths_bump
  fun_prop

theorem aux_lem_resolvents_to_paths_bump_eq_zero {t0 δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : t ∉ Set.Ioo t0 (t0 + δ)) : aux_lem_resolvents_to_paths_bump t0 δ t = 0 := by
  unfold aux_lem_resolvents_to_paths_bump
  apply max_eq_left
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at ht
  rcases ht with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem aux_lem_resolvents_to_paths_bump_pos {t0 δ t : ℝ} (ht : t ∈ Set.Ioo t0 (t0 + δ)) :
    0 < aux_lem_resolvents_to_paths_bump t0 δ t := by
  unfold aux_lem_resolvents_to_paths_bump
  exact lt_max_of_lt_right (mul_pos (by linarith [ht.1]) (by linarith [ht.2]))

theorem aux_lem_resolvents_to_paths_bump_le_exp {t0 δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    aux_lem_resolvents_to_paths_bump t0 δ t ≤ δ ^ 2 * Real.exp (t0 + δ) * Real.exp (-t) := by
  by_cases ht : t ∈ Set.Ioo t0 (t0 + δ)
  · have h1 : aux_lem_resolvents_to_paths_bump t0 δ t ≤ δ ^ 2 := by
      unfold aux_lem_resolvents_to_paths_bump
      apply max_le (by positivity)
      nlinarith [sq_nonneg (t - t0 - δ / 2), ht.1, ht.2]
    have h2 : 1 ≤ Real.exp (t0 + δ) * Real.exp (-t) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [ht.2])
    calc _ ≤ δ ^ 2 := h1
      _ = δ ^ 2 * 1 := (mul_one _).symm
      _ ≤ δ ^ 2 * (Real.exp (t0 + δ) * Real.exp (-t)) := by gcongr
      _ = _ := by ring
  · rw [aux_lem_resolvents_to_paths_bump_eq_zero hδ ht]; positivity

/-- **Weierstrass in the variable `e^{-t}`**: the bump is uniformly approximated, with weight
`e^{-t}`, by `e^{-t} q(e^{-t})` for a polynomial `q`. -/
theorem aux_lem_resolvents_to_paths_bump_poly_approx {t0 δ : ℝ} (hδ : 0 < δ) {η : ℝ}
    (hη : 0 < η) :
    ∃ q : Polynomial ℝ, ∀ t : ℝ, 0 ≤ t →
      |aux_lem_resolvents_to_paths_bump t0 δ t - Real.exp (-t) * q.eval (Real.exp (-t))| ≤
        η * Real.exp (-t) := by
  classical
  set k : ℝ → ℝ := fun u => if u ≤ 0 then 0 else
    aux_lem_resolvents_to_paths_bump t0 δ (-Real.log u) / u with hkdef
  have hk : ContinuousOn k (Set.Icc 0 1) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · have hev : k =ᶠ[𝓝 u] fun _ => 0 := by
        rw [← h0]
        have hpos' : 0 < Real.exp (-(t0 + δ)) := Real.exp_pos _
        filter_upwards [Iio_mem_nhds hpos'] with v hv
        simp only [hkdef]
        split_ifs with hv0
        · rfl
        · rw [not_le] at hv0
          have hlt : t0 + δ < -Real.log v := by
            have := Real.log_lt_log hv0 hv
            rw [Real.log_exp] at this; linarith
          rw [aux_lem_resolvents_to_paths_bump_eq_zero hδ.le (fun h => by linarith [h.2])]
          simp
      exact continuousAt_const.congr hev.symm
    · have hev : k =ᶠ[𝓝 u] fun v => aux_lem_resolvents_to_paths_bump t0 δ (-Real.log v) / v := by
        filter_upwards [Ioi_mem_nhds hpos] with v hv
        simp only [hkdef, ite_eq_right (not_le.mpr (show (0:ℝ) < v from hv))]
      refine ContinuousAt.congr ?_ hev.symm
      exact (((aux_lem_resolvents_to_paths_bump_continuous t0 δ).continuousAt.comp
        (Real.continuousAt_log hpos.ne').neg)).div continuousAt_id hpos.ne'
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 k hk η hη
  refine ⟨q, fun t ht => ?_⟩
  have he := Real.exp_pos (-t)
  have hu : Real.exp (-t) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨he.le, Real.exp_le_one_iff.mpr (by linarith)⟩
  have h := hq _ hu
  have hku : k (Real.exp (-t)) = aux_lem_resolvents_to_paths_bump t0 δ t / Real.exp (-t) := by
    simp only [hkdef, ite_eq_right (not_le.mpr he), Real.log_exp, neg_neg]
  rw [hku] at h
  have heq : aux_lem_resolvents_to_paths_bump t0 δ t - Real.exp (-t) * q.eval (Real.exp (-t)) =
      -(Real.exp (-t) * (q.eval (Real.exp (-t)) -
        aux_lem_resolvents_to_paths_bump t0 δ t / Real.exp (-t))) := by
    field_simp; ring
  rw [heq, abs_neg, abs_mul, abs_of_pos he, mul_comm η]
  exact mul_le_mul_of_nonneg_left h.le he.le

/-- Laplace data at the integer frequencies determine the integrals against `e^{-t} q(e^{-t})`. -/
theorem aux_lem_resolvents_to_paths_laplace_poly {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgb : ∀ t, |g t| ≤ C) (q : Polynomial ℝ) :
    ∫ t in Set.Ioi (0:ℝ), (Real.exp (-t) * q.eval (Real.exp (-t))) * g t =
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i *
        ∫ t in Set.Ioi (0:ℝ), Real.exp (-((i : ℝ) + 1) * t) * g t := by
  have hint : ∀ i : ℕ, IntegrableOn (fun t => q.coeff i * (Real.exp (-((i : ℝ) + 1) * t) * g t))
      (Set.Ioi 0) := by
    intro i
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by positivity : (0:ℝ) < (i:ℝ) + 1)).const_mul C)
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hg).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb t) (Real.exp_pos _).le
  have hpt : ∀ t, (Real.exp (-t) * q.eval (Real.exp (-t))) * g t =
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (Real.exp (-((i : ℝ) + 1) * t) * g t) := by
    intro t
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Real.exp (-((i : ℝ) + 1) * t) = Real.exp (-t) * Real.exp (-t) ^ i := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]

/-- **Laplace inversion under equicontinuity** (`mfd:prop-as-forms`, the identification of the
one-time marginals).  Bounded functions whose integer-frequency Laplace transforms converge,
and which are (eventually) equicontinuous from the right at `t₀`, converge at `t₀`. -/
theorem aux_lem_resolvents_to_paths_laplace_pointwise (a : ℕ → ℝ → ℝ) (b : ℝ → ℝ) {C : ℝ}
    (ha : ∀ n, Measurable (a n)) (hb : Measurable b)
    (hab : ∀ n t, |a n t| ≤ C) (hbb : ∀ t, |b t| ≤ C)
    (hlap : ∀ m : ℕ, Tendsto (fun n => ∫ t in Set.Ioi (0:ℝ), Real.exp (-((m : ℝ) + 1) * t) * a n t)
      atTop (𝓝 (∫ t in Set.Ioi (0:ℝ), Real.exp (-((m : ℝ) + 1) * t) * b t)))
    {t0 : ℝ} (ht0 : 0 ≤ t0)
    (hequi : ∀ ε > 0, ∃ δ > 0, ∀ᶠ n in atTop, ∀ s, t0 ≤ s → s ≤ t0 + δ → |a n s - a n t0| ≤ ε)
    (hbcont : ∀ ε > 0, ∃ δ > 0, ∀ s, t0 ≤ s → s ≤ t0 + δ → |b s - b t0| ≤ ε) :
    Tendsto (fun n => a n t0) atTop (𝓝 (b t0)) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbb 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / 5 with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ1, hδ1, hev1⟩ := hequi ε' hε'
  obtain ⟨δ2, hδ2, hb2⟩ := hbcont ε' hε'
  set δ := min δ1 δ2 with hδdef
  have hδ : 0 < δ := lt_min hδ1 hδ2
  set κ := aux_lem_resolvents_to_paths_bump t0 δ with hκdef
  have hκ0 : ∀ t, 0 ≤ κ t := aux_lem_resolvents_to_paths_bump_nonneg t0 δ
  have hκc : Continuous κ := aux_lem_resolvents_to_paths_bump_continuous t0 δ
  set K0 : ℝ := δ ^ 2 * Real.exp (t0 + δ) with hK0def
  have hκe : ∀ t, κ t ≤ K0 * Real.exp (-t) := aux_lem_resolvents_to_paths_bump_le_exp hδ.le
  have hexpi : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (zero_lt_one : (0:ℝ) < 1)
  have hκi : IntegrableOn κ (Set.Ioi 0) :=
    Integrable.mono' (hexpi.const_mul K0) hκc.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hκ0 t)]; exact hκe t)
  -- integrability of `κ g` for bounded measurable `g`
  have hκg : ∀ g : ℝ → ℝ, Measurable g → (∀ t, |g t| ≤ C) →
      IntegrableOn (fun t => κ t * g t) (Set.Ioi 0) := by
    intro g hg hgb
    refine Integrable.mono' (hκi.mul_const C) (hκc.measurable.mul hg).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hκ0 t)]
    exact mul_le_mul_of_nonneg_left (hgb t) (hκ0 t)
  -- the normalisation
  set c : ℝ := ∫ t in Set.Ioi (0:ℝ), κ t with hcdef
  have hc : 0 < c := by
    rw [hcdef, integral_pos_iff_support_of_nonneg hκ0 hκi]
    have hsub : Set.Ioo t0 (t0 + δ) ⊆ Function.support κ := fun t ht =>
      (aux_lem_resolvents_to_paths_bump_pos ht).ne'
    calc (0 : ℝ≥0∞) < volume (Set.Ioo t0 (t0 + δ)) := by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
      _ = (volume.restrict (Set.Ioi (0:ℝ))) (Set.Ioo t0 (t0 + δ)) := by
          rw [Measure.restrict_apply measurableSet_Ioo,
            Set.inter_eq_left.mpr (show Set.Ioo t0 (t0 + δ) ⊆ Set.Ioi 0 from
              fun t ht => lt_of_le_of_lt ht0 ht.1)]
      _ ≤ _ := measure_mono hsub
  -- (i) averaging error
  have havg : ∀ g : ℝ → ℝ, Measurable g → (∀ t, |g t| ≤ C) →
      (∀ s, t0 ≤ s → s ≤ t0 + δ → |g s - g t0| ≤ ε') →
      |c * g t0 - ∫ t in Set.Ioi (0:ℝ), κ t * g t| ≤ ε' * c := by
    intro g hg hgb hgc
    have hsplit : c * g t0 - ∫ t in Set.Ioi (0:ℝ), κ t * g t =
        ∫ t in Set.Ioi (0:ℝ), κ t * (g t0 - g t) := by
      rw [hcdef, ← integral_mul_const, ← integral_sub (hκi.mul_const _) (hκg g hg hgb)]
      congr 1; funext t; ring
    rw [hsplit]
    have hint2 : IntegrableOn (fun t => κ t * (g t0 - g t)) (Set.Ioi 0) := by
      have := (hκi.mul_const (g t0)).sub (hκg g hg hgb)
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.sub_apply]; ring
    calc |∫ t in Set.Ioi (0:ℝ), κ t * (g t0 - g t)|
        ≤ ∫ t in Set.Ioi (0:ℝ), |κ t * (g t0 - g t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioi (0:ℝ), κ t * ε' := by
          refine integral_mono hint2.abs (hκi.mul_const _) fun t => ?_
          · rw [abs_mul, abs_of_nonneg (hκ0 t)]
            by_cases ht : t ∈ Set.Ioo t0 (t0 + δ)
            · exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hgc t ht.1.le ht.2.le)
                (hκ0 t)
            · have : κ t = 0 := aux_lem_resolvents_to_paths_bump_eq_zero hδ.le ht
              rw [this]; simp
      _ = ε' * c := by rw [integral_mul_const, mul_comm]
  -- (iii) polynomial approximation
  set η : ℝ := ε' * c / (2 * C + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨q, hq⟩ := aux_lem_resolvents_to_paths_bump_poly_approx (t0 := t0) hδ hη
  set pq : ℝ → ℝ := fun t => Real.exp (-t) * q.eval (Real.exp (-t)) with hpqdef
  have hpqm : Measurable pq := by
    simp only [hpqdef]
    exact (Real.measurable_exp.comp measurable_neg).mul
      ((Polynomial.continuous q).measurable.comp (Real.measurable_exp.comp measurable_neg))
  have happrox : ∀ g : ℝ → ℝ, Measurable g → (∀ t, |g t| ≤ C) →
      |(∫ t in Set.Ioi (0:ℝ), κ t * g t) - ∫ t in Set.Ioi (0:ℝ), pq t * g t| ≤ C * η := by
    intro g hg hgb
    have hpqi : IntegrableOn (fun t => pq t * g t) (Set.Ioi 0) := by
      have : ∀ t ∈ Set.Ioi (0:ℝ), |pq t * g t| ≤ (K0 + η) * C * Real.exp (-t) := by
        intro t ht
        have h1 := hq t (le_of_lt ht)
        have h2 : |pq t| ≤ (K0 + η) * Real.exp (-t) := by
          have := abs_sub_abs_le_abs_sub (pq t) (κ t)
          rw [abs_sub_comm] at h1
          have hk := hκe t
          rw [abs_of_nonneg (hκ0 t)] at this
          nlinarith [Real.exp_pos (-t)]
        rw [abs_mul]
        calc |pq t| * |g t| ≤ (K0 + η) * Real.exp (-t) * C :=
              mul_le_mul h2 (hgb t) (abs_nonneg _) (by positivity)
          _ = _ := by ring
      refine Integrable.mono' ((hexpi.const_mul ((K0 + η) * C))) (hpqm.mul hg).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun t ht => by rw [Real.norm_eq_abs]; exact this t ht
    rw [← integral_sub (hκg g hg hgb) hpqi]
    calc |∫ t in Set.Ioi (0:ℝ), (κ t * g t - pq t * g t)|
        ≤ ∫ t in Set.Ioi (0:ℝ), |κ t * g t - pq t * g t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioi (0:ℝ), C * η * Real.exp (-t) := by
          refine setIntegral_mono_on ((hκg g hg hgb).sub hpqi).abs (hexpi.const_mul _)
            measurableSet_Ioi fun t ht => ?_
          rw [← sub_mul, abs_mul]
          calc |κ t - pq t| * |g t| ≤ η * Real.exp (-t) * C :=
                mul_le_mul (hq t (le_of_lt ht)) (hgb t) (abs_nonneg _) (by positivity)
            _ = C * η * Real.exp (-t) := by ring
      _ = C * η := by
          rw [integral_const_mul]
          have := aux_lem_resolvents_to_paths_integral_exp_Ioi (zero_lt_one : (0:ℝ) < 1) 0
          simp only [neg_mul, one_mul, mul_zero, Real.exp_zero, div_one] at this
          rw [this, mul_one]
  have hCη : C * η ≤ ε' * c / 2 := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ ε' * c := by positivity
    nlinarith
  -- (iv) Laplace convergence against `pq`
  have hlim : Tendsto (fun n => ∫ t in Set.Ioi (0:ℝ), pq t * a n t) atTop
      (𝓝 (∫ t in Set.Ioi (0:ℝ), pq t * b t)) := by
    simp only [hpqdef]
    rw [aux_lem_resolvents_to_paths_laplace_poly hb hbb q]
    simp_rw [aux_lem_resolvents_to_paths_laplace_poly (ha _) (hab _) q]
    exact tendsto_finsetSum _ fun i _ => (hlap i).const_mul _
  obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.mp hlim (ε' * c) (by positivity)
  obtain ⟨n2, hn2⟩ := eventually_atTop.mp hev1
  refine ⟨max n1 n2, fun n hn => ?_⟩
  have e1 := havg (a n) (ha n) (hab n) (fun s h1 h2 =>
    hn2 n (le_trans (le_max_right _ _) hn) s h1 (h2.trans (by linarith [min_le_left δ1 δ2])))
  have e2 := havg b hb hbb (fun s h1 h2 => hb2 s h1 (h2.trans (by linarith [min_le_right δ1 δ2])))
  have e3 := happrox (a n) (ha n) (hab n)
  have e4 := happrox b hb hbb
  have e5 := hn1 n (le_trans (le_max_left _ _) hn)
  rw [Real.dist_eq] at e5 ⊢
  have key : c * |a n t0 - b t0| < c * ε := by
    rw [← abs_of_pos hc, ← abs_mul, abs_of_pos hc]
    have := abs_sub_lt_iff.mp e5
    rw [abs_le] at e1 e2 e3 e4
    rw [abs_lt]
    constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
  exact lt_of_mul_lt_mul_left key hc.le


/-! ### RtpMarginal -/

theorem aux_lem_resolvents_to_paths_continuous_marginal {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsProbabilityMeasure μ] (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (fun s : ℝ => ∫ p, h (p (Real.toNNReal s)) ∂μ) := by
  refine continuous_of_dominated (bound := fun _ => ‖h‖) ?_ ?_ (integrable_const _) ?_
  · intro s
    exact (h.continuous.comp (continuous_eval_const _)).aestronglyMeasurable
  · intro s
    exact Eventually.of_forall fun p => h.norm_coe_le_norm _
  · exact Eventually.of_forall fun p =>
      h.continuous.comp (p.continuous.comp continuous_real_toNNReal)

theorem aux_lem_resolvents_to_paths_abs_marginal_le {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsProbabilityMeasure μ] (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (s : ℝ) :
    |∫ p, h (p (Real.toNNReal s)) ∂μ| ≤ ‖h‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ p, h (p (Real.toNNReal s)) ∂μ‖ ≤ ‖h‖ * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall fun p => h.norm_coe_le_norm _)
    _ = ‖h‖ := by rw [probReal_univ, mul_one]

/-- Fubini: the Laplace transform of the one-time marginal is the discounted path functional. -/
theorem aux_lem_resolvents_to_paths_laplace_marginal {d : ℕ} (μ : Measure (DiffusionPath d))
    [IsProbabilityMeasure μ] (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ) {lam : ℝ}
    (hlam : 0 < lam) :
    ∫ s in Set.Ioi (0:ℝ), Real.exp (-lam * s) * ∫ p, h (p (Real.toNNReal s)) ∂μ =
      ∫ p, aux_lem_resolvents_to_paths_wf lam h p ∂μ := by
  unfold aux_lem_resolvents_to_paths_wf
  have e1 : ∀ s : ℝ, Real.exp (-lam * s) * ∫ p, h (p (Real.toNNReal s)) ∂μ =
      ∫ p, Real.exp (-lam * s) * h (p (Real.toNNReal s)) ∂μ := fun s =>
    (integral_const_mul _ _).symm
  rw [show (fun s : ℝ => Real.exp (-lam * s) * ∫ p, h (p (Real.toNNReal s)) ∂μ) =
      (fun s : ℝ => ∫ p, Real.exp (-lam * s) * h (p (Real.toNNReal s)) ∂μ) from funext e1]
  refine integral_integral_swap ?_
  have hc : Continuous (Function.uncurry fun (s : ℝ) (p : DiffusionPath d) =>
      Real.exp (-lam * s) * h (p (Real.toNNReal s))) := by
    refine (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul ?_
    exact h.continuous.comp (continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst)))
  refine Integrable.mono' (((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖h‖).comp_fst μ)
    hc.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rcases z with ⟨s, p⟩
  simp only [Function.uncurry_apply_pair]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm _) (Real.exp_pos _).le

/-- Right-equicontinuity of one-time marginals over a family of laws carrying a common compact
set of paths up to mass `η`. -/
theorem aux_lem_resolvents_to_paths_marginal_equi {d : ℕ}
    (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (t0 : ℝ) {ε : ℝ} (hε : 0 < ε)
    (Kp : Set (DiffusionPath d)) (hKp : IsCompact Kp) :
    ∃ δ > 0, ∀ (μ : Measure (DiffusionPath d)), IsProbabilityMeasure μ →
      μ Kpᶜ ≤ ENNReal.ofReal (ε / (4 * (‖h‖ + 1))) →
      ∀ s, t0 ≤ s → s ≤ t0 + δ →
        |(∫ p, h (p (Real.toNNReal s)) ∂μ) - ∫ p, h (p (Real.toNNReal t0)) ∂μ| ≤ ε := by
  set F : ℝ × DiffusionPath d → ℝ := fun z => h (z.2 (Real.toNNReal z.1)) -
    h (z.2 (Real.toNNReal t0)) with hFdef
  have hFc : Continuous F := by
    refine (h.continuous.comp (continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst)))).sub ?_
    exact h.continuous.comp ((continuous_eval_const _).comp continuous_snd)
  have hP : ∀ p ∈ Kp, ∀ᶠ z : ℝ × DiffusionPath d in 𝓝 (t0, p), |F z| < ε / 2 := by
    intro p _
    have h0 : F (t0, p) = 0 := by simp [hFdef]
    have := hFc.continuousAt.eventually (Metric.ball_mem_nhds (F (t0, p)) (by positivity : 0 < ε / 2))
    filter_upwards [this] with z hz
    rw [h0, Real.dist_eq, sub_zero] at hz
    exact hz
  have htube := hKp.eventually_forall_of_forall_eventually (P := fun s p => |F (s, p)| < ε / 2) hP
  obtain ⟨δ', hδ', hδ'P⟩ := Metric.eventually_nhds_iff.mp htube
  refine ⟨δ' / 2, by positivity, fun μ hμ hμK s hs1 hs2 => ?_⟩
  have hsd : dist s t0 < δ' := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have hKpm : MeasurableSet Kp := hKp.isClosed.measurableSet
  have hi1 : Integrable (fun p : DiffusionPath d => h (p (Real.toNNReal s))) μ :=
    (h.compContinuous ⟨fun p : DiffusionPath d => p (Real.toNNReal s),
      continuous_eval_const _⟩).integrable μ
  have hi2 : Integrable (fun p : DiffusionPath d => h (p (Real.toNNReal t0))) μ :=
    (h.compContinuous ⟨fun p : DiffusionPath d => p (Real.toNNReal t0),
      continuous_eval_const _⟩).integrable μ
  rw [← integral_sub hi1 hi2]
  have hpt : ∀ p, |h (p (Real.toNNReal s)) - h (p (Real.toNNReal t0))| ≤
      ε / 2 + 2 * ‖h‖ * Kpᶜ.indicator (fun _ => (1 : ℝ)) p := by
    intro p
    by_cases hp : p ∈ Kp
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hp), mul_zero, add_zero]
      exact (hδ'P hsd p hp).le
    · rw [Set.indicator_of_mem (Set.mem_compl hp), mul_one]
      have e1 := h.norm_coe_le_norm (p (Real.toNNReal s))
      have e2 := h.norm_coe_le_norm (p (Real.toNNReal t0))
      rw [Real.norm_eq_abs] at e1 e2
      calc _ ≤ |h (p (Real.toNNReal s))| + |h (p (Real.toNNReal t0))| := abs_sub _ _
        _ ≤ 2 * ‖h‖ := by linarith
        _ ≤ ε / 2 + 2 * ‖h‖ := by linarith
  have hμKr : μ.real Kpᶜ ≤ ε / (4 * (‖h‖ + 1)) := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal (by positivity) hμK
  calc |∫ p, (h (p (Real.toNNReal s)) - h (p (Real.toNNReal t0))) ∂μ|
      ≤ ∫ p, |h (p (Real.toNNReal s)) - h (p (Real.toNNReal t0))| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, (ε / 2 + 2 * ‖h‖ * Kpᶜ.indicator (fun _ => (1 : ℝ)) p) ∂μ :=
        integral_mono (hi1.sub hi2).abs ((integrable_const _).add
          (((integrable_const (1:ℝ)).indicator hKpm.compl).const_mul _)) hpt
    _ = ε / 2 + 2 * ‖h‖ * μ.real Kpᶜ := by
        rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator
          hKpm.compl).const_mul _), integral_const, probReal_univ, one_smul, integral_const_mul,
          aux_lem_resolvents_to_paths_integral_indicator_one μ _ hKpm.compl]
    _ ≤ ε := by
        have h1 : 2 * ‖h‖ * μ.real Kpᶜ ≤ 2 * ‖h‖ * (ε / (4 * (‖h‖ + 1))) :=
          mul_le_mul_of_nonneg_left hμKr (by positivity)
        have h2 : 2 * ‖h‖ * (ε / (4 * (‖h‖ + 1))) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [norm_nonneg h]
        linarith

/-- **One-time marginals at moving starts** (`mfd:prop-as-forms`): tightness at moving starts and
convergence of the whole-space resolvents give convergence of every one-time marginal. -/
theorem aux_lem_resolvents_to_paths_marginal_moving
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (htight : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
        (∀ n, KN (φ n) (omega, u n) Kpᶜ ≤ ENNReal.ofReal eps) ∧
        K (omega, x) Kpᶜ ≤ ENNReal.ofReal eps)
    (hres : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Tendsto (fun n ↦ ∫ path, aux_lem_resolvents_to_paths_wf lam f path
            ∂(KN (φ n) (omega, u n)))
          atTop (𝓝 (∫ path, aux_lem_resolvents_to_paths_wf lam f path ∂(K (omega, x))))) :
    ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ (t : ℝ≥0) (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Tendsto (fun n ↦ ∫ p, h (p t) ∂(KN (φ n) (omega, u n))) atTop
          (𝓝 (∫ p, h (p t) ∂(K (omega, x)))) := by
  intro u x φ hφ hu t h
  have : ∀ n, IsProbabilityMeasure (KN (φ n) (omega, u n)) := fun n =>
    (hKN _).isProbabilityMeasure _
  have : IsProbabilityMeasure (K (omega, x)) := hK.isProbabilityMeasure _
  have key := aux_lem_resolvents_to_paths_laplace_pointwise
    (fun n s => ∫ p, h (p (Real.toNNReal s)) ∂(KN (φ n) (omega, u n)))
    (fun s => ∫ p, h (p (Real.toNNReal s)) ∂(K (omega, x))) (C := ‖h‖)
    (fun n => (aux_lem_resolvents_to_paths_continuous_marginal _ h).measurable)
    (aux_lem_resolvents_to_paths_continuous_marginal _ h).measurable
    (fun n s => aux_lem_resolvents_to_paths_abs_marginal_le _ h s)
    (fun s => aux_lem_resolvents_to_paths_abs_marginal_le _ h s)
    (fun m => by
      have hl : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      simp_rw [aux_lem_resolvents_to_paths_laplace_marginal _ h hl]
      exact hres u x φ hφ hu _ hl h)
    (t0 := (t : ℝ)) t.coe_nonneg
    (fun ε hε => by
      obtain ⟨Kp, hKp, hKpn, hKpx⟩ := htight u x φ hφ hu (ε / (4 * (‖h‖ + 1))) (by positivity)
      obtain ⟨δ, hδ, hδμ⟩ := aux_lem_resolvents_to_paths_marginal_equi h (t : ℝ) hε Kp hKp
      exact ⟨δ, hδ, Eventually.of_forall fun n s hs1 hs2 =>
        hδμ _ inferInstance (hKpn n) s hs1 hs2⟩)
    (fun ε hε => by
      obtain ⟨Kp, hKp, hKpn, hKpx⟩ := htight u x φ hφ hu (ε / (4 * (‖h‖ + 1))) (by positivity)
      obtain ⟨δ, hδ, hδμ⟩ := aux_lem_resolvents_to_paths_marginal_equi h (t : ℝ) hε Kp hKp
      exact ⟨δ, hδ, fun s hs1 hs2 => hδμ _ inferInstance hKpx s hs1 hs2⟩)
  simpa only [Real.toNNReal_coe] using key


/-! ### RtpFDD -/

/-- Continuous convergence of a sequence of functions: `g k (z k) → gl y` whenever `z k → y`. -/
def aux_lem_resolvents_to_paths_ccv {Y : Type*} [TopologicalSpace Y] (g : ℕ → Y → ℝ)
    (gl : Y → ℝ) : Prop :=
  ∀ (z : ℕ → Y) (y : Y), Tendsto z atTop (𝓝 y) → Tendsto (fun k => g k (z k)) atTop (𝓝 (gl y))

/-- Continuous convergence passes to subsequences. -/
theorem aux_lem_resolvents_to_paths_ccv_subseq {Y : Type*} [TopologicalSpace Y]
    {g : ℕ → Y → ℝ} {gl : Y → ℝ} (hg : aux_lem_resolvents_to_paths_ccv g gl)
    {κ : ℕ → ℕ} (hκ : StrictMono κ) {z : ℕ → Y} {y : Y} (hz : Tendsto z atTop (𝓝 y)) :
    Tendsto (fun j => g (κ j) (z j)) atTop (𝓝 (gl y)) := by
  classical
  set w : ℕ → Y := fun m => if h : ∃ j, κ j = m then z (Classical.choose h) else y with hwdef
  have hwκ : ∀ j, w (κ j) = z j := by
    intro j
    have h : ∃ j', κ j' = κ j := ⟨j, rfl⟩
    simp only [hwdef, dite_eq_left h]
    exact congrArg z (hκ.injective (Classical.choose_spec h))
  have hw : Tendsto w atTop (𝓝 y) := by
    rw [tendsto_nhds]
    intro V hV hyV
    obtain ⟨J, hJ⟩ := eventually_atTop.mp ((tendsto_nhds.mp hz) V hV hyV)
    refine eventually_atTop.mpr ⟨κ J, fun m hm => ?_⟩
    simp only [hwdef]
    split_ifs with h
    · have hj := Classical.choose_spec h
      apply hJ
      by_contra hlt
      rw [not_le] at hlt
      have := hκ hlt
      omega
    · exact hyV
  have := (hg w y hw).comp hκ.tendsto_atTop
  exact this.congr fun j => by simp only [Function.comp_apply, hwκ]

/-- The limit of a continuously convergent sequence is continuous. -/
theorem aux_lem_resolvents_to_paths_ccv_continuous {Y : Type*} [MetricSpace Y] {g : ℕ → Y → ℝ} {gl : Y → ℝ}
    (hg : aux_lem_resolvents_to_paths_ccv g gl) : Continuous gl := by
  rw [continuous_iff_seqContinuous]
  intro y yj hy
  have hev : ∀ j, ∀ᶠ k in atTop, |g k (y j) - gl (y j)| < 1 / ((j : ℝ) + 1) := by
    intro j
    have h := hg (fun _ => y j) (y j) tendsto_const_nhds
    have := (Metric.tendsto_atTop.mp h) (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨K, hK⟩ := this
    exact eventually_atTop.mpr ⟨K, fun k hk => by rw [← Real.dist_eq]; exact hK k hk⟩
  obtain ⟨κ, hκ, hκP⟩ := extraction_forall_of_eventually hev
  have h1 := aux_lem_resolvents_to_paths_ccv_subseq hg hκ hy
  have h2 : Tendsto (fun j => g (κ j) (y j) - gl (y j)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => (hκP j).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have := h1.sub h2
  simp only [sub_sub_cancel, sub_zero] at this
  exact this

/-- Continuous convergence is uniform on compact sets. -/
theorem aux_lem_resolvents_to_paths_ccv_uniform {Y : Type*} [MetricSpace Y] {g : ℕ → Y → ℝ} {gl : Y → ℝ}
    (hg : aux_lem_resolvents_to_paths_ccv g gl) {C : Set Y} (hC : IsCompact C) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ y ∈ C, |g k y - gl y| < ε := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨κ, hκ, hκP⟩ := extraction_of_frequently_atTop hcon
  have hex : ∀ j, ∃ y ∈ C, ε ≤ |g (κ j) y - gl y| := by
    intro j
    have := hκP j
    push Not at this
    exact this
  choose yj hyjC hyjε using hex
  obtain ⟨a, haC, ψ, hψ, hlim⟩ := hC.tendsto_subseq hyjC
  have h1 := aux_lem_resolvents_to_paths_ccv_subseq hg (hκ.comp hψ) hlim
  have h2 : Tendsto (fun j => gl ((yj ∘ ψ) j)) atTop (𝓝 (gl a)) :=
    ((aux_lem_resolvents_to_paths_ccv_continuous hg).tendsto a).comp hlim
  have h3 := h1.sub h2
  rw [sub_self] at h3
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp h3) ε hε
  have := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact absurd (hyjε (ψ J)) (not_le.mpr this)

/-- A constant sequence of a continuous function converges continuously. -/
theorem aux_lem_resolvents_to_paths_ccv_const {Y : Type*} [TopologicalSpace Y] {g : Y → ℝ}
    (hg : Continuous g) : aux_lem_resolvents_to_paths_ccv (fun _ => g) g :=
  fun _ y hz => (hg.tendsto y).comp hz

/-- **Moving test functions against convergent tight laws.** -/
theorem aux_lem_resolvents_to_paths_integral_ccv {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (m : ℕ → Measure Y) (hm : ∀ k, IsProbabilityMeasure (m k)) (ml : Measure Y)
    [IsProbabilityMeasure ml]
    (hconv : ∀ h : BoundedContinuousFunction Y ℝ,
      Tendsto (fun k => ∫ y, h y ∂(m k)) atTop (𝓝 (∫ y, h y ∂ml)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ C : Set Y, IsCompact C ∧ ∀ k, m k Cᶜ ≤ ENNReal.ofReal ε)
    (g : ℕ → Y → ℝ) (gl : Y → ℝ) (hgm : ∀ k, Measurable (g k)) {M : ℝ} (hM0 : 0 ≤ M)
    (hgb : ∀ k y, |g k y| ≤ M) (hg : aux_lem_resolvents_to_paths_ccv g gl) :
    Tendsto (fun k => ∫ y, g k y ∂(m k)) atTop (𝓝 (∫ y, gl y ∂ml)) := by
  have hcont := aux_lem_resolvents_to_paths_ccv_continuous hg
  have hglb : ∀ y, |gl y| ≤ M := by
    intro y
    have h := hg (fun _ => y) y tendsto_const_nhds
    exact le_of_tendsto' ((continuous_abs.tendsto _).comp h) (fun k => hgb k y)
  set G : BoundedContinuousFunction Y ℝ := BoundedContinuousFunction.mkOfBound
    ⟨gl, hcont⟩ (2 * M) (fun y y' => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := hglb y; have := hglb y'
      rw [abs_le] at *; constructor <;> linarith) with hGdef
  have h2 := hconv G
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC, hCm⟩ := htight (ε / (8 * (M + 1))) (by positivity)
  have hCmeas : MeasurableSet C := hC.isClosed.measurableSet
  obtain ⟨k1, hk1⟩ := eventually_atTop.mp (aux_lem_resolvents_to_paths_ccv_uniform hg hC
    (by positivity : (0:ℝ) < ε / 4))
  obtain ⟨k2, hk2⟩ := Metric.tendsto_atTop.mp h2 (ε / 4) (by positivity)
  refine ⟨max k1 k2, fun k hk => ?_⟩
  have := hm k
  have hk1' := hk1 k (le_trans (le_max_left _ _) hk)
  have hk2' := hk2 k (le_trans (le_max_right _ _) hk)
  have hgi : Integrable (g k) (m k) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable M (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hgb k y)
  have hGi : Integrable gl (m k) := G.integrable (m k)
  have hpt : ∀ y, |g k y - gl y| ≤ ε / 4 + 2 * M * Cᶜ.indicator (fun _ => (1:ℝ)) y := by
    intro y
    by_cases hy : y ∈ C
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy), mul_zero, add_zero]
      exact (hk1' y hy).le
    · rw [Set.indicator_of_mem (Set.mem_compl hy), mul_one]
      have := hgb k y; have := hglb y
      calc |g k y - gl y| ≤ |g k y| + |gl y| := abs_sub _ _
        _ ≤ 2 * M := by linarith
        _ ≤ ε / 4 + 2 * M := by linarith
  have hmC : (m k).real Cᶜ ≤ ε / (8 * (M + 1)) := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hCm k)
  have hfirst : |(∫ y, g k y ∂(m k)) - ∫ y, gl y ∂(m k)| ≤ ε / 2 := by
    rw [← integral_sub hgi hGi]
    calc |∫ y, (g k y - gl y) ∂(m k)| ≤ ∫ y, |g k y - gl y| ∂(m k) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ y, (ε / 4 + 2 * M * Cᶜ.indicator (fun _ => (1:ℝ)) y) ∂(m k) :=
          integral_mono (hgi.sub hGi).abs ((integrable_const _).add
            (((integrable_const (1:ℝ)).indicator hCmeas.compl).const_mul _)) hpt
      _ = ε / 4 + 2 * M * (m k).real Cᶜ := by
          rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator
            hCmeas.compl).const_mul _), integral_const, probReal_univ, one_smul,
            integral_const_mul]
          congr 2
          change ∫ y, Cᶜ.indicator 1 y ∂(m k) = _
          rw [integral_indicator_one hCmeas.compl]
      _ ≤ ε / 2 := by
          have h1 : 2 * M * (m k).real Cᶜ ≤ 2 * M * (ε / (8 * (M + 1))) :=
            mul_le_mul_of_nonneg_left hmC (by positivity)
          have h2 : 2 * M * (ε / (8 * (M + 1))) ≤ ε / 4 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          linarith
  rw [Real.dist_eq] at hk2' ⊢
  have hk2'' : |(∫ y, gl y ∂(m k)) - ∫ y, gl y ∂ml| < ε / 4 := by
    simpa [hGdef] using hk2'
  calc |(∫ y, g k y ∂(m k)) - ∫ y, gl y ∂ml|
      ≤ |(∫ y, g k y ∂(m k)) - ∫ y, gl y ∂(m k)| + |(∫ y, gl y ∂(m k)) - ∫ y, gl y ∂ml| :=
        abs_sub_le _ _ _
    _ < ε := by linarith


/-! ### RtpFDD2 -/

theorem aux_lem_resolvents_to_paths_tendsto_cons {X : Type*} [TopologicalSpace X] {n : ℕ}
    {a : ℕ → X} {a0 : X} {w : ℕ → (Fin n → X)} {w0 : Fin n → X}
    (ha : Tendsto a atTop (𝓝 a0)) (hw : Tendsto w atTop (𝓝 w0)) :
    Tendsto (fun k => (Fin.cons (a k) (w k) : Fin (n + 1) → X)) atTop
      (𝓝 (Fin.cons a0 w0 : Fin (n + 1) → X)) := by
  rw [tendsto_pi_nhds]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using ha
  · simpa only [Fin.cons_succ] using tendsto_pi_nhds.mp hw j

/-- The successor finite-time integral as an iterated integral. -/
theorem aux_lem_resolvents_to_paths_ftk_integral_succ {X : Type*} [MeasurableSpace X]
    (P : SubMarkovKernelSemigroup X) (hP : P.IsConservative) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) (f : (Fin (n + 1) → X) → ℝ) (hf : Measurable f)
    {M : ℝ} (hfb : ∀ w, |f w| ≤ M) (y : X) :
    ∫ w, f w ∂(SubMarkovKernelSemigroup.finiteTimeKernel P times y) =
      ∫ a, (∫ w', f (Fin.cons a w') ∂(SubMarkovKernelSemigroup.finiteTimeKernel P
        times.relativeTail a)) ∂(P (times 0) y) := by
  have : IsMarkovKernel (P (times 0)) := hP.isMarkovKernel (times 0)
  have : IsMarkovKernel (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail) :=
    SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel P hP _
  rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
    Kernel.map_apply _ measurable_finCons,
    integral_map measurable_finCons.aemeasurable hf.aestronglyMeasurable]
  rw [ProbabilityTheory.integral_compProd]
  · simp only [Kernel.prodMkLeft_apply]
  · exact Integrable.of_bound (hf.comp measurable_finCons).aestronglyMeasurable M
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hfb _)

/-- **Finite-dimensional distributions converge at moving starts, by induction on the number
of observation times** (`mfd:prop-as-forms`: iteration of the one-time statements). -/
theorem aux_lem_resolvents_to_paths_ftk_ccv {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    (Q : ℕ → SubMarkovKernelSemigroup X) (Ql : SubMarkovKernelSemigroup X)
    (hQc : ∀ k, (Q k).IsConservative) (hQlc : Ql.IsConservative)
    (hOT : ∀ (t : ℝ≥0) (g : ℕ → X → ℝ) (gl : X → ℝ), (∀ k, Measurable (g k)) →
      ∀ M : ℝ, 0 ≤ M → (∀ k y, |g k y| ≤ M) → aux_lem_resolvents_to_paths_ccv g gl →
        aux_lem_resolvents_to_paths_ccv (fun k y => ∫ z, g k z ∂(Q k t y))
          (fun y => ∫ z, gl z ∂(Ql t y))) :
    ∀ (n : ℕ) (times : FiniteOrderedTimes n) (g : ℕ → (Fin n → X) → ℝ)
      (gl : (Fin n → X) → ℝ), (∀ k, Measurable (g k)) →
      ∀ M : ℝ, 0 ≤ M → (∀ k w, |g k w| ≤ M) → aux_lem_resolvents_to_paths_ccv g gl →
        aux_lem_resolvents_to_paths_ccv
          (fun k y => ∫ w, g k w ∂(SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times y))
          (fun y => ∫ w, gl w ∂(SubMarkovKernelSemigroup.finiteTimeKernel Ql times y)) := by
  intro n
  induction n with
  | zero =>
    intro times g gl hgm M hM hgb hg z y hz
    have e : ∀ (P : SubMarkovKernelSemigroup X) (f : (Fin 0 → X) → ℝ), Measurable f → ∀ y,
        ∫ w, f w ∂(SubMarkovKernelSemigroup.finiteTimeKernel P times y) =
          f (FiniteOrderedTimes.emptyPath X) := by
      intro P f hf y
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero, Kernel.const_apply,
        integral_dirac' _ _ hf.stronglyMeasurable]
    simp only [e _ _ (hgm _), e _ gl (measurable_of_countable gl)]
    exact hg (fun _ => FiniteOrderedTimes.emptyPath X) _ tendsto_const_nhds
  | succ n ih =>
    intro times g gl hgm M hM hgb hg
    set G : ℕ → X → ℝ := fun k a => ∫ w', g k (Fin.cons a w')
      ∂(SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times.relativeTail a) with hGdef
    set Gl : X → ℝ := fun a => ∫ w', gl (Fin.cons a w')
      ∂(SubMarkovKernelSemigroup.finiteTimeKernel Ql times.relativeTail a) with hGldef
    have hGccv : aux_lem_resolvents_to_paths_ccv G Gl := by
      intro a_ a ha
      refine ih times.relativeTail (fun k w' => g k (Fin.cons (a_ k) w'))
        (fun w' => gl (Fin.cons a w')) (fun k => (hgm k).comp (measurable_finCons.comp
          (measurable_const.prodMk measurable_id))) M hM (fun k w' => hgb k _) ?_ a_ a ha
      intro w_ w hw
      exact hg _ _ (aux_lem_resolvents_to_paths_tendsto_cons ha hw)
    have hGm : ∀ k, Measurable (G k) := by
      intro k
      have : IsMarkovKernel (SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times.relativeTail) :=
        SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel _ (hQc k) _
      have hsm : StronglyMeasurable (Function.uncurry fun (a : X) (w' : Fin n → X) =>
          g k (Fin.cons a w')) :=
        ((hgm k).comp measurable_finCons).stronglyMeasurable
      exact (hsm.integral_kernel_prod_right
        (κ := SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times.relativeTail)).measurable
    have hGb : ∀ k a, |G k a| ≤ M := by
      intro k a
      have : IsMarkovKernel (SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times.relativeTail) :=
        SubMarkovKernelSemigroup.IsConservative.isMarkovKernel_finiteTimeKernel _ (hQc k) _
      rw [← Real.norm_eq_abs]
      calc ‖G k a‖ ≤ M * (SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times.relativeTail a).real
            Set.univ := norm_integral_le_of_norm_le_const (Eventually.of_forall fun w' => by
              rw [Real.norm_eq_abs]; exact hgb k _)
        _ = M := by rw [probReal_univ, mul_one]
    have hstep := hOT (times 0) G Gl hGm M hM hGb hGccv
    intro z y hz
    have hrep : ∀ k, ∫ w, g k w ∂(SubMarkovKernelSemigroup.finiteTimeKernel (Q k) times (z k)) =
        ∫ a, G k a ∂(Q k (times 0) (z k)) := fun k =>
      aux_lem_resolvents_to_paths_ftk_integral_succ (Q k) (hQc k) times (g k) (hgm k)
        (hgb k) (z k)
    simp only [hrep]
    have hrepl : ∫ w, gl w ∂(SubMarkovKernelSemigroup.finiteTimeKernel Ql times y) =
        ∫ a, Gl a ∂(Ql (times 0) y) := by
      have hglm : Measurable gl := by
        have := aux_lem_resolvents_to_paths_ccv_continuous hg
        exact this.measurable
      have hglb : ∀ w, |gl w| ≤ M := by
        intro w
        have h := hg (fun _ => w) w tendsto_const_nhds
        exact le_of_tendsto' ((continuous_abs.tendsto _).comp h) (fun k => hgb k w)
      exact aux_lem_resolvents_to_paths_ftk_integral_succ Ql hQlc times gl hglm hglb y
    rw [hrepl]
    exact hstep z y hz


/-! ### RtpFDD3 -/

theorem aux_lem_resolvents_to_paths_conservative_of {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) (hK : IsMarkovKernel K)
    (omega : BilateralField d)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) : P.IsConservative := by
  intro t y
  rw [← aux_lem_resolvents_to_paths_map_eval_of P K omega hfdd t y,
    Measure.map_apply (show Measurable (fun path : DiffusionPath d => path t) from
      (ContinuousPath.continuous_eval t).measurable) MeasurableSet.univ, Set.preimage_univ]
  have := hK.isProbabilityMeasure (omega, y)
  exact measure_univ

/-- **One-time step with moving test functions** for the finite-cutoff semigroups along a
subsequence, from the one-time marginals at moving starts and tightness. -/
theorem aux_lem_resolvents_to_paths_one_time_ccv
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (omega : BilateralField d)
    (hfdd : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (hlimAt : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (htight : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
        (∀ n, KN (φ n) (omega, u n) Kpᶜ ≤ ENNReal.ofReal eps) ∧
        K (omega, x) Kpᶜ ≤ ENNReal.ofReal eps)
    (hmarg : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ (t : ℝ≥0) (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Tendsto (fun n ↦ ∫ p, h (p t) ∂(KN (φ n) (omega, u n))) atTop
          (𝓝 (∫ p, h (p t) ∂(K (omega, x)))))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∀ (t : ℝ≥0) (g : ℕ → SpatialCoordinates d → ℝ) (gl : SpatialCoordinates d → ℝ),
      (∀ k, Measurable (g k)) → ∀ M : ℝ, 0 ≤ M → (∀ k y, |g k y| ≤ M) →
      aux_lem_resolvents_to_paths_ccv g gl →
        aux_lem_resolvents_to_paths_ccv (fun k y => ∫ z, g k z ∂(PN (φ k) omega t y))
          (fun y => ∫ z, gl z ∂(P omega t y)) := by
  intro t g gl hgm M hM hgb hg u x hu
  have hev : Measurable (fun p : DiffusionPath d => p t) :=
    (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) t).measurable
  have hmk : ∀ k, (PN (φ k) omega t (u k)) = (KN (φ k) (omega, u k)).map (fun p => p t) :=
    fun k => (aux_lem_resolvents_to_paths_map_eval_of (PN (φ k) omega) (KN (φ k)) omega
      (hfdd (φ k)) t (u k)).symm
  have hml : P omega t x = (K (omega, x)).map (fun p => p t) :=
    (aux_lem_resolvents_to_paths_map_eval_of (P omega) K omega hlimAt t x).symm
  simp only [hmk, hml]
  have : ∀ k, IsProbabilityMeasure (KN (φ k) (omega, u k)) := fun k =>
    (hKN _).isProbabilityMeasure _
  have : IsProbabilityMeasure (K (omega, x)) := hK.isProbabilityMeasure _
  have : IsProbabilityMeasure ((K (omega, x)).map (fun p => p t)) :=
    inferInstance
  refine aux_lem_resolvents_to_paths_integral_ccv
    (fun k => (KN (φ k) (omega, u k)).map (fun p => p t))
    (fun k => inferInstance)
    ((K (omega, x)).map (fun p => p t)) ?_ ?_ g gl hgm hM hgb hg
  · intro h
    simp only [integral_map hev.aemeasurable h.continuous.aestronglyMeasurable]
    exact hmarg u x φ hφ hu t h
  · intro ε hε
    obtain ⟨Kp, hKp, hKpn, _⟩ := htight u x φ hφ hu ε hε
    refine ⟨(fun p : DiffusionPath d => p t) '' Kp,
      hKp.image (ContinuousPath.continuous_eval t), fun k => ?_⟩
    have hCm : MeasurableSet ((fun p : DiffusionPath d => p t) '' Kp)ᶜ :=
      (hKp.image (ContinuousPath.continuous_eval t)).isClosed.measurableSet.compl
    rw [Measure.map_apply hev hCm]
    refine le_trans (measure_mono fun p hp => ?_) (hKpn k)
    intro hpK
    exact hp ⟨p, hpK, rfl⟩

/-- **Cylinder convergence at moving starts** (`mfd:prop-as-forms`). -/
theorem aux_lem_resolvents_to_paths_cyl_moving
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (omega : BilateralField d)
    (hfdd : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (hlimAt : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (htight : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
        (∀ n, KN (φ n) (omega, u n) Kpᶜ ≤ ENNReal.ofReal eps) ∧
        K (omega, x) Kpᶜ ≤ ENNReal.ofReal eps)
    (hmarg : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ (t : ℝ≥0) (h : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Tendsto (fun n ↦ ∫ p, h (p t) ∂(KN (φ n) (omega, u n))) atTop
          (𝓝 (∫ p, h (p t) ∂(K (omega, x))))) :
    ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ (I : Finset ℝ≥0) (g : (I → SpatialCoordinates d) →ᵇ ℝ),
        Tendsto (fun n ↦ ∫ z, g (ContinuousPath.finsetEvaluation I z)
            ∂(KN (φ n) (omega, u n))) atTop
          (𝓝 (∫ z, g (ContinuousPath.finsetEvaluation I z) ∂(K (omega, x)))) := by
  intro u x φ hφ hu I g
  have hev : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) :=
    Measurable.of_eval fun s => (continuous_eval_const ((s : ℝ≥0))).measurable
  have hord : Continuous (SubMarkovKernelSemigroup.orderedPathToFiniteSet
      (α := SpatialCoordinates d) I) :=
    continuous_pi fun s => continuous_apply _
  set g' : (Fin I.card → SpatialCoordinates d) → ℝ :=
    fun w => g (SubMarkovKernelSemigroup.orderedPathToFiniteSet I w) with hg'def
  have hg'c : Continuous g' := g.continuous.comp hord
  have hrep : ∀ (Q : SubMarkovKernelSemigroup (SpatialCoordinates d))
      (L' : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hfdd' : ∀ I x, L'.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel Q I x) (y : SpatialCoordinates d),
      ∫ z, g (ContinuousPath.finsetEvaluation I z) ∂(L' (omega, y)) =
        ∫ w, g' w ∂(SubMarkovKernelSemigroup.finiteTimeKernel Q
          (SubMarkovKernelSemigroup.finiteSetTimes I) y) := by
    intro Q L' hfdd' y
    rw [← integral_map hev.aemeasurable g.continuous.aestronglyMeasurable,
      ← Kernel.map_apply L' hev, hfdd', SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
      Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I),
      integral_map (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I).aemeasurable
        g.continuous.aestronglyMeasurable]
  simp only [hrep (PN _ omega) (KN _) (hfdd _), hrep (P omega) K hlimAt]
  have hQc : ∀ k, (PN (φ k) omega).IsConservative := fun k =>
    aux_lem_resolvents_to_paths_conservative_of (PN (φ k) omega) (KN (φ k)) (hKN _) omega
      (hfdd (φ k))
  have hQlc : (P omega).IsConservative :=
    aux_lem_resolvents_to_paths_conservative_of (P omega) K hK omega hlimAt
  have hOT := aux_lem_resolvents_to_paths_one_time_ccv PN KN hKN K hK P omega hfdd hlimAt htight
    hmarg φ hφ
  have hind := aux_lem_resolvents_to_paths_ftk_ccv (fun k => PN (φ k) omega) (P omega) hQc hQlc
    hOT I.card (SubMarkovKernelSemigroup.finiteSetTimes I) (fun _ => g') g'
    (fun _ => hg'c.measurable) ‖g‖ (norm_nonneg _) (fun _ w => by
      rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _)
    (aux_lem_resolvents_to_paths_ccv_const hg'c)
  exact hind u x hu


/-! ### Assembly glue (from the pool candidate) -/


theorem aux_lem_resolvents_to_paths_tight_union {d : ℕ} (mu : ℕ → Measure (DiffusionPath d)) (nu : Measure (DiffusionPath d)) (hmu : ∀ eps : ℝ, 0 < eps → ∃ K1 : Set (DiffusionPath d), IsCompact K1 ∧ ∀ n, mu n K1ᶜ ≤ ENNReal.ofReal eps) (hnu : ∀ eps : ℝ, 0 < eps → ∃ K2 : Set (DiffusionPath d), IsCompact K2 ∧ nu K2ᶜ ≤ ENNReal.ofReal eps) : ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧ (∀ n, mu n Kpᶜ ≤ ENNReal.ofReal eps) ∧ nu Kpᶜ ≤ ENNReal.ofReal eps := by
  intro eps heps
  obtain ⟨K1, hK1, h1⟩ := hmu eps heps
  obtain ⟨K2, hK2, h2⟩ := hnu eps heps
  refine ⟨K1 ∪ K2, hK1.union hK2, fun n => ?_, ?_⟩
  · exact le_trans (measure_mono (Set.compl_subset_compl_of_subset Set.subset_union_left)) (h1 n)
  · exact le_trans (measure_mono (Set.compl_subset_compl_of_subset Set.subset_union_right)) h2


theorem aux_lem_resolvents_to_paths_single_tight {d : ℕ} (nu : Measure (DiffusionPath d)) [IsProbabilityMeasure nu] : ∀ eps : ℝ, 0 < eps → ∃ K2 : Set (DiffusionPath d), IsCompact K2 ∧ nu K2ᶜ ≤ ENNReal.ofReal eps := by
  intro eps heps
  have ht := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton_of_innerRegular (μ := nu))
    (ENNReal.ofReal eps) (ENNReal.ofReal_pos.mpr heps)
  obtain ⟨K, hK, hmass⟩ := ht
  exact ⟨K, hK, hmass nu (Set.mem_singleton nu)⟩

/-! ### Shell (auxiliary ) -/

/-- The path Lévy–Prokhorov distance is the metric of `LevyProkhorov (ProbabilityMeasure _)`. -/
theorem aux_lem_resolvents_to_paths_lp_eq_dist {d : ℕ}
    (mu nu : ProbabilityMeasure (DiffusionPath d)) :
    letI : MetricSpace (DiffusionPath d) :=
      TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
    pathLevyProkhorovDist mu nu
      = dist (LevyProkhorov.ofMeasure mu) (LevyProkhorov.ofMeasure nu) := by
  let : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  exact (LevyProkhorov.dist_probabilityMeasure_def
    (LevyProkhorov.ofMeasure mu) (LevyProkhorov.ofMeasure nu)).symm

theorem aux_lem_resolvents_to_paths_lp_nonneg {d : ℕ}
    (mu nu : ProbabilityMeasure (DiffusionPath d)) :
    0 ≤ pathLevyProkhorovDist mu nu := by
  let : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  rw [aux_lem_resolvents_to_paths_lp_eq_dist]
  exact dist_nonneg

theorem aux_lem_resolvents_to_paths_lp_comm {d : ℕ}
    (mu nu : ProbabilityMeasure (DiffusionPath d)) :
    pathLevyProkhorovDist mu nu = pathLevyProkhorovDist nu mu := by
  let : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  rw [aux_lem_resolvents_to_paths_lp_eq_dist, aux_lem_resolvents_to_paths_lp_eq_dist]
  exact dist_comm _ _

/-- Triangle inequality for the path Lévy–Prokhorov distance. -/
theorem aux_lem_resolvents_to_paths_lp_triangle {d : ℕ}
    (mu nu rho : ProbabilityMeasure (DiffusionPath d)) :
    pathLevyProkhorovDist mu rho ≤
      pathLevyProkhorovDist mu nu + pathLevyProkhorovDist nu rho := by
  let : MetricSpace (DiffusionPath d) := TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  rw [aux_lem_resolvents_to_paths_lp_eq_dist, aux_lem_resolvents_to_paths_lp_eq_dist,
    aux_lem_resolvents_to_paths_lp_eq_dist]
  exact dist_triangle _ _ _


/-- Convergence in distribution forces the path Lévy–Prokhorov distance to zero
(path space `C(ℝ≥0, ℝ^d)` is separable and completely metrizable). -/
theorem aux_lem_resolvents_to_paths_lp_tendsto_zero {d : ℕ}
    (mu : ℕ → ProbabilityMeasure (DiffusionPath d))
    (nu : ProbabilityMeasure (DiffusionPath d))
    (h : Tendsto mu atTop (𝓝 nu)) :
    Tendsto (fun n ↦ pathLevyProkhorovDist (mu n) nu) atTop (𝓝 0) := by
  let : MetricSpace (DiffusionPath d) := TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have h_cont := (LevyProkhorov.continuous_ofMeasure_probabilityMeasure (Ω := DiffusionPath d)).tendsto nu
  have h_conv : Tendsto (fun n ↦ LevyProkhorov.ofMeasure (mu n)) atTop
      (𝓝 (LevyProkhorov.ofMeasure nu)) := h_cont.comp h
  have h_dist : Tendsto (fun n ↦ dist (LevyProkhorov.ofMeasure (mu n))
      (LevyProkhorov.ofMeasure nu)) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp h_conv
  simpa [aux_lem_resolvents_to_paths_lp_eq_dist] using h_dist


/-- Three epsilons:
one compact set of paths carrying all but `eps` of every law of the family AND of the
limit, together with convergence of every bounded cylinder functional, gives convergence
of every bounded continuous path functional. No Prokhorov theorem is used. -/
theorem aux_lem_resolvents_to_paths_integral_tendsto_of_tight_cylinder {d : ℕ}
    (mu : ℕ → Measure (DiffusionPath d)) [∀ n, IsProbabilityMeasure (mu n)]
    (nu : Measure (DiffusionPath d)) [IsProbabilityMeasure nu]
    (htight : ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
      (∀ n, mu n Kpᶜ ≤ ENNReal.ofReal eps) ∧ nu Kpᶜ ≤ ENNReal.ofReal eps)
    (hcyl : ∀ (I : Finset ℝ≥0) (g : (I → SpatialCoordinates d) →ᵇ ℝ),
      Tendsto (fun n ↦ ∫ z, g (ContinuousPath.finsetEvaluation I z) ∂(mu n)) atTop
        (𝓝 (∫ z, g (ContinuousPath.finsetEvaluation I z) ∂nu)))
    (F : DiffusionPath d →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ z, F z ∂(mu n)) atTop (𝓝 (∫ z, F z ∂nu)) := by
  let : MetricSpace (DiffusionPath d) := TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  rw [Metric.tendsto_nhds]
  intro eps heps
  set eps5 : ℝ := eps / 5 with heps5def
  have heps5 : 0 < eps5 := by positivity
  set Ctot : ℝ := ‖F‖ + (‖F‖ + eps5) with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    have := norm_nonneg F
    linarith
  set eta : ℝ := eps5 / Ctot with hetadef
  have hetapos : 0 < eta := div_pos heps5 hCtotpos
  obtain ⟨Kp, hKpcompact, hKmass, hKmass_nu⟩ := htight eta hetapos
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hKpcompact heps5
  have hKpmeas : MeasurableSet Kp := hKpcompact.isClosed.measurableSet
  have herror : ∀ mu' : Measure (DiffusionPath d), ∀ _ : IsProbabilityMeasure mu',
      mu' Kpᶜ ≤ ENNReal.ofReal eta →
      |(∫ z, F z ∂mu') - ∫ z, G z ∂mu'| ≤ 2 * eps5 := by
    intro mu' hmuprob hmass
    have hmassreal : mu'.real Kpᶜ ≤ eta := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hetapos.le hmass
    have hbase := abs_integral_sub_le_of_approx_on mu' F G hKpmeas heps5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ Ctot := by
      rw [hCtotdef]
      linarith [hGnorm]
    have hprod : (‖F‖ + ‖G‖) * mu'.real Kpᶜ ≤ eps5 := by
      calc (‖F‖ + ‖G‖) * mu'.real Kpᶜ ≤ Ctot * eta :=
            mul_le_mul hFG hmassreal measureReal_nonneg hCtotpos.le
        _ = eps5 := by
            rw [hetadef]
            field_simp
    linarith [hbase, hprod]
  obtain ⟨I, g, hg⟩ := hGcyl
  have hcyl' : Tendsto (fun n ↦ ∫ z, G z ∂(mu n)) atTop (𝓝 (∫ z, G z ∂nu)) := by
    simp only [hg]
    exact hcyl I g
  have hnear : ∀ᶠ n in atTop, |(∫ z, G z ∂(mu n)) - ∫ z, G z ∂nu| < eps5 := by
    have h := Metric.tendsto_nhds.mp hcyl' eps5 heps5
    simpa only [Real.dist_eq] using h
  filter_upwards [hnear] with n hnear
  rw [Real.dist_eq]
  have h1 := herror (mu n) inferInstance (hKmass n)
  have h2 := herror nu inferInstance hKmass_nu
  have h2' : |(∫ z, G z ∂nu) - ∫ z, F z ∂nu| ≤ 2 * eps5 := by
    rw [abs_sub_comm]
    exact h2
  have htri1 := abs_sub_le (∫ z, F z ∂(mu n))
    (∫ z, G z ∂(mu n))
    (∫ z, F z ∂nu)
  have htri2 := abs_sub_le (∫ z, G z ∂(mu n))
    (∫ z, G z ∂nu)
    (∫ z, F z ∂nu)
  rw [heps5def] at h1 h2' hnear
  linarith [htri1, htri2, h1, h2', hnear]


/-- Convergence in distribution from tightness and cylinder convergence . -/
theorem aux_lem_resolvents_to_paths_tendsto_of_tight_cylinder {d : ℕ}
    (mu : ℕ → ProbabilityMeasure (DiffusionPath d))
    (nu : ProbabilityMeasure (DiffusionPath d))
    (htight : ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
      (∀ n, (mu n : Measure (DiffusionPath d)) Kpᶜ ≤ ENNReal.ofReal eps) ∧
      (nu : Measure (DiffusionPath d)) Kpᶜ ≤ ENNReal.ofReal eps)
    (hcyl : ∀ (I : Finset ℝ≥0) (g : (I → SpatialCoordinates d) →ᵇ ℝ),
      Tendsto (fun n ↦ ∫ z, g (ContinuousPath.finsetEvaluation I z)
          ∂(mu n : Measure (DiffusionPath d))) atTop
        (𝓝 (∫ z, g (ContinuousPath.finsetEvaluation I z) ∂(nu : Measure (DiffusionPath d))))) :
    Tendsto mu atTop (𝓝 nu) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun F ↦ ?_
  exact aux_lem_resolvents_to_paths_integral_tendsto_of_tight_cylinder
    (fun n ↦ (mu n : Measure (DiffusionPath d))) (nu : Measure (DiffusionPath d))
    htight hcyl F

/-- Moving comparison: both sequences converge to the same law . -/
theorem aux_lem_resolvents_to_paths_lp_moving {d : ℕ}
    (mu nu : ℕ → ProbabilityMeasure (DiffusionPath d))
    (rho : ProbabilityMeasure (DiffusionPath d))
    (hmu : Tendsto mu atTop (𝓝 rho)) (hnu : Tendsto nu atTop (𝓝 rho)) :
    Tendsto (fun n ↦ pathLevyProkhorovDist (mu n) (nu n)) atTop (𝓝 0) := by
  have h1 := aux_lem_resolvents_to_paths_lp_tendsto_zero mu rho hmu
  have h2 := aux_lem_resolvents_to_paths_lp_tendsto_zero nu rho hnu
  have hsum : Tendsto (fun n ↦ pathLevyProkhorovDist (mu n) rho +
      pathLevyProkhorovDist (nu n) rho) atTop (𝓝 0) := by
    simpa only [add_zero] using h1.add h2
  refine squeeze_zero (fun n ↦ aux_lem_resolvents_to_paths_lp_nonneg _ _) (fun n ↦ ?_) hsum
  calc pathLevyProkhorovDist (mu n) (nu n)
      ≤ pathLevyProkhorovDist (mu n) rho + pathLevyProkhorovDist rho (nu n) :=
        aux_lem_resolvents_to_paths_lp_triangle _ _ _
    _ = pathLevyProkhorovDist (mu n) rho + pathLevyProkhorovDist (nu n) rho := by
        rw [aux_lem_resolvents_to_paths_lp_comm rho (nu n)]

/-- Final compact-starting-set step (proved; `tendstoUniformlyOn_of_compact_moving_points`). -/
theorem aux_lem_resolvents_to_paths_uniform_from_moving
    {d : ℕ}
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B)
    (mu : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (nu : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hmoving : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d)
      (φ : ℕ → ℕ),
      (∀ n, u n ∈ B) → x ∈ B → StrictMono φ →
      Tendsto u atTop (𝓝 x) →
      Tendsto (fun n ↦ pathLevyProkhorovDist (mu (φ n) (u n)) (nu (u n)))
        atTop (𝓝 0)) :
    ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist (mu N x) (nu x) < eps := by
  let F : ℕ → SpatialCoordinates d → ℝ :=
    fun N x ↦ pathLevyProkhorovDist (mu N x) (nu x)
  have hF : TendstoUniformlyOn F (fun _ ↦ (0 : ℝ)) atTop B := by
    apply SubdiffusiveProcess.tendstoUniformlyOn_of_compact_moving_points hB
    · exact continuousOn_const
    · intro u x φ hu hx hφ hux
      simpa only [F] using hmoving u x φ hu hx hφ hux
  intro eps heps
  rw [Metric.tendstoUniformlyOn_iff] at hF
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hF eps heps)
  refine ⟨N0, fun N hN x hx ↦ ?_⟩
  have hdist := hN0 N hN x hx
  have hzero : (0 : ℝ) ≤ F N x := aux_lem_resolvents_to_paths_lp_nonneg _ _
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hzero] at hdist
  simpa only [F] using hdist



theorem aux_lem_resolvents_to_paths_of_tight_cylinder
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (hcontK : Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x))
    (htight : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
        (∀ n, KN (φ n) (omega, u n) Kpᶜ ≤ ENNReal.ofReal eps) ∧
        K (omega, x) Kpᶜ ≤ ENNReal.ofReal eps)
    (hcyl : ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ (I : Finset ℝ≥0) (g : (I → SpatialCoordinates d) →ᵇ ℝ),
        Tendsto (fun n ↦ ∫ z, g (ContinuousPath.finsetEvaluation I z)
            ∂(KN (φ n) (omega, u n))) atTop
          (𝓝 (∫ z, g (ContinuousPath.finsetEvaluation I z) ∂(K (omega, x))))) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) < eps := by
  intro B hB
  refine aux_lem_resolvents_to_paths_uniform_from_moving B hB
    (fun N x ↦ jointPathProbabilityMeasure (KN N) (hKN N) omega x)
    (fun x ↦ jointPathProbabilityMeasure K hK omega x) ?_
  intro u x φ _ _ hφ hu
  have hw : Tendsto (fun n ↦ jointPathProbabilityMeasure (KN (φ n)) (hKN (φ n)) omega (u n))
      atTop (𝓝 (jointPathProbabilityMeasure K hK omega x)) :=
    aux_lem_resolvents_to_paths_tendsto_of_tight_cylinder _ _
      (htight u x φ hφ hu) (hcyl u x φ hφ hu)
  have hK' : Tendsto (fun n ↦ jointPathProbabilityMeasure K hK omega (u n)) atTop
      (𝓝 (jointPathProbabilityMeasure K hK omega x)) :=
    (hcontK.tendsto x).comp hu
  exact aux_lem_resolvents_to_paths_lp_moving _ _ _ hw hK'

/-! ### Tightness (auxiliary ) -/

/-- Modulus bound for every member plus a compact start set gives one compact set. -/
theorem aux_lem_resolvents_to_paths_seq_tight {d : ℕ}
    (mu : ℕ → Measure (DiffusionPath d))
    (K0 : Set (SpatialCoordinates d)) (hK0 : IsCompact K0)
    (hstart : ∀ n, mu n {z : DiffusionPath d | z 0 ∉ K0} = 0)
    (hmod : ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ delta : ℝ≥0∞, 0 < delta ∧
        ∀ n, mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps) :
    ∀ eps : ℝ, 0 < eps → ∃ K1 : Set (DiffusionPath d), IsCompact K1 ∧
      ∀ n, mu n K1ᶜ ≤ ENNReal.ofReal eps := by
  intro eps heps
  have heps' : 0 < ENNReal.ofReal eps := ENNReal.ofReal_pos.mpr heps
  have h_tight : IsTightMeasureSet (Set.range mu) :=
    ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le hK0
      (fun mu' hmu' => by
        rcases hmu' with ⟨n, rfl⟩
        exact hstart n)
      (fun T r hr' eps'' heps'' => by
        rcases hmod T r hr' eps'' heps'' with ⟨delta, hdelta, h⟩
        exact ⟨delta, hdelta, fun mu' hmu' => by
          rcases hmu' with ⟨n, rfl⟩
          exact h n⟩)
  rcases (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp h_tight) (ENNReal.ofReal eps) heps' with
    ⟨K, hK_compact, hK⟩
  refine ⟨K, hK_compact, fun n => ?_⟩
  exact hK (mu n) ⟨n, rfl⟩


/-- Type annotation: the implicit `alpha` in `ContinuousPath.modulusSet`
is a bare metavariable in a stated `⊆`-goal between two `modulusSet` terms (nothing pins it to
`SpatialCoordinates d` before the tactic block runs), which leaves `PseudoEMetricSpace ?m` stuck.
Stating it here as a top-level term with an explicit `{d : ℕ}` binder and consuming it by
`exact`/application (never restating the bare `⊆` as a fresh tactic goal) keeps `alpha`
resolved to `SpatialCoordinates d` throughout. Monotonicity direction: a smaller `delta`
imposes the closeness constraint on fewer time-pairs, hence gives a larger `modulusSet`. -/
theorem aux_lem_resolvents_to_paths_modulusSet_mono {d : ℕ} (T : ℝ≥0) (r : ℝ≥0∞)
    {delta₁ delta₂ : ℝ≥0∞} (h : delta₁ ≤ delta₂) :
    (ContinuousPath.modulusSet T delta₂ r : Set (DiffusionPath d)) ⊆
      ContinuousPath.modulusSet T delta₁ r := by
  intro ω hω s t hs ht h_edist
  exact hω s t hs ht (h_edist.trans h)

theorem aux_lem_resolvents_to_paths_modulus_all {d : ℕ}
    (mu : ℕ → Measure (DiffusionPath d)) [∀ n, IsFiniteMeasure (mu n)]
    (hev : ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ delta : ℝ≥0∞, 0 < delta ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
        mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps) :
    ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ delta : ℝ≥0∞, 0 < delta ∧
        ∀ n, mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
  intro T r hr eps heps
  rcases hev T r hr eps heps with ⟨delta0, hdelta0_pos, n0, hn0⟩
  have h_exceptions : ∀ n, n < n0 → ∃ delta : ℝ≥0∞, 0 < delta ∧ mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
    intro n hn
    exact aux_lem_resolvents_to_paths_single_modulus (mu n) T r hr eps heps
  -- Build a delta that is ≤ delta0 and ≤ every delta_n (n < n0)
  -- Use strong induction on k ≤ n0: there exists delta > 0 such that
  -- for all n < k, mu n (modulusSet T delta r)ᶜ ≤ eps
  have h_exists : ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ n, mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
    
    -- `delta ≤ delta0`, so the final `n0 ≤ n` case can transfer `hn0` (stated at `delta0`)
    -- down to `delta` by `modulusSet`-monotonicity instead of a bare (invalid) identification
    -- of `delta` with `delta0`.
    have h_ind : ∀ k, k ≤ n0 → ∃ delta : ℝ≥0∞, 0 < delta ∧ delta ≤ delta0 ∧
        (∀ n, n < k → mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps) := by
      intro k hk
      induction k with
      | zero =>
        exact ⟨delta0, hdelta0_pos, le_refl delta0, fun n hn => (Nat.not_lt_zero _).elim hn⟩
      | succ k ih =>
        have hk_le : k ≤ n0 := Nat.le_of_succ_le hk
        rcases ih hk_le with ⟨delta, hdelta_pos, hdelta_le_delta0, hdelta_except⟩
        have hk_lt_n0 : k < n0 := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        rcases h_exceptions k hk_lt_n0 with ⟨delta_k, hdelta_k_pos, hdelta_k_bound⟩
        let delta_new := min delta delta_k
        have h_delta_new_pos : 0 < delta_new := lt_min hdelta_pos hdelta_k_pos
        have h_delta_new_le_delta0 : delta_new ≤ delta0 :=
          le_trans (min_le_left delta delta_k) hdelta_le_delta0
        have h_delta_new_except : ∀ n, n < k + 1 → mu n (ContinuousPath.modulusSet T delta_new r)ᶜ ≤ eps := by
          intro n hn
          have hn_le_k : n ≤ k := Nat.le_of_lt_succ hn
          rcases Nat.eq_or_lt_of_le hn_le_k with (rfl | hn_lt_k)
          · -- n = k: use hdelta_k_bound, since delta_new ≤ delta_k
            have h_sub : (ContinuousPath.modulusSet T delta_new r : Set (DiffusionPath d))ᶜ ⊆
                (ContinuousPath.modulusSet T delta_k r)ᶜ :=
              Set.compl_subset_compl_of_subset (aux_lem_resolvents_to_paths_modulusSet_mono T r (min_le_right delta delta_k))
            exact le_trans (measure_mono h_sub) hdelta_k_bound
          · -- n < k: use hdelta_except, since delta_new ≤ delta
            have h_sub : (ContinuousPath.modulusSet T delta_new r : Set (DiffusionPath d))ᶜ ⊆
                (ContinuousPath.modulusSet T delta r)ᶜ :=
              Set.compl_subset_compl_of_subset (aux_lem_resolvents_to_paths_modulusSet_mono T r (min_le_left delta delta_k))
            exact le_trans (measure_mono h_sub) (hdelta_except n hn_lt_k)
        exact ⟨delta_new, h_delta_new_pos, h_delta_new_le_delta0, h_delta_new_except⟩
    rcases h_ind n0 (le_refl n0) with ⟨delta, hdelta_pos, hdelta_le_delta0, hdelta_except⟩
    refine ⟨delta, hdelta_pos, fun n => ?_⟩
    by_cases hn_lt_n0 : n < n0
    · exact hdelta_except n hn_lt_n0
    · push Not at hn_lt_n0
      have h_sub : (ContinuousPath.modulusSet T delta r : Set (DiffusionPath d))ᶜ ⊆
          (ContinuousPath.modulusSet T delta0 r)ᶜ :=
        Set.compl_subset_compl_of_subset (aux_lem_resolvents_to_paths_modulusSet_mono T r hdelta_le_delta0)
      exact le_trans (measure_mono h_sub) (hn0 n hn_lt_n0)
  exact h_exists


/-- Assembly: tightness of the moving-start family (`mfd:prop-as-forms`). The laws
start at `u n → x` and satisfy the modulus bound for all large indices. -/
theorem aux_lem_resolvents_to_paths_moving_tight_of_modulus {d : ℕ}
    (mu : ℕ → Measure (DiffusionPath d)) [∀ n, IsFiniteMeasure (mu n)]
    (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d)
    (hu : Tendsto u atTop (𝓝 x))
    (hstart : ∀ n, mu n {z : DiffusionPath d | z 0 ≠ u n} = 0)
    (hev : ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
      ∃ delta : ℝ≥0∞, 0 < delta ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
        mu n (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps) :
    ∀ eps : ℝ, 0 < eps → ∃ K1 : Set (DiffusionPath d), IsCompact K1 ∧
      ∀ n, mu n K1ᶜ ≤ ENNReal.ofReal eps := by
  refine aux_lem_resolvents_to_paths_seq_tight mu (insert x (Set.range u))
    hu.isCompact_insert_range (fun n ↦ ?_) (aux_lem_resolvents_to_paths_modulus_all mu hev)
  refine measure_mono_null (fun z hz ↦ ?_) (hstart n)
  simp only [Set.mem_ofPred_eq] at hz ⊢
  intro hzu
  exact hz (hzu ▸ Set.mem_insert_of_mem x ⟨n, rfl⟩)

/-! ### assembly : proved glue and auxiliary proof steps. -/

/-- Moving-start tightness of the cutoff laws together with the limit law, from start
pinning and a modulus bound uniform over compact starting sets for all large cutoffs
(`mfd:prop-as-forms`). Proved glue of the auxiliary/auxiliary pieces. -/
theorem aux_lem_resolvents_to_paths_moving_tight
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (hstart : ∀ N y, KN N (omega, y) {z : DiffusionPath d | z 0 ≠ y} = 0)
    (hunif : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ (T : ℝ≥0) (r : ℝ≥0∞), 0 < r → ∀ eps : ℝ≥0∞, 0 < eps →
        ∃ delta : ℝ≥0∞, 0 < delta ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ y ∈ B,
          KN N (omega, y) (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps) :
    ∀ (u : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d) (φ : ℕ → ℕ),
      StrictMono φ → Tendsto u atTop (𝓝 x) →
      ∀ eps : ℝ, 0 < eps → ∃ Kp : Set (DiffusionPath d), IsCompact Kp ∧
        (∀ n, KN (φ n) (omega, u n) Kpᶜ ≤ ENNReal.ofReal eps) ∧
        K (omega, x) Kpᶜ ≤ ENNReal.ofReal eps := by
  intro u x φ hφ hu
  have : ∀ N, IsMarkovKernel (KN N) := hKN
  have : IsMarkovKernel K := hK
  refine aux_lem_resolvents_to_paths_tight_union (fun n ↦ KN (φ n) (omega, u n))
    (K (omega, x)) ?_ (aux_lem_resolvents_to_paths_single_tight (K (omega, x)))
  refine aux_lem_resolvents_to_paths_moving_tight_of_modulus
    (fun n ↦ KN (φ n) (omega, u n)) u x hu (fun n ↦ hstart (φ n) (u n)) ?_
  intro T r hr eps heps
  obtain ⟨delta, hdelta, N0, hN0⟩ :=
    hunif (insert x (Set.range u)) hu.isCompact_insert_range T r hr eps heps
  exact ⟨delta, hdelta, N0, fun n hn ↦
    hN0 (φ n) (hn.trans (hφ.id_le n)) (u n) (Set.mem_insert_of_mem x ⟨n, rfl⟩)⟩

/-- `mfd:prop-as-forms` (paths start at their initial point): the singleton-time
finite-dimensional attachment at time `0` pins the start, since `PN N omega 0 = id`. -/
theorem aux_lem_resolvents_to_paths_start_pinned
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d)
    (hfdd : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) :
    ∀ N y, KN N (omega, y) {z : DiffusionPath d | z 0 ≠ y} = 0 := by
  intro N y
  have hev : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) :=
    Measurable.of_eval fun t => (continuous_eval_const ((t : ℝ≥0))).measurable
  have hfdd0 : (KN N (omega, y)).map (ContinuousPath.finsetEvaluation ({0} : Finset ℝ≥0))
      = SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) ({0} : Finset ℝ≥0) y := by
    rw [← Kernel.map_apply (KN N) hev (omega, y)]
    exact hfdd N ({0} : Finset ℝ≥0) y
  have heval := map_eval_eq_of_finsetEvaluation (PN N omega) (KN N (omega, y)) y 0 hfdd0
  have hev0 : Measurable (fun path : DiffusionPath d => path 0) :=
    (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0).measurable
  have hset : {z : DiffusionPath d | z 0 ≠ y}
      = (fun path : DiffusionPath d => path 0) ⁻¹' ({y}ᶜ) := rfl
  rw [hset, ← Measure.map_apply hev0 (measurableSet_singleton y).compl, heval,
    (PN N omega).kernel_zero, Kernel.id_apply]
  simp



theorem lem_resolvents_to_paths
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (_hin : in_crossing M H PN KN)
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (_hP : ∀ omega, (P omega).IsConservative)
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)))
    (omega : BilateralField d)
    (hcutoffAt :
      (∀ N, ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
          (SpatialCoordinates d),
        (∀ mu, DenseRange (D.operator mu)) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
        ∀ (mu : Semigroup.PositiveShift)
          (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
          D.solution mu f x =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
              kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
      (∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x))
    (L : ℕ → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N x, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
      (KN N (omega, x)) = L N x)
    (_hLlocal : ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N))
    (hLstrong : ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N))
    (hlimAt : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hkilled : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ (closure (centeredCube (Qc n) (Qr n) (hQr n) :
              Set (SpatialCoordinates d))),
              |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(KN N (omega, x)))
                - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                      ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                  ∂(K (omega, x)))| < eps)
    (hcontK : Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x))
    (_hstrong : HasStrongMarkovRestart K omega)
    (_hcontKN : ∀ N, Continuous (fun x ↦
      jointPathProbabilityMeasure (KN N) (hKN N) omega x)) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) < eps := by
  have hstart := aux_lem_resolvents_to_paths_start_pinned PN KN omega hcutoffAt.2
  have hunif := aux_lem_resolvents_to_paths_uniform_modulus_core PN KN hKN K hK P Qc Qr hQr hQ
    omega hcutoffAt.2 L hL hLstrong hlimAt hkilled hcontK
  have htight := aux_lem_resolvents_to_paths_moving_tight KN hKN K hK omega hstart hunif
  have hres := aux_lem_resolvents_to_paths_resolvent_moving' KN hKN K hK omega Qc Qr hQr hQ
    hkilled hcontK
  have hmarg := aux_lem_resolvents_to_paths_marginal_moving KN hKN K hK omega htight hres
  have hcyl := aux_lem_resolvents_to_paths_cyl_moving PN KN hKN K hK P omega hcutoffAt.2 hlimAt
    htight hmarg
  exact aux_lem_resolvents_to_paths_of_tight_cylinder KN hKN K hK omega hcontK htight hcyl

end SubdiffusiveProcess.Paper
