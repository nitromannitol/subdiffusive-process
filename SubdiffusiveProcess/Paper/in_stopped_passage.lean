import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.lem_tightness_deterministic_restart
import SubdiffusiveProcess.Paper.limit_kernel_markov_passage
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import MarkovProcess.Path.ExitTime
import MarkovProcess.Path.ExitTimeShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal LevyProkhorov

namespace Paper

/-! ### Generic helpers for the stopped occupation passage -/

/-- Lower semicontinuity of an extended-valued function from sequential lower bounds, in a
first-countable space. -/
theorem aux_in_stopped_passage_lsc_of_seq {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {G : X → ℝ≥0∞}
    (h : ∀ (x : X) (u : ℕ → X), Tendsto u atTop (𝓝 x) →
      G x ≤ liminf (fun k => G (u k)) atTop) :
    LowerSemicontinuous G := by
  intro x y hy
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨u, hu, hle⟩ := exists_seq_forall_of_frequently hne
  have h2 : liminf (fun k => G (u k)) atTop ≤ y :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun k => not_lt.mp (hle k))
  exact absurd (hy.trans_le ((h x u hu).trans h2)) (lt_irrefl y)

/-- Portmanteau for a finite lower-semicontinuous extended-valued functional. -/
theorem aux_in_stopped_passage_lsc_portmanteau {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {G : X → ℝ≥0∞} (hG : LowerSemicontinuous G)
    (hGtop : ∀ x, G x ≠ ⊤) :
    ∫⁻ x, G x ∂(μ : Measure X) ≤
      liminf (fun j => ∫⁻ x, G x ∂(μs j : Measure X)) atTop := by
  have hGm : Measurable G := hG.measurable
  have hrep : ∀ ν : Measure X, ∫⁻ x, G x ∂ν =
      ∫⁻ t in Set.Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < G x} := by
    intro ν
    have h1 : ∫⁻ x, G x ∂ν = ∫⁻ x, ENNReal.ofReal ((G x).toReal) ∂ν := by
      congr 1
      funext x
      rw [ENNReal.ofReal_toReal (hGtop x)]
    rw [h1, lintegral_eq_lintegral_meas_lt ν
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hGm.ennreal_toReal.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hGtop x)).symm
  have hopen : ∀ t : ℝ, IsOpen {x | ENNReal.ofReal t < G x} := fun t =>
    lowerSemicontinuous_iff_isOpen_preimage.mp hG _
  have hmeas : ∀ ν : Measure X,
      Measurable (fun t : ℝ => ν {x | ENNReal.ofReal t < G x}) := by
    intro ν
    refine Antitone.measurable (fun t t' htt' => measure_mono fun x hx => ?_)
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt') hx
  rw [hrep]
  simp_rw [hrep]
  calc ∫⁻ t in Set.Ioi (0 : ℝ), (μ : Measure X) {x | ENNReal.ofReal t < G x}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
          liminf (fun j => (μs j : Measure X) {x | ENNReal.ofReal t < G x}) atTop :=
        lintegral_mono fun t => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ (hopen t)
    _ ≤ liminf (fun j => ∫⁻ t in Set.Ioi (0 : ℝ),
          (μs j : Measure X) {x | ENNReal.ofReal t < G x}) atTop :=
        lintegral_liminf_le fun j => hmeas _

/-- A function continuous on a closed ball and vanishing on its sphere is uniformly small in a
thin inner shell. -/
theorem aux_in_stopped_passage_boundary_small {d : ℕ} (z : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) (u : SpatialCoordinates d → ℝ) (hu : ContinuousOn u (Metric.closedBall z ρ))
    (hzero : ∀ y ∈ Metric.sphere z ρ, u y = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, ρ - δ < dist y z → dist y z ≤ ρ → |u y| < ε := by
  have huc := (isCompact_closedBall z ρ).uniformContinuousOn_of_continuous hu
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min δ ρ, lt_min hδ hρ, fun y hy1 hy2 => ?_⟩
  have hmin : min δ ρ ≤ ρ := min_le_right δ ρ
  have hminδ : min δ ρ ≤ δ := min_le_left δ ρ
  have hyz : 0 < dist y z := by linarith
  have hyz' : 0 < ‖y - z‖ := by rwa [← dist_eq_norm]
  set y' : SpatialCoordinates d := z + (ρ / ‖y - z‖) • (y - z) with hy'
  have hy'sphere : y' ∈ Metric.sphere z ρ := by
    rw [mem_sphere_iff_norm, hy', add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hρ hyz'), div_mul_cancel₀ ρ hyz'.ne']
  have hdist : dist y y' < δ := by
    have hyy' : y - y' = (1 - ρ / ‖y - z‖) • (y - z) := by
      rw [hy', sub_smul, one_smul]
      abel
    rw [dist_eq_norm, hyy', norm_smul, Real.norm_eq_abs]
    rw [dist_eq_norm] at hy1 hy2
    have hle : 1 ≤ ρ / ‖y - z‖ := by rw [le_div_iff₀ hyz']; linarith
    rw [abs_of_nonpos (by linarith), neg_sub, sub_mul, div_mul_cancel₀ ρ hyz'.ne', one_mul]
    linarith
  have hy_mem : y ∈ Metric.closedBall z ρ := Metric.mem_closedBall.mpr hy2
  have := hδu y hy_mem y' (Metric.sphere_subset_closedBall hy'sphere) hdist
  rwa [hzero y' hy'sphere, Real.dist_eq, sub_zero] at this


/-! ### The killed discounted occupation functional -/



noncomputable def aux_in_stopped_passage_occ {d : ℕ} (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t

/-- The extended-valued version of the occupation functional (for nonnegative data). -/
noncomputable def aux_in_stopped_passage_occPos {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (path : DiffusionPath d) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
    (Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)

/-- The discounted exit weight `exp (-lam τ_U)`, equal to zero on paths that never exit. -/
noncomputable def aux_in_stopped_passage_expExit {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (path : DiffusionPath d) : ℝ :=
  if ContinuousPath.exitTime U path = ⊤ then 0
  else Real.exp (-lam * (ContinuousPath.exitTime U path).toReal)

theorem aux_in_stopped_passage_exp_Ioi {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    ∫ x in Set.Ioi c, Real.exp (-lam * x) = Real.exp (-lam * c) / lam := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hlam) c, neg_div_neg_eq]

theorem aux_in_stopped_passage_integrand_measurable {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) :
    Measurable (Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s)))) := by
  refine Measurable.indicator ?_ (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (f.continuous.comp (path.continuous.comp continuous_real_toNNReal))).measurable

theorem aux_in_stopped_passage_integrand_norm_le {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d)
    (t : ℝ) :
    ‖Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖ ≤
        ‖f‖ * Real.exp (-lam * t) := by
  refine (norm_indicator_le_norm_self _ t).trans ?_
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le

theorem aux_in_stopped_passage_integrand_integrable {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (path : DiffusionPath d) :
    Integrable (Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
  Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖)
    (aux_in_stopped_passage_integrand_measurable U lam f path).aestronglyMeasurable
    (Eventually.of_forall (aux_in_stopped_passage_integrand_norm_le U lam f path))

theorem aux_in_stopped_passage_occ_abs_le {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (path : DiffusionPath d) :
    |aux_in_stopped_passage_occ U lam f path| ≤ ‖f‖ / lam := by
  have h := norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖)
    (Eventually.of_forall (aux_in_stopped_passage_integrand_norm_le U lam f path))
  rw [integral_const_mul, aux_in_stopped_passage_exp_Ioi hlam, mul_zero, Real.exp_zero,
    ← div_eq_mul_one_div] at h
  exact h

theorem aux_in_stopped_passage_occ_measurable {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (aux_in_stopped_passage_occ U lam f) := by
  have hS : MeasurableSet {p : DiffusionPath d × ℝ |
      ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_fst)
  have hg : Continuous (fun p : DiffusionPath d × ℝ =>
      Real.exp (-lam * p.2) * f (p.1 (Real.toNNReal p.2))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
      (f.continuous.comp (continuous_eval.comp
        (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))))
  have heq : (fun p : DiffusionPath d × ℝ =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U p.1}
        (fun s => Real.exp (-lam * s) * f (p.1 (Real.toNNReal s))) p.2) =
      Set.indicator {p : DiffusionPath d × ℝ |
        ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1}
        (fun p => Real.exp (-lam * p.2) * f (p.1 (Real.toNNReal p.2))) := by
    funext p
    by_cases hp : ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1
    · rw [Set.indicator_of_mem (show p.2 ∈ {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime U p.1} from hp),
        Set.indicator_of_mem (show p ∈ {p : DiffusionPath d × ℝ |
          ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} from hp)]
    · rw [Set.indicator_of_notMem (show p.2 ∉ {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime U p.1} from hp),
        Set.indicator_of_notMem (show p ∉ {p : DiffusionPath d × ℝ |
          ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} from hp)]
  have hF : StronglyMeasurable (fun p : DiffusionPath d × ℝ =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U p.1}
        (fun s => Real.exp (-lam * s) * f (p.1 (Real.toNNReal s))) p.2) := by
    rw [heq]
    exact (hg.measurable.indicator hS).stronglyMeasurable
  exact (hF.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

theorem aux_in_stopped_passage_occ_integrable {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (P : Measure (DiffusionPath d)) [IsFiniteMeasure P] :
    Integrable (aux_in_stopped_passage_occ U lam f) P :=
  Integrable.of_bound (aux_in_stopped_passage_occ_measurable U hU lam f).aestronglyMeasurable
    (‖f‖ / lam) (Eventually.of_forall fun path => by
      rw [Real.norm_eq_abs]
      exact aux_in_stopped_passage_occ_abs_le U hlam f path)

theorem aux_in_stopped_passage_occ_lin {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (g f₁ f₂ : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (a b : ℝ) (h : ∀ y, g y = a * f₁ y + b * f₂ y) (path : DiffusionPath d) :
    aux_in_stopped_passage_occ U lam g path =
      a * aux_in_stopped_passage_occ U lam f₁ path +
        b * aux_in_stopped_passage_occ U lam f₂ path := by
  unfold aux_in_stopped_passage_occ
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((aux_in_stopped_passage_integrand_integrable U hlam f₁ path).const_mul a)
    ((aux_in_stopped_passage_integrand_integrable U hlam f₂ path).const_mul b)]
  congr 1
  funext t
  by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem ht, h]
    ring
  · simp only [Set.indicator_of_notMem ht]
    ring

theorem aux_in_stopped_passage_occ_one {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (path : DiffusionPath d) :
    aux_in_stopped_passage_occ U lam (BoundedContinuousFunction.const _ 1) path =
      (1 - aux_in_stopped_passage_expExit U lam path) / lam := by
  unfold aux_in_stopped_passage_occ aux_in_stopped_passage_expExit
  simp only [BoundedContinuousFunction.const_apply, mul_one]
  have hS : MeasurableSet {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  rw [integral_indicator hS, Measure.restrict_restrict hS]
  have hset : {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path} =
      {t : ℝ | ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U path} := rfl
  rw [hset, ContinuousPath.survivalSet]
  split_ifs with htop
  · rw [aux_in_stopped_passage_exp_Ioi hlam, mul_zero, Real.exp_zero, sub_zero]
  · set T := (ContinuousPath.exitTime U path).toReal with hTdef
    have hT : 0 ≤ T := ENNReal.toReal_nonneg
    rw [← integral_Ioc_eq_integral_Ioo]
    have hsplit := setIntegral_union (f := fun x => Real.exp (-lam * x))
      (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := T)) measurableSet_Ioi
      ((exp_neg_integrableOn_Ioi 0 hlam).mono_set Set.Ioc_subset_Ioi_self)
      (exp_neg_integrableOn_Ioi T hlam)
    rw [Set.Ioc_union_Ioi_eq_Ioi hT, aux_in_stopped_passage_exp_Ioi hlam,
      aux_in_stopped_passage_exp_Ioi hlam, mul_zero, Real.exp_zero] at hsplit
    rw [sub_div, hsplit]
    ring

theorem aux_in_stopped_passage_ofReal_occ {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hf : ∀ y, 0 ≤ f y) (path : DiffusionPath d) :
    ENNReal.ofReal (aux_in_stopped_passage_occ U lam f path) =
      aux_in_stopped_passage_occPos U lam f path :=
  ofReal_integral_eq_lintegral_ofReal (aux_in_stopped_passage_integrand_integrable U hlam f path)
    (Eventually.of_forall fun t => Set.indicator_nonneg
      (fun _ _ => mul_nonneg (Real.exp_pos _).le (hf _)) t)

/-- Survival past a deterministic time is an open condition on paths. -/
theorem aux_in_stopped_passage_isOpen_survival {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (t : ℝ≥0) :
    IsOpen {v : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U v} := by
  have hiff : ∀ v : DiffusionPath d, (t : ℝ≥0∞) < ContinuousPath.exitTime U v ↔
      Set.MapsTo v (Set.Icc 0 t) U := by
    intro v
    constructor
    · intro h s hs
      exact ContinuousPath.mem_of_lt_exitTime U v s
        (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hs.2) h)
    · intro h
      by_contra hle
      push_neg at hle
      obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t v).mp hle
      exact hs (h ⟨zero_le _, s.2⟩)
  have heq : {v : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U v} =
      {v : DiffusionPath d | Set.MapsTo v (Set.Icc 0 t) U} := by
    ext v
    exact hiff v
  rw [heq]
  exact ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc hU

theorem aux_in_stopped_passage_occPos_lsc {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    LowerSemicontinuous (aux_in_stopped_passage_occPos U lam f) := by
  refine aux_in_stopped_passage_lsc_of_seq fun w u hu => ?_
  unfold aux_in_stopped_passage_occPos
  refine le_trans (lintegral_mono fun s => ?_)
    (lintegral_liminf_le fun k => ENNReal.measurable_ofReal.comp
      (aux_in_stopped_passage_integrand_measurable U lam f (u k)))
  by_cases hs : ENNReal.ofReal s < ContinuousPath.exitTime U w
  · have hopen : IsOpen {v : DiffusionPath d |
        ENNReal.ofReal s < ContinuousPath.exitTime U v} :=
      aux_in_stopped_passage_isOpen_survival U hU (Real.toNNReal s)
    have hev : ∀ᶠ k in atTop, ENNReal.ofReal s < ContinuousPath.exitTime U (u k) :=
      hu (hopen.mem_nhds hs)
    have h1 : Tendsto (fun k => ENNReal.ofReal
        (Real.exp (-lam * s) * f (u k (Real.toNNReal s)))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-lam * s) * f (w (Real.toNNReal s))))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((continuous_const.mul (f.continuous.comp
          (continuous_eval_const (Real.toNNReal s)))).continuousAt.tendsto.comp hu)
    have h2 : Tendsto (fun k => ENNReal.ofReal
        (Set.indicator {r : ℝ | ENNReal.ofReal r < ContinuousPath.exitTime U (u k)}
          (fun r => Real.exp (-lam * r) * f (u k (Real.toNNReal r))) s)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-lam * s) * f (w (Real.toNNReal s))))) := by
      refine h1.congr' ?_
      filter_upwards [hev] with k hk
      rw [Set.indicator_of_mem (show s ∈ {r : ℝ | ENNReal.ofReal r <
        ContinuousPath.exitTime U (u k)} from hk)]
    rw [h2.liminf_eq, Set.indicator_of_mem (show s ∈ {r : ℝ | ENNReal.ofReal r <
      ContinuousPath.exitTime U w} from hs)]
  · rw [Set.indicator_of_notMem (show s ∉ {r : ℝ | ENNReal.ofReal r <
      ContinuousPath.exitTime U w} from hs), ENNReal.ofReal_zero]
    exact zero_le _


/-! ### The discounted exit weight -/

theorem aux_in_stopped_passage_expExit_measurable {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (lam : ℝ) :
    Measurable (aux_in_stopped_passage_expExit U lam : DiffusionPath d → ℝ) := by
  have hout : Measurable (fun τ : ℝ≥0∞ =>
      if τ = ⊤ then (0 : ℝ) else Real.exp (-lam * τ.toReal)) :=
    Measurable.ite (measurableSet_singleton ⊤) measurable_const
      (Real.measurable_exp.comp (measurable_const.mul ENNReal.measurable_toReal))
  exact hout.comp (ContinuousPath.measurable_exitTime U hU)

theorem aux_in_stopped_passage_expExit_nonneg {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (path : DiffusionPath d) : 0 ≤ aux_in_stopped_passage_expExit U lam path := by
  unfold aux_in_stopped_passage_expExit
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem aux_in_stopped_passage_expExit_le_one {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 ≤ lam) (path : DiffusionPath d) :
    aux_in_stopped_passage_expExit U lam path ≤ 1 := by
  unfold aux_in_stopped_passage_expExit
  split_ifs
  · exact zero_le_one
  · exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) ENNReal.toReal_nonneg)

/-- Before the exit time, the discounted exit weight factors through the shifted path. -/
theorem aux_in_stopped_passage_expExit_shift {d : ℕ} (U : Set (SpatialCoordinates d))
    (lam : ℝ) (w : DiffusionPath d) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U w) :
    aux_in_stopped_passage_expExit U lam w =
      Real.exp (-lam * t) *
        aux_in_stopped_passage_expExit U lam (ContinuousPath.shift t w) := by
  have hadd := ContinuousPath.exitTime_shift_add U w t ht
  unfold aux_in_stopped_passage_expExit
  by_cases htop : ContinuousPath.exitTime U (ContinuousPath.shift t w) = ⊤
  · have hw : ContinuousPath.exitTime U w = ⊤ := by rw [← hadd, htop, top_add]
    rw [if_pos hw, if_pos htop, mul_zero]
  · have hw : ContinuousPath.exitTime U w ≠ ⊤ := by
      rw [← hadd]
      exact ENNReal.add_ne_top.mpr ⟨htop, ENNReal.coe_ne_top⟩
    rw [if_neg hw, if_neg htop, ← Real.exp_add, ← hadd,
      ENNReal.toReal_add htop ENNReal.coe_ne_top, ENNReal.coe_toReal]
    congr 1
    ring

/-- After the exit time, the discounted exit weight dominates the deterministic weight. -/
theorem aux_in_stopped_passage_expExit_ge {d : ℕ} (U : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 ≤ lam) (w : DiffusionPath d) (t : ℝ≥0)
    (ht : ContinuousPath.exitTime U w ≤ (t : ℝ≥0∞)) :
    Real.exp (-lam * t) ≤ aux_in_stopped_passage_expExit U lam w := by
  have hne : ContinuousPath.exitTime U w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  unfold aux_in_stopped_passage_expExit
  rw [if_neg hne]
  apply Real.exp_le_exp.mpr
  have hT : (ContinuousPath.exitTime U w).toReal ≤ t := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top ht
    rwa [ENNReal.coe_toReal] at this
  exact mul_le_mul_of_nonpos_left hT (neg_nonpos.mpr hlam)

theorem aux_in_stopped_passage_expExit_integrable {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) {lam : ℝ} (hlam : 0 ≤ lam) (P : Measure (DiffusionPath d))
    [IsFiniteMeasure P] :
    Integrable (aux_in_stopped_passage_expExit U lam) P :=
  Integrable.of_bound (aux_in_stopped_passage_expExit_measurable U hU lam).aestronglyMeasurable
    1 (Eventually.of_forall fun path => by
      rw [Real.norm_eq_abs, abs_of_nonneg (aux_in_stopped_passage_expExit_nonneg U lam path)]
      exact aux_in_stopped_passage_expExit_le_one U hlam path)

theorem aux_in_stopped_passage_integral_occ_one {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) {lam : ℝ} (hlam : 0 < lam) (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] :
    ∫ p, aux_in_stopped_passage_occ U lam (BoundedContinuousFunction.const _ 1) p ∂P =
      (1 - ∫ p, aux_in_stopped_passage_expExit U lam p ∂P) / lam := by
  simp_rw [aux_in_stopped_passage_occ_one U hlam]
  rw [integral_div, integral_sub (integrable_const 1)
    (aux_in_stopped_passage_expExit_integrable U hU hlam.le P)]
  simp

theorem aux_in_stopped_passage_lintegral_expExit {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) {lam : ℝ} (hlam : 0 ≤ lam) (P : Measure (DiffusionPath d))
    [IsFiniteMeasure P] :
    ∫⁻ p, ENNReal.ofReal (aux_in_stopped_passage_expExit U lam p) ∂P =
      ENNReal.ofReal (∫ p, aux_in_stopped_passage_expExit U lam p ∂P) :=
  (ofReal_integral_eq_lintegral_ofReal (aux_in_stopped_passage_expExit_integrable U hU hlam P)
    (Eventually.of_forall (aux_in_stopped_passage_expExit_nonneg U lam))).symm

/-! ### Grid hitting of a closed inner set -/

/-- The grid time `k / (m + 1)`. -/
noncomputable def aux_in_stopped_passage_grid (m k : ℕ) : ℝ≥0 := (k : ℝ≥0) / ((m : ℝ≥0) + 1)

theorem aux_in_stopped_passage_grid_coe (m k : ℕ) :
    ((aux_in_stopped_passage_grid m k : ℝ≥0) : ℝ) = (k : ℝ) / ((m : ℝ) + 1) := by
  simp [aux_in_stopped_passage_grid]

theorem aux_in_stopped_passage_grid_mono (m : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    aux_in_stopped_passage_grid m j ≤ aux_in_stopped_passage_grid m k := by
  rw [← NNReal.coe_le_coe, aux_in_stopped_passage_grid_coe, aux_in_stopped_passage_grid_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)

/-- The discounted weight of the first grid time at which the path is outside `F`. -/
noncomputable def aux_in_stopped_passage_gridHit {d : ℕ} (F : Set (SpatialCoordinates d))
    (lam : ℝ) (m : ℕ) (p : DiffusionPath d) : ℝ≥0∞ :=
  ⨆ k : ℕ, Set.indicator {q : DiffusionPath d | q (aux_in_stopped_passage_grid m k) ∉ F}
    (fun _ => ENNReal.ofReal (Real.exp (-lam * aux_in_stopped_passage_grid m k))) p

theorem aux_in_stopped_passage_gridHit_lsc {d : ℕ} (F : Set (SpatialCoordinates d))
    (hF : IsClosed F) (lam : ℝ) (m : ℕ) :
    LowerSemicontinuous (aux_in_stopped_passage_gridHit F lam m) := by
  refine lowerSemicontinuous_iSup fun k => ?_
  exact IsOpen.lowerSemicontinuous_indicator
    (hF.isOpen_compl.preimage (continuous_eval_const (aux_in_stopped_passage_grid m k)))
    (zero_le _)

theorem aux_in_stopped_passage_gridHit_le_one {d : ℕ} (F : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 ≤ lam) (m : ℕ) (p : DiffusionPath d) :
    aux_in_stopped_passage_gridHit F lam m p ≤ 1 := by
  refine iSup_le fun k => ?_
  refine (Set.indicator_le_self _ _ p).trans ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) (NNReal.coe_nonneg _)))

theorem aux_in_stopped_passage_gridHit_ne_top {d : ℕ} (F : Set (SpatialCoordinates d))
    {lam : ℝ} (hlam : 0 ≤ lam) (m : ℕ) (p : DiffusionPath d) :
    aux_in_stopped_passage_gridHit F lam m p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (aux_in_stopped_passage_gridHit_le_one F hlam m p)

/-- **Grid Markov inequality.**  If every start in the shell `U \ F` has discounted exit weight
at least `c`, the deterministic-time restart identity at the grid times gives
`c · E[gridHit] ≤ E[exp (-lam τ_U)]`. -/
theorem aux_in_stopped_passage_grid_markov {d : ℕ}
    (κ : SpatialCoordinates d → Measure (DiffusionPath d))
    (hrestart : ∀ (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(κ x)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(κ (p t)) ∂(κ x))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (F : Set (SpatialCoordinates d))
    (hF : IsClosed F) {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ≥0∞) (hc : c ≤ 1)
    (hbd : ∀ y ∈ U, y ∉ F →
      c ≤ ∫⁻ q, ENNReal.ofReal (aux_in_stopped_passage_expExit U lam q) ∂(κ y))
    (m : ℕ) (x : SpatialCoordinates d) :
    c * ∫⁻ p, aux_in_stopped_passage_gridHit F lam m p ∂(κ x) ≤
      ∫⁻ p, ENNReal.ofReal (aux_in_stopped_passage_expExit U lam p) ∂(κ x) := by
  classical
  let t : ℕ → ℝ≥0 := fun k => aux_in_stopped_passage_grid m k
  let w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (-lam * t k))
  let E : DiffusionPath d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (aux_in_stopped_passage_expExit U lam p)
  let A : ℕ → Set (DiffusionPath d) := fun k => {p | p (t k) ∉ F ∧ ∀ j < k, p (t j) ∈ F}
  have hw_anti : ∀ j k, j ≤ k → w k ≤ w j := by
    intro j k hjk
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonpos_left
      (NNReal.coe_le_coe.mpr (aux_in_stopped_passage_grid_mono m hjk)) (neg_nonpos.mpr hlam)
  have hEm : Measurable E :=
    ENNReal.measurable_ofReal.comp (aux_in_stopped_passage_expExit_measurable U hU lam)
  have hAF : ∀ k, MeasurableSet[ContinuousPath.canonicalFiltration
      (alpha := SpatialCoordinates d) (t k)] (A k) := by
    intro k
    have hset : A k = {p : DiffusionPath d | p (t k) ∈ Fᶜ} ∩
        ⋂ j ∈ Finset.range k, {p : DiffusionPath d | p (t j) ∈ F} := by
      ext p
      simp [A, Finset.mem_range]
    rw [hset]
    refine MeasurableSet.inter ?_ ?_
    · exact (ContinuousPath.measurable_coordinateProcess_canonicalFiltration (t k))
        hF.isOpen_compl.measurableSet
    · refine Finset.measurableSet_biInter _ fun j hj => ?_
      have hjk : t j ≤ t k :=
        aux_in_stopped_passage_grid_mono m (Finset.mem_range.mp hj).le
      exact (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)).mono hjk _
        ((ContinuousPath.measurable_coordinateProcess_canonicalFiltration (t j))
          hF.measurableSet)
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)).le (t k) _ (hAF k)
  -- Step 1: the supremum is dominated by the first-hitting decomposition.
  have hstep1 : ∀ p, aux_in_stopped_passage_gridHit F lam m p ≤
      ∑' k, (A k).indicator (fun _ => w k) p := by
    intro p
    refine iSup_le fun k => ?_
    by_cases hk : p (t k) ∉ F
    · rw [Set.indicator_of_mem (show p ∈ {q : DiffusionPath d |
        q (aux_in_stopped_passage_grid m k) ∉ F} from hk)]
      have hex : ∃ k, p (t k) ∉ F := ⟨k, hk⟩
      have hk0 : p (t (Nat.find hex)) ∉ F := Nat.find_spec hex
      have hk0le : Nat.find hex ≤ k := Nat.find_min' hex hk
      have hmemA : p ∈ A (Nat.find hex) :=
        ⟨hk0, fun j hj => by
          by_contra hjF
          exact Nat.find_min hex hj hjF⟩
      calc ENNReal.ofReal (Real.exp (-lam * aux_in_stopped_passage_grid m k))
          = w k := rfl
        _ ≤ w (Nat.find hex) := hw_anti _ _ hk0le
        _ = (A (Nat.find hex)).indicator (fun _ => w (Nat.find hex)) p :=
          (Set.indicator_of_mem hmemA (fun _ => w (Nat.find hex))).symm
        _ ≤ ∑' k, (A k).indicator (fun _ => w k) p := ENNReal.le_tsum (Nat.find hex)
    · rw [Set.indicator_of_notMem (show p ∉ {q : DiffusionPath d |
        q (aux_in_stopped_passage_grid m k) ∉ F} from hk)]
      exact zero_le _
  -- Step 2: integrate the decomposition.
  have hstep2 : ∫⁻ p, ∑' k, (A k).indicator (fun _ => w k) p ∂(κ x) =
      ∑' k, w k * κ x (A k) := by
    rw [lintegral_tsum fun k => (measurable_const.indicator (hAm k)).aemeasurable]
    congr 1
    funext k
    exact lintegral_indicator_const (hAm k) (w k)
  -- Step 3: the restart identity on each first-hitting event.
  have hstep3 : ∀ k, c * (w k * κ x (A k)) ≤ ∫⁻ p in A k, E p ∂(κ x) := by
    intro k
    let T : Set (DiffusionPath d) :=
      {p | (t k : ℝ≥0∞) < ContinuousPath.exitTime U p}
    have hTF : MeasurableSet[ContinuousPath.canonicalFiltration
        (alpha := SpatialCoordinates d) (t k)] T :=
      ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU (t k)
    have hTm : MeasurableSet T := ContinuousPath.measurableSet_lt_exitTime U hU (t k)
    rw [← lintegral_inter_add_diff E (A k) hTm, ← measure_inter_add_diff (A k) hTm,
      mul_add, mul_add]
    refine add_le_add ?_ ?_
    · have heq : ∫⁻ p in A k ∩ T, E p ∂(κ x) =
          w k * ∫⁻ p in A k ∩ T, E (ContinuousPath.shift (t k) p) ∂(κ x) := by
        have hEsm : Measurable (fun p : DiffusionPath d => E (ContinuousPath.shift (t k) p)) :=
          hEm.comp (ContinuousPath.continuous_shift_fixed (t k)).measurable
        rw [← lintegral_const_mul (w k) hEsm]
        refine setLIntegral_congr_fun ((hAm k).inter hTm) fun p hp => ?_
        change ENNReal.ofReal (aux_in_stopped_passage_expExit U lam p) =
          ENNReal.ofReal (Real.exp (-lam * t k)) *
            ENNReal.ofReal (aux_in_stopped_passage_expExit U lam
              (ContinuousPath.shift (t k) p))
        rw [aux_in_stopped_passage_expExit_shift U lam p (t k) hp.2,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [heq, hrestart x (t k) (A k ∩ T) ((hAF k).inter hTF) E hEm]
      calc c * (w k * κ x (A k ∩ T)) = w k * ∫⁻ _p in A k ∩ T, c ∂(κ x) := by
            rw [setLIntegral_const]
            ring
        _ ≤ w k * ∫⁻ p in A k ∩ T, ∫⁻ q, E q ∂(κ (p (t k))) ∂(κ x) := by
          refine mul_le_mul' le_rfl ?_
          refine setLIntegral_mono' ((hAm k).inter hTm) fun p hp => hbd _ ?_ hp.1.1
          exact ContinuousPath.mem_of_lt_exitTime U p (t k) hp.2
    · calc c * (w k * κ x (A k \ T)) ≤ 1 * (w k * κ x (A k \ T)) := by
            gcongr
        _ = ∫⁻ _p in A k \ T, w k ∂(κ x) := by rw [one_mul, setLIntegral_const]
        _ ≤ ∫⁻ p in A k \ T, E p ∂(κ x) := by
          refine setLIntegral_mono' ((hAm k).diff hTm) fun p hp => ?_
          have hle : ContinuousPath.exitTime U p ≤ (t k : ℝ≥0∞) := not_lt.mp hp.2
          exact ENNReal.ofReal_le_ofReal (aux_in_stopped_passage_expExit_ge U hlam p (t k) hle)
  -- Step 4: the first-hitting events are disjoint.
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.mpr fun p hpi hpj => hpi.1 (hpj.2 i h)
    · exact Set.disjoint_left.mpr fun p hpi hpj => hpj.1 (hpi.2 j h)
  have hstep4 : ∑' k, ∫⁻ p in A k, E p ∂(κ x) ≤ ∫⁻ p, E p ∂(κ x) := by
    rw [← lintegral_iUnion hAm hdisj]
    exact setLIntegral_le_lintegral _ _
  calc c * ∫⁻ p, aux_in_stopped_passage_gridHit F lam m p ∂(κ x)
      ≤ c * ∫⁻ p, ∑' k, (A k).indicator (fun _ => w k) p ∂(κ x) :=
        by gcongr with p; exact hstep1 p
    _ = c * ∑' k, w k * κ x (A k) := by rw [hstep2]
    _ = ∑' k, c * (w k * κ x (A k)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' k, ∫⁻ p in A k, E p ∂(κ x) := ENNReal.tsum_le_tsum hstep3
    _ ≤ ∫⁻ p, E p ∂(κ x) := hstep4

/-- Refining the grid, the grid hitting weight of a closed `F ⊆ U` eventually dominates the
discounted exit weight of `U`. -/
theorem aux_in_stopped_passage_gridHit_liminf {d : ℕ} (U F : Set (SpatialCoordinates d))
    (hF : IsClosed F) (hFU : F ⊆ U) {lam : ℝ} (hlam : 0 ≤ lam) (p : DiffusionPath d) :
    ENNReal.ofReal (aux_in_stopped_passage_expExit U lam p) ≤
      liminf (fun m => aux_in_stopped_passage_gridHit F lam m p) atTop := by
  unfold aux_in_stopped_passage_expExit
  split_ifs with htop
  · rw [ENNReal.ofReal_zero]
    exact zero_le _
  · set T := (ContinuousPath.exitTime U p).toReal with hTdef
    have hη : ∀ η : ℝ, 0 < η → ENNReal.ofReal (Real.exp (-lam * (T + η))) ≤
        liminf (fun m => aux_in_stopped_passage_gridHit F lam m p) atTop := by
      intro η hη
      have hlt : ContinuousPath.exitTime U p <
          ContinuousPath.exitTime U p + ENNReal.ofReal (η / 2) :=
        ENNReal.lt_add_right htop (ENNReal.ofReal_pos.mpr (half_pos hη)).ne'
      obtain ⟨s, ⟨t0, rfl, ht0U⟩, hs⟩ := sInf_lt_iff.mp hlt
      have ht0 : (t0 : ℝ) < T + η / 2 := by
        have h1 := ENNReal.toReal_strict_mono
          (ENNReal.add_ne_top.mpr ⟨htop, ENNReal.ofReal_ne_top⟩) hs
        rwa [ENNReal.coe_toReal, ENNReal.toReal_add htop ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (half_pos hη).le] at h1
      have ht0F : p t0 ∈ Fᶜ := fun h => ht0U (hFU h)
      obtain ⟨r, hr, hball⟩ :=
        Metric.isOpen_iff.mp (hF.isOpen_compl.preimage p.continuous) t0 ht0F
      have hev : ∀ᶠ m : ℕ in atTop, 1 / ((m : ℝ) + 1) < min r (η / 2) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (gt_mem_nhds (lt_min hr (half_pos hη)))
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hev] with m hm
      have hm1 : 1 / ((m : ℝ) + 1) < r := lt_of_lt_of_le hm (min_le_left _ _)
      have hm2 : 1 / ((m : ℝ) + 1) < η / 2 := lt_of_lt_of_le hm (min_le_right _ _)
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      set k := ⌈(t0 : ℝ) * ((m : ℝ) + 1)⌉₊ with hk
      have hk1 : (t0 : ℝ) ≤ aux_in_stopped_passage_grid m k := by
        rw [aux_in_stopped_passage_grid_coe, le_div_iff₀ hpos]
        exact Nat.le_ceil _
      have hk2 : (aux_in_stopped_passage_grid m k : ℝ) < t0 + 1 / ((m : ℝ) + 1) := by
        rw [aux_in_stopped_passage_grid_coe, div_lt_iff₀ hpos, add_mul,
          one_div_mul_cancel hpos.ne']
        exact Nat.ceil_lt_add_one (by positivity)
      have hmem : p (aux_in_stopped_passage_grid m k) ∉ F := by
        apply hball
        rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (by linarith)]
        linarith
      calc ENNReal.ofReal (Real.exp (-lam * (T + η)))
          ≤ ENNReal.ofReal (Real.exp (-lam * aux_in_stopped_passage_grid m k)) := by
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
            exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hlam)
        _ = Set.indicator {q : DiffusionPath d | q (aux_in_stopped_passage_grid m k) ∉ F}
              (fun _ => ENNReal.ofReal (Real.exp (-lam * aux_in_stopped_passage_grid m k)))
              p := (Set.indicator_of_mem hmem
                (fun _ => ENNReal.ofReal (Real.exp (-lam * aux_in_stopped_passage_grid m k)))).symm
        _ ≤ aux_in_stopped_passage_gridHit F lam m p :=
            le_iSup (fun k => Set.indicator
              {q : DiffusionPath d | q (aux_in_stopped_passage_grid m k) ∉ F}
              (fun _ => ENNReal.ofReal (Real.exp (-lam * aux_in_stopped_passage_grid m k))) p) k
    have hcont : Tendsto (fun η : ℝ => ENNReal.ofReal (Real.exp (-lam * (T + η))))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (Real.exp (-lam * T)))) := by
      have hc : Continuous (fun η : ℝ => ENNReal.ofReal (Real.exp (-lam * (T + η)))) :=
        ENNReal.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul (continuous_const.add continuous_id)))
      have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h0
    exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun η hη' => hη η hη')


/-! ### Identification of the limit at one environment -/

/-- Levy--Prokhorov path convergence gives weak convergence of path laws. -/
theorem aux_in_stopped_passage_tendsto_of_pathLP {d : ℕ}
    {μs : ℕ → ProbabilityMeasure (DiffusionPath d)} {μ : ProbabilityMeasure (DiffusionPath d)}
    (h : ∀ ε : ℝ, 0 < ε → ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → pathLevyProkhorovDist (μs j) μ < ε) :
    Tendsto μs atTop (𝓝 μ) := by
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  apply aux_limit_kernel_markov_passage_tendsto_of_dist
  intro ε hε
  obtain ⟨J0, hJ0⟩ := h ε hε
  filter_upwards [eventually_ge_atTop J0] with j hj
  exact hJ0 j hj

/-- **Lower half.**  For nonnegative data, lower semicontinuity of the killed occupation
functional and the portmanteau theorem bound the limiting occupation integral by the limit of
the cutoff occupation integrals. -/
theorem aux_in_stopped_passage_lower {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    {lam : ℝ} (hlam : 0 < lam) (g : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hg : ∀ y, 0 ≤ g y) {μs : ℕ → ProbabilityMeasure (DiffusionPath d)}
    {μ : ProbabilityMeasure (DiffusionPath d)} (hμ : Tendsto μs atTop (𝓝 μ)) {L : ℝ}
    (hL : Tendsto (fun j => ∫ p, aux_in_stopped_passage_occ U lam g p ∂(μs j : Measure _))
      atTop (𝓝 L)) :
    ∫ p, aux_in_stopped_passage_occ U lam g p ∂(μ : Measure _) ≤ L := by
  have hocc_nn : ∀ p, 0 ≤ aux_in_stopped_passage_occ U lam g p := fun p =>
    integral_nonneg fun t => Set.indicator_nonneg
      (fun _ _ => mul_nonneg (Real.exp_pos _).le (hg _)) t
  have hlin : ∀ ν : ProbabilityMeasure (DiffusionPath d),
      ENNReal.ofReal (∫ p, aux_in_stopped_passage_occ U lam g p ∂(ν : Measure _)) =
        ∫⁻ p, aux_in_stopped_passage_occPos U lam g p ∂(ν : Measure _) := by
    intro ν
    rw [ofReal_integral_eq_lintegral_ofReal
      (aux_in_stopped_passage_occ_integrable U hU hlam g (ν : Measure _))
      (Eventually.of_forall hocc_nn)]
    exact lintegral_congr fun p => aux_in_stopped_passage_ofReal_occ U hlam g hg p
  have hL0 : 0 ≤ L := ge_of_tendsto' hL fun j => integral_nonneg hocc_nn
  have hport := aux_in_stopped_passage_lsc_portmanteau hμ
    (aux_in_stopped_passage_occPos_lsc U hU lam g) (fun p => by
      rw [← aux_in_stopped_passage_ofReal_occ U hlam g hg p]
      exact ENNReal.ofReal_ne_top)
  have hlim : Tendsto (fun j => ∫⁻ p, aux_in_stopped_passage_occPos U lam g p
      ∂(μs j : Measure _)) atTop (𝓝 (ENNReal.ofReal L)) :=
    Tendsto.congr (fun j => hlin (μs j)) ((ENNReal.continuous_ofReal.tendsto L).comp hL)
  rw [hlim.liminf_eq, ← hlin μ] at hport
  exact (ENNReal.ofReal_le_ofReal_iff hL0).mp hport

/-- **Upper half for the constant datum.**  The deterministic-time restart identity at grid
times, the uniform smallness of the limit near the frontier, weak convergence along the
subsequence, and grid refinement give `R x ≤ E_x ∫_0^τ e^{-lam t} dt` under the limit law. -/
theorem aux_in_stopped_passage_upper_one {d : ℕ} (z : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) {lam : ℝ} (hlam : 0 < lam)
    (μN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (μ : ProbabilityMeasure (DiffusionPath d))
    (hrestart : ∀ (N : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(μN N x : Measure _)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(μN N (p t) : Measure _) ∂(μN N x : Measure _))
    (R : SpatialCoordinates d → ℝ) (hRc : ContinuousOn R (Metric.closedBall z ρ))
    (hR0 : ∀ y ∈ Metric.sphere z ρ, R y = 0)
    (hunif : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ y ∈ Metric.closedBall z ρ,
      |∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam
          (BoundedContinuousFunction.const _ 1) p ∂(μN N y : Measure _) - R y| < ε)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball z ρ) (hμ : Tendsto (fun j => μN (phi j) x) atTop (𝓝 μ)) :
    R x ≤ ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam
      (BoundedContinuousFunction.const _ 1) p ∂(μ : Measure _) := by
  have hQ : IsOpen (Metric.ball z ρ) := Metric.isOpen_ball
  have hE : ∀ ν : ProbabilityMeasure (DiffusionPath d),
      ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p ∂(ν : Measure _) =
        1 - lam * ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam
          (BoundedContinuousFunction.const _ 1) p ∂(ν : Measure _) := by
    intro ν
    rw [aux_in_stopped_passage_integral_occ_one _ hQ hlam (ν : Measure _)]
    field_simp
    ring
  have hxcl : x ∈ Metric.closedBall z ρ := Metric.ball_subset_closedBall hx
  have hconvx : Tendsto (fun N => ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam
      (BoundedContinuousFunction.const _ 1) p ∂(μN N x : Measure _)) atTop (𝓝 (R x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N0, hN0⟩ := hunif ε hε
    exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN x hxcl⟩
  have hEconv : Tendsto (fun N => ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p
      ∂(μN N x : Measure _)) atTop (𝓝 (1 - lam * R x)) := by
    simp_rw [hE]
    exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hconvx)
  have hb0 : 0 ≤ 1 - lam * R x := ge_of_tendsto' hEconv fun N =>
    integral_nonneg (aux_in_stopped_passage_expExit_nonneg _ lam)
  have hI0 : 0 ≤ ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p
      ∂(μ : Measure _) := integral_nonneg (aux_in_stopped_passage_expExit_nonneg _ lam)
  have hI1 : ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p
      ∂(μ : Measure _) ≤ 1 := by
    calc ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p ∂(μ : Measure _)
        ≤ ∫ _p, (1 : ℝ) ∂(μ : Measure (DiffusionPath d)) :=
          integral_mono (aux_in_stopped_passage_expExit_integrable _ hQ hlam.le _)
            (integrable_const 1) (aux_in_stopped_passage_expExit_le_one _ hlam.le)
      _ = 1 := by simp
  have hmain : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (1 - ε) * ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p
        ∂(μ : Measure _) ≤ 1 - lam * R x := by
    intro ε hε hε1
    have hη : 0 < ε / (2 * lam) := by positivity
    obtain ⟨δ, hδ, hδR⟩ := aux_in_stopped_passage_boundary_small z hρ R hRc hR0 hη
    obtain ⟨N0, hN0⟩ := hunif (ε / (2 * lam)) hη
    have hF : IsClosed (Metric.closedBall z (ρ - δ)) := Metric.isClosed_closedBall
    have hFU : Metric.closedBall z (ρ - δ) ⊆ Metric.ball z ρ := fun y hy =>
      Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith))
    have hc1 : ENNReal.ofReal (1 - ε) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hbd : ∀ N : ℕ, N0 ≤ N → ∀ y ∈ Metric.ball z ρ, y ∉ Metric.closedBall z (ρ - δ) →
        ENNReal.ofReal (1 - ε) ≤ ∫⁻ q, ENNReal.ofReal
          (aux_in_stopped_passage_expExit (Metric.ball z ρ) lam q) ∂(μN N y : Measure _) := by
      intro N hN y hyQ hyF
      have hyz1 : ρ - δ < dist y z :=
        lt_of_not_ge (fun h => hyF (Metric.mem_closedBall.mpr h))
      have hyz2 : dist y z ≤ ρ := (Metric.mem_ball.mp hyQ).le
      have h1 := abs_lt.mp (hδR y hyz1 hyz2)
      have h2 := abs_lt.mp (hN0 N hN y (Metric.mem_closedBall.mpr hyz2))
      rw [aux_in_stopped_passage_lintegral_expExit _ hQ hlam.le, hE]
      apply ENNReal.ofReal_le_ofReal
      have ha : ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam
          (BoundedContinuousFunction.const _ 1) p ∂(μN N y : Measure _) <
            2 * (ε / (2 * lam)) := by linarith [h1.2, h2.2]
      have hlam2 : lam * (2 * (ε / (2 * lam))) = ε := by field_simp
      nlinarith [mul_lt_mul_of_pos_left ha hlam]
    have hmarkov : ∀ N : ℕ, N0 ≤ N → ∀ m : ℕ,
        ENNReal.ofReal (1 - ε) * ∫⁻ p, aux_in_stopped_passage_gridHit
          (Metric.closedBall z (ρ - δ)) lam m p ∂(μN N x : Measure _) ≤
          ENNReal.ofReal (∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p
            ∂(μN N x : Measure _)) := by
      intro N hN m
      rw [← aux_in_stopped_passage_lintegral_expExit _ hQ hlam.le]
      exact aux_in_stopped_passage_grid_markov (fun y => (μN N y : Measure _)) (hrestart N)
        (Metric.ball z ρ) hQ (Metric.closedBall z (ρ - δ)) hF hlam.le (ENNReal.ofReal (1 - ε))
        hc1 (hbd N hN) m x
    have hlimit : ∀ m : ℕ, ENNReal.ofReal (1 - ε) * ∫⁻ p, aux_in_stopped_passage_gridHit
        (Metric.closedBall z (ρ - δ)) lam m p ∂(μ : Measure _) ≤
          ENNReal.ofReal (1 - lam * R x) := by
      intro m
      have hport := aux_in_stopped_passage_lsc_portmanteau hμ
        (aux_in_stopped_passage_gridHit_lsc _ hF lam m)
        (aux_in_stopped_passage_gridHit_ne_top _ hlam.le m)
      have hY : Tendsto (fun j => ENNReal.ofReal (∫ p, aux_in_stopped_passage_expExit
          (Metric.ball z ρ) lam p ∂(μN (phi j) x : Measure _))) atTop
          (𝓝 (ENNReal.ofReal (1 - lam * R x))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hEconv.comp hphi.tendsto_atTop)
      have hev : ∀ᶠ j in atTop, ((fun _ : ℕ => ENNReal.ofReal (1 - ε)) *
          fun j => ∫⁻ p, aux_in_stopped_passage_gridHit (Metric.closedBall z (ρ - δ)) lam m p
            ∂(μN (phi j) x : Measure _)) j ≤
          ENNReal.ofReal (∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p
            ∂(μN (phi j) x : Measure _)) := by
        filter_upwards [hphi.tendsto_atTop.eventually_ge_atTop N0] with j hj
        exact hmarkov (phi j) hj m
      calc ENNReal.ofReal (1 - ε) * ∫⁻ p, aux_in_stopped_passage_gridHit
            (Metric.closedBall z (ρ - δ)) lam m p ∂(μ : Measure _)
          ≤ ENNReal.ofReal (1 - ε) * liminf (fun j => ∫⁻ p, aux_in_stopped_passage_gridHit
            (Metric.closedBall z (ρ - δ)) lam m p ∂(μN (phi j) x : Measure _)) atTop :=
            mul_le_mul' le_rfl hport
        _ = liminf (fun _ : ℕ => ENNReal.ofReal (1 - ε)) atTop *
            liminf (fun j => ∫⁻ p, aux_in_stopped_passage_gridHit
              (Metric.closedBall z (ρ - δ)) lam m p ∂(μN (phi j) x : Measure _)) atTop := by
            rw [liminf_const]
        _ ≤ liminf ((fun _ : ℕ => ENNReal.ofReal (1 - ε)) *
            fun j => ∫⁻ p, aux_in_stopped_passage_gridHit
              (Metric.closedBall z (ρ - δ)) lam m p ∂(μN (phi j) x : Measure _)) atTop :=
            ENNReal.le_liminf_mul
        _ ≤ liminf (fun j => ENNReal.ofReal (∫ p, aux_in_stopped_passage_expExit
            (Metric.ball z ρ) lam p ∂(μN (phi j) x : Measure _))) atTop :=
            liminf_le_liminf hev
        _ = ENNReal.ofReal (1 - lam * R x) := hY.liminf_eq
    have hfatou : ∫⁻ p, ENNReal.ofReal (aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p)
        ∂(μ : Measure _) ≤ liminf (fun m => ∫⁻ p, aux_in_stopped_passage_gridHit
          (Metric.closedBall z (ρ - δ)) lam m p ∂(μ : Measure _)) atTop :=
      (lintegral_mono fun p => aux_in_stopped_passage_gridHit_liminf _ _ hF hFU hlam.le p).trans
        (lintegral_liminf_le fun m => (aux_in_stopped_passage_gridHit_lsc _ hF lam m).measurable)
    have hfinal : ENNReal.ofReal (1 - ε) * ∫⁻ p, ENNReal.ofReal
        (aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p) ∂(μ : Measure _) ≤
          ENNReal.ofReal (1 - lam * R x) := by
      calc ENNReal.ofReal (1 - ε) * ∫⁻ p, ENNReal.ofReal
            (aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p) ∂(μ : Measure _)
          ≤ ENNReal.ofReal (1 - ε) * liminf (fun m => ∫⁻ p, aux_in_stopped_passage_gridHit
            (Metric.closedBall z (ρ - δ)) lam m p ∂(μ : Measure _)) atTop :=
            mul_le_mul' le_rfl hfatou
        _ = liminf (fun _ : ℕ => ENNReal.ofReal (1 - ε)) atTop *
            liminf (fun m => ∫⁻ p, aux_in_stopped_passage_gridHit
              (Metric.closedBall z (ρ - δ)) lam m p ∂(μ : Measure _)) atTop := by
            rw [liminf_const]
        _ ≤ liminf ((fun _ : ℕ => ENNReal.ofReal (1 - ε)) *
            fun m => ∫⁻ p, aux_in_stopped_passage_gridHit
              (Metric.closedBall z (ρ - δ)) lam m p ∂(μ : Measure _)) atTop :=
            ENNReal.le_liminf_mul
        _ ≤ ENNReal.ofReal (1 - lam * R x) :=
            liminf_le_of_frequently_le' (Frequently.of_forall hlimit)
    rw [aux_in_stopped_passage_lintegral_expExit _ hQ hlam.le,
      ← ENNReal.ofReal_mul (by linarith)] at hfinal
    exact (ENNReal.ofReal_le_ofReal_iff hb0).mp hfinal
  have hIb : ∫ p, aux_in_stopped_passage_expExit (Metric.ball z ρ) lam p ∂(μ : Measure _) ≤
      1 - lam * R x := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases lt_or_ge ε 1 with h | h
    · have := hmain ε hε h
      nlinarith
    · linarith
  rw [aux_in_stopped_passage_integral_occ_one _ hQ hlam (μ : Measure _), le_div_iff₀ hlam]
  linarith

/-- Integrated linearity of the occupation functional. -/
theorem aux_in_stopped_passage_integral_occ_lin {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) {lam : ℝ} (hlam : 0 < lam)
    (g f₁ f₂ : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (a b : ℝ)
    (h : ∀ y, g y = a * f₁ y + b * f₂ y) (P : Measure (DiffusionPath d)) [IsFiniteMeasure P] :
    ∫ p, aux_in_stopped_passage_occ U lam g p ∂P =
      a * ∫ p, aux_in_stopped_passage_occ U lam f₁ p ∂P +
        b * ∫ p, aux_in_stopped_passage_occ U lam f₂ p ∂P := by
  simp_rw [aux_in_stopped_passage_occ_lin U hlam g f₁ f₂ a b h]
  rw [integral_add ((aux_in_stopped_passage_occ_integrable U hU hlam f₁ P).const_mul a)
      ((aux_in_stopped_passage_occ_integrable U hU hlam f₂ P).const_mul b),
    integral_const_mul, integral_const_mul]

/-- **Identification at one environment.**  The lower and upper halves, combined through the
linearity of the occupation functional, identify the limit of the full cutoff sequence. -/
theorem aux_in_stopped_passage_identify {d : ℕ} (z : SpatialCoordinates d) {ρ : ℝ}
    (hρ : 0 < ρ) {lam : ℝ} (hlam : 0 < lam)
    (μN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (μ : ProbabilityMeasure (DiffusionPath d))
    (hrestart : ∀ (N : ℕ) (x : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(μN N x : Measure _)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(μN N (p t) : Measure _) ∂(μN N x : Measure _))
    (Rl : BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRc : ContinuousOn (Rl (BoundedContinuousFunction.const _ 1)) (Metric.closedBall z ρ))
    (hR0 : ∀ y ∈ Metric.sphere z ρ, Rl (BoundedContinuousFunction.const _ 1) y = 0)
    (hunif : ∀ g : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ y ∈ Metric.closedBall z ρ,
        |∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam g p ∂(μN N y : Measure _) -
          Rl g y| < ε)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball z ρ) (hμ : Tendsto (fun j => μN (phi j) x) atTop (𝓝 μ))
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Tendsto (fun N => ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam f p
      ∂(μN N x : Measure _)) atTop
      (𝓝 (∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam f p ∂(μ : Measure _))) := by
  have hQ : IsOpen (Metric.ball z ρ) := Metric.isOpen_ball
  have hxcl : x ∈ Metric.closedBall z ρ := Metric.ball_subset_closedBall hx
  have hL : ∀ g : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      Tendsto (fun N => ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam g p
        ∂(μN N x : Measure _)) atTop (𝓝 (Rl g x)) := by
    intro g
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N0, hN0⟩ := hunif g ε hε
    exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN x hxcl⟩
  have hsub : ∀ g : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      Tendsto (fun j => ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam g p
        ∂(μN (phi j) x : Measure _)) atTop (𝓝 (Rl g x)) := fun g =>
    (hL g).comp hphi.tendsto_atTop
  set one : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
    BoundedContinuousFunction.const _ 1 with hone
  set c : ℝ := ‖f‖ with hc
  set g₁ : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
    f + BoundedContinuousFunction.const _ c with hg₁
  set g₂ : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
    BoundedContinuousFunction.const _ c - f with hg₂
  have hfb : ∀ y, |f y| ≤ c := fun y => by
    rw [← Real.norm_eq_abs]
    exact f.norm_coe_le_norm y
  have hg₁nn : ∀ y, 0 ≤ g₁ y := fun y => by
    simp only [hg₁, BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply]
    linarith [(abs_le.mp (hfb y)).1]
  have hg₂nn : ∀ y, 0 ≤ g₂ y := fun y => by
    simp only [hg₂, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply]
    linarith [(abs_le.mp (hfb y)).2]
  have honenn : ∀ y, 0 ≤ one y := fun y => by
    simp only [hone, BoundedContinuousFunction.const_apply]
    exact zero_le_one
  have hg₁lin : ∀ y, g₁ y = 1 * f y + c * one y := fun y => by
    simp only [hg₁, hone, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply]
    ring
  have hg₂lin : ∀ y, g₂ y = c * one y + (-1) * f y := fun y => by
    simp only [hg₂, hone, BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.const_apply]
    ring
  -- limits of the combined data
  have hRg₁ : Rl g₁ x = 1 * Rl f x + c * Rl one x := by
    refine tendsto_nhds_unique (hL g₁) ?_
    have h := ((hL f).const_mul 1).add ((hL one).const_mul c)
    refine h.congr fun N => ?_
    exact (aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₁ f one 1 c hg₁lin _).symm
  have hRg₂ : Rl g₂ x = c * Rl one x + (-1) * Rl f x := by
    refine tendsto_nhds_unique (hL g₂) ?_
    have h := ((hL one).const_mul c).add ((hL f).const_mul (-1))
    refine h.congr fun N => ?_
    exact (aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₂ one f c (-1) hg₂lin _).symm
  -- the two halves
  have hA₁ := aux_in_stopped_passage_lower _ hQ hlam g₁ hg₁nn hμ (hsub g₁)
  have hA₂ := aux_in_stopped_passage_lower _ hQ hlam g₂ hg₂nn hμ (hsub g₂)
  have hB := aux_in_stopped_passage_upper_one z hρ hlam μN μ hrestart (Rl one) hRc hR0
    (hunif one) phi hphi x hx hμ
  rw [aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₁ f one 1 c hg₁lin, hRg₁] at hA₁
  rw [aux_in_stopped_passage_integral_occ_lin _ hQ hlam g₂ one f c (-1) hg₂lin, hRg₂] at hA₂
  have hid : Rl f x = ∫ p, aux_in_stopped_passage_occ (Metric.ball z ρ) lam f p
      ∂(μ : Measure _) := by
    have hc0 : 0 ≤ c := norm_nonneg f
    nlinarith
  rw [← hid]
  exact hL f




theorem in_stopped_passage
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hin : in_crossing M H PN KN)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → ∀ x ∈ B,
          pathLevyProkhorovDist
            (jointPathProbabilityMeasure (KN (phi j)) (hKN (phi j)) omega x)
            (jointPathProbabilityMeasure K hK omega x) < eps)
    (hcontinuous : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x => jointPathProbabilityMeasure K hK omega x))
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (Rlim : ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hident : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
              (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
          ∀ x ∈ closure (centeredCube (Qc n) (Qr n) (hQr n) : Set _),
            |RN n N omega lam f x - Rlim n omega lam f x| < eps)
    (hboundary : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (Rlim n omega lam f)
            (closure (centeredCube (Qc n) (Qr n) (hQr n) : Set _)) ∧
          (∀ x ∈ frontier (centeredCube (Qc n) (Qr n) (hQr n) : Set _),
            Rlim n omega lam f x = 0) ∧
          ∀ N : ℕ, ContinuousOn (RN n N omega lam f)
            (closure (centeredCube (Qc n) (Qr n) (hQr n) : Set _)) ∧
            (∀ x ∈ frontier (centeredCube (Qc n) (Qr n) (hQr n) : Set _),
              RN n N omega lam f x = 0)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          Tendsto (fun N ↦ ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                  (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
            atTop
            (nhds (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                  Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                    ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                    (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                ∂(K (omega, x)))) := by
  have hrest := lem_tightness_deterministic_restart hd M H PN KN hKN hin
  filter_upwards [hrest, hconv, hres, hboundary] with omega hrω hcω hresω hbω
  intro n lam hlam f x hx
  have hρ : 0 < Qr n / 2 := half_pos (hQr n)
  have hQ : (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) =
      Metric.ball (Qc n) (Qr n / 2) := rfl
  have hcl : closure (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) =
      Metric.closedBall (Qc n) (Qr n / 2) := by
    rw [hQ, closure_ball _ hρ.ne']
  have hfr : frontier (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) =
      Metric.sphere (Qc n) (Qr n / 2) := by
    rw [hQ, frontier_ball _ hρ.ne']
  let μN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d) :=
    fun N y => jointPathProbabilityMeasure (KN N) (hKN N) omega y
  have hrestart : ∀ (N : ℕ) (y : SpatialCoordinates d) (t : ℝ≥0) (A : Set (DiffusionPath d)),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) t] A →
        ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
          (∫⁻ p in A, F (ContinuousPath.shift t p) ∂(μN N y : Measure _)) =
            ∫⁻ p in A, ∫⁻ q, F q ∂(μN N (p t) : Measure _) ∂(μN N y : Measure _) :=
    fun N y t A hA F hF => hrω N y t A hA F hF
  have hunif : ∀ g : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ y ∈ Metric.closedBall (Qc n) (Qr n / 2),
          |∫ p, aux_in_stopped_passage_occ (Metric.ball (Qc n) (Qr n / 2)) lam g p
              ∂(μN N y : Measure _) - Rlim n omega lam g y| < ε := by
    intro g ε hε
    obtain ⟨N0, hN0⟩ := hresω n lam hlam g ε hε
    refine ⟨N0, fun N hN y hy => ?_⟩
    have h := hN0 N hN y (by rw [hcl]; exact hy)
    rw [hident] at h
    exact h
  have hRc : ContinuousOn (Rlim n omega lam (BoundedContinuousFunction.const _ 1))
      (Metric.closedBall (Qc n) (Qr n / 2)) := by
    rw [← hcl]
    exact (hbω n lam hlam (BoundedContinuousFunction.const _ 1)).1
  have hR0 : ∀ y ∈ Metric.sphere (Qc n) (Qr n / 2),
      Rlim n omega lam (BoundedContinuousFunction.const _ 1) y = 0 := by
    intro y hy
    rw [← hfr] at hy
    exact (hbω n lam hlam (BoundedContinuousFunction.const _ 1)).2.1 y hy
  have hμ : Tendsto (fun j => μN (phi j) x) atTop
      (𝓝 (jointPathProbabilityMeasure K hK omega x)) := by
    refine aux_in_stopped_passage_tendsto_of_pathLP fun ε hε => ?_
    obtain ⟨J0, hJ0⟩ := hcω {x} isCompact_singleton ε hε
    exact ⟨J0, fun j hj => hJ0 j hj x rfl⟩
  exact aux_in_stopped_passage_identify (Qc n) hρ hlam μN
    (jointPathProbabilityMeasure K hK omega x) hrestart (Rlim n omega lam) hRc hR0 hunif
    phi hphi x hx hμ f

end Paper
