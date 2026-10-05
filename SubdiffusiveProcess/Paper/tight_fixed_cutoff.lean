module

public import SubdiffusiveProcess.Paper.tight_subharmonic
public import SubdiffusiveProcess.Paper.tight_static_estimates
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_cutoff_fdd_start_continuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import MarkovProcess.Continuity.PathModulus
public import MarkovProcess.Trajectory.StartingPointContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeLaplaceUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FellerBridge
public import SubdiffusiveProcess.Model.LifetimeProcess
public import MarkovProcess.Path.RandomShiftMeasurability
public import MarkovProcess.Path.ExitTimeShift
public import MarkovProcess.Lifetime.ExitTimeStopping
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
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
public import SubdiffusiveProcess.Probability.PathLawMetricSeparation
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import MarkovProcess.Trajectory.CylinderAlgebra
public import MarkovProcess.Trajectory.WeakContinuity
public import MarkovProcess.Continuity.PathTightness
public import MarkovProcess.Path.ClosedSetDetection
public import Mathlib.MeasureTheory.Measure.Tight

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess Classical
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators ZeroAtInfty
open scoped BoundedContinuousFunction
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_feller
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hin : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      (PN N omega).IsFellerKernelSemigroup := by
  rcases hin with ⟨hres, hcons, hfdd⟩
  filter_upwards [hres, hfdd] with omega hres hfdd
  intro N
  obtain ⟨D, hDdense, hDweak, hDlap⟩ := hres N
  let Q : SubMarkovKernelSemigroup (SpatialCoordinates d) :=
    D.fellerKernelSemigroup hDdense
  have hQfeller : Q.IsFellerKernelSemigroup :=
    D.isFellerKernelSemigroup_fellerKernelSemigroup hDdense
  have hmap : ∀ (t : ℝ≥0) (x : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (KN N (omega, x)) =
        (PN N omega) t x := by
    intro t x
    simpa only [Kernel.map_apply] using!
      (SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
        (PN N omega) (KN N (omega, x)) x t
        (by
          have h := hfdd N ({t} : Finset ℝ≥0) x
          rw [Kernel.map_apply (KN N)
            (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0))] at h
          exact h))
  have hKfinite : ∀ x, IsFiniteMeasure (KN N (omega, x)) := by
    intro x
    have hmass : (KN N (omega, x)) Set.univ = 1 := by
      calc
        (KN N (omega, x)) Set.univ =
            Measure.map (ContinuousPath.eval (0 : ℝ≥0))
              (KN N (omega, x)) Set.univ := by
                rw [Measure.map_apply (ContinuousPath.continuous_eval 0).measurable
                  MeasurableSet.univ, Set.preimage_univ]
        _ = (PN N omega) 0 x Set.univ := by rw [hmap 0 x]
        _ = 1 := by
          let : IsMarkovKernel ((PN N omega) 0) :=
            (hcons N omega).isMarkovKernel 0
          exact IsProbabilityMeasure.measure_univ
    exact ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hEq : PN N omega = Q := by
    apply aux_in_cutoff_fdd_start_continuity_kernel_eq_of_laplace
      (PN N omega) Q hQfeller (fun x => KN N (omega, x)) hKfinite hmap
    intro mu g x
    calc
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral ((PN N omega) (Real.toNNReal t)) g x) =
          D.solution mu g x := (hDlap mu g x).symm
      _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (Q (Real.toNNReal t)) g x := by
            simpa only [Q] using D.solution_eq_laplace hDdense mu g x
  rw [hEq]
  exact hQfeller

/-- **Step 1 of the soft route.**  Uniform one-time smallness of the displacement, as the
time tends to zero, over a compact set of starting points.  This is what the strong
continuity of the Feller semigroup buys, and it replaces the quantitative small-time
estimate that `kolmogorov_moments` cannot supply below the cutoff scale. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_one_time
    {alpha : Type*} [MetricSpace alpha] [ProperSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [SecondCountableTopology alpha]
    (P : SubMarkovKernelSemigroup alpha) (hF : P.IsFellerKernelSemigroup)
    (K1 : Set alpha) (hK1 : IsCompact K1) (rho : ℝ) (hrho : 0 < rho)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ h : ℝ≥0, 0 < h ∧ ∀ y ∈ K1, ∀ s : ℝ≥0, s ≤ h →
      (P s y) {z | rho ≤ dist z y} ≤ ENNReal.ofReal eps := by
  classical
  set hC0 := hF.mapsC0 with hC0def
  -- a finite `rho/4`-net of `K1`
  have hcover : K1 ⊆ ⋃ y ∈ K1, Metric.ball y (rho / 4) := by
    intro y hy
    exact Set.mem_biUnion hy (Metric.mem_ball_self (by linarith))
  obtain ⟨F, hFsub, hFfin, hFcov⟩ :=
    hK1.elim_finite_subcover_image (fun y _ => Metric.isOpen_ball) hcover
  have : Fintype F := hFfin.fintype
  -- a `C₀` bump at each net point
  have hbump : ∀ c : alpha, ∃ f : C₀(alpha, ℝ),
      (∀ z, z ∈ Metric.closedBall c (rho / 4) → f z = 1) ∧
      (∀ z, rho / 2 ≤ dist z c → f z = 0) ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ 1) := by
    intro c
    obtain ⟨g, hg1, hg0, hgsupp, hgmem⟩ :=
      exists_continuous_one_zero_of_isCompact
        (isCompact_closedBall c (rho / 4))
        (Metric.isOpen_ball (x := c) (ε := rho / 2)).isClosed_compl
        (by
          rw [Set.disjoint_compl_right_iff_subset]
          intro z hz
          exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
    refine ⟨PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap ⟨g, hgsupp⟩, ?_, ?_, ?_⟩
    · intro z hz
      rw [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]
      exact hg1 hz
    · intro z hz
      rw [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]
      exact hg0 (by simpa [Metric.mem_ball, not_lt] using hz)
    · intro z
      rw [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]
      exact ⟨(hgmem z).1, (hgmem z).2⟩
  choose bump hbump1 hbump0 hbumpmem using hbump
  -- strong continuity gives a common time scale
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝 0, ∀ c ∈ hFfin.toFinset,
      ‖bump c - P.c0Operator hC0 s (bump c)‖ < eps := by
    refine (Filter.eventually_all_finset _).2 fun c _ => ?_
    have hcont : Continuous fun s : ℝ≥0 => ‖bump c - P.c0Operator hC0 s (bump c)‖ :=
      (continuous_const.sub (hF.hasContinuousC0Orbits (bump c))).norm
    have htend : Filter.Tendsto (fun s : ℝ≥0 => ‖bump c - P.c0Operator hC0 s (bump c)‖)
        (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      simpa [P.c0Operator_zero hC0] using this
    exact htend.eventually_lt_const heps
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨del, hdel, hdelspec⟩ := hev
  refine ⟨Real.toNNReal (del / 2), Real.toNNReal_pos.mpr (by linarith), ?_⟩
  intro y hy s hs
  obtain ⟨c, hcF, hcy⟩ : ∃ c ∈ F, y ∈ Metric.ball c (rho / 4) := by
    simpa only [Set.mem_iUnion, exists_prop] using hFcov hy
  have hsdel : dist s (0 : ℝ≥0) < del := by
    have h1 : (s : ℝ) ≤ del / 2 := by
      have := (NNReal.coe_le_coe (r₁ := s) (r₂ := Real.toNNReal (del / 2))).2 hs
      rwa [Real.coe_toNNReal (del / 2) (by linarith)] at this
    have hd : dist s (0 : ℝ≥0) = (s : ℝ) := by
      simp [NNReal.dist_eq]
    rw [hd]
    linarith
  have hnorm : ‖bump c - P.c0Operator hC0 s (bump c)‖ < eps :=
    hdelspec hsdel c (hFfin.mem_toFinset.mpr hcF)
  -- the measure estimate
  let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
  let : IsFiniteMeasure (P s y) := IsFiniteKernel.isFiniteMeasure y
  set S : Set alpha := {z | rho ≤ dist z y} with hS
  have hSmeas : MeasurableSet S :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  have hzero : ∀ z ∈ S, bump c z = 0 := by
    intro z hz
    refine hbump0 c z ?_
    have h1 : rho ≤ dist z y := hz
    have h2 : dist y c < rho / 4 := Metric.mem_ball.mp hcy
    have h3 : dist z y ≤ dist z c + dist c y := dist_triangle _ _ _
    rw [dist_comm c y] at h3
    linarith
  have hone : bump c y = 1 :=
    hbump1 c y (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hcy)))
  have hint : ∫ z, bump c z ∂(P s y) ≤ (P s y).real Sᶜ := by
    have hle : ∀ z, bump c z ≤ Set.indicator Sᶜ (fun _ => (1 : ℝ)) z := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_notMem (by simpa using hz), hzero z hz]
      · rw [Set.indicator_of_mem (by simpa using hz)]
        exact (hbumpmem c z).2
    have hintbump : Integrable (fun z => bump c z) (P s y) :=
      ((bump c).toBCF).integrable (P s y)
    have hintind : Integrable (Set.indicator Sᶜ (fun _ => (1 : ℝ))) (P s y) :=
      (integrable_indicator_iff hSmeas.compl).2 ((integrable_const (1 : ℝ)).integrableOn)
    calc ∫ z, bump c z ∂(P s y) ≤ ∫ z, Set.indicator Sᶜ (fun _ => (1 : ℝ)) z ∂(P s y) :=
          integral_mono hintbump hintind hle
      _ = (P s y).real Sᶜ := by
          rw [integral_indicator_const (1 : ℝ) hSmeas.compl]
          simp [Measure.real]
  have hsum : (P s y).real S + (P s y).real Sᶜ = (P s y).real Set.univ :=
    measureReal_add_measureReal_compl hSmeas
  have huniv : (P s y).real Set.univ ≤ 1 := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using (P.isSubMarkovKernel s y))
  have hop : ∫ z, bump c z ∂(P s y) = P.c0Operator hC0 s (bump c) y := rfl
  have hdiff : bump c y - P.c0Operator hC0 s (bump c) y ≤ eps := by
    refine le_trans ?_ hnorm.le
    have hb := (bump c - P.c0Operator hC0 s (bump c)).toBCF.norm_coe_le_norm y
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hb
    have hval : (bump c - P.c0Operator hC0 s (bump c)).toBCF y
        = bump c y - P.c0Operator hC0 s (bump c) y := rfl
    rw [hval, Real.norm_eq_abs] at hb
    exact le_trans (le_abs_self _) hb
  have hfinal : (P s y).real S ≤ eps := by
    rw [hone] at hdiff
    rw [hop] at hint
    linarith [hsum, huniv, hint, hdiff]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P s y) S)]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- The elementary half of Steps 1 and 3: a `[0,1]`-valued function vanishing on `S` bounds
the mass of `S` by the defect of its integral. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_measure_le_of_bump
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha) [IsFiniteMeasure mu]
    (f : alpha → ℝ) (hfint : Integrable f mu) (_hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (S : Set alpha) (hS : MeasurableSet S) (hfS : ∀ z ∈ S, f z = 0) :
    mu.real S ≤ mu.real Set.univ - ∫ z, f z ∂mu := by
  have hle : ∀ z, f z ≤ Set.indicator Sᶜ (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_notMem (by simpa using hz), hfS z hz]
    · rw [Set.indicator_of_mem (by simpa using hz)]
      exact hf1 z
  have hintind : Integrable (Set.indicator Sᶜ (fun _ => (1 : ℝ))) mu :=
    (integrable_indicator_iff hS.compl).2 ((integrable_const (1 : ℝ)).integrableOn)
  have hint : ∫ z, f z ∂mu ≤ mu.real Sᶜ := by
    calc ∫ z, f z ∂mu ≤ ∫ z, Set.indicator Sᶜ (fun _ => (1 : ℝ)) z ∂mu :=
          integral_mono hfint hintind hle
      _ = mu.real Sᶜ := by
          rw [integral_indicator_const (1 : ℝ) hS.compl]
          simp [Measure.real]
  have hsum : mu.real S + mu.real Sᶜ = mu.real Set.univ :=
    measureReal_add_measureReal_compl hS
  linarith

/-- **Step 3 of the soft route.**  Uniform escape bound: on a compact set of starting points
and a compact time interval, the mass outside a large ball is uniformly small.  Only
conservativity and the Feller property are used, through Dini's theorem; no quantitative
estimate enters. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_escape
    {alpha : Type*} [MetricSpace alpha] [ProperSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [SecondCountableTopology alpha]
    (P : SubMarkovKernelSemigroup alpha) (hF : P.IsFellerKernelSemigroup)
    (hC : P.IsConservative)
    (K1 : Set alpha) (hK1 : IsCompact K1) (x0 : alpha) (hbound : ℝ≥0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ K1, ∀ s : ℝ≥0, s ≤ hbound →
      (P s y) {z | R ≤ dist z x0} ≤ ENNReal.ofReal eps := by
  classical
  set hC0 := hF.mapsC0 with hC0def
  -- an increasing exhaustion of `C₀` bumps
  have hbumpex : ∀ n : ℕ, ∃ g : C₀(alpha, ℝ),
      (∀ z, dist z x0 ≤ (n : ℝ) → g z = 1) ∧
      (∀ z, (n : ℝ) + 1 ≤ dist z x0 → g z = 0) ∧
      (∀ z, 0 ≤ g z ∧ g z ≤ 1) := by
    intro n
    obtain ⟨g, hg1, hg0, hgsupp, hgmem⟩ :=
      exists_continuous_one_zero_of_isCompact
        (isCompact_closedBall x0 (n : ℝ))
        (Metric.isOpen_ball (x := x0) (ε := (n : ℝ) + 1)).isClosed_compl
        (by
          rw [Set.disjoint_compl_right_iff_subset]
          intro z hz
          exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
    refine ⟨PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap ⟨g, hgsupp⟩, ?_, ?_, ?_⟩
    · intro z hz
      rw [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]
      exact hg1 (Metric.mem_closedBall.mpr hz)
    · intro z hz
      rw [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]
      exact hg0 (by simpa [Metric.mem_ball, not_lt] using hz)
    · intro z
      rw [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]
      exact ⟨(hgmem z).1, (hgmem z).2⟩
  choose g hg1 hg0 hgmem using hbumpex
  have hgmono : ∀ n : ℕ, ∀ z, g n z ≤ g (n + 1) z := by
    intro n z
    by_cases hz : dist z x0 ≤ ((n : ℝ) + 1)
    · rw [hg1 (n + 1) z (by push_cast; linarith)]
      exact (hgmem n z).2
    · rw [hg0 n z (by push Not at hz; linarith)]
      exact (hgmem (n + 1) z).1
  -- the orbit functions
  set F : ℕ → alpha × ℝ≥0 → ℝ :=
    fun n p => P.c0Operator hC0 p.2 (g n) p.1 with hFdef
  have hFcont : ∀ n : ℕ, Continuous (F n) := by
    intro n
    have h1 : Continuous fun s : ℝ≥0 => (P.c0Operator hC0 s (g n)).toBCF :=
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
        (hF.hasContinuousC0Orbits (g n))
    exact ContinuousEval.continuous_eval.comp
      ((h1.comp continuous_snd).prodMk continuous_fst)
  have hmemfin : ∀ (s : ℝ≥0) (y : alpha), IsFiniteMeasure (P s y) := by
    intro s y
    let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
    exact IsFiniteKernel.isFiniteMeasure y
  have hFint : ∀ (n : ℕ) (p : alpha × ℝ≥0),
      F n p = ∫ z, g n z ∂(P p.2 p.1) := fun n p => rfl
  have hFmono : ∀ p : alpha × ℝ≥0, Monotone fun n : ℕ => F n p := by
    intro p
    refine monotone_nat_of_le_succ fun n => ?_
    let := hmemfin p.2 p.1
    rw [hFint, hFint]
    exact integral_mono ((g n).toBCF.integrable _) ((g (n + 1)).toBCF.integrable _)
      (fun z => hgmono n z)
  have hFtend : ∀ p : alpha × ℝ≥0, Filter.Tendsto (fun n : ℕ => F n p) Filter.atTop (𝓝 1) := by
    intro p
    let := hmemfin p.2 p.1
    have hmass : (P p.2 p.1) Set.univ = 1 := hC p.2 p.1
    have : IsProbabilityMeasure (P p.2 p.1) := ⟨hmass⟩
    have hdom := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P p.2 p.1) (F := fun n : ℕ => fun z => g n z) (f := fun _ : alpha => (1 : ℝ))
      (bound := fun _ => (1 : ℝ))
      (fun n => ((g n).toBCF.continuous).aestronglyMeasurable)
      (integrable_const 1)
      (fun n => Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgmem n z).1]
        exact (hgmem n z).2)
      (Filter.Eventually.of_forall fun z => by
        obtain ⟨n0, hn0⟩ := exists_nat_ge (dist z x0)
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.eventually_ge_atTop n0] with n hn
        exact (hg1 n z (le_trans hn0 (by exact_mod_cast hn))).symm)
    simpa [hFint, integral_const] using hdom
  -- Dini on the compact product
  have hcompact : IsCompact (K1 ×ˢ Set.Icc (0 : ℝ≥0) hbound) := hK1.prod isCompact_Icc
  have hdini := Monotone.tendstoUniformlyOn_of_forall_tendsto (F := F)
    (f := fun _ : alpha × ℝ≥0 => (1 : ℝ)) hcompact
    (fun n => (hFcont n).continuousOn)
    (fun p _ => hFmono p) continuousOn_const (fun p _ => hFtend p)
  rw [Metric.tendstoUniformlyOn_iff] at hdini
  obtain ⟨n, hn⟩ := (hdini eps heps).exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  intro y hy s hs
  let := hmemfin s y
  set S : Set alpha := {z | (n : ℝ) + 1 ≤ dist z x0} with hSdef
  have hSmeas : MeasurableSet S :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  have hkey := aux_tight_fixed_cutoff_soft_measure_le_of_bump (P s y) (fun z => g n z)
    ((g n).toBCF.integrable _) (fun z => (hgmem n z).1) (fun z => (hgmem n z).2)
    S hSmeas (fun z hz => hg0 n z hz)
  have hmass : (P s y).real Set.univ = 1 := by
    rw [Measure.real, hC s y]
    simp
  have hclose : dist (1 : ℝ) (F n (y, s)) < eps := hn (y, s) ⟨hy, ⟨zero_le, hs⟩⟩
  have hlt : 1 - ∫ z, g n z ∂(P s y) < eps := by
    have : F n (y, s) = ∫ z, g n z ∂(P s y) := rfl
    rw [this] at hclose
    have := abs_lt.mp (by rwa [Real.dist_eq] at hclose)
    linarith [this.2]
  have hfinal : (P s y).real S ≤ eps := by
    rw [hmass] at hkey
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P s y) S)]
  exact ENNReal.ofReal_le_ofReal hfinal



-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_sm_transport {d : ℕ}
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
  have hTmeas : Measurable T := by simpa only using! hT.measurable'
  have hS : MeasurableSet (B ∩ {w : Path d | T w < w.lifetime}) :=
    (hT.measurableSpace_le _ hB).inter
      (measurableSet_lt hTmeas LifetimePath.measurable_lifetime)
  have h := hSM.2.2 x T hT B hB g hg
  rw [← hL x, Measure.restrict_map hemb.measurable hS, hemb.lintegral_map,
    hemb.lintegral_map] at h
  simp only [SubdiffusiveProcess.Model.LifetimeProcess.shift_ofContinuousPath,
    SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath] at h
  rw [h]
  refine setLIntegral_congr_fun_ae (hemb.measurable hS) (ae_of_all _ fun p _ => ?_)
  rw [← hL, hemb.lintegral_map]

/-- The Section 9 position at a fixed time is measurable on lifetime paths. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_measurable_position {d : ℕ} (t : ℝ≥0) :
    Measurable (position (d := d) t) := by
  unfold position
  exact (measurable_id.sumElim measurable_const).comp (LifetimePath.measurable_coordinate t)

/-- **The stopped one-time bound (Step 2 of the soft route, exact form).**  Let `τ` be the exit
time from an open set `U` containing the starting point.  If, from every point `z` of the
frontier of `U` and at every time `s ≤ h`, the pair `(z, path s)` lies in the open set `O` with
probability at most `c`, then the pair (exit position, position at time `h`) lies in `O` on
`{τ ≤ h}` with probability at most `c` times that of `{τ ≤ h}`.  The remaining time `h - τ` is
random: it is discretised on the grid `k h / (n + 1)` through events of the stopped
σ-algebra, the strong Markov identity of `hSM` is applied on each slice with a fixed
functional, and the grid is refined using path continuity and the openness of `O`. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_stopped_bound {d : ℕ}
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (hSM : StrongMarkov L)
    (h0 : ∀ z, ∀ᵐ q ∂K z, q 0 = z)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (x : SpatialCoordinates d) (hx : x ∈ U) (h : ℝ≥0)
    (O : Set (SpatialCoordinates d × SpatialCoordinates d)) (hO : IsOpen O) (c : ℝ≥0∞)
    (hc : ∀ z ∈ frontier U, ∀ s : ℝ≥0, s ≤ h → K z {q | (z, q s) ∈ O} ≤ c) :
    K x {p | ContinuousPath.exitTime U p ≤ h ∧
        (p (ContinuousPath.exitTime U p).toNNReal, p h) ∈ O} ≤
      c * K x {p | ContinuousPath.exitTime U p ≤ h} := by
  classical
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  set f := LifetimePath.ofContinuousPath (α := SpatialCoordinates d) with hfdef
  have hfmeas : Measurable f := LifetimePath.measurable_ofContinuousPath
  set τ : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞ := ContinuousPath.exitTime U with hτdef
  have hτL : IsStoppingTime LifetimePath.canonicalFiltration
      (LifetimePath.exitTime U : Path d → ℝ≥0∞) := LifetimePath.isStoppingTime_exitTime U hU
  have hτf : ∀ p, LifetimePath.exitTime U (f p) = τ p := fun p =>
    LifetimePath.exitTime_ofContinuousPath U p
  have hτmeas : Measurable τ := ContinuousPath.measurable_exitTime U hU
  -- the grid
  set δ : ℕ → ℝ≥0 := fun n => h / ((n : ℝ≥0) + 1) with hδdef
  set t : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * δ n with htdef
  set r : ℕ → ℕ → ℝ≥0 := fun n k => h - t n k with hrdef
  set A : ℕ → ℕ → Set (Path d) :=
    fun n k => {w | LifetimePath.exitTime U w ≤ ((t n k : ℝ≥0) : ℝ≥0∞)} with hAdef
  set B : ℕ → ℕ → Set (Path d) := fun n => disjointed (A n) with hBdef
  have hAmeasT : ∀ n k, MeasurableSet[hτL.measurableSpace] (A n k) := fun n k =>
    hτL.measurableSet_le' (t n k)
  have hBmeasT : ∀ n k, MeasurableSet[hτL.measurableSpace] (B n k) := fun n k =>
    @MeasurableSet.disjointed _ hτL.measurableSpace _ (hAmeasT n) k
  have hBmeas : ∀ n k, MeasurableSet (B n k) := fun n k =>
    hτL.measurableSpace_le _ (hBmeasT n k)
  have htle : ∀ n k, k ≤ n + 1 → t n k ≤ h := by
    intro n k hk
    simp only [htdef, hδdef]
    rw [mul_div_assoc']
    apply div_le_of_le_mul₀ (by positivity) (zero_le)
    rw [mul_comm]
    gcongr
    exact_mod_cast hk
  have httop : ∀ n, t n (n + 1) = h := by
    intro n
    simp only [htdef, hδdef]
    push_cast
    field_simp

  have hAmono : ∀ n, Monotone (A n) := by
    intro n i j hij w hw
    simp only [hAdef, Set.mem_ofPred_eq] at hw ⊢
    refine hw.trans ?_
    simp only [htdef]
    gcongr
  have hBA : ∀ n k, B n k ⊆ A n k := fun n k => disjointed_subset (A n) k
  have hB0 : ∀ n, B n 0 = A n 0 := fun n => disjointed_zero (A n)
  have hBsucc : ∀ n j, B n (j + 1) = A n (j + 1) \ A n j := fun n j =>
    (hAmono n).disjointed_succ (not_isMax j)
  have hfin : ∀ n k p, f p ∈ B n k → τ p ≠ ⊤ := by
    intro n k p hp
    have := hBA n k hp
    simp only [hAdef, Set.mem_ofPred_eq, hτf] at this
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top this
  set Ev : ℕ → ℕ → Set (ContinuousPath (SpatialCoordinates d)) := fun n k =>
    {p | (p (τ p).toNNReal, p ((τ p).toNNReal + r n k)) ∈ O} with hEvdef
  have hτnn : Measurable fun p : ContinuousPath (SpatialCoordinates d) => (τ p).toNNReal :=
    ENNReal.measurable_toNNReal.comp hτmeas
  have hEvmeas : ∀ n k, MeasurableSet (Ev n k) := by
    intro n k
    have h2 : Measurable fun p : ContinuousPath (SpatialCoordinates d) =>
        (τ p).toNNReal + r n k := hτnn.add_const _
    exact hO.measurableSet.preimage
      ((ContinuousPath.measurable_eval_of_measurable _ hτnn).prodMk
        (ContinuousPath.measurable_eval_of_measurable _ h2))
  have hstep : ∀ n k, K x (f ⁻¹' B n k ∩ Ev n k) ≤ c * K x (f ⁻¹' B n k) := by
    intro n k
    set g : Path d → ℝ≥0∞ := fun v => O.indicator 1 (position 0 v, position (r n k) v)
      with hgdef
    have hg : Measurable g := (measurable_one.indicator hO.measurableSet).comp
      ((aux_tight_fixed_cutoff_soft_measurable_position 0).prodMk (aux_tight_fixed_cutoff_soft_measurable_position (r n k)))
    have hSeq : f ⁻¹' (B n k ∩ {w | LifetimePath.exitTime U w < w.lifetime}) =
        f ⁻¹' B n k := by
      ext p
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [hτf]
      have hlt : (f p).lifetime = ⊤ := LifetimePath.lifetime_ofContinuousPath p
      rw [hlt]
      exact ⟨fun hp => hp.1, fun hp => ⟨hp, lt_top_iff_ne_top.2 (hfin n k p hp)⟩⟩
    have hT := aux_tight_fixed_cutoff_soft_sm_transport K L hL hSM x _ hτL (B n k) (hBmeasT n k) g hg
    rw [hSeq] at hT
    simp only [LifetimePath.exitTime_ofContinuousPath] at hT
    have hind : ∀ p, g (LifetimePath.ofContinuousPath
        (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p)) =
          (Ev n k).indicator 1 p := by
      intro p
      simp only [hgdef, SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath,
        ContinuousPath.shift_apply, add_zero, Set.indicator_apply, hEvdef, Set.mem_ofPred_eq,
        Pi.one_apply]
      rfl
    simp_rw [hind] at hT
    rw [lintegral_indicator_one (hEvmeas n k),
      Measure.restrict_apply (hEvmeas n k), Set.inter_comm] at hT
    rw [hT]
    have hz : ∀ᵐ p ∂(K x).restrict (f ⁻¹' B n k),
        (∫⁻ q, g (f q) ∂K (p (τ p).toNNReal)) ≤ c := by
      rw [ae_restrict_iff' (hfmeas (hBmeas n k))]
      filter_upwards [h0 x] with p hp0 hpS
      have hzF : p (τ p).toNNReal ∈ frontier U :=
        ContinuousPath.coordinate_exitTime_mem_frontier U hU p (hp0 ▸ hx) (hfin n k p hpS)
      set z := p (τ p).toNNReal with hzdef
      have hQmeas : MeasurableSet
          {q : ContinuousPath (SpatialCoordinates d) | (q 0, q (r n k)) ∈ O} :=
        hO.measurableSet.preimage
          ((ContinuousPath.continuous_eval 0).measurable.prodMk
            (ContinuousPath.continuous_eval (r n k)).measurable)
      have hgq : ∀ q, g (f q) =
          {q : ContinuousPath (SpatialCoordinates d) | (q 0, q (r n k)) ∈ O}.indicator 1 q := by
        intro q
        show g (LifetimePath.ofContinuousPath q) = _
        simp only [hgdef, SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath,
          Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      simp_rw [hgq]
      rw [lintegral_indicator_one hQmeas]
      have hae : {q : ContinuousPath (SpatialCoordinates d) | (q 0, q (r n k)) ∈ O}
          =ᵐ[K z] {q | (z, q (r n k)) ∈ O} := by
        filter_upwards [h0 z] with q hq
        rw [hq]
      rw [measure_congr hae]
      exact hc z hzF (r n k) tsub_le_self
    calc ∫⁻ p in f ⁻¹' B n k, (∫⁻ q, g (f q) ∂K (p (τ p).toNNReal)) ∂K x
        ≤ ∫⁻ _ in f ⁻¹' B n k, c ∂K x := lintegral_mono_ae hz
      _ = c * K x (f ⁻¹' B n k) := setLIntegral_const _ _
  set En : ℕ → Set (ContinuousPath (SpatialCoordinates d)) :=
    fun n => ⋃ k ∈ Finset.range (n + 2), f ⁻¹' B n k ∩ Ev n k with hEndef
  have hsum : ∀ n, K x (En n) ≤ c * K x {p | τ p ≤ h} := by
    intro n
    calc K x (En n)
        ≤ ∑ k ∈ Finset.range (n + 2), K x (f ⁻¹' B n k ∩ Ev n k) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range (n + 2), c * K x (f ⁻¹' B n k) :=
          Finset.sum_le_sum fun k _ => hstep n k
      _ = c * K x (⋃ k ∈ Finset.range (n + 2), f ⁻¹' B n k) := by
          rw [← Finset.mul_sum, measure_biUnion_finset]
          · intro i _ j _ hij
            exact (disjoint_disjointed (A n) hij).preimage f
          · intro k _
            exact hfmeas (hBmeas n k)
      _ ≤ c * K x {p | τ p ≤ h} := by
          gcongr
          intro p hp
          simp only [Set.mem_iUnion, Finset.mem_range] at hp
          obtain ⟨k, hk, hpk⟩ := hp
          have := hBA n k hpk
          simp only [hAdef, Set.mem_ofPred_eq, hτf] at this
          exact this.trans (by exact_mod_cast htle n k (by omega))
  have hsub : {p | τ p ≤ h ∧ (p (τ p).toNNReal, p h) ∈ O} ⊆
      ⋃ N, ⋂ n ∈ Set.Ici N, En n := by
    rintro p ⟨hph, hpO⟩
    set τ0 := (τ p).toNNReal with hτ0
    have hτfin : τ p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hph
    have hτcoe : (τ0 : ℝ≥0∞) = τ p := ENNReal.coe_toNNReal hτfin
    have hV : IsOpen {u : ℝ≥0 | (p τ0, p u) ∈ O} :=
      hO.preimage (continuous_const.prodMk p.continuous)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV h hpO
    obtain ⟨N, hN⟩ := exists_nat_gt ((h : ℝ) / ε)
    refine Set.mem_iUnion.2 ⟨N, Set.mem_iInter₂.2 fun n hn => ?_⟩
    have hδ : (δ n : ℝ) < ε := by
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast (Set.mem_Ici.1 hn)
      simp only [hδdef, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hN
      nlinarith
    have hpA : f p ∈ A n (n + 1) := by
      simp only [hAdef, Set.mem_ofPred_eq, hτf, httop]
      exact hph
    have hU' : f p ∈ ⋃ k, B n k := by
      rw [hBdef, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨n + 1, hpA⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hU'
    have hkle : k ≤ n + 1 := by
      by_contra hlt
      push Not at hlt
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hBsucc] at hk
      exact hk.2 (hAmono n (by omega : n + 1 ≤ j) hpA)
    refine Set.mem_biUnion (Finset.mem_range.2 (by omega)) ⟨hk, ?_⟩
    show (p τ0, p (τ0 + r n k)) ∈ O
    apply hball
    rw [Metric.mem_ball, NNReal.dist_eq]
    have htk : t n k ≤ h := htle n k hkle
    have hτ0le : τ0 ≤ t n k := by
      have := hBA n k hk
      simp only [hAdef, Set.mem_ofPred_eq, hτf] at this
      rw [← hτcoe] at this
      exact_mod_cast this
    have hlow : (t n k : ℝ) - δ n ≤ τ0 := by
      rcases k with _ | j
      · have h0' : (t n 0 : ℝ) = 0 := by simp [htdef]
        rw [h0']
        have := NNReal.coe_nonneg τ0
        have := NNReal.coe_nonneg (δ n)
        linarith
      · rw [hBsucc] at hk
        have h2 := hk.2
        simp only [hAdef, Set.mem_ofPred_eq, hτf, not_le] at h2
        rw [← hτcoe] at h2
        have h3 : t n j < τ0 := by exact_mod_cast h2
        have h4 : (t n (j + 1) : ℝ) = t n j + δ n := by
          simp only [htdef]; push_cast; ring
        rw [h4]
        have : (t n j : ℝ) < τ0 := by exact_mod_cast h3
        linarith
    have hr : ((τ0 + r n k : ℝ≥0) : ℝ) = τ0 + h - t n k := by
      simp only [hrdef]
      rw [NNReal.coe_add, NNReal.coe_sub htk]
      ring
    rw [hr, abs_lt]
    have hτ0le' : (τ0 : ℝ) ≤ t n k := by exact_mod_cast hτ0le
    constructor <;> linarith
  calc K x {p | τ p ≤ h ∧ (p (τ p).toNNReal, p h) ∈ O}
      ≤ K x (⋃ N, ⋂ n ∈ Set.Ici N, En n) := measure_mono hsub
    _ = ⨆ N, K x (⋂ n ∈ Set.Ici N, En n) :=
        Monotone.measure_iUnion fun N M hNM =>
          Set.biInter_mono (Set.Ici_subset_Ici.2 hNM) fun _ _ => le_rfl
    _ ≤ c * K x {p | τ p ≤ h} :=
        iSup_le fun N => (measure_mono (Set.biInter_subset_of_mem Set.self_mem_Ici)).trans
          (hsum N)

/-- The path law starts where it is told, read off the time-zero marginal. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_start {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (hmap : ∀ (t : ℝ≥0) (z : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K z) = P t z)
    (z : SpatialCoordinates d) : ∀ᵐ q ∂K z, q 0 = z := by
  have hm : MeasurableSet ({z}ᶜ : Set (SpatialCoordinates d)) :=
    (measurableSet_singleton z).compl
  rw [ae_iff]
  have h1 := congrArg (fun μ : Measure (SpatialCoordinates d) => μ {z}ᶜ) (hmap 0 z)
  rw [Measure.map_apply (ContinuousPath.continuous_eval 0).measurable hm, P.zero,
    Kernel.id_apply, Measure.dirac_apply' _ hm] at h1
  simpa using! h1

/-- One-time marginals as path-law masses. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_marginal {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (hmap : ∀ (t : ℝ≥0) (z : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K z) = P t z)
    (t : ℝ≥0) (z : SpatialCoordinates d) (A : Set (SpatialCoordinates d))
    (hA : MeasurableSet A) : K z {q | q t ∈ A} = P t z A := by
  rw [← hmap t z, Measure.map_apply (ContinuousPath.continuous_eval t).measurable hA]
  rfl

/-- **Step 2 of the soft route (maximal inequality at small times).**  Uniformly over a compact
set of starting points, the probability that the path moves by `2 * rho` before a small time is
small.  This is the stopped form of the one-time estimate: at the exit time from the ball of
radius `2 * rho` the path sits on the sphere, in a fixed compact set, and the strong Markov
property restarts it there. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_small_time {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hF : P.IsFellerKernelSemigroup)
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (hKprob : ∀ z, IsProbabilityMeasure (K z))
    (hmap : ∀ (t : ℝ≥0) (z : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K z) = P t z)
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (hSM : StrongMarkov L)
    (K1 : Set (SpatialCoordinates d)) (hK1 : IsCompact K1) (rho : ℝ) (hrho : 0 < rho)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ h : ℝ≥0, 0 < h ∧ ∀ y ∈ K1,
      K y {p | ∃ s : ℝ≥0, s ≤ h ∧ 2 * rho ≤ dist (p s) y} ≤ ENNReal.ofReal eps := by
  have hK2 : IsCompact (Metric.cthickening (2 * rho) K1) := hK1.cthickening
  obtain ⟨h, hpos, hh⟩ := aux_tight_fixed_cutoff_soft_one_time P hF _ hK2 rho hrho (eps / 2) (by positivity)
  refine ⟨h, hpos, fun y hy => ?_⟩
  have h0 := aux_tight_fixed_cutoff_soft_start P K hmap
  set U : Set (SpatialCoordinates d) := Metric.ball y (2 * rho) with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by positivity)
  set O : Set (SpatialCoordinates d × SpatialCoordinates d) := {zw | rho < dist zw.2 zw.1}
    with hOdef
  have hO : IsOpen O := isOpen_lt continuous_const (continuous_snd.dist continuous_fst)
  have hc : ∀ z ∈ frontier U, ∀ s : ℝ≥0, s ≤ h →
      K z {q | (z, q s) ∈ O} ≤ ENNReal.ofReal (eps / 2) := by
    intro z hz s hs
    have hzK : z ∈ Metric.cthickening (2 * rho) K1 := by
      have hzc : z ∈ closure U := frontier_subset_closure hz
      have hzb : dist z y ≤ 2 * rho :=
        Metric.mem_closedBall.1 (Metric.closure_ball_subset_closedBall hzc)
      exact Metric.mem_cthickening_of_dist_le z y _ K1 hy hzb
    have hmeas : MeasurableSet {w : SpatialCoordinates d | rho ≤ dist w z} :=
      measurableSet_le measurable_const (measurable_id.dist measurable_const)
    calc K z {q | (z, q s) ∈ O} ≤ K z {q | q s ∈ {w | rho ≤ dist w z}} := by
          apply measure_mono
          intro q hq
          have hq' : rho < dist (q s) z := hq
          exact le_of_lt hq'
      _ = P s z {w | rho ≤ dist w z} := aux_tight_fixed_cutoff_soft_marginal P K hmap s z _ hmeas
      _ ≤ ENNReal.ofReal (eps / 2) := hh z hzK s hs
  have hcore := aux_tight_fixed_cutoff_soft_stopped_bound K L hL hSM h0 U hU y hyU h O hO _ hc
  set τ := ContinuousPath.exitTime U with hτdef
  have hsplit : {p : ContinuousPath (SpatialCoordinates d) | τ p ≤ h} ⊆
      {p | p h ∈ {w | rho ≤ dist w y}} ∪
        ({p | τ p ≤ h ∧ (p (τ p).toNNReal, p h) ∈ O} ∪ {p | p 0 ≠ y}) := by
    intro p hp
    by_cases h1 : rho ≤ dist (p h) y
    · exact Or.inl h1
    · refine Or.inr ?_
      by_cases h2 : p 0 = y
      · refine Or.inl ⟨hp, ?_⟩
        have hfin : τ p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hp
        have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU p (h2 ▸ hyU) hfin
        rw [hU.frontier_eq] at hfr
        have hout : 2 * rho ≤ dist (p (τ p).toNNReal) y := by
          have := hfr.2
          simpa [hUdef, Metric.mem_ball, not_lt] using this
        push Not at h1
        show rho < dist (p h) (p (τ p).toNNReal)
        have htri := dist_triangle (p (τ p).toNNReal) (p h) y
        rw [dist_comm (p (τ p).toNNReal) (p h)] at htri
        linarith
      · exact Or.inr h2
  have hnull : K y {p : ContinuousPath (SpatialCoordinates d) | p 0 ≠ y} = 0 := by
    have := h0 y
    rwa [ae_iff] at this
  have hmeasy : MeasurableSet {w : SpatialCoordinates d | rho ≤ dist w y} :=
    measurableSet_le measurable_const (measurable_id.dist measurable_const)
  have hm : K y {p | τ p ≤ h} ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := by
    calc K y {p | τ p ≤ h}
        ≤ K y {p | p h ∈ {w | rho ≤ dist w y}} +
            (K y {p | τ p ≤ h ∧ (p (τ p).toNNReal, p h) ∈ O} + K y {p | p 0 ≠ y}) :=
          (measure_mono hsplit).trans
            ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ ENNReal.ofReal (eps / 2) + (ENNReal.ofReal (eps / 2) * 1 + 0) := by
          gcongr
          · rw [aux_tight_fixed_cutoff_soft_marginal P K hmap h y _ hmeasy]
            exact hh y (Metric.self_subset_cthickening K1 hy) h le_rfl
          · exact hcore.trans (mul_le_mul_right prob_le_one _)
          · exact hnull.le
      _ = ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := by simp
  have hsub : {p : ContinuousPath (SpatialCoordinates d) | ∃ s : ℝ≥0, s ≤ h ∧
      2 * rho ≤ dist (p s) y} ⊆ {p | τ p ≤ h} := by
    rintro p ⟨s, hs, hd⟩
    have hnot : p s ∉ U := by
      simp only [hUdef, Metric.mem_ball, not_lt]
      exact hd
    exact (ContinuousPath.exitTime_le_of_notMem U p s hnot).trans (by exact_mod_cast hs)
  calc K y {p | ∃ s : ℝ≥0, s ≤ h ∧ 2 * rho ≤ dist (p s) y} ≤ K y {p | τ p ≤ h} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := hm
    _ = ENNReal.ofReal eps := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **No return from infinity.**  For a Feller semigroup and a bounded target, the mass that
reaches the target by any time of `[0, T]` from a far-away starting point is uniformly small.
The orbit `s ↦ P_s g` of a `C₀` bump over `[0, T]` is compact in `C₀`, hence uniformly
vanishing at infinity. -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_no_return
    {alpha : Type*} [MetricSpace alpha] [ProperSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [SecondCountableTopology alpha]
    (P : SubMarkovKernelSemigroup alpha) (hF : P.IsFellerKernelSemigroup)
    (x0 : alpha) (R0 : ℝ) (T : ℝ≥0) (eps : ℝ) (heps : 0 < eps) :
    ∃ R1 : ℝ, ∀ z, R1 ≤ dist z x0 → ∀ s : ℝ≥0, s ≤ T →
      (P s z) {w | dist w x0 < R0} ≤ ENNReal.ofReal eps := by
  classical
  set hC0 := hF.mapsC0 with hC0def
  obtain ⟨g0, hg1, _hg0, hgsupp, hgmem⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_closedBall x0 R0) (Metric.isOpen_ball (x := x0) (ε := R0 + 1)).isClosed_compl
      (by
        rw [Set.disjoint_compl_right_iff_subset]
        intro z hz
        exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  set g : C₀(alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap ⟨g0, hgsupp⟩ with hgdef
  have hgval : ∀ z, g z = g0 z := fun z =>
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply _ z
  set F : ℝ≥0 → C₀(alpha, ℝ) := fun s => P.c0Operator hC0 s g with hFdef
  have hFc : Continuous F := hF.hasContinuousC0Orbits g
  have hS : IsCompact (F '' Set.Icc 0 T) := isCompact_Icc.image hFc
  obtain ⟨t, htfin, hcover⟩ :=
    (Metric.totallyBounded_iff.1 hS.totallyBounded) (eps / 2) (by positivity)
  have hev : ∀ᶠ z in cocompact alpha, ∀ y ∈ t, |(y : C₀(alpha, ℝ)) z| < eps / 2 := by
    rw [Filter.eventually_all_finite htfin]
    intro y _
    have htend := y.zero_at_infty'
    filter_upwards [(Metric.tendsto_nhds.1 htend) (eps / 2) (by positivity)] with z hz
    simpa [Real.dist_eq] using hz
  obtain ⟨Kc, hKc, hKcsub⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨R', hR'⟩ := hKc.isBounded.subset_closedBall x0
  refine ⟨R' + 1, fun z hz s hs => ?_⟩
  have hzK : z ∉ Kc := fun hzK => by
    have := Metric.mem_closedBall.1 (hR' hzK)
    linarith
  have hzev : ∀ y ∈ t, |(y : C₀(alpha, ℝ)) z| < eps / 2 := hKcsub hzK
  obtain ⟨y, hyt, hyF⟩ : ∃ y ∈ t, F s ∈ Metric.ball y (eps / 2) := by
    have := hcover ⟨s, ⟨zero_le, hs⟩, rfl⟩
    simpa only [Set.mem_iUnion, exists_prop] using this
  have hval : |F s z| < eps := by
    have h1 : |F s z - y z| ≤ ‖F s - y‖ := by
      have hb := (F s - y).toBCF.norm_coe_le_norm z
      rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hb
      have hv : (F s - y).toBCF z = F s z - y z := rfl
      rwa [hv, Real.norm_eq_abs] at hb
    have h2 : ‖F s - y‖ < eps / 2 := by rw [← dist_eq_norm]; exact hyF
    have h3 := hzev y hyt
    have h4 := abs_sub_abs_le_abs_sub (F s z) (y z)
    linarith
  let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
  let : IsFiniteMeasure (P s z) := IsFiniteKernel.isFiniteMeasure z
  set A : Set alpha := {w | dist w x0 < R0} with hAdef
  have hAmeas : MeasurableSet A :=
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).measurableSet
  have hint : (P s z).real A ≤ ∫ w, g w ∂(P s z) := by
    rw [← integral_indicator_one hAmeas]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hAmeas)
      (g.toBCF.integrable _) fun w => ?_
    by_cases hw : w ∈ A
    · rw [Set.indicator_of_mem hw, hgval]
      exact le_of_eq (hg1 (Metric.mem_closedBall.2 (le_of_lt hw))).symm
    · rw [Set.indicator_of_notMem hw, hgval]
      exact (hgmem w).1
  have hop : ∫ w, g w ∂(P s z) = F s z := rfl
  rw [hop] at hint
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P s z) A)]
  exact ENNReal.ofReal_le_ofReal (hint.trans ((le_abs_self _).trans hval.le))

/-- **Compact containment (Steps 2–3 of the soft route).**  Uniformly over a compact set of
starting points, the path stays in a fixed ball up to time `T`, except on a set of small mass.
At the exit time from a large ball the path is far away; from there it cannot come back to the
bounded region where it has to be at time `T` (`aux_tight_fixed_cutoff_soft_no_return`), and it is unlikely to be
outside that region at time `T` (`aux_tight_fixed_cutoff_soft_escape`). -/


-- Reused from `finite_cutoff_local_path_bounds`.
theorem aux_tight_fixed_cutoff_soft_containment {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hF : P.IsFellerKernelSemigroup)
    (hC : P.IsConservative)
    (K : SpatialCoordinates d → Measure (ContinuousPath (SpatialCoordinates d)))
    (hKprob : ∀ z, IsProbabilityMeasure (K z))
    (hmap : ∀ (t : ℝ≥0) (z : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K z) = P t z)
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (hSM : StrongMarkov L)
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B) (T : ℝ≥0) (eps : ℝ) (heps : 0 < eps) :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ B,
      K y {p | ∃ s : ℝ≥0, s ≤ T ∧ R ≤ dist (p s) 0} ≤ ENNReal.ofReal eps := by
  obtain ⟨R0, _hR0pos, hR0⟩ := aux_tight_fixed_cutoff_soft_escape P hF hC B hB 0 T (eps / 2) (by positivity)
  obtain ⟨R1, hR1⟩ := aux_tight_fixed_cutoff_soft_no_return P hF 0 R0 T (eps / 2) (by positivity)
  obtain ⟨Rb, hRb⟩ := hB.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  set R : ℝ := max (max R1 (Rb + 1)) 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR1R : R1 ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRbR : Rb + 1 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨R, hRpos, fun y hy => ?_⟩
  have h0 := aux_tight_fixed_cutoff_soft_start P K hmap
  set U : Set (SpatialCoordinates d) := Metric.ball 0 R with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := by
    have := Metric.mem_closedBall.1 (hRb hy)
    exact Metric.mem_ball.2 (by linarith)
  set O : Set (SpatialCoordinates d × SpatialCoordinates d) := {zw | dist zw.2 0 < R0}
    with hOdef
  have hO : IsOpen O := isOpen_lt (continuous_snd.dist continuous_const) continuous_const
  have hc : ∀ z ∈ frontier U, ∀ s : ℝ≥0, s ≤ T →
      K z {q | (z, q s) ∈ O} ≤ ENNReal.ofReal (eps / 2) := by
    intro z hz s hs
    rw [hU.frontier_eq] at hz
    have hzR : R ≤ dist z 0 := by
      have := hz.2
      simpa [hUdef, Metric.mem_ball, not_lt] using this
    have hmeas : MeasurableSet {w : SpatialCoordinates d | dist w 0 < R0} :=
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const).measurableSet
    calc K z {q | (z, q s) ∈ O} = K z {q | q s ∈ {w | dist w 0 < R0}} := rfl
      _ = P s z {w | dist w 0 < R0} := aux_tight_fixed_cutoff_soft_marginal P K hmap s z _ hmeas
      _ ≤ ENNReal.ofReal (eps / 2) := hR1 z (hR1R.trans hzR) s hs
  have hcore := aux_tight_fixed_cutoff_soft_stopped_bound K L hL hSM h0 U hU y hyU T O hO _ hc
  set τ := ContinuousPath.exitTime U with hτdef
  have hsplit : {p : ContinuousPath (SpatialCoordinates d) | τ p ≤ T} ⊆
      {p | p T ∈ {w | R0 ≤ dist w 0}} ∪ {p | τ p ≤ T ∧ (p (τ p).toNNReal, p T) ∈ O} := by
    intro p hp
    by_cases h1 : R0 ≤ dist (p T) 0
    · exact Or.inl h1
    · exact Or.inr ⟨hp, lt_of_not_ge h1⟩
  have hmeas0 : MeasurableSet {w : SpatialCoordinates d | R0 ≤ dist w 0} :=
    measurableSet_le measurable_const (measurable_id.dist measurable_const)
  have hm : K y {p | τ p ≤ T} ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := by
    calc K y {p | τ p ≤ T}
        ≤ K y {p | p T ∈ {w | R0 ≤ dist w 0}} +
            K y {p | τ p ≤ T ∧ (p (τ p).toNNReal, p T) ∈ O} :=
          (measure_mono hsplit).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) * 1 := by
          gcongr
          · rw [aux_tight_fixed_cutoff_soft_marginal P K hmap T y _ hmeas0]
            exact hR0 y hy T le_rfl
          · exact hcore.trans (mul_le_mul_right prob_le_one _)
      _ = ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := by rw [mul_one]
  have hsub : {p : ContinuousPath (SpatialCoordinates d) | ∃ s : ℝ≥0, s ≤ T ∧
      R ≤ dist (p s) 0} ⊆ {p | τ p ≤ T} := by
    rintro p ⟨s, hs, hd⟩
    have hnot : p s ∉ U := by
      simp only [hUdef, Metric.mem_ball, not_lt]
      exact hd
    exact (ContinuousPath.exitTime_le_of_notMem U p s hnot).trans (by exact_mod_cast hs)
  calc K y {p | ∃ s : ℝ≥0, s ≤ T ∧ R ≤ dist (p s) 0} ≤ K y {p | τ p ≤ T} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) := hm
    _ = ENNReal.ofReal eps := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- Every continuous path has, on `[0, T]`, a modulus of continuity at every tolerance: the
complements of the modulus sets decrease to the empty set as the scale tends to zero. -/


-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sm_transport {d : ℕ}
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
  have hTmeas : Measurable T := by simpa only using! hT.measurable'
  have hS : MeasurableSet (B ∩ {w : Path d | T w < w.lifetime}) :=
    (hT.measurableSpace_le _ hB).inter
      (measurableSet_lt hTmeas LifetimePath.measurable_lifetime)
  have h := hSM.2.2 x T hT B hB g hg
  rw [← hL x, Measure.restrict_map hemb.measurable hS, hemb.lintegral_map,
    hemb.lintegral_map] at h
  simp only [SubdiffusiveProcess.Model.LifetimeProcess.shift_ofContinuousPath,
    SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath] at h
  rw [h]
  refine setLIntegral_congr_fun_ae (hemb.measurable hS) (ae_of_all _ fun p _ => ?_)
  rw [← hL, hemb.lintegral_map]

/-- Random time shift by a measurable time is measurable on path space. -/


-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurable_shift {d : ℕ}
    (τ : ContinuousPath (SpatialCoordinates d) → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun p : ContinuousPath (SpatialCoordinates d) => ContinuousPath.shift (τ p) p) :=
  ContinuousPath.continuous_shift.measurable.comp (hτ.prodMk measurable_id)



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sm_weighted {d : ℕ}
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
  have hF : Measurable F := hg.comp (aux_tight_fixed_cutoff_restart_measurable_shift _ hτnn)
  have hG : Measurable G :=
    (hg.lintegral_kernel (κ := k)).comp (ContinuousPath.measurable_eval_of_measurable _ hτnn)
  have hSm : MeasurableSet S := measurableSet_lt hτmeas measurable_const
  have hid : ∀ A, MeasurableSet[MeasurableSpace.comap f hT.measurableSpace] A → ∫⁻ p in A ∩ S, F p ∂k x = ∫⁻ p in A ∩ S, G p ∂k x := by
    rintro A ⟨B, hB, rfl⟩
    have h := aux_tight_fixed_cutoff_restart_sm_transport (fun z => k z) L hL hSM x _ hT B hB g' hg'
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


-- Reused from `lem_resolvents_to_paths`.
def aux_tight_fixed_cutoff_restart_ex {d : ℕ} (ρ : ℝ) (p : DiffusionPath d) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (p 0) ρ) p



-- Reused from `lem_resolvents_to_paths`.
def aux_tight_fixed_cutoff_restart_tex {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) : ℝ≥0∞ :=
  if p 0 ∈ C then aux_tight_fixed_cutoff_restart_ex ρ p else ⊤

/-- Successive exit epochs: `σ₀ = 0`, `σ_{j+1} = σ_j + τ̃ ∘ θ_{σ_j}` (`⊤` absorbs). -/


-- Reused from `lem_resolvents_to_paths`.
def aux_tight_fixed_cutoff_restart_sig {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ) :
    ℕ → DiffusionPath d → ℝ≥0∞
  | 0, _ => 0
  | j + 1, p => aux_tight_fixed_cutoff_restart_sig C ρ j p + aux_tight_fixed_cutoff_restart_tex C ρ
        (ContinuousPath.shift (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal p)



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_ex_eq {d : ℕ} (ρ : ℝ) (p : DiffusionPath d) :
    aux_tight_fixed_cutoff_restart_ex ρ p = ContinuousPath.exitTime (Metric.ball 0 ρ)
      (p - ContinuousMap.const ℝ≥0 (p 0)) := by
  unfold aux_tight_fixed_cutoff_restart_ex ContinuousPath.exitTime
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, dist_eq_norm, sub_zero]



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurable_ex {d : ℕ} (ρ : ℝ) :
    Measurable (aux_tight_fixed_cutoff_restart_ex (d := d) ρ) := by
  have hΔ : Continuous (fun p : DiffusionPath d => p - ContinuousMap.const ℝ≥0 (p 0)) :=
    continuous_id.sub (ContinuousMap.continuous_const'.comp (ContinuousPath.continuous_eval 0))
  have h := (ContinuousPath.measurable_exitTime (Metric.ball (0 : SpatialCoordinates d) ρ)
    Metric.isOpen_ball).comp hΔ.measurable
  have heq : aux_tight_fixed_cutoff_restart_ex (d := d) ρ =
      (ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) ρ)) ∘
        (fun p : DiffusionPath d => p - ContinuousMap.const ℝ≥0 (p 0)) := by
    funext p; exact aux_tight_fixed_cutoff_restart_ex_eq ρ p
  rw [heq]; exact h



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurable_tex {d : ℕ} (C : Set (SpatialCoordinates d))
    (hC : MeasurableSet C) (ρ : ℝ) :
    Measurable (aux_tight_fixed_cutoff_restart_tex C ρ) := by
  classical
  unfold aux_tight_fixed_cutoff_restart_tex
  exact Measurable.ite (hC.preimage (ContinuousPath.continuous_eval 0).measurable)
    (aux_tight_fixed_cutoff_restart_measurable_ex ρ) measurable_const



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurable_sig {d : ℕ} (C : Set (SpatialCoordinates d))
    (hC : MeasurableSet C) (ρ : ℝ) (j : ℕ) :
    Measurable (aux_tight_fixed_cutoff_restart_sig C ρ j) := by
  classical
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hs : Measurable (fun p : DiffusionPath d => ContinuousPath.shift
        (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal p) :=
      aux_tight_fixed_cutoff_restart_measurable_shift _ (ENNReal.measurable_toNNReal.comp ih)
    exact ih.add ((aux_tight_fixed_cutoff_restart_measurable_tex C hC ρ).comp hs)



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_zero {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) : aux_tight_fixed_cutoff_restart_sig C ρ 0 p = 0 := rfl



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_succ {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (j : ℕ) (p : DiffusionPath d) :
    aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p = aux_tight_fixed_cutoff_restart_sig C ρ j p +
      aux_tight_fixed_cutoff_restart_tex C ρ
        (ContinuousPath.shift (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal p) := rfl



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_succ_top {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) (hj : aux_tight_fixed_cutoff_restart_sig C ρ j p = ⊤) :
    aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p = ⊤ := by
  rw [aux_tight_fixed_cutoff_restart_sig_succ, hj, top_add]



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_mono_succ {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) :
    aux_tight_fixed_cutoff_restart_sig C ρ j p ≤ aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p := by
  rw [aux_tight_fixed_cutoff_restart_sig_succ]; exact le_self_add

/-- **Front recursion** for the successive exit epochs. -/


-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_front {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) (ha : aux_tight_fixed_cutoff_restart_tex C ρ p ≠ ⊤) :
    aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p = aux_tight_fixed_cutoff_restart_tex C ρ p +
      aux_tight_fixed_cutoff_restart_sig C ρ j
        (ContinuousPath.shift (aux_tight_fixed_cutoff_restart_tex C ρ p).toNNReal p) := by
  induction j generalizing p with
  | zero =>
    rw [aux_tight_fixed_cutoff_restart_sig_succ]
    simp [aux_tight_fixed_cutoff_restart_sig_zero, ContinuousPath.shift_zero]
  | succ j ih =>
    set a := aux_tight_fixed_cutoff_restart_tex C ρ p with hadef
    set q := ContinuousPath.shift a.toNNReal p with hqdef
    have hIH := ih p ha
    by_cases hb : aux_tight_fixed_cutoff_restart_sig C ρ j q = ⊤
    · have h1 : aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p = ⊤ := by
        rw [hIH, hb, add_top]
      rw [aux_tight_fixed_cutoff_restart_sig_succ_top C ρ (j + 1) p h1,
        aux_tight_fixed_cutoff_restart_sig_succ_top C ρ j q hb, add_top]
    · have hne : aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p ≠ ⊤ := by
        rw [hIH]; exact ENNReal.add_ne_top.mpr ⟨ha, hb⟩
      rw [aux_tight_fixed_cutoff_restart_sig_succ C ρ (j + 1) p,
        aux_tight_fixed_cutoff_restart_sig_succ C ρ j q, hIH, add_assoc]
      congr 2
      rw [hqdef, ContinuousPath.shift_add, ENNReal.toNNReal_add ha hb]



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_one {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) :
    aux_tight_fixed_cutoff_restart_sig C ρ 1 p = aux_tight_fixed_cutoff_restart_tex C ρ p := by
  rw [aux_tight_fixed_cutoff_restart_sig_succ, aux_tight_fixed_cutoff_restart_sig_zero, zero_add]
  simp [ContinuousPath.shift_zero]



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_mono {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (p : DiffusionPath d) : Monotone (fun j => aux_tight_fixed_cutoff_restart_sig C ρ j p) :=
  monotone_nat_of_le_succ fun j => aux_tight_fixed_cutoff_restart_sig_mono_succ C ρ j p



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_succ_eq_top {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (j : ℕ) (p : DiffusionPath d) (ha : aux_tight_fixed_cutoff_restart_tex C ρ p = ⊤) :
    aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p = ⊤ := by
  have h1 : aux_tight_fixed_cutoff_restart_sig C ρ 1 p ≤ aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p :=
    aux_tight_fixed_cutoff_restart_sig_mono C ρ p (by omega)
  rw [aux_tight_fixed_cutoff_restart_sig_one, ha] at h1
  exact top_le_iff.mp h1

/-- Exponential weight `e^{-s/h}` of an extended time, `0` at `⊤`. -/


-- Reused from `lem_resolvents_to_paths`.
def aux_tight_fixed_cutoff_restart_wt (h : ℝ) (s : ℝ≥0∞) : ℝ≥0∞ :=
  if s = ⊤ then 0 else ENNReal.ofReal (Real.exp (-s.toReal / h))



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_wt_top (h : ℝ) : aux_tight_fixed_cutoff_restart_wt h ⊤ = 0 := by
  simp [aux_tight_fixed_cutoff_restart_wt]



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_wt_zero (h : ℝ) : aux_tight_fixed_cutoff_restart_wt h 0 = 1 := by
  simp [aux_tight_fixed_cutoff_restart_wt]



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_wt_add (h : ℝ) (a b : ℝ≥0∞) :
    aux_tight_fixed_cutoff_restart_wt h (a + b) =
      aux_tight_fixed_cutoff_restart_wt h a * aux_tight_fixed_cutoff_restart_wt h b := by
  by_cases ha : a = ⊤
  · simp [ha, aux_tight_fixed_cutoff_restart_wt_top]
  by_cases hb : b = ⊤
  · simp [hb, aux_tight_fixed_cutoff_restart_wt_top]
  have hab : a + b ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha, hb⟩
  simp only [aux_tight_fixed_cutoff_restart_wt, ite_eq_right ha, ite_eq_right hb, ite_eq_right hab]
  rw [ENNReal.toReal_add ha hb, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurable_wt (h : ℝ) :
    Measurable (aux_tight_fixed_cutoff_restart_wt h) := by
  unfold aux_tight_fixed_cutoff_restart_wt
  exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (ENNReal.measurable_toReal.neg.div_const h)))



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_wt_le_one {h : ℝ} (hh : 0 < h) (s : ℝ≥0∞) :
    aux_tight_fixed_cutoff_restart_wt h s ≤ 1 := by
  unfold aux_tight_fixed_cutoff_restart_wt
  split_ifs
  · exact zero_le_one
  · rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr ?_)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ENNReal.toReal_nonneg) hh.le



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_wt_le_split {h : ℝ} (hh : 0 < h) {h1 : ℝ} (hh1 : 0 ≤ h1)
    (s : ℝ≥0∞) :
    aux_tight_fixed_cutoff_restart_wt h s ≤
      {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator 1 s + ENNReal.ofReal (Real.exp (-h1 / h)) := by
  by_cases hs : s ≤ ENNReal.ofReal h1
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} from hs), Pi.one_apply]
    exact (aux_tight_fixed_cutoff_restart_wt_le_one hh s).trans le_self_add
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} from hs), zero_add]
    unfold aux_tight_fixed_cutoff_restart_wt
    split_ifs with htop
    · exact zero_le
    · refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      rw [not_le] at hs
      have : h1 < s.toReal := by
        rw [← ENNReal.ofReal_lt_iff_lt_toReal hh1 htop]; exact hs
      exact div_le_div_of_nonneg_right (by linarith) hh.le



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_wt_ge {h : ℝ} (hh : 0 < h) {T : ℝ} (hT : 0 ≤ T) {s : ℝ≥0∞}
    (hs : s ≤ ENNReal.ofReal T) :
    ENNReal.ofReal (Real.exp (-T / h)) ≤ aux_tight_fixed_cutoff_restart_wt h s := by
  have htop : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  unfold aux_tight_fixed_cutoff_restart_wt
  rw [ite_eq_right htop]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have : s.toReal ≤ T := ENNReal.toReal_le_of_le_ofReal hT hs
  exact div_le_div_of_nonneg_right (by linarith) hh.le



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_exitTime_measurable_stopped {d : ℕ}
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


-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurable_stopped_comp {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (F : ℝ≥0∞ → ℝ≥0∞) (hF : Measurable F) :
    Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      (fun p : ContinuousPath (SpatialCoordinates d) => F (ContinuousPath.exitTime U p)) := by
  have hc : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace,
      (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
      (LifetimePath.ofContinuousPath (α := SpatialCoordinates d)) := fun s hs => ⟨s, hs, rfl⟩
  have h := hF.comp ((aux_tight_fixed_cutoff_restart_exitTime_measurable_stopped U hU).comp hc)
  have heq : (fun p : ContinuousPath (SpatialCoordinates d) => F (ContinuousPath.exitTime U p)) =
      F ∘ (LifetimePath.exitTime U ∘ LifetimePath.ofContinuousPath) := by
    funext p; simp [LifetimePath.exitTime_ofContinuousPath]
  rw [heq]; exact h



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_tex_of_start {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (p : DiffusionPath d) (z : SpatialCoordinates d) (hp0 : p 0 = z) :
    aux_tight_fixed_cutoff_restart_tex C ρ p =
      if z ∈ C then ContinuousPath.exitTime (Metric.ball z ρ) p else ⊤ := by
  classical
  unfold aux_tight_fixed_cutoff_restart_tex aux_tight_fixed_cutoff_restart_ex
  subst hp0
  rfl



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_sig_moment {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) (ρ : ℝ) {h : ℝ}
    (γ : ℝ≥0∞)
    (hγ : ∀ y ∈ C, ∫⁻ p, aux_tight_fixed_cutoff_restart_wt h
      (ContinuousPath.exitTime (Metric.ball y ρ) p) ∂k y ≤ γ) :
    ∀ j z, ∫⁻ p, aux_tight_fixed_cutoff_restart_wt h (aux_tight_fixed_cutoff_restart_sig C ρ j p) ∂k z
      ≤ γ ^ j := by
  classical
  intro j
  induction j with
  | zero =>
    intro z
    simp only [aux_tight_fixed_cutoff_restart_sig_zero, aux_tight_fixed_cutoff_restart_wt_zero,
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
      have hae : ∀ᵐ p ∂k z, aux_tight_fixed_cutoff_restart_wt h
          (aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p) =
          S.indicator (fun p => aux_tight_fixed_cutoff_restart_wt h (ContinuousPath.exitTime U p) *
            aux_tight_fixed_cutoff_restart_wt h (aux_tight_fixed_cutoff_restart_sig C ρ j
              (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p))) p := by
        filter_upwards [h0 z] with p hp0
        have htex := aux_tight_fixed_cutoff_restart_tex_of_start C ρ p z hp0
        rw [ite_eq_left hz] at htex
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS]
          have hne : aux_tight_fixed_cutoff_restart_tex C ρ p ≠ ⊤ := by
            rw [htex]; exact ne_of_lt hpS
          rw [aux_tight_fixed_cutoff_restart_sig_front C ρ j p hne, aux_tight_fixed_cutoff_restart_wt_add,
            htex]
        · rw [Set.indicator_of_notMem hpS]
          have htop : aux_tight_fixed_cutoff_restart_tex C ρ p = ⊤ := by
            rw [htex]; exact not_lt_top_iff.mp hpS
          rw [aux_tight_fixed_cutoff_restart_sig_succ_eq_top C ρ j p htop,
            aux_tight_fixed_cutoff_restart_wt_top]
      rw [lintegral_congr_ae hae, lintegral_indicator hSm]
      have hW := aux_tight_fixed_cutoff_restart_measurable_stopped_comp U hU _
        (aux_tight_fixed_cutoff_restart_measurable_wt h)
      have hg : Measurable (fun p => aux_tight_fixed_cutoff_restart_wt h
          (aux_tight_fixed_cutoff_restart_sig C ρ j p)) :=
        (aux_tight_fixed_cutoff_restart_measurable_wt h).comp
          (aux_tight_fixed_cutoff_restart_measurable_sig C hC ρ j)
      have hSMid := aux_tight_fixed_cutoff_restart_sm_weighted k L hL hSM U hU z _ hW _ hg
      rw [hSMid]
      calc ∫⁻ p in S, aux_tight_fixed_cutoff_restart_wt h (ContinuousPath.exitTime U p) *
            ∫⁻ q, aux_tight_fixed_cutoff_restart_wt h (aux_tight_fixed_cutoff_restart_sig C ρ j q)
              ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k z
          ≤ ∫⁻ p in S, aux_tight_fixed_cutoff_restart_wt h (ContinuousPath.exitTime U p) * γ ^ j
              ∂k z := lintegral_mono fun p => by gcongr; exact ih _
        _ ≤ ∫⁻ p, aux_tight_fixed_cutoff_restart_wt h (ContinuousPath.exitTime U p) * γ ^ j ∂k z :=
            setLIntegral_le_lintegral _ _
        _ = (∫⁻ p, aux_tight_fixed_cutoff_restart_wt h (ContinuousPath.exitTime U p) ∂k z) * γ ^ j :=
            lintegral_mul_const _ ((aux_tight_fixed_cutoff_restart_measurable_wt h).comp
              (ContinuousPath.measurable_exitTime U hU))
        _ ≤ γ * γ ^ j := by gcongr; exact hγ z hz
        _ = γ ^ (j + 1) := by rw [pow_succ, mul_comm]
    · have hae : ∀ᵐ p ∂k z, aux_tight_fixed_cutoff_restart_wt h
          (aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p) = 0 := by
        filter_upwards [h0 z] with p hp0
        have htex := aux_tight_fixed_cutoff_restart_tex_of_start C ρ p z hp0
        rw [ite_eq_right hz] at htex
        rw [aux_tight_fixed_cutoff_restart_sig_succ_eq_top C ρ j p htex,
          aux_tight_fixed_cutoff_restart_wt_top]
      rw [lintegral_congr_ae hae, lintegral_zero]
      exact zero_le


/-! ### RtpCount2 -/

/-- The `j`-th epoch is finite and the following gap is at most `δ`. -/


-- Reused from `lem_resolvents_to_paths`.
def aux_tight_fixed_cutoff_restart_gapEv {d : ℕ} (C : Set (SpatialCoordinates d)) (ρ : ℝ)
    (δ : ℝ≥0∞) (j : ℕ) : Set (DiffusionPath d) :=
  {p | aux_tight_fixed_cutoff_restart_sig C ρ j p ≠ ⊤ ∧ aux_tight_fixed_cutoff_restart_tex C ρ
    (ContinuousPath.shift (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal p) ≤ δ}



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_measurableSet_gapEv {d : ℕ} (C : Set (SpatialCoordinates d))
    (hC : MeasurableSet C) (ρ : ℝ) (δ : ℝ≥0∞) (j : ℕ) :
    MeasurableSet (aux_tight_fixed_cutoff_restart_gapEv (d := d) C ρ δ j) := by
  have hs := aux_tight_fixed_cutoff_restart_measurable_sig (d := d) C hC ρ j
  have hsh : Measurable (fun p : DiffusionPath d => ContinuousPath.shift
      (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal p) :=
    aux_tight_fixed_cutoff_restart_measurable_shift _ (ENNReal.measurable_toNNReal.comp hs)
  exact (hs (measurableSet_singleton ⊤).compl).inter
    (measurableSet_le ((aux_tight_fixed_cutoff_restart_measurable_tex C hC ρ).comp hsh)
      measurable_const)



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_gapEv_front {d : ℕ} (C : Set (SpatialCoordinates d))
    (ρ : ℝ) (δ : ℝ≥0∞) (j : ℕ) (p : DiffusionPath d)
    (ha : aux_tight_fixed_cutoff_restart_tex C ρ p ≠ ⊤) :
    p ∈ aux_tight_fixed_cutoff_restart_gapEv C ρ δ (j + 1) ↔
      ContinuousPath.shift (aux_tight_fixed_cutoff_restart_tex C ρ p).toNNReal p ∈
        aux_tight_fixed_cutoff_restart_gapEv C ρ δ j := by
  set q := ContinuousPath.shift (aux_tight_fixed_cutoff_restart_tex C ρ p).toNNReal p with hqdef
  have hf := aux_tight_fixed_cutoff_restart_sig_front C ρ j p ha
  simp only [aux_tight_fixed_cutoff_restart_gapEv, Set.mem_ofPred_eq, hf]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : aux_tight_fixed_cutoff_restart_sig C ρ j q ≠ ⊤ := fun hb => h1 (by rw [hb, add_top])
    refine ⟨hb, ?_⟩
    rw [ENNReal.toNNReal_add ha hb, ← ContinuousPath.shift_add] at h2
    exact h2
  · rintro ⟨hb, h2⟩
    refine ⟨ENNReal.add_ne_top.mpr ⟨ha, hb⟩, ?_⟩
    rw [ENNReal.toNNReal_add ha hb, ← ContinuousPath.shift_add]
    exact h2



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_gap_prob {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) (ρ : ℝ) (δ : ℝ≥0∞) (hδ : δ ≠ ⊤)
    (β : ℝ≥0∞)
    (hβ : ∀ y ∈ C, k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ δ} ≤ β) :
    ∀ j z, k z (aux_tight_fixed_cutoff_restart_gapEv C ρ δ j) ≤ β := by
  classical
  intro j
  induction j with
  | zero =>
    intro z
    by_cases hz : z ∈ C
    · refine le_trans (measure_mono_ae ?_) (hβ z hz)
      filter_upwards [h0 z] with p hp0 hp
      have htex := aux_tight_fixed_cutoff_restart_tex_of_start C ρ p z hp0
      rw [ite_eq_left hz] at htex
      have hp' : aux_tight_fixed_cutoff_restart_tex C ρ p ≤ δ := by
        have := hp.2
        simpa [aux_tight_fixed_cutoff_restart_sig_zero, ContinuousPath.shift_zero] using this
      rw [htex] at hp'
      exact hp'
    · have h0' : k z (aux_tight_fixed_cutoff_restart_gapEv C ρ δ 0) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h0 z] with p hp0 hp
        have htex := aux_tight_fixed_cutoff_restart_tex_of_start C ρ p z hp0
        rw [ite_eq_right hz] at htex
        have hp' : aux_tight_fixed_cutoff_restart_tex C ρ p ≤ δ := by
          have := hp.2
          simpa [aux_tight_fixed_cutoff_restart_sig_zero, ContinuousPath.shift_zero] using this
        rw [htex, top_le_iff] at hp'
        exact hδ hp'
      rw [h0']; exact zero_le
  | succ j ih =>
    intro z
    have hGm := aux_tight_fixed_cutoff_restart_measurableSet_gapEv (d := d) C hC ρ δ j
    by_cases hz : z ∈ C
    · set U := Metric.ball z ρ with hUdef
      have hU : IsOpen U := Metric.isOpen_ball
      set S : Set (ContinuousPath (SpatialCoordinates d)) :=
        {p | ContinuousPath.exitTime U p < ⊤} with hSdef
      have hSm : MeasurableSet S :=
        measurableSet_lt (ContinuousPath.measurable_exitTime U hU) measurable_const
      have hae : ∀ᵐ p ∂k z,
          (aux_tight_fixed_cutoff_restart_gapEv C ρ δ (j + 1)).indicator (1 : DiffusionPath d → ℝ≥0∞) p =
          S.indicator (fun p => (1 : ℝ≥0∞) * (aux_tight_fixed_cutoff_restart_gapEv C ρ δ j).indicator 1
            (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p)) p := by
        filter_upwards [h0 z] with p hp0
        have htex := aux_tight_fixed_cutoff_restart_tex_of_start C ρ p z hp0
        rw [ite_eq_left hz] at htex
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS, one_mul]
          have hne : aux_tight_fixed_cutoff_restart_tex C ρ p ≠ ⊤ := by
            rw [htex]; exact ne_of_lt hpS
          have hiff := aux_tight_fixed_cutoff_restart_gapEv_front C ρ δ j p hne
          rw [htex] at hiff
          by_cases hq : ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p ∈
              aux_tight_fixed_cutoff_restart_gapEv C ρ δ j
          · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (hiff.mpr hq)]
            rfl
          · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq (hiff.mp h))]
        · rw [Set.indicator_of_notMem hpS]
          have htop : aux_tight_fixed_cutoff_restart_tex C ρ p = ⊤ := by
            rw [htex]; exact not_lt_top_iff.mp hpS
          have hnot : p ∉ aux_tight_fixed_cutoff_restart_gapEv C ρ δ (j + 1) := by
            intro hp
            exact hp.1 (aux_tight_fixed_cutoff_restart_sig_succ_eq_top C ρ j p htop)
          rw [Set.indicator_of_notMem hnot]
      rw [← lintegral_indicator_one (aux_tight_fixed_cutoff_restart_measurableSet_gapEv C hC ρ δ _),
        lintegral_congr_ae hae, lintegral_indicator hSm]
      have hW : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
          (LifetimePath.isStoppingTime_exitTime (alpha := SpatialCoordinates d) U hU).measurableSpace]
          (fun _ : ContinuousPath (SpatialCoordinates d) => (1 : ℝ≥0∞)) := measurable_const
      have hg : Measurable ((aux_tight_fixed_cutoff_restart_gapEv C ρ δ j).indicator
          (1 : ContinuousPath (SpatialCoordinates d) → ℝ≥0∞)) := measurable_one.indicator hGm
      have hSMid := aux_tight_fixed_cutoff_restart_sm_weighted k L hL hSM U hU z _ hW _ hg
      rw [hSMid]
      calc ∫⁻ p in S, 1 * ∫⁻ q, (aux_tight_fixed_cutoff_restart_gapEv C ρ δ j).indicator 1 q
            ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k z
          ≤ ∫⁻ p in S, β ∂k z := by
            refine lintegral_mono fun p => ?_
            rw [one_mul, lintegral_indicator_one hGm]
            exact ih _
        _ ≤ ∫⁻ _p, β ∂k z := setLIntegral_le_lintegral _ _
        _ = β := by rw [lintegral_const, measure_univ, mul_one]
    · have h0' : k z (aux_tight_fixed_cutoff_restart_gapEv C ρ δ (j + 1)) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h0 z] with p hp0 hp
        have htex := aux_tight_fixed_cutoff_restart_tex_of_start C ρ p z hp0
        rw [ite_eq_right hz] at htex
        exact hp.1 (aux_tight_fixed_cutoff_restart_sig_succ_eq_top C ρ j p htex)
      rw [h0']; exact zero_le


/-! ### RtpCount3 -/

/-- Between two successive epochs the path stays within `ρ` of its value at the first one. -/


-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_dist_le_on_interval {d : ℕ} (C : Set (SpatialCoordinates d))
    {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) (p : DiffusionPath d)
    (hfin : aux_tight_fixed_cutoff_restart_sig C ρ j p ≠ ⊤)
    (hC : p (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal ∈ C) (t : ℝ≥0)
    (ht1 : aux_tight_fixed_cutoff_restart_sig C ρ j p ≤ t)
    (ht2 : (t : ℝ≥0∞) ≤ aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p) :
    dist (p t) (p (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal) ≤ ρ := by
  classical
  set a : ℝ≥0 := (aux_tight_fixed_cutoff_restart_sig C ρ j p).toNNReal with hadef
  have ha : (a : ℝ≥0∞) = aux_tight_fixed_cutoff_restart_sig C ρ j p := ENNReal.coe_toNNReal hfin
  set q := ContinuousPath.shift a p with hqdef
  have hq0 : q 0 = p a := by simp [hqdef, ContinuousPath.shift_apply]
  have htexq : aux_tight_fixed_cutoff_restart_tex C ρ q =
      ContinuousPath.exitTime (Metric.ball (q 0) ρ) q := by
    unfold aux_tight_fixed_cutoff_restart_tex aux_tight_fixed_cutoff_restart_ex
    rw [ite_eq_left (hq0 ▸ hC)]
  have hsucc : aux_tight_fixed_cutoff_restart_sig C ρ (j + 1) p =
      aux_tight_fixed_cutoff_restart_sig C ρ j p + aux_tight_fixed_cutoff_restart_tex C ρ q :=
    aux_tight_fixed_cutoff_restart_sig_succ C ρ j p
  have hat : a ≤ t := by
    have : (a : ℝ≥0∞) ≤ t := ha ▸ ht1
    exact_mod_cast this
  set u : ℝ≥0 := t - a with hudef
  have htu : t = a + u := (add_tsub_cancel_of_le hat).symm
  have hu : (u : ℝ≥0∞) ≤ aux_tight_fixed_cutoff_restart_tex C ρ q := by
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

/-- **Epochs control the modulus** (`tight:prop-tightness`).  If the path stays in `C` up to `T`, the
`n`-th epoch is after `T`, and every gap starting by `T` is longer than `δ`, then the
oscillation over `[0, T]` at scale `δ` is at most `3ρ`. -/


-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_modulus_of_epochs {d : ℕ} (C : Set (SpatialCoordinates d))
    {ρ : ℝ} (hρ : 0 < ρ) (T δ : ℝ≥0) (n : ℕ) (p : DiffusionPath d)
    (hstay : ∀ s : ℝ≥0, s ≤ T → p s ∈ C)
    (hn : (T : ℝ≥0∞) < aux_tight_fixed_cutoff_restart_sig C ρ n p)
    (hgap : ∀ j < n, aux_tight_fixed_cutoff_restart_sig C ρ j p ≤ T →
      p ∉ aux_tight_fixed_cutoff_restart_gapEv C ρ (δ : ℝ≥0∞) j) :
    p ∈ ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)) := by
  classical
  set σ := fun j => aux_tight_fixed_cutoff_restart_sig C ρ j p with hσdef
  -- the key two-point bound for `s ≤ t`
  have key : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → (t : ℝ) ≤ s + δ → dist (p s) (p t) ≤ 3 * ρ := by
    intro s t hst htT htsδ
    have hsT : s ≤ T := hst.trans htT
    have hex : ∃ i, (s : ℝ≥0∞) < σ (i + 1) := by
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [aux_tight_fixed_cutoff_restart_sig_zero] at hn
      refine ⟨n - 1, ?_⟩
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
      exact lt_of_le_of_lt (by exact_mod_cast hsT) hn
    set i := Nat.find hex with hidef
    have hi1 : (s : ℝ≥0∞) < σ (i + 1) := Nat.find_spec hex
    have hi0 : σ i ≤ s := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h]; simp [hσdef, aux_tight_fixed_cutoff_restart_sig_zero]
      · obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hlt : i' < Nat.find hex := by rw [← hidef]; omega
        have := Nat.find_min hex hlt
        rw [hi']
        exact not_lt.mp this
    have hin : i + 1 ≤ n := by
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp [aux_tight_fixed_cutoff_restart_sig_zero] at hn
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
      aux_tight_fixed_cutoff_restart_dist_le_on_interval C hρ i p hfin_i hCi s hi0 hi1.le
    by_cases hti : (t : ℝ≥0∞) ≤ σ (i + 1)
    · have hdt : dist (p t) (p (σ i).toNNReal) ≤ ρ :=
        aux_tight_fixed_cutoff_restart_dist_le_on_interval C hρ i p hfin_i hCi t
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
      have hlong : (δ : ℝ≥0∞) < aux_tight_fixed_cutoff_restart_tex C ρ
          (ContinuousPath.shift (σ (i + 1)).toNNReal p) := by
        by_contra hcon
        exact hg ⟨hfin1, not_lt.mp hcon⟩
      have hσ2 : σ (i + 2) = σ (i + 1) + aux_tight_fixed_cutoff_restart_tex C ρ
          (ContinuousPath.shift (σ (i + 1)).toNNReal p) :=
        aux_tight_fixed_cutoff_restart_sig_succ C ρ (i + 1) p
      have ht2 : (t : ℝ≥0∞) ≤ σ (i + 2) := by
        rw [hσ2]
        have htsδ' : (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) + δ := by
          have : t ≤ s + δ := by
            rw [← NNReal.coe_le_coe, NNReal.coe_add]; exact htsδ
          exact_mod_cast this
        calc (t : ℝ≥0∞) ≤ (s : ℝ≥0∞) + δ := htsδ'
          _ ≤ σ (i + 1) + aux_tight_fixed_cutoff_restart_tex C ρ
              (ContinuousPath.shift (σ (i + 1)).toNNReal p) := add_le_add hi1.le hlong.le
      have hdt : dist (p t) (p (σ (i + 1)).toNNReal) ≤ ρ :=
        aux_tight_fixed_cutoff_restart_dist_le_on_interval C hρ (i + 1) p hfin1 hC1 t hti.le ht2
      have hd1 : dist (p (σ (i + 1)).toNNReal) (p (σ i).toNNReal) ≤ ρ :=
        aux_tight_fixed_cutoff_restart_dist_le_on_interval C hρ i p hfin_i hCi _
          (by rw [ENNReal.coe_toNNReal hfin1]; exact aux_tight_fixed_cutoff_restart_sig_mono_succ C ρ i p)
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



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_modulus_bound {d : ℕ}
    (k : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel k]
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L) (h0 : ∀ z, ∀ᵐ p ∂k z, p 0 = z)
    (C : Set (SpatialCoordinates d)) (hC : MeasurableSet C) {ρ : ℝ} (hρ : 0 < ρ)
    (T δ : ℝ≥0) {h : ℝ} (hh : 0 < h) (γ : ℝ≥0∞)
    (hγ : ∀ y ∈ C, ∫⁻ p, aux_tight_fixed_cutoff_restart_wt h
      (ContinuousPath.exitTime (Metric.ball y ρ) p) ∂k y ≤ γ)
    (β : ℝ≥0∞)
    (hβ : ∀ y ∈ C, k y {p | ContinuousPath.exitTime (Metric.ball y ρ) p ≤ (δ : ℝ≥0∞)} ≤ β)
    (n : ℕ) (z : SpatialCoordinates d) :
    k z (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ ≤
      k z {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ C} +
        ENNReal.ofReal (Real.exp (T / h)) * γ ^ n + n * β := by
  set A : Set (DiffusionPath d) := {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ C} with hAdef
  set B : Set (DiffusionPath d) := {p | aux_tight_fixed_cutoff_restart_sig C ρ n p ≤ (T : ℝ≥0∞)}
    with hBdef
  have hBm : MeasurableSet B :=
    measurableSet_le (aux_tight_fixed_cutoff_restart_measurable_sig C hC ρ n) measurable_const
  have hsub : (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ ⊆
      A ∪ B ∪ ⋃ j ∈ Finset.range n, aux_tight_fixed_cutoff_restart_gapEv C ρ (δ : ℝ≥0∞) j := by
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨⟨hA, hB⟩, hG⟩ := hcon
    apply hp
    refine aux_tight_fixed_cutoff_restart_modulus_of_epochs C hρ T δ n p ?_ ?_ ?_
    · intro s hs
      by_contra hsC
      exact hA ⟨s, hs, hsC⟩
    · exact not_le.mp hB
    · intro j hj _
      exact hG j hj
  have hBbound : k z B ≤ ENNReal.ofReal (Real.exp (T / h)) * γ ^ n := by
    have hmom := aux_tight_fixed_cutoff_restart_sig_moment k L hL hSM h0 C hC ρ γ hγ n z
    calc k z B = ∫⁻ p, B.indicator 1 p ∂k z := (lintegral_indicator_one hBm).symm
      _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (T / h)) *
            aux_tight_fixed_cutoff_restart_wt h (aux_tight_fixed_cutoff_restart_sig C ρ n p) ∂k z := by
          refine lintegral_mono fun p => ?_
          by_cases hpB : p ∈ B
          · rw [Set.indicator_of_mem hpB, Pi.one_apply]
            have hw := aux_tight_fixed_cutoff_restart_wt_ge hh (T := (T : ℝ)) T.coe_nonneg
              (s := aux_tight_fixed_cutoff_restart_sig C ρ n p) (by
                rw [ENNReal.ofReal_coe_nnreal]; exact hpB)
            calc (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (T / h)) *
                  ENNReal.ofReal (Real.exp (-(T : ℝ) / h)) := by
                  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
                  simp [neg_div]
              _ ≤ _ := by gcongr
          · rw [Set.indicator_of_notMem hpB]; exact zero_le
      _ = ENNReal.ofReal (Real.exp (T / h)) * ∫⁻ p,
            aux_tight_fixed_cutoff_restart_wt h (aux_tight_fixed_cutoff_restart_sig C ρ n p) ∂k z :=
          lintegral_const_mul _ ((aux_tight_fixed_cutoff_restart_measurable_wt h).comp
            (aux_tight_fixed_cutoff_restart_measurable_sig C hC ρ n))
      _ ≤ _ := by gcongr
  have hgap := aux_tight_fixed_cutoff_restart_gap_prob k L hL hSM h0 C hC ρ (δ : ℝ≥0∞)
    ENNReal.coe_ne_top β hβ
  calc k z (ContinuousPath.modulusSet T (δ : ℝ≥0∞) (ENNReal.ofReal (3 * ρ)))ᶜ
      ≤ k z (A ∪ B ∪ ⋃ j ∈ Finset.range n, aux_tight_fixed_cutoff_restart_gapEv C ρ (δ : ℝ≥0∞) j) :=
        measure_mono hsub
    _ ≤ k z (A ∪ B) + k z (⋃ j ∈ Finset.range n,
          aux_tight_fixed_cutoff_restart_gapEv C ρ (δ : ℝ≥0∞) j) := measure_union_le _ _
    _ ≤ (k z A + k z B) + ∑ j ∈ Finset.range n,
          k z (aux_tight_fixed_cutoff_restart_gapEv C ρ (δ : ℝ≥0∞) j) :=
        add_le_add (measure_union_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ (k z A + ENNReal.ofReal (Real.exp (T / h)) * γ ^ n) + ∑ _j ∈ Finset.range n, β :=
        add_le_add (add_le_add le_rfl hBbound) (Finset.sum_le_sum fun j _ => hgap j z)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-! ### RtpModulus -/



-- Reused from `lem_resolvents_to_paths`.
theorem aux_tight_fixed_cutoff_restart_exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h4




/-- The compact-containment half of `tight_fixed_cutoff`, with only `LocalDiffusion`.
The proof reuses the existing Feller/strong-Markov argument. -/
theorem aux_tight_fixed_cutoff_containment
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ T : ℝ≥0, ∀ eta : ℝ≥0∞, 0 < eta →
          ∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta := by
  rcases hin with ⟨hres, hcons, hfdd⟩
  have hfell := aux_tight_fixed_cutoff_soft_feller M H PN KN ⟨hres, hcons, hfdd⟩
  filter_upwards [hfell, hLloc, hfdd] with omega hFe hLD hfdd
  intro N B hB T eta heta
  have : IsMarkovKernel (KN N) := hKN N
  set K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)) :=
    (KN N).comap (Prod.mk omega) measurable_prodMk_left with hKdef
  have hKapp : ∀ z, K z = KN N (omega, z) := fun z => Kernel.comap_apply _ _ _
  have hmap : ∀ (t : ℝ≥0) (x : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K x) = (PN N omega) t x := by
    intro t x
    rw [hKapp]
    simpa only [Kernel.map_apply] using!
      (SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
        (PN N omega) (KN N (omega, x)) x t
        (by
          have h := hfdd N ({t} : Finset ℝ≥0) x
          rw [Kernel.map_apply (KN N)
            (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0))] at h
          exact h))
  have hLz : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L N omega z := by
    intro z
    rw [hKapp]
    exact hL N omega z
  have hjoint : ∀ x, ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)) = K x := by
    intro x
    rw [hKapp]
    rfl
  by_cases hetop : eta = ⊤
  · exact ⟨∅, isCompact_empty, fun x _ => by rw [hetop]; exact le_top⟩
  obtain ⟨R, _hRpos, hR⟩ := aux_tight_fixed_cutoff_soft_containment (PN N omega) (hFe N) (hcons N omega)
    (⇑K) (fun z => inferInstance) hmap (L N omega) hLz (hLD N).1 B hB T eta.toReal
    (ENNReal.toReal_pos heta.ne' hetop)
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, fun x hx => ?_⟩
  rw [hjoint]
  refine (measure_mono ?_).trans ((hR x hx).trans (ENNReal.ofReal_toReal hetop).le)
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hp
  obtain ⟨s, hs, hsK⟩ := hp
  refine ⟨s, hs, ?_⟩
  have : R < dist (p s) 0 := by
    simpa only [Metric.mem_closedBall, not_le] using hsK
  exact this.le

/-- Uniform path-modulus specification, proved by
`aux_tight_fixed_cutoff_modulus` below from the conservative Feller
semigroup and strong Markov hypotheses. -/
def aux_tight_fixed_cutoff_modulus_goal : Prop :=
  ∀ (d : ℕ) (P : SubMarkovKernelSemigroup (SpatialCoordinates d)),
    P.IsFellerKernelSemigroup → P.IsConservative →
    ∀ (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d))),
    IsMarkovKernel K →
    (∀ (t : ℝ≥0) (x : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K x) = P t x) →
    ∀ (L : Kernel (SpatialCoordinates d) (Path d)),
    (∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = L x) →
    StrongMarkov L →
    ∀ (B : Set (SpatialCoordinates d)), IsCompact B →
    ∀ (T : ℝ≥0) (r : ℝ), 0 < r → ∀ eps : ℝ, 0 < eps →
    ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x ∈ B,
      K x (ContinuousPath.modulusSet T delta (ENNReal.ofReal r))ᶜ ≤ ENNReal.ofReal eps

/-- The Feller maximal inequality gives uniformly small exit probabilities on
compact starting sets; only strong Markov transport is needed. -/
theorem aux_tight_fixed_cutoff_short_exit {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hF : P.IsFellerKernelSemigroup)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)))
    [IsMarkovKernel K]
    (hmap : ∀ (t : ℝ≥0) (x : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K x) = P t x)
    (L : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = L x)
    (hSM : StrongMarkov L)
    (B : Set (SpatialCoordinates d)) (hB : IsCompact B)
    (rho eps : ℝ) (hrho : 0 < rho) (heps : 0 < eps) :
    ∃ h : ℝ≥0, 0 < h ∧ ∀ y ∈ B,
      K y {p | ContinuousPath.exitTime (Metric.ball y rho) p ≤ (h : ℝ≥0∞)} ≤
        ENNReal.ofReal eps := by
  obtain ⟨h, hh, hbound⟩ := aux_tight_fixed_cutoff_soft_small_time P hF (⇑K) (fun z => inferInstance)
    hmap L hL hSM B hB (rho / 2) (by positivity) eps heps
  refine ⟨h, hh, fun y hy => (measure_mono ?_).trans (hbound y hy)⟩
  intro p hp
  obtain ⟨⟨t, ht⟩, hnot⟩ :=
    (ContinuousPath.exitTime_le_iff_mem_hitsSetBy (Metric.ball y rho)
      Metric.isOpen_ball h p).1 hp
  refine ⟨t, ht, ?_⟩
  have hd : rho ≤ dist (p t) y := by
    exact le_of_not_gt (by simpa only [Metric.mem_ball] using! hnot)
  linarith only [hd]

/-- Uniform modulus on compact starting sets for any conservative Feller family
of continuous paths with strong Markov transport. The proof combines the soft
small-time inequality with the already proved successive-exit counting bound. -/
theorem aux_tight_fixed_cutoff_modulus : aux_tight_fixed_cutoff_modulus_goal := by
  intro d P hF hC K hK hmap L hL hSM B hB T r hr eps heps
  let : IsMarkovKernel K := hK
  set ρ : ℝ := r / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  obtain ⟨R, _hRpos, hR⟩ := aux_tight_fixed_cutoff_soft_containment P hF hC (⇑K)
    (fun z => inferInstance) hmap L hL hSM B hB T (eps / 3) (by positivity)
  set CR := Metric.closedBall (0 : SpatialCoordinates d) R with hCRdef
  have hCRc : IsCompact CR := isCompact_closedBall _ _
  have hCRm : MeasurableSet CR := Metric.isClosed_closedBall.measurableSet
  obtain ⟨h1, hh1, hN2⟩ := aux_tight_fixed_cutoff_short_exit P hF K hmap L hL hSM
    CR hCRc ρ (1 / 4) hρ (by norm_num)
  have hh1r : (0 : ℝ) < h1 := by exact_mod_cast hh1
  set hh : ℝ := (h1 : ℝ) / 2 with hhhdef
  have hhpos : 0 < hh := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 * Real.exp (T / hh) / eps)
    (by norm_num : (1 : ℝ) < 2)
  obtain ⟨h2, hh2, hN3⟩ := aux_tight_fixed_cutoff_short_exit P hF K hmap L hL hSM
    CR hCRc ρ (eps / (3 * ((n : ℝ) + 1))) hρ (by positivity)
  refine ⟨(h2 : ℝ≥0∞), ENNReal.coe_pos.mpr hh2, fun y hy => ?_⟩
  have h0k : ∀ z, ∀ᵐ p ∂K z, p 0 = z := aux_tight_fixed_cutoff_soft_start P (⇑K) hmap
  have hγ : ∀ z ∈ CR, ∫⁻ p, aux_tight_fixed_cutoff_restart_wt hh
      (ContinuousPath.exitTime (Metric.ball z ρ) p) ∂K z ≤ ENNReal.ofReal (1 / 2) := by
    intro z hz
    have hτm : Measurable (ContinuousPath.exitTime (Metric.ball z ρ) :
        ContinuousPath (SpatialCoordinates d) → ℝ≥0∞) :=
      ContinuousPath.measurable_exitTime _ Metric.isOpen_ball
    have hEm : MeasurableSet {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} := measurableSet_Iic
    calc ∫⁻ p, aux_tight_fixed_cutoff_restart_wt hh (ContinuousPath.exitTime (Metric.ball z ρ) p) ∂K z
        ≤ ∫⁻ p, ({s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator (1 : ℝ≥0∞ → ℝ≥0∞)
            (ContinuousPath.exitTime (Metric.ball z ρ) p) +
            ENNReal.ofReal (Real.exp (-(h1 : ℝ) / hh))) ∂K z :=
          lintegral_mono fun p => aux_tight_fixed_cutoff_restart_wt_le_split hhpos h1.coe_nonneg _
      _ = K z {p | ContinuousPath.exitTime (Metric.ball z ρ) p ≤ (h1 : ℝ≥0∞)} +
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
          refine add_le_add (hN2 z hz) (ENNReal.ofReal_le_ofReal ?_)
          have : -(h1 : ℝ) / hh = -2 := by rw [hhhdef]; field_simp
          rw [this]; exact aux_tight_fixed_cutoff_restart_exp_neg_two_le
      _ = ENNReal.ofReal (1 / 2) := by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hβ : ∀ z ∈ CR, K z {p | ContinuousPath.exitTime (Metric.ball z ρ) p ≤ (h2 : ℝ≥0∞)} ≤
      ENNReal.ofReal (eps / (3 * ((n : ℝ) + 1))) := hN3
  have hbound := aux_tight_fixed_cutoff_restart_modulus_bound K L hL hSM h0k CR hCRm
    hρ T h2 hhpos (ENNReal.ofReal (1 / 2)) hγ _ hβ n y
  have hA : K y {p | ∃ s : ℝ≥0, s ≤ T ∧ p s ∉ CR} ≤ ENNReal.ofReal (eps / 3) := by
    refine (measure_mono ?_).trans (hR y hy)
    rintro p ⟨t, ht, hnot⟩
    refine ⟨t, ht, ?_⟩
    have : R < dist (p t) 0 := by simpa only [hCRdef, Metric.mem_closedBall, not_le] using! hnot
    exact this.le
  have hpow : ENNReal.ofReal (Real.exp (T / hh)) * ENNReal.ofReal (1 / 2) ^ n ≤
      ENNReal.ofReal (eps / 3) := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ h2n]
    rw [div_lt_iff₀ heps] at hn
    nlinarith
  have hsum : (n : ℝ≥0∞) * ENNReal.ofReal (eps / (3 * ((n : ℝ) + 1))) ≤ ENNReal.ofReal (eps / 3) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3ρ : 3 * ρ = r := by rw [hρdef]; ring
  rw [h3ρ] at hbound
  calc K y (ContinuousPath.modulusSet T (h2 : ℝ≥0∞) (ENNReal.ofReal r))ᶜ
      ≤ _ := hbound
    _ ≤ ENNReal.ofReal (eps / 3) + ENNReal.ofReal (eps / 3) + ENNReal.ofReal (eps / 3) :=
        add_le_add (add_le_add hA hpow) hsum
    _ = ENNReal.ofReal eps := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- Conditional assembly only: proving `aux_tight_fixed_cutoff_modulus_goal`
closes the exact principal conclusion. The additional premise is an explicit
remaining goal, and this helper is not the principal theorem. -/
theorem aux_tight_fixed_cutoff_of_modulus
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (hmod : aux_tight_fixed_cutoff_modulus_goal) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ T : ℝ≥0, ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
          (∃ delta : ℝ≥0∞, 0 < delta ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
          (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta) := by
  rcases hin with ⟨hres, hcons, hfdd⟩
  have hfell := aux_tight_fixed_cutoff_soft_feller M H PN KN ⟨hres, hcons, hfdd⟩
  filter_upwards [hfell, hLloc, hfdd] with omega hFe hLD hfdd
  intro N B hB T r hr eta heta
  have : IsMarkovKernel (KN N) := hKN N
  set K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)) :=
    (KN N).comap (Prod.mk omega) measurable_prodMk_left with hKdef
  have hKapp : ∀ z, K z = KN N (omega, z) := fun z => Kernel.comap_apply _ _ _
  have hmap : ∀ (t : ℝ≥0) (x : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (K x) = (PN N omega) t x := by
    intro t x
    rw [hKapp]
    simpa only [Kernel.map_apply] using!
      (SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
        (PN N omega) (KN N (omega, x)) x t
        (by
          have h := hfdd N ({t} : Finset ℝ≥0) x
          rw [Kernel.map_apply (KN N)
            (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0))] at h
          exact h))
  have hLz : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L N omega z := by
    intro z
    rw [hKapp]
    exact hL N omega z
  have hjoint : ∀ x, ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
      ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d)) = K x := by
    intro x
    rw [hKapp]
    rfl
  refine ⟨?_, ?_⟩
  · by_cases hrtop : r = ⊤
    · refine ⟨1, one_pos, fun x _ => ?_⟩
      have huniv : ContinuousPath.modulusSet (alpha := SpatialCoordinates d) T 1 r =
          Set.univ := by
        ext p
        simp [ContinuousPath.modulusSet, hrtop]
      rw [hjoint, huniv, Set.compl_univ, measure_empty]
      exact zero_le
    by_cases hetop : eta = ⊤
    · exact ⟨1, one_pos, fun x _ => by rw [hetop]; exact le_top⟩
    obtain ⟨delta, hdpos, hdel⟩ := hmod d (PN N omega) (hFe N) (hcons N omega) K inferInstance
      hmap (L N omega) hLz (hLD N).1 B hB T r.toReal
      (ENNReal.toReal_pos hr.ne' hrtop) eta.toReal (ENNReal.toReal_pos heta.ne' hetop)
    refine ⟨delta, hdpos, fun x hx => ?_⟩
    rw [hjoint]
    have hx' := hdel x hx
    rwa [ENNReal.ofReal_toReal hrtop, ENNReal.ofReal_toReal hetop] at hx'
  · by_cases hetop : eta = ⊤
    · exact ⟨∅, isCompact_empty, fun x _ => by rw [hetop]; exact le_top⟩
    obtain ⟨R, _hRpos, hR⟩ := aux_tight_fixed_cutoff_soft_containment (PN N omega) (hFe N) (hcons N omega)
      (⇑K) (fun z => inferInstance) hmap (L N omega) hLz (hLD N).1 B hB T eta.toReal
      (ENNReal.toReal_pos heta.ne' hetop)
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, fun x hx => ?_⟩
    rw [hjoint]
    refine (measure_mono ?_).trans ((hR x hx).trans (ENNReal.ofReal_toReal hetop).le)
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hp
    obtain ⟨s, hs, hsK⟩ := hp
    refine ⟨s, hs, ?_⟩
    have : R < dist (p s) 0 := by
      simpa [Metric.mem_closedBall, not_le] using hsK
    exact this.le


/-- Proof step of `tight:prop-tightness`: at each fixed cutoff the coefficients
are smooth, and the quenched path laws are almost surely tight uniformly over compact starting
sets.  The conclusion is literally that of `finite_cutoff_local_path_bounds`, but the process
input is the heat-kernel-free `LocalDiffusion` package instead of `LocalDiffusionData`, and no
disorder threshold is needed. -/
theorem tight_fixed_cutoff
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ T : ℝ≥0, ∀ r : ℝ≥0∞, 0 < r → ∀ eta : ℝ≥0∞, 0 < eta →
          (∃ delta : ℝ≥0∞, 0 < delta ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                (ContinuousPath.modulusSet T delta r)ᶜ ≤ eta) ∧
          (∃ K0 : Set (SpatialCoordinates d), IsCompact K0 ∧
            ∀ x ∈ B,
              ((jointPathProbabilityMeasure (KN N) (hKN N) omega x :
                ProbabilityMeasure (DiffusionPath d)) : Measure (DiffusionPath d))
                {path : DiffusionPath d | ∀ s : ℝ≥0, s ≤ T → path s ∈ K0}ᶜ ≤ eta) := by
  exact aux_tight_fixed_cutoff_of_modulus hd M H hH PN KN hKN hin L hL hLloc
    aux_tight_fixed_cutoff_modulus


end SubdiffusiveProcess.Paper






