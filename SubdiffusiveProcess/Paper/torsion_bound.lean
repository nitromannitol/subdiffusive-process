module

public import SubdiffusiveProcess.Paper.tight_fixed_cutoff
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import MarkovProcess.Trajectory.ExpectedExitTime
public import Mathlib.MeasureTheory.Measure.OpenPos
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
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
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.cube_exhaustion
public import SubdiffusiveProcess.Paper.cutoff_campanato_bound
public import SubdiffusiveProcess.Paper.lem_as_coarse
public import SubdiffusiveProcess.Paper.lem_as_regularity
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.MultiplicativeChaos.ExitMoment
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_cutoff_oscillation
public import SubdiffusiveProcess.Paper.killed_zero_extension_bound
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.Model.LifetimeProcess
public import MarkovProcess.Killed.Nested
public import MarkovProcess.Lifetime.ExitTime
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_torsion_bound_exit_survival_open
    {E : Type*} [PseudoMetricSpace E] (U : Set E) (hU : IsOpen U) (t : ℝ≥0) :
    IsOpen {p : ContinuousPath E | (t : ℝ≥0∞) < ContinuousPath.exitTime U p} := by
  have heq : {p : ContinuousPath E | (t : ℝ≥0∞) < ContinuousPath.exitTime U p} =
      {p : ContinuousPath E | Set.MapsTo p (Set.Iic t) U} := by
    ext p
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← not_le,
      ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t p]
    simp only [ContinuousPath.hitsSetBy, Set.mem_ofPred_eq, not_exists,
      Set.mem_compl_iff, not_not, Set.MapsTo, Subtype.forall, Set.mem_Iic]
  rw [heq]
  exact ContinuousMap.isOpen_setOfPred_mapsTo (by simpa only [Set.Icc_bot] using
    (isCompact_Icc : IsCompact (Set.Icc (⊥ : ℝ≥0) t))) hU

theorem aux_torsion_bound_exit_lsc
    {E : Type*} [PseudoMetricSpace E] (U : Set E) (hU : IsOpen U) :
    LowerSemicontinuous (ContinuousPath.exitTime U) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro t
  rcases eq_or_ne t ⊤ with rfl | ht
  · simpa only [Set.preimage, Set.mem_Ioi, not_top_lt, Set.ofPred_false] using isOpen_empty
  · lift t to ℝ≥0 using ht
    exact aux_torsion_bound_exit_survival_open U hU t

/-- Portmanteau for nonnegative lower semicontinuous real functions. -/
theorem aux_torsion_bound_lintegral_le_liminf
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {μs : ℕ → Measure E} {f : E → ℝ}
    (hf : LowerSemicontinuous f) (hfn : ∀ x, 0 ≤ f x)
    (hopen : ∀ G, IsOpen G → μ G ≤ liminf (fun n => μs n G) atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂(μs n)) atTop := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hfn)
    hf.measurable.aemeasurable]
  refine (lintegral_mono (fun t => hopen _ (hf.isOpen_preimage t))).trans ?_
  exact lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
    measure_mono (fun x hx => lt_of_le_of_lt hst hx)))

theorem aux_torsion_bound_lintegral_lsc
    {X E : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (P : X → ProbabilityMeasure E) (hP : Continuous P)
    (f : E → ℝ) (hf : LowerSemicontinuous f) (hfn : ∀ x, 0 ≤ f x) :
    LowerSemicontinuous (fun x => ∫⁻ p, ENNReal.ofReal (f p) ∂(P x : Measure E)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  apply IsSeqClosed.isClosed
  intro u x hu hx
  exact (aux_torsion_bound_lintegral_le_liminf hf hfn
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      ((hP.tendsto x).comp hx) hG)).trans
    (liminf_le_of_frequently_le (Frequently.of_forall hu))

/-- Full support upgrades an a.e. upper bound for an l.s.c. function on an open set. -/
theorem aux_torsion_bound_lsc_le_of_ae
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f)
    {U : Set X} (hU : IsOpen U) {C : ℝ≥0∞}
    (hae : ∀ᵐ x ∂μ.restrict U, f x ≤ C) :
    ∀ x ∈ U, f x ≤ C := by
  intro x hx
  by_contra h
  have hopen : IsOpen (U ∩ {x | C < f x}) := hU.inter (hf.isOpen_preimage C)
  have hzero : μ (U ∩ {x | C < f x}) = 0 := by
    rw [ae_iff] at hae
    rw [Measure.restrict_apply₀] at hae
    · simpa only [not_le, Set.inter_comm] using hae
    · simpa only [not_le] using! (hf.isOpen_preimage C).nullMeasurableSet
        (μ := μ.restrict U)
  exact (hopen.measure_ne_zero μ ⟨x, hx, lt_of_not_ge h⟩) hzero

theorem aux_torsion_bound_truncated_exit_lsc
    {E : Type*} [PseudoMetricSpace E] (U : Set E) (hU : IsOpen U) (T : ℝ≥0) :
    LowerSemicontinuous (fun p : ContinuousPath E =>
      (min (ContinuousPath.exitTime U p) (T : ℝ≥0∞)).toReal) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  by_cases hr : 0 ≤ r
  · have heq : (fun p : ContinuousPath E =>
        (min (ContinuousPath.exitTime U p) (T : ℝ≥0∞)).toReal) ⁻¹' Set.Ioi r =
        (fun p => min (ContinuousPath.exitTime U p) (T : ℝ≥0∞)) ⁻¹'
          Set.Ioi (ENNReal.ofReal r) := by
      ext p
      exact (ENNReal.ofReal_lt_iff_lt_toReal hr
        (ne_of_lt ((min_le_right _ _).trans_lt ENNReal.coe_lt_top))).symm
    rw [heq]
    exact ((aux_torsion_bound_exit_lsc U hU).inf lowerSemicontinuous_const).isOpen_preimage _
  · have heq : (fun p : ContinuousPath E =>
        (min (ContinuousPath.exitTime U p) (T : ℝ≥0∞)).toReal) ⁻¹' Set.Ioi r = Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact (lt_of_not_ge hr).trans_le ENNReal.toReal_nonneg
    rw [heq]
    exact isOpen_univ

theorem aux_torsion_bound_expected_truncated_exit_lsc
    {X E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [PseudoMetricSpace E]
    [HasOuterApproxClosed (ContinuousPath E)]
    (P : X → ProbabilityMeasure (ContinuousPath E)) (hP : Continuous P)
    (U : Set E) (hU : IsOpen U) (T : ℝ≥0) :
    LowerSemicontinuous (fun x =>
      ∫⁻ p, min (ContinuousPath.exitTime U p) (T : ℝ≥0∞) ∂(P x : Measure _)) := by
  have heq : (fun p : ContinuousPath E =>
      ENNReal.ofReal (min (ContinuousPath.exitTime U p) (T : ℝ≥0∞)).toReal) =
      fun p => min (ContinuousPath.exitTime U p) (T : ℝ≥0∞) := by
    funext p
    exact ENNReal.ofReal_toReal (ne_of_lt ((min_le_right _ _).trans_lt ENNReal.coe_lt_top))
  have h := aux_torsion_bound_lintegral_lsc P hP _
    (aux_torsion_bound_truncated_exit_lsc U hU T) (fun _ => ENNReal.toReal_nonneg)
  rwa [heq] at h

theorem aux_torsion_bound_expected_exit_lsc
    {X E : Type*} [TopologicalSpace X] [FirstCountableTopology X] [PseudoMetricSpace E]
    [HasOuterApproxClosed (ContinuousPath E)]
    (P : X → ProbabilityMeasure (ContinuousPath E)) (hP : Continuous P)
    (U : Set E) (hU : IsOpen U) :
    LowerSemicontinuous (fun x =>
      ∫⁻ p, ContinuousPath.exitTime U p ∂(P x : Measure _)) := by
  have heq : (fun x => ∫⁻ p, ContinuousPath.exitTime U p ∂(P x : Measure _)) =
      fun x => ⨆ n : ℕ, ∫⁻ p, min (ContinuousPath.exitTime U p) (n : ℝ≥0∞)
        ∂(P x : Measure _) := by
    funext x
    have hsup : (fun p : ContinuousPath E => ContinuousPath.exitTime U p) =
        fun p => ⨆ n : ℕ, min (ContinuousPath.exitTime U p) (n : ℝ≥0∞) := by
      funext p
      simpa only [ContinuousPath.coe_exitTimeTrunc_ennreal, ENNReal.coe_natCast]
        using (ContinuousPath.iSup_exitTimeTrunc U p).symm
    rw [hsup]
    exact lintegral_iSup
      (fun n => ((aux_torsion_bound_exit_lsc U hU).inf lowerSemicontinuous_const).measurable)
      (fun m n hmn p => min_le_min_left _ (by exact_mod_cast hmn))
  rw [heq]
  exact lowerSemicontinuous_iSup fun n =>
    aux_torsion_bound_expected_truncated_exit_lsc P hP U hU n





/--  The standing exponent gives `1/4 ≤ 1/2 - (d+2)ε`. -/
theorem aux_torsion_bound_quarter_le (d : ℕ) (epsilon : ℝ)
    (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) (1 / (8 * ((d : ℝ) + 2)))) :
    1 / 4 ≤ 1 / 2 - ((d : ℝ) + 2) * epsilon := by
  obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hepsilon
  have hpos : (0 : ℝ) < 8 * ((d : ℝ) + 2) := by positivity
  have h2 : epsilon * (8 * ((d : ℝ) + 2)) < 1 := (lt_div_iff₀ hpos).mp h1
  nlinarith [h2, h0, hpos]

/--  The `L²` norm on a cube is controlled by the
cube-normalized fractional norm. -/
theorem aux_torsion_bound_L2_le_cubeFractional {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) :
    ‖v‖ ^ 2 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm hd z r hr s v := by
  have hV : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d := by
    rw [measureReal_def, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
  have hVpos : 0 < r ^ d := pow_pos hr d
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq
  rw [Fin.sum_univ_one, hV]
  rw [mul_add, mul_div_cancel₀ _ hVpos.ne']
  exact le_add_of_nonneg_left (mul_nonneg hVpos.le (sq_nonneg _))

/--  Every point of an open cube of side `s` is within
sup-distance `s` of a point outside it. -/
theorem aux_torsion_bound_exists_outside {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z s hs : Set (SpatialCoordinates d))) :
    ∃ y : SpatialCoordinates d,
      y ∉ (centeredCube z s hs : Set (SpatialCoordinates d)) ∧ dist x y ≤ s := by
  have hd1 : 0 < d := by omega
  let i0 : Fin d := ⟨0, hd1⟩
  have hx_i0 : z i0 - s / 2 < x i0 ∧ x i0 < z i0 + s / 2 := by
    have hmem : x ∈ Set.univ.pi (fun i => Set.Ioo (z i - s / 2) (z i + s / 2)) := by
      have h := hx
      rw [centeredCube_eq_pi] at h
      exact h
    exact Set.mem_Ioo.mp (Set.mem_univ_pi.mp hmem i0)
  refine ⟨Function.update x i0 (z i0 + s / 2), ?_, ?_⟩
  · intro hy
    rw [centeredCube_eq_pi] at hy
    have h := Set.mem_univ_pi.mp hy i0
    rw [Set.mem_Ioo] at h
    rw [Function.update_self] at h
    exact (lt_irrefl (z i0 + s / 2)) h.2
  · rw [dist_pi_le_iff hs.le]
    intro i
    by_cases hi : i = i0
    · rw [hi, Function.update_self, Real.dist_eq, abs_le]
      constructor <;> linarith [hx_i0.1, hx_i0.2]
    · rw [Function.update_of_ne hi, dist_self]
      exact hs.le

/--  Chaining a local Hölder bound at distances at most
one along a segment. -/
theorem aux_torsion_bound_chain {d : ℕ} (v : SpatialCoordinates d → ℝ) (C alpha : ℝ)
    (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hhol : ∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
      |v x - v y| ≤ C * dist x y ^ alpha) :
    ∀ (n : ℕ) (x y : SpatialCoordinates d), dist x y ≤ (n : ℝ) + 1 →
      |v x - v y| ≤ ((n : ℝ) + 1) * C := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      have h1 : dist x y ≤ 1 := by simpa using hxy
      have hpow : dist x y ^ alpha ≤ 1 := Real.rpow_le_one dist_nonneg h1 halpha.le
      have hbase := hhol x y h1
      calc |v x - v y| ≤ C * dist x y ^ alpha := hbase
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
        _ = (((0 : ℕ) : ℝ) + 1) * C := by ring
  | succ n ih =>
      intro x y hxy
      set c : ℝ := 1 / ((n : ℝ) + 2) with hcdef
      let p : SpatialCoordinates d := AffineMap.lineMap x y c
      have hd2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hcpos : 0 < c := by rw [hcdef]; positivity
      have h1c : 0 < 1 - c := by
        rw [sub_pos, hcdef, div_lt_one hd2pos]; linarith
      have hxy2 : dist x y ≤ (n : ℝ) + 2 := by
        have h := hxy; rw [Nat.cast_succ] at h; linarith
      have hxp : dist x p = c * dist x y := by
        change dist x (AffineMap.lineMap x y c) = c * dist x y
        rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos hcpos]
      have hpy : dist p y = (1 - c) * dist x y := by
        change dist (AffineMap.lineMap x y c) y = (1 - c) * dist x y
        rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_pos h1c]
      have hdistxp1 : dist x p ≤ 1 := by
        rw [hxp, hcdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ hd2pos]
        linarith
      have hdistpy1 : dist p y ≤ (n : ℝ) + 1 := by
        rw [hpy, hcdef]
        have hcoef : 0 ≤ 1 - 1 / ((n : ℝ) + 2) := by
          rw [sub_nonneg, div_le_one hd2pos]; linarith
        calc (1 - 1 / ((n : ℝ) + 2)) * dist x y
            ≤ (1 - 1 / ((n : ℝ) + 2)) * ((n : ℝ) + 2) :=
              mul_le_mul_of_nonneg_left hxy2 hcoef
          _ = (n : ℝ) + 1 := by
              rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hd2pos)]; ring
      have hxp_est : |v x - v p| ≤ C := by
        have hh := hhol x p hdistxp1
        calc |v x - v p| ≤ C * dist x p ^ alpha := hh
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left
              (Real.rpow_le_one dist_nonneg hdistxp1 halpha.le) hC
          _ = C := by ring
      have hpy_est : |v p - v y| ≤ (n : ℝ) * C + C := by
        have hh := ih p y hdistpy1
        calc |v p - v y| ≤ ((n : ℝ) + 1) * C := hh
          _ = (n : ℝ) * C + C := by ring
      calc |v x - v y| ≤ |v x - v p| + |v p - v y| := abs_sub_le _ _ _
        _ ≤ C + ((n : ℝ) * C + C) := add_le_add hxp_est hpy_est
        _ = (((n.succ : ℕ) : ℝ) + 1) * C := by push_cast; ring

/-- Discounted survival bound (`mfd:cor-finite-exit`, lambda to 0 by monotone convergence).  A bound `B` on every
discounted survival integral of a probability law on paths bounds its mean exit time. -/
theorem aux_torsion_bound_exit_le_of_survival_le {d : ℕ}
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q)
    (nu : Measure (DiffusionPath d)) [IsProbabilityMeasure nu] (B : ℝ) (_hB : 0 ≤ B)
    (hsurv : ∀ k : ℕ,
      ∫ path, survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q path) ∂nu ≤ B) :
    ∫⁻ path, ContinuousPath.exitTime Q path ∂nu ≤ ENNReal.ofReal B := by
  have hmeas : ∀ k, Measurable (fun (p : DiffusionPath d) =>
      ENNReal.ofReal (survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q p))) := by
    intro k
    have hmeas_surv : Measurable (survivalIntegral (discountSeq k)) :=
      measurable_survivalIntegral (discountSeq_pos k)
    have hmeas_exit : Measurable (ContinuousPath.exitTime Q) :=
      ContinuousPath.measurable_exitTime Q hQ
    exact (ENNReal.measurable_ofReal.comp (hmeas_surv.comp hmeas_exit))
  have hmono : ∀ k l, k ≤ l → ∀ p, ENNReal.ofReal (survivalIntegral (discountSeq k)
      (ContinuousPath.exitTime Q p)) ≤ ENNReal.ofReal (survivalIntegral (discountSeq l)
      (ContinuousPath.exitTime Q p)) := by
    intro k l hkl p
    refine ENNReal.ofReal_le_ofReal (monotone_survivalIntegral (ContinuousPath.exitTime Q p) hkl)
  have hint : ∀ k, Integrable (fun (p : DiffusionPath d) =>
      survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q p)) nu := by
    intro k
    have hbound : ∀ p, survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q p) ≤ (discountSeq k)⁻¹ :=
      fun p => survivalIntegral_le_inv (discountSeq_pos k) (ContinuousPath.exitTime Q p)
    have h_int : Integrable (fun _ : DiffusionPath d => (discountSeq k)⁻¹) nu :=
      integrable_const _
    have hmeas_surv' : Measurable (survivalIntegral (discountSeq k)) :=
      measurable_survivalIntegral (discountSeq_pos k)
    have hmeas_exit' : Measurable (ContinuousPath.exitTime Q) :=
      ContinuousPath.measurable_exitTime Q hQ
    have hmeas : Measurable (fun (p : DiffusionPath d) =>
        survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q p)) :=
      hmeas_surv'.comp hmeas_exit'
    have h_norm : ∀ᵐ p ∂nu, ‖survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q p)‖ ≤
        (fun _ : DiffusionPath d => (discountSeq k)⁻¹) p := by
      filter_upwards with p
      simp [hbound p, abs_of_nonneg (survivalIntegral_nonneg _ _)]
    refine (h_int.mono' hmeas.aestronglyMeasurable h_norm)
  have h_mono_seq : Monotone (fun (k : ℕ) (p : DiffusionPath d) =>
      ENNReal.ofReal (survivalIntegral (discountSeq k) (ContinuousPath.exitTime Q p))) := by
    intro k l hkl p
    refine ENNReal.ofReal_le_ofReal (monotone_survivalIntegral (ContinuousPath.exitTime Q p) hkl)
  calc
    ∫⁻ path, ContinuousPath.exitTime Q path ∂nu
        = ∫⁻ path, (⨆ k : ℕ, ENNReal.ofReal (survivalIntegral (discountSeq k)
            (ContinuousPath.exitTime Q path))) ∂nu := by
      refine lintegral_congr_ae ?_
      filter_upwards with p
      simp [iSup_ofReal_survivalIntegral]
    _ = ⨆ k : ℕ, ∫⁻ path, ENNReal.ofReal (survivalIntegral (discountSeq k)
        (ContinuousPath.exitTime Q path)) ∂nu := by
      refine lintegral_iSup hmeas h_mono_seq
    _ = ⨆ k : ℕ, ENNReal.ofReal (∫ path, survivalIntegral (discountSeq k)
        (ContinuousPath.exitTime Q path) ∂nu) := by
      refine iSup_congr fun k => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
        (ae_of_all _ (fun p => survivalIntegral_nonneg _ _))]
    _ ≤ ⨆ k : ℕ, ENNReal.ofReal B := by
      refine iSup_mono fun k => ENNReal.ofReal_le_ofReal (hsurv k)
    _ = ENNReal.ofReal B := by
      simp

/-- Finite-chain supremum bound (`mfd:cor-finite-exit` `mfd:cor-finite-exit`: "finite chains across the fixed supporting cube give
the supremum bound").  A function vanishing off the open cube of side `s` and locally
`alpha`-Hölder at distances at most one with constant `C` is bounded by `C * (s + 2)`.
Follows from the lemmas `aux_torsion_bound_exists_outside` and
`aux_torsion_bound_chain`. -/
theorem aux_torsion_bound_abs_le_of_local_holder {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (v : SpatialCoordinates d → ℝ) (C alpha : ℝ) (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hzero : ∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), v x = 0)
    (hhol : ∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
      |v x - v y| ≤ C * dist x y ^ alpha) :
    ∀ x : SpatialCoordinates d, |v x| ≤ C * (s + 2) := by
  intro x
  have hCs : 0 ≤ C * (s + 2) := mul_nonneg hC (by linarith)
  by_cases hx : x ∈ (centeredCube z s hs : Set (SpatialCoordinates d))
  · obtain ⟨y, hy, hxy⟩ := aux_torsion_bound_exists_outside hd z s hs x hx
    have hceil : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    have hceil2 : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one hs.le
    have hch := aux_torsion_bound_chain v C alpha hC halpha hhol ⌈s⌉₊ x y (by linarith)
    rw [hzero y hy, sub_zero] at hch
    calc |v x| ≤ ((⌈s⌉₊ : ℝ) + 1) * C := hch
      _ ≤ (s + 2) * C := mul_le_mul_of_nonneg_right (by linarith) hC
      _ = C * (s + 2) := mul_comm _ _
  · rw [hzero x hx, abs_zero]
    exact hCs

/-- Uses `aux_prop_uniform_resolvent_camp_holder` and the preceding two estimates.  Fixed environment and cube: a Campanato
oscillation bound on the zero-extended representatives `w N lam`, uniform in the cutoff and the
discount, plus the a.e. and pointwise identifications, bound every finite-cutoff mean exit time
from the cube. -/
theorem aux_torsion_bound_fixed_omega {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (Kx : ℕ → SpatialCoordinates d → Measure (DiffusionPath d))
    (hKx : ∀ N x, IsProbabilityMeasure (Kx N x))
    (w : ℕ → ℝ → DomainL2 (centeredCube z s hs))
    (Cc A beta : ℝ) (hCc : 0 < Cc) (hA : 0 ≤ A) (hbeta : 1 / 4 ≤ beta)
    (hC : ∀ (z' : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
        (u : SpatialCoordinates d → ℝ) (A' : ℝ), 0 ≤ A' →
        LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
        (∀ x ∉ (centeredCube z' rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
        (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
              (u y - (volume.real (Metric.ball x r))⁻¹ *
                ∫ w in Metric.ball x r, u w) ^ 2) ≤
            A' ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ))) →
        ∃ v : SpatialCoordinates d → ℝ,
          v =ᵐ[volume] u ∧
          (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
            |v x - v y| ≤ Cc * A' * dist x y ^ (1 / 4 : ℝ)) ∧
          ∀ x ∉ (centeredCube z' rQ hrQ : Set (SpatialCoordinates d)), v x = 0)
    (hosc : ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
        (∫ y in Metric.ball x r,
          (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
              (fun y => w N lam y) y -
            (volume.real (Metric.ball x r))⁻¹ *
              ∫ w' in Metric.ball x r,
                Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                  (fun y => w N lam y) w') ^ 2) ≤
          A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * beta))
    (hfin : ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      (fun x => ∫ path, survivalIntegral lam
          (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path)
          ∂(Kx N x))
        =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (w N lam : SpatialCoordinates d → ℝ))
    (hlsc : ∀ N, LowerSemicontinuous (fun x =>
      ∫⁻ path, ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path
        ∂(Kx N x))) :
    ∀ (N : ℕ), ∀ x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)),
      ∫⁻ path, ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path
          ∂(Kx N x) ≤ ENNReal.ofReal (Cc * A * (s + 2)) := by
  intro N x hx
  have hQo : IsOpen (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    (centeredCube z s hs).isOpen
  have hQm : MeasurableSet (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    hQo.measurableSet
  have := hKx N x
  have hB : 0 ≤ Cc * A * (s + 2) := by
    have : 0 ≤ s + 2 := by linarith
    positivity
  have hdisc : ∀ k : ℕ, ∀ᵐ y ∂volume.restrict
      (centeredCube z s hs : Set (SpatialCoordinates d)),
      ∫ path, survivalIntegral (discountSeq k)
        (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path)
        ∂(Kx N y) ≤ Cc * A * (s + 2) := by
    intro k
    obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := aux_prop_uniform_resolvent_camp_holder z s hs Cc hC
      beta hbeta A hA (w N (discountSeq k)) (hosc N (discountSeq k) (discountSeq_pos k))
    have hvRN : v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
        fun y => ∫ path, survivalIntegral (discountSeq k)
          (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path)
          ∂(Kx N y) := by
      have h1 : v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (w N (discountSeq k) : SpatialCoordinates d → ℝ) := by
        filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem hQm] with y hy1 hy2
        rw [hy1, Set.indicator_of_mem hy2]
      exact h1.trans (hfin N (discountSeq k) (discountSeq_pos k)).symm
    filter_upwards [hvRN] with y hy
    rw [← hy]
    have hsup := aux_torsion_bound_abs_le_of_local_holder hd z s hs v (Cc * A) (1 / 4)
      (mul_nonneg hCc.le hA) (by norm_num) hv0 hvhol y
    exact (le_abs_self _).trans hsup
  have hmean : ∀ᵐ y ∂volume.restrict
      (centeredCube z s hs : Set (SpatialCoordinates d)),
      ∫⁻ path, ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path
        ∂(Kx N y) ≤ ENNReal.ofReal (Cc * A * (s + 2)) := by
    filter_upwards [ae_all_iff.mpr hdisc] with y hy
    have := hKx N y
    exact aux_torsion_bound_exit_le_of_survival_le _ hQo (Kx N y) _ hB hy
  exact aux_torsion_bound_lsc_le_of_ae volume (hlsc N) hQo hmean x hx


/-- Plumbing : at a fixed environment the discounted killed survival
resolvent of the cube is square integrable on the cube (it is measurable and bounded by
`lam⁻¹`). -/
theorem aux_torsion_bound_resolvent_memLp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (omega : BilateralField d) (lam : ℝ) (hlam : 0 < lam) :
    MemLp (fun x => ∫ path, survivalIntegral lam
        (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path)
        ∂(K (omega, x)))
      2 (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))) := by
  have hQo : IsOpen (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    (centeredCube z s hs).isOpen
  have hQfin : volume (centeredCube z s hs : Set (SpatialCoordinates d)) ≠ ∞ :=
    (centeredCube_isBounded z hs).measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.2 hQfin
  have hg : Measurable (fun q : SpatialCoordinates d × DiffusionPath d =>
      survivalIntegral lam
        (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) q.2)) :=
    (measurable_survivalIntegral hlam).comp
      ((ContinuousPath.measurable_exitTime _ hQo).comp measurable_snd)
  have hsm := hg.stronglyMeasurable.integral_kernel_prod_right'' (η := K) (a := omega)
  refine MemLp.of_bound hsm.aestronglyMeasurable lam⁻¹ (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun p => survivalIntegral_nonneg _ _)]
  calc (∫ path, survivalIntegral lam
          (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) path)
          ∂(K (omega, x)))
        ≤ ∫ _path, lam⁻¹ ∂(K (omega, x)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => survivalIntegral_nonneg _ _)
            (integrable_const _)
            (Filter.Eventually.of_forall fun p => survivalIntegral_le_inv hlam _)
    _ = lam⁻¹ := by simp

/-- Plumbing : the square-mean oscillation bound of a zero extension depends
only on the a.e. class of the function on the cube. -/
theorem aux_torsion_bound_osc_congr {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : MeasurableSet Q) (f g : SpatialCoordinates d → ℝ)
    (hfg : f =ᵐ[volume.restrict Q] g) (A beta : ℝ)
    (h : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      (∫ y in Metric.ball x r,
          (Set.indicator Q f y - (volume.real (Metric.ball x r))⁻¹ *
            ∫ w' in Metric.ball x r, Set.indicator Q f w') ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * beta)) :
    ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      (∫ y in Metric.ball x r,
          (Set.indicator Q g y - (volume.real (Metric.ball x r))⁻¹ *
            ∫ w' in Metric.ball x r, Set.indicator Q g w') ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * beta) := by
  have hind : Set.indicator Q f =ᵐ[volume] Set.indicator Q g := by
    have h1 := (ae_restrict_iff' hQ).1 hfg
    filter_upwards [h1] with y hy
    by_cases hyQ : y ∈ Q
    · rw [Set.indicator_of_mem hyQ, Set.indicator_of_mem hyQ, hy hyQ]
    · rw [Set.indicator_of_notMem hyQ, Set.indicator_of_notMem hyQ]
  intro x r hr0 hr1
  have hint : (∫ w' in Metric.ball x r, Set.indicator Q g w') =
      ∫ w' in Metric.ball x r, Set.indicator Q f w' :=
    integral_congr_ae (ae_restrict_of_ae hind.symm)
  rw [hint]
  refine (integral_congr_ae ?_).trans_le (h x r hr0 hr1)
  filter_upwards [ae_restrict_of_ae hind] with y hy
  rw [hy]



theorem aux_torsion_bound_core_path
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (_hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath
        (KN N (omega, x)) = L N omega x)
    (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
        (L N omega))
    (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      Continuous (fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
          (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
          LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
          (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
          (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            (∫ y in Metric.ball x r,
                (u y - (volume.real (Metric.ball x r))⁻¹ *
                  ∫ w in Metric.ball x r, u w) ^ 2) ≤
              A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
          ∃ v : SpatialCoordinates d → ℝ,
            v =ᵐ[volume] u ∧
            (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
              |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
            ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0)
    (hosc : ∀ n : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ A : ℝ, 0 ≤ A ∧
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
            (Set.indicator (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))
                (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
                  (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path)
                  ∂(KN N (omega, y))) y -
              (volume.real (Metric.ball x r))⁻¹ *
                ∫ w' in Metric.ball x r,
                  Set.indicator
                    (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))
                    (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
                      (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path)
                      ∂(KN N (omega, y))) w') ^ 2) ≤
            A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n : ℕ, ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ,
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          ∫⁻ path, ContinuousPath.exitTime
              (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path
            ∂(KN N (omega, x)) ≤ ENNReal.ofReal Cw := by
  obtain ⟨Cc, hCc, hC⟩ := hcamp (1 / 4) ⟨by norm_num, by norm_num⟩
  rw [ae_all_iff]
  intro n
  filter_upwards [hosc n, hstart] with omega hA hstartomega
  obtain ⟨A, hA0, hAb⟩ := hA
  have hQm : MeasurableSet (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) :=
    (centeredCube (Qc n) (Qr n) (hQr n)).isOpen.measurableSet
  have hmem : ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      MemLp (fun x => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
          (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path)
          ∂(KN N (omega, x))) 2
        (volume.restrict (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) := by
    intro N lam hlam
    have := hKN N
    exact aux_torsion_bound_resolvent_memLp (Qc n) (Qr n) (hQr n) (KN N) omega lam hlam
  classical
  let w : ℕ → ℝ → DomainL2 (centeredCube (Qc n) (Qr n) (hQr n)) := fun N lam =>
    if h : 0 < lam then (hmem N lam h).toLp _ else 0
  have hwae : ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      (w N lam : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))]
          fun x => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
            (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path)
            ∂(KN N (omega, x)) := by
    intro N lam hlam
    have hw : w N lam = (hmem N lam hlam).toLp _ := dite_eq_left hlam
    rw [hw]
    exact MemLp.coeFn_toLp _
  refine ⟨Cc * A * (Qr n + 2), mul_nonneg (mul_nonneg hCc.le hA0) (by linarith [hQr n]), ?_⟩
  exact aux_torsion_bound_fixed_omega hd (Qc n) (Qr n) (hQr n)
    (fun N x => KN N (omega, x)) (fun N x => by have := hKN N; infer_instance)
    w Cc A (1 / 4) hCc hA0 le_rfl hC
    (fun N lam hlam => aux_torsion_bound_osc_congr _ hQm _ _ (hwae N lam hlam).symm A (1 / 4)
      (hAb N lam hlam))
    (fun N lam hlam => (hwae N lam hlam).symm)
    (fun N => aux_torsion_bound_expected_exit_lsc
      (fun x => jointPathProbabilityMeasure (KN N) (hKN N) omega x) (hstartomega N)
      _ (centeredCube (Qc n) (Qr n) (hQr n)).isOpen)

section TbA
open Set
open _root_.SubdiffusiveProcess.EllipticRegularity
/-- One triadic increment in `L²(ν)`, in geometric form. -/
theorem aux_torsion_bound_osc_level_bound {d : ℕ} (hd : 2 ≤ d) (Qs : Homogenization.TriadicCube d) (z : SpatialCoordinates d) (s : ℝ)
    (hr : 0 < s)
    (hroot : (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qs))
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Qs))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qs), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))))
    (V Ir : ℝ) (hV : ν.real univ ≤ V) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z
      s hr : Set (SpatialCoordinates d)) f ≤
        ENNReal.ofReal Ir)
    (m : ℕ) :
    eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E z
        s hr f (m + 1) x -
      aux_prop_uniform_resolvent_cutoff_oscillation_E z
        s hr f m x) 2 ν ≤
      ENNReal.ofReal (Real.sqrt ((K + V) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ m) := by
  have hinc := globalTriadicAverages_memLp_and_increment_bound hd Qs
    z hr hroot K t hK ht m ν inferInstance hsupp hgrowth f hf
  dsimp only at hinc
  have hsq := hinc.2.2
  have hα : 0 < t - d + 1 := by linarith
  set C0 : ℝ := (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have hcoef := aux_prop_uniform_resolvent_cutoff_oscillation_level_coeff (d := d) s t hr m
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow s (t - d + 1) hr m
  set ell : ℝ := s / (2 * (triadicHalf m : ℝ) + 1) with hell
  have hellpos : 0 < ell := by rw [hell]; positivity
  have hVnn : 0 ≤ ν.real univ := measureReal_nonneg
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := Real.sq_sqrt hq0
  set X : ℝ := (K + V) * C0 * s ^ (t - d + 1) * Ir with hX
  have hXnn : 0 ≤ X := by
    have : 0 ≤ K + V := by linarith
    positivity
  apply aux_prop_uniform_resolvent_cutoff_oscillation_ennreal_le_of_sq_le (by positivity)
  refine hsq.trans ?_
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) * ell := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hsqrtd (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) *
        aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z s hr :
          Set (SpatialCoordinates d)) f
      ≤ ENNReal.ofReal ((K + ν.real univ) * (ell / 3) ^ t * ((ell / 3) ^ d * ell ^ d)⁻¹ *
          (Real.sqrt (d : ℝ) * ell) ^ ((d : ℝ) + 1)) * ENNReal.ofReal Ir := by
        gcongr
    _ = ENNReal.ofReal ((K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m))
          * Ir) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc (K + ν.real univ), mul_assoc (K + ν.real univ), hell, hcoef, hscale]
    _ ≤ ENNReal.ofReal ((Real.sqrt X * q ^ m) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, Real.sq_sqrt hXnn, ← pow_mul, mul_comm m 2, pow_mul, hq2, hX]
        have hA : 0 ≤ C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m) := by positivity
        have hB : K + ν.real univ ≤ K + V := by linarith
        calc (K + ν.real univ) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir
            ≤ (K + V) * (C0 * (s ^ (t - d + 1) * ((3 : ℝ) ^ (-(t - d + 1))) ^ m)) * Ir := by
              gcongr
          _ = (K + V) * C0 * s ^ (t - d + 1) * Ir * ((3 : ℝ) ^ (-(t - d + 1))) ^ m := by ring

/-- The triadic trace difference `‖φ - Π_n φ‖_{L²(μ|_Q)}` (general centre, support cube `Qs`). -/
theorem aux_torsion_bound_osc_trace_diff {d : ℕ} (hd : 2 ≤ d) (Qs : Homogenization.TriadicCube d) (z : SpatialCoordinates d) (s : ℝ)
    (hr : 0 < s)
    (hroot : (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qs))
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qs), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube z
        s hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (φ : SpatialCoordinates d → ℝ)
    (hφ : MemLp φ 2 (volume.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))))
    (Ir : ℝ) (hIr : 0 ≤ Ir)
    (hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z
      s hr : Set (SpatialCoordinates d)) φ ≤
        ENNReal.ofReal Ir)
    (n : ℕ) :
    eLpNorm (fun x => φ x - aux_prop_uniform_resolvent_cutoff_oscillation_E z
        s hr φ n x) 2
      (μ.restrict (centeredCube z
        s hr : Set (SpatialCoordinates d))) ≤
      ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) *
        (Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ n /
          (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))))) := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hr : Set (SpatialCoordinates d))
    with hQdef
  set ν := μ.restrict Q with hνdef
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hsupp : ν (closure (Homogenization.openCubeSet Qs))ᶜ = 0 := by
    rw [hνdef, Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    have : (closure (Homogenization.openCubeSet Qs))ᶜ ∩ Q = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hx.1 (hroot hx.2)
    rw [this, measure_empty]
  have hgrowthν : ∀ x ∈ closure (Homogenization.openCubeSet Qs), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t) := by
    intro x hx ρ hρ hρ1
    exact (Measure.restrict_apply_le Q _).trans (hgrowth x hx ρ hρ hρ1)
  have hVr : ν.real univ ≤ V0 := by
    rw [measureReal_def, hνdef, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  have hα : 0 < t - d + 1 := by linarith
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1' : (3 : ℝ) ^ (-(t - d + 1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set q : ℝ := Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact hq1'
  have hstep : ∀ m, n ≤ m →
      eLpNorm (fun x => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ (m + 1) x - aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) 2 ν ≤
        ENNReal.ofReal (Real.sqrt ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) * s ^ (t - d + 1) * Ir) * q ^ m) :=
    fun m _ => aux_torsion_bound_osc_level_bound hd Qs z s hr hroot Km t hKm ht ν hsupp hgrowthν φ hφ V0 Ir hVr hIr
      hI m
  have hint : IntegrableOn φ Q volume := hφ.integrable one_le_two
  have hleb := aux_prop_uniform_resolvent_cutoff_oscillation_triadic_tendsto_ae hd z hr φ hint
  have hνac : ν ≪ volume := hac
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m x) atTop (𝓝 (φ x)) := by
    filter_upwards [hνac.ae_le hleb, ae_restrict_mem (centeredCube z s hr).isOpen.measurableSet]
      with x hx hxQ
    exact hx hxQ
  exact aux_prop_uniform_resolvent_cutoff_oscillation_fatou_tail ν (fun m => aux_prop_uniform_resolvent_cutoff_oscillation_E z s hr φ m) φ
    (fun m => (aux_prop_uniform_resolvent_cutoff_oscillation_E_measurable z hr φ m).aestronglyMeasurable) hlim n _ q
    (Real.sqrt_nonneg _) hq0 hq1 hstep


/-- Energy estimate for the difference of the measure-source and comparison solutions. -/
theorem aux_torsion_bound_osc_w_bound {d : ℕ} (hd : 2 ≤ d) (Qs : Homogenization.TriadicCube d) (z : SpatialCoordinates d) (s : ℝ)
    (hr : 0 < s)
    (hroot : (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qs))
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc B : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hB : 0 ≤ B)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Qs), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ t))
    (hV : μ (centeredCube z
        s hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube z
      s hr))
    (w : killedSobolevGraph (centeredCube z
      s hr))
    (hcw1 : ‖(w : SobolevData (centeredCube z
        s hr)).1‖ ^ 2 ≤
      Kc * sobolevCoefficientForm a w.val w.val)
    (hcw2 : globalFractionalSqNorm (3 / 4)
        (Set.indicator ((centeredCube z
          s hr) : Set (SpatialCoordinates d))
          (fun x => (w : SobolevData (centeredCube z
            s hr)).1 x)) ≤
      ENNReal.ofReal (Kc * sobolevCoefficientForm a w.val w.val))
    (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))))
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (n : ℕ)
    (hEw : sobolevCoefficientForm a w.val w.val =
      (∫ x in (centeredCube z
          s hr : Set (SpatialCoordinates d)),
        h x * (w : SobolevData (centeredCube z
          s hr)).1 x ∂μ) -
      ∫ x, h x * aux_prop_uniform_resolvent_cutoff_oscillation_E z
          s hr
          (fun y => (w : SobolevData (centeredCube z
            s hr)).1 y) n x
        ∂(μ.restrict (centeredCube z
          s hr : Set (SpatialCoordinates d)))) :
    ‖(w : SobolevData (centeredCube z
        s hr)).1‖ ^ 2 ≤
      Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
          (3 : ℝ) ^ ((d : ℝ) - t)) *
          (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
        (1 - Real.sqrt ((3 : ℝ) ^ (-(t - d + 1)))) ^ 2 * B ^ 2 *
        (s / (3 : ℝ) ^ n) ^ (t - d + 1) := by
  have : IsFiniteMeasure (μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = sobolevCoefficientForm a w.val w.val := ⟨_, rfl⟩
  rw [← hEdef] at hcw1 hcw2 hEw
  have hE0 : 0 ≤ E := by rw [hEdef]; exact sobolevCoefficientForm_nonneg a _
  have hφ2 : MemLp (fun y => (w : SobolevData (centeredCube z
      s hr)).1 y) 2
      (volume.restrict (centeredCube z
        s hr : Set (SpatialCoordinates d))) := Lp.memLp _
  have hφs : StronglyMeasurable (fun y => (w : SobolevData (centeredCube
      z s hr)).1 y) :=
    Lp.stronglyMeasurable _
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ,
      cs = (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ) :=
    ⟨_, rfl⟩
  have hcs0 : 0 ≤ cs := by rw [hcsdef]; positivity
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ,
      C0 = (Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) * (3 : ℝ) ^ ((d : ℝ) - t) := ⟨_, rfl⟩
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  have hIr0 : 0 ≤ cs * (Kc * E) := by positivity
  have hI : aux_prop_uniform_resolvent_cutoff_oscillation_I (centeredCube z
      s hr : Set (SpatialCoordinates d))
      (fun y => (w : SobolevData (centeredCube z
        s hr)).1 y) ≤ ENNReal.ofReal (cs * (Kc * E)) := by
    refine (aux_prop_uniform_resolvent_cutoff_oscillation_kernel_compare _ hr _ hφs.measurable).trans ?_
    rw [ENNReal.ofReal_mul hcs0, ← hcsdef]
    gcongr
  have hT := aux_torsion_bound_osc_trace_diff hd Qs z s hr hroot t ht μ hac Km V0 hKm hV0 hgrowth hV _ hφ2
    (cs * (Kc * E)) hIr0 hI n
  rw [← hC0def] at hT
  have hα : 0 < t - d + 1 := by linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.sqrt ((3 : ℝ) ^ (-(t - d + 1))) := ⟨_, rfl⟩
  rw [← hqdef] at hT ⊢
  have hq0' : 0 ≤ (3 : ℝ) ^ (-(t - d + 1)) := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, Real.sqrt_lt' one_pos, one_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ q := by rw [hqdef]; exact Real.sqrt_nonneg _
  have h1q : 0 < 1 - q := by linarith
  have hT0 : 0 ≤ Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
      (1 - q) := by positivity
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pair_diff_bound _ h _ _ B _ hB hT0 hh hbound hφs.aestronglyMeasurable
    (aux_prop_uniform_resolvent_cutoff_oscillation_E_memLp _ hr _ n _) hT
  have hVr : Real.sqrt ((μ.restrict (centeredCube z
      s hr : Set (SpatialCoordinates d))).real univ) ≤
      Real.sqrt V0 := by
    apply Real.sqrt_le_sqrt
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = B * Real.sqrt V0 *
      (Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q)) := ⟨_, rfl⟩
  have hEA : E ≤ A * Real.sqrt E := by
    have h1 := hpair.2.2
    rw [← hEw] at h1
    have h3 : Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * (Kc * E))) * q ^ n /
        (1 - q) = Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
        Real.sqrt E := by
      rw [show (Km + V0) * C0 * s ^ (t - d + 1) * (cs * (Kc * E)) =
        ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * E by ring,
        Real.sqrt_mul' _ hE0]
      ring
    rw [h3] at h1
    calc E ≤ B * Real.sqrt ((μ.restrict (centeredCube z
          s hr : Set (SpatialCoordinates d))).real univ) *
          (Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := h1
      _ ≤ B * Real.sqrt V0 *
          (Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) * (cs * Kc)) * q ^ n / (1 - q) *
            Real.sqrt E) := by gcongr
      _ = A * Real.sqrt E := by rw [hAdef]; ring
  have hEA2 := aux_prop_uniform_resolvent_cutoff_oscillation_sqrt_absorb E A hE0 hEA
  have hKmV : 0 ≤ Km + V0 := by linarith
  have hscale := aux_prop_uniform_resolvent_cutoff_oscillation_level_scale_pow _ (t - d + 1) hr n
  have hq2 : q ^ 2 = (3 : ℝ) ^ (-(t - d + 1)) := by rw [hqdef]; exact Real.sq_sqrt hq0'
  rw [← hC0def, ← hcsdef]
  calc _ ≤ Kc * E := hcw1
    _ ≤ Kc * A ^ 2 := mul_le_mul_of_nonneg_left hEA2 hKc
    _ = Kc ^ 2 * V0 * ((Km + V0) * C0 * cs) / (1 - q) ^ 2 * B ^ 2 *
          (s / (3 : ℝ) ^ n) ^ (t - d + 1) := by
        have hsq1 : Real.sqrt V0 ^ 2 = V0 := Real.sq_sqrt hV0
        have hsq2 : Real.sqrt ((Km + V0) * C0 * s ^ (t - d + 1) *
            (cs * Kc)) ^ 2 = (Km + V0) * C0 * s ^ (t - d + 1) *
            (cs * Kc) := Real.sq_sqrt (by positivity)
        have hq2n : (q ^ n) ^ 2 = ((3 : ℝ) ^ (-(t - d + 1))) ^ n := by
          rw [← pow_mul, mul_comm n 2, pow_mul, hq2]
        rw [hscale, hAdef, mul_pow, mul_pow, div_pow, mul_pow, hsq1, hsq2, hq2n]
        field_simp


/-- The oscillation engine of `prop_uniform_resolvent_cutoff_oscillation` for an arbitrary centre. -/
theorem aux_torsion_bound_osc_instance {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon1 : epsilon < 1)
    (Qs : Homogenization.TriadicCube d) (z : SpatialCoordinates d) (s : ℝ)
    (hr : 0 < s)
    (hroot : (centeredCube z s hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qs))
    (μ : Measure (SpatialCoordinates d))
    (hac : μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)) ≪ volume)
    (Km V0 Kc Kh : ℝ) (hKm : 0 ≤ Km) (hV0 : 0 ≤ V0) (hKc : 0 ≤ Kc) (hKh : 0 ≤ Kh)
    (hgrowth : ∀ x ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ ((d : ℝ) - epsilon)))
    (hgrowthS : ∀ x ∈ closure (Homogenization.openCubeSet Qs), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      μ (Metric.ball x ρ) ≤ ENNReal.ofReal (Km * ρ ^ ((d : ℝ) - epsilon)))
    (hV : μ (centeredCube z s hr : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal V0)
    (a : PositiveCoefficient (centeredCube z s hr))
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z s hr),
      ‖(v : SobolevData (centeredCube z s hr)).1‖ ^ 2 ≤ Kc * sobolevCoefficientForm a v.val v.val ∧
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d)) (fun x => (v : SobolevData (centeredCube z s hr)).1 x)) ≤
        ENNReal.ofReal (Kc * sobolevCoefficientForm a v.val v.val))
    (hHol : ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube z s hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) → ∀ v : killedSobolevGraph (centeredCube z s hr),
        (∀ w : killedSobolevGraph (centeredCube z s hr), sobolevCoefficientForm a v.val w.val =
          ∫ x in (centeredCube z s hr : Set (SpatialCoordinates d)), F0 x * (w : SobolevData (centeredCube z s hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube z s hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z s hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube z s hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)), ∀ y ∈ closure (centeredCube z s hr : Set (SpatialCoordinates d)),
            |vc x - vc y| ≤ Kh * MF * dist x y ^ (1 / 2 : ℝ)))
    (u : killedSobolevGraph (centeredCube z s hr)) (h : SpatialCoordinates d → ℝ)
    (hh : AEStronglyMeasurable h (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d)))) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂(μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))), |h x| ≤ B)
    (hfin : ∀ w : killedSobolevGraph (centeredCube z s hr), sobolevCoefficientForm a u.val w.val =
      ∫ x in (centeredCube z s hr : Set (SpatialCoordinates d)), h x * (w : SobolevData (centeredCube z s hr)).1 x ∂μ)
    (u0 : SpatialCoordinates d → ℝ)
    (hzero : ∀ x, u0 x = Set.indicator (centeredCube z s hr : Set (SpatialCoordinates d)) (fun y => (u : SobolevData (centeredCube z s hr)).1 y) x)
    (x : SpatialCoordinates d) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ y in Metric.ball x r,
        (u0 y - (volume.real (Metric.ball x r))⁻¹ * ∫ w in Metric.ball x r, u0 w) ^ 2) ≤
      (aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s Km V0 Kc Kh * B) ^ 2 *
        volume.real (Metric.ball x r) * r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) := by
  have hQm : MeasurableSet (centeredCube z s hr : Set (SpatialCoordinates d)) := (centeredCube z s hr).isOpen.measurableSet
  have : IsFiniteMeasure (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hV.trans_lt ENNReal.ofReal_lt_top
  have hR0 : 0 < r ^ ((d : ℝ) + 2) := Real.rpow_pos_of_pos hr0 _
  have hR1 : r ^ ((d : ℝ) + 2) ≤ 1 := Real.rpow_le_one hr0.le hr1 (by positivity)
  obtain ⟨n, hn1, hn2⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_level_choice s
    (r ^ ((d : ℝ) + 2)) hr hR0 hR1
  have ht0 : 0 < (d : ℝ) - epsilon := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htd : (d : ℝ) - 1 < (d : ℝ) - epsilon := by linarith
  have hℓpos : 0 < s / (3 : ℝ) ^ n := by positivity
  have hℓ2 : s / (3 : ℝ) ^ n ≤ 2 := by linarith
  obtain ⟨MF, hMFdef⟩ : ∃ MF : ℝ, MF = B * Km *
      (s / (3 : ℝ) ^ n) ^ ((d : ℝ) - epsilon) /
        (s / (3 : ℝ) ^ n) ^ d := ⟨_, rfl⟩
  have hMF0 : 0 ≤ MF := by rw [hMFdef]; positivity
  have hF0b : ∀ y, |aux_prop_uniform_resolvent_cutoff_oscillation_source z
      s hr (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h n y| ≤ MF := by
    intro y
    rw [hMFdef]
    exact aux_prop_uniform_resolvent_cutoff_oscillation_source_bound _ hr μ h B hB hbound Km _ hKm ht0 hgrowth n hℓ2 y
  have hF0m := aux_prop_uniform_resolvent_cutoff_oscillation_source_measurable z hr
    (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h n
  have hF0L2 : MemLp (aux_prop_uniform_resolvent_cutoff_oscillation_source z
      s hr (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h n) 2 (volume.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hF0m.aestronglyMeasurable MF
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact hF0b y))
  obtain ⟨v, hv⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_comparison_exists a Kc (fun v => (hcoer v).1) _ hF0L2
  obtain ⟨vc, hvcae, hvc0, hvcHol⟩ := hHol _ hF0m MF hMF0 (fun y _ => hF0b y) v hv
  have hC : 0 ≤ Kh * MF := mul_nonneg hKh hMF0
  have hglob := aux_prop_uniform_resolvent_cutoff_oscillation_holder_global (centeredCube z s hr : Set (SpatialCoordinates d)) (centeredCube z s hr).isOpen vc (Kh * MF) hC hvc0 hvcHol
  have hhint : Integrable h (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) := by
    refine Integrable.mono' (integrable_const B) hh ?_
    filter_upwards [hbound] with y hy
    simpa [Real.norm_eq_abs] using hy
  have hwint : IntegrableOn (fun y => ((u - v : killedSobolevGraph (centeredCube z s hr)) :
      SobolevData (centeredCube z s hr)).1 y) (centeredCube z s hr : Set (SpatialCoordinates d)) volume :=
    (Lp.memLp _).integrable one_le_two
  have hpair := aux_prop_uniform_resolvent_cutoff_oscillation_pairing z hr n (μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) h hhint
    _ hwint
  have hEw : sobolevCoefficientForm a (u - v : killedSobolevGraph (centeredCube z s hr)).val
      (u - v : killedSobolevGraph (centeredCube z s hr)).val =
      (∫ y in (centeredCube z s hr : Set (SpatialCoordinates d)), h y * ((u - v : killedSobolevGraph (centeredCube z s hr)) : SobolevData (centeredCube z s hr)).1 y ∂μ) -
      ∫ y, h y * aux_prop_uniform_resolvent_cutoff_oscillation_E z
          s hr
          (fun y0 => ((u - v : killedSobolevGraph (centeredCube z s hr)) : SobolevData (centeredCube z s hr)).1 y0) n y
        ∂(μ.restrict (centeredCube z s hr : Set (SpatialCoordinates d))) := by
    rw [aux_prop_uniform_resolvent_cutoff_oscillation_form_sub, hfin, hv, hpair]
  have hwb := aux_torsion_bound_osc_w_bound hd Qs z s hr hroot ((d : ℝ) - epsilon) htd μ hac Km V0 Kc B hKm hV0 hKc
    hB hgrowthS hV a (u - v) (hcoer (u - v)).1 (hcoer (u - v)).2 h hh hbound n hEw
  have hdecomp := aux_prop_uniform_resolvent_cutoff_oscillation_decomp (centeredCube z s hr) u v vc hvcae hvc0 u0 hzero
  have hW2 := (aux_prop_uniform_resolvent_cutoff_oscillation_L2_norm_sq
    ((u - v : killedSobolevGraph (centeredCube z
      s hr)) : SobolevData (centeredCube
        z s hr)).1).trans_le hwb
  have hcamp := aux_prop_uniform_resolvent_cutoff_oscillation_campanato_assembly (centeredCube z s hr : Set (SpatialCoordinates d)) hQm u0 vc _ vc.continuous (Kh * MF) hC hglob
    hdecomp (Lp.memLp _) _ hW2 x r
  refine hcamp.trans ?_
  have hvol : volume.real (Metric.ball x r) = (2 * r) ^ d := by
    rw [measureReal_def, Real.volume_pi_ball x hr0, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, hMFdef]
  have hσ : 0 < min s (1 / 3) := lt_min hr (by norm_num)
  have hCw : 0 ≤ Kc ^ 2 * V0 * ((Km + V0) * ((Real.sqrt (d : ℝ)) ^ ((d : ℝ) + 1) *
        (3 : ℝ) ^ ((d : ℝ) - ((d : ℝ) - epsilon))) *
        (Real.sqrt (d : ℝ) * s) ^ (1 / 2 : ℝ)) /
      (1 - Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) - epsilon - d + 1)))) ^ 2 := by
    have : 0 ≤ Km + V0 := by linarith
    positivity
  exact aux_prop_uniform_resolvent_cutoff_oscillation_final_algebra (d := d) epsilon r _ _ B Km Kh _ hepsilon hepsilon1 hr0 hr1 hσ hCw
    hn1 hn2

end TbA

section TbB
open Set
/-! ### Identification of the finite-cutoff survival resolvent with the killed weak solution -/

/-- The killed survival integrand is jointly measurable in (path, time). -/
theorem aux_torsion_bound_surv_F_measurable {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (lam : ℝ) :
    Measurable (fun q : ContinuousPath (SpatialCoordinates d) × ℝ =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q q.1}
        (fun s : ℝ => Real.exp (-lam * s)) q.2) := by
  have heq : (fun q : ContinuousPath (SpatialCoordinates d) × ℝ =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q q.1}
        (fun s : ℝ => Real.exp (-lam * s)) q.2) =
      Set.indicator {q : ContinuousPath (SpatialCoordinates d) × ℝ |
        ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1}
        (fun q => Real.exp (-lam * q.2)) := by
    funext q
    simp only [Set.indicator, mem_ofPred_eq]
  rw [heq]
  refine Measurable.indicator ?_ ?_
  · exact Real.measurable_exp.comp (measurable_const.mul measurable_snd)
  · exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_fst)

/-- Fubini for the survival resolvent: `E_x ∫_0^τ e^{-λt} dt = ∫_0^∞ e^{-λt} P_x(t < τ) dt`. -/
theorem aux_torsion_bound_surv_swap {d : ℕ}
    (ν : Measure (ContinuousPath (SpatialCoordinates d))) [IsProbabilityMeasure ν]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam) :
    (∫ p, survivalIntegral lam (ContinuousPath.exitTime Q p) ∂ν) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        ν.real {p | ENNReal.ofReal t < ContinuousPath.exitTime Q p} := by
  have hmeasF := aux_torsion_bound_surv_F_measurable Q hQ lam
  have hint : Integrable (Function.uncurry (fun (p : ContinuousPath (SpatialCoordinates d))
      (t : ℝ) => Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
        (fun s : ℝ => Real.exp (-lam * s)) t)) (ν.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hg : Integrable (fun q : ContinuousPath (SpatialCoordinates d) × ℝ =>
        (1 : ℝ) * Real.exp (-lam * q.2)) (ν.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) (exp_neg_integrableOn_Ioi 0 hlam)
    refine hg.mono' hmeasF.aestronglyMeasurable (ae_of_all _ (fun q => ?_))
    simp only [Function.uncurry, one_mul]
    by_cases hq : ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1
    · rw [Set.indicator_of_mem (by exact hq), Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    · rw [Set.indicator_of_notMem (by exact hq), norm_zero]
      exact (Real.exp_pos _).le
  have hsw := integral_integral_swap hint
  simp only [survivalIntegral]
  rw [hsw]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  have hSm : MeasurableSet {p : ContinuousPath (SpatialCoordinates d) |
      ENNReal.ofReal t < ContinuousPath.exitTime Q p} :=
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime Q hQ)
  have hfun : (fun p : ContinuousPath (SpatialCoordinates d) =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
        (fun s : ℝ => Real.exp (-lam * s)) t) =
      Set.indicator {p : ContinuousPath (SpatialCoordinates d) |
        ENNReal.ofReal t < ContinuousPath.exitTime Q p} (fun _ => Real.exp (-lam * t)) := by
    funext p
    simp only [Set.indicator, mem_ofPred_eq]
  rw [hfun, integral_indicator_const _ hSm, smul_eq_mul, mul_comm]

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- The Section 9 killed resolvent of the constant `1` is `λ` times the survival resolvent. -/
theorem aux_torsion_bound_kres_one {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d))) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (x : SpatialCoordinates d) :
    killedResolvent law Q lam⁻¹ (fun _ => (1 : ℝ)) x =
      lam * ∫ p, survivalIntegral lam (ContinuousPath.exitTime Q p) ∂K x := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hmass : ∀ t : ℝ, (∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime Q w},
      (1 : ℝ) ∂law x) =
      (K x).real {p | ENNReal.ofReal t < ContinuousPath.exitTime Q p} := by
    intro t
    have hS : MeasurableSet {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime Q w} :=
      measurableSet_lt measurable_const (LifetimePath.measurable_exitTime Q hQ)
    rw [setIntegral_const, smul_eq_mul, mul_one, ← hL x, measureReal_def, measureReal_def,
      Measure.map_apply LifetimePath.measurable_ofContinuousPath hS]
    congr 2
    ext p
    simp only [Set.mem_preimage, mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath]
  rw [aux_torsion_bound_surv_swap (K x) Q hQ lam hlam]
  unfold killedResolvent
  rw [inv_inv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only
  rw [hmass t]
  congr 2
  field_simp

/-- The cutoff coefficient carrier equals its continuous formula a.e. on the cube. -/
theorem aux_torsion_bound_coef_ae {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr).val x = cutoffCoefficient M H omega N x := by
  have h1 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N z hr) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N z hr)
    1 one_pos
  filter_upwards [h1, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient
  rw [hx hxm, div_one]
  rfl

/-- The speed density is `ahom` times the coefficient. -/
theorem aux_torsion_bound_density_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffSpeedDensity M H omega N x =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x := by
  have hpos := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  unfold cutoffSpeedDensity cutoffCoefficient
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

theorem aux_torsion_bound_density_continuous {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  have h : cutoffSpeedDensity M H omega N =
      fun x => SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x :=
    funext (aux_torsion_bound_density_eq M H omega N)
  rw [h]
  exact continuous_const.mul (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N)

theorem aux_torsion_bound_density_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffSpeedDensity M H omega N x :=
  Real.exp_pos _

/-- A continuous function is bounded on a cube. -/
theorem aux_torsion_bound_cube_bound {d : ℕ} (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |g x| ≤ C := by
  have hcomp : IsCompact (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (centeredCube_isBounded z hr).closure
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x (subset_closure hx)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Set integrals against the cutoff speed measure are density-weighted Lebesgue integrals. -/
theorem aux_torsion_bound_speed_integral {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (Q : Set (SpatialCoordinates d)) (hQ : MeasurableSet Q) (g : SpatialCoordinates d → ℝ) :
    (∫ x in Q, g x ∂(cutoffSpeedMeasure M H omega N)) =
      ∫ x in Q, cutoffSpeedDensity M H omega N x * g x := by
  have hm : Measurable (ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N) :=
    ENNReal.measurable_ofReal.comp (aux_torsion_bound_density_continuous M H omega N).measurable
  unfold cutoffSpeedMeasure
  rw [restrict_withDensity hQ, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (ae_of_all _ (fun x => ?_))
  simp only [Function.comp, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (aux_torsion_bound_density_pos M H omega N x).le]

/-- Integrability of a bounded measurable weight times a product of two `L²` functions. -/
theorem aux_torsion_bound_int_w_mul {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    (c f g : α → ℝ) (C : ℝ) (hc : AEStronglyMeasurable c μ) (hcb : ∀ᵐ x ∂μ, |c x| ≤ C)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => c x * (f x * g x)) μ := by
  have hfg : Integrable (f * g) μ := hf.integrable_mul hg
  exact Integrable.bdd_mul hfg hc (by filter_upwards [hcb] with x hx; rwa [Real.norm_eq_abs])

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **Identification** (`mfd:cor-finite-exit`): at a fixed sample and cutoff, the zero-boundary
survival resolvent of the cube is a.e. the killed weak solution of
`E_N(u, w) = ∫_Q (1 - λ u) w dμ_N`. -/
theorem aux_torsion_bound_ident {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d))) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (hLD : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) law)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam) :
    ∃ u : killedSobolevGraph (centeredCube z r hr),
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (fun x => ∫ p, survivalIntegral lam
            (ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) p) ∂K x) ∧
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) u.val w.val =
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (1 - lam * ∫ p, survivalIntegral lam
              (ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) p) ∂K x) *
              (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (SpatialCoordinates d),
      Q = (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hQo : IsOpen Q := hQdef ▸ (centeredCube z r hr).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQb : Bornology.IsBounded Q := hQdef ▸ centeredCube_isBounded z hr
  obtain ⟨S, hSdef⟩ : ∃ S : SpatialCoordinates d → ℝ,
      S = fun x => ∫ p, survivalIntegral lam (ContinuousPath.exitTime Q p) ∂K x := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : SpatialCoordinates d → ℝ, ρ = cutoffSpeedDensity M H omega N :=
    ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : SpatialCoordinates d → ℝ, c = cutoffCoefficient M H omega N :=
    ⟨_, rfl⟩
  have hρc : Continuous ρ := hρdef ▸ aux_torsion_bound_density_continuous M H omega N
  have hρpos : ∀ x, 0 < ρ x := fun x => hρdef ▸ aux_torsion_bound_density_pos M H omega N x
  have hcc : Continuous c := hcdef ▸ _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N
  obtain ⟨Cρ, hCρ0, hCρ⟩ := aux_torsion_bound_cube_bound ρ hρc z hr
  obtain ⟨Cc, hCc0, hCc⟩ := aux_torsion_bound_cube_bound c hcc z hr
  rw [← hQdef] at hCρ hCc
  have hρb : ∀ᵐ x ∂volume.restrict Q, |ρ x| ≤ Cρ := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCρ x hx
  have hcb : ∀ᵐ x ∂volume.restrict Q, |c x| ≤ Cc := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCc x hx
  -- the weighted measure on the cube is finite and equivalent to Lebesgue
  have hfinW : IsFiniteMeasure ((weightedMeasure ρ).restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, weightedMeasure, withDensity_apply _ hQm]
    calc (∫⁻ x in Q, ENNReal.ofReal (ρ x)) ≤ ∫⁻ _x in Q, ENNReal.ofReal Cρ := by
          refine setLIntegral_mono' hQm (fun x hx => ENNReal.ofReal_le_ofReal ?_)
          exact (le_abs_self _).trans (hCρ x hx)
      _ = ENNReal.ofReal Cρ * volume Q := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQb.measure_lt_top
  have hac : volume.restrict Q ≪ (weightedMeasure ρ).restrict Q := by
    rw [weightedMeasure, restrict_withDensity hQm]
    exact withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hρc.measurable).aemeasurable
      (ae_of_all _ (fun x => by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hρpos x))
  have hmem1 : MemLp (fun _ : SpatialCoordinates d => (1 : ℝ)) 2
      ((weightedMeasure ρ).restrict Q) := memLp_const 1
  have hsol := hLD.2.2 Q hQo hQb lam⁻¹ (inv_pos.2 hlam) (fun _ => (1 : ℝ))
    (by rw [← hρdef]; exact hmem1)
  obtain ⟨u0, hu0a, hu0w⟩ := hsol
  rw [← hρdef] at hu0a
  rw [← hρdef, ← hcdef, inv_inv] at hu0w
  -- `u0 = λ S` Lebesgue-a.e. on the cube
  have hu0S : ∀ᵐ x ∂volume.restrict Q, u0.toH1Function.toFun x = lam * S x := by
    filter_upwards [hac.ae_le hu0a] with x hx
    rw [hx, aux_torsion_bound_kres_one K law hL Q hQo lam hlam x, hSdef]
  -- the killed carrier of `u0`
  subst hQdef
  have hK := _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 (Ω := centeredCube z r hr) u0
  obtain ⟨U, hUv, hUg⟩ := hK
  refine ⟨lam⁻¹ • U, ?_, ?_⟩
  · have hsm := Lp.coeFn_smul lam⁻¹ (U : SobolevData (centeredCube z r hr)).1
    have hc1 : ((lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1 = lam⁻¹ • (U : SobolevData (centeredCube z r hr)).1 :=
      rfl
    rw [hc1]
    filter_upwards [hsm, hUv, hu0S] with x h1 h2 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, h3, hSdef, ← mul_assoc, inv_mul_cancel₀ hlam.ne',
      one_mul]
  · intro w
    have hφ := exists_nativeH10Function_of_killedSobolevGraph w
    obtain ⟨φ, hφv, hφg⟩ := hφ
    have heq := hu0w φ
    -- left side: the coefficient form
    have hL1 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)).val w.val =
        lam⁻¹ * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          U.val w.val := by
      rw [Submodule.coe_smul, map_smul, smul_apply, smul_eq_mul]
    have hgradU : ∀ i : Fin d, MemLp (fun x => u0.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => u0.toH1Function.gradMemL2 i
    have hgradφ : ∀ i : Fin d, MemLp (fun x => φ.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => φ.toH1Function.gradMemL2 i
    have hcm : AEStronglyMeasurable c
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hcc.aestronglyMeasurable
    have hL2 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        U.val w.val =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x) := by
      rw [_root_.SubdiffusiveProcess.EllipticRegularity.sobolevCoefficientForm_eq_sum_integral]
      have hsum : (fun x => Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
          fun x => ∑ i : Fin d, c x * (u0.toH1Function.grad x i * φ.toH1Function.grad x i) := by
        funext x
        simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hsum, integral_finsetSum _ (fun i _ =>
        aux_torsion_bound_int_w_mul _ c _ _ Cc hcm hcb (hgradU i) (hgradφ i))]
      refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
      filter_upwards [aux_torsion_bound_coef_ae M H omega N z hr, hUg i] with x hx1 hx2
      rw [hx1, hx2, ← hcdef]
      have hw : (w : SobolevData (centeredCube z r hr)).2 i x = φ.toH1Function.grad x i := by
        rw [hφg]
      rw [hw]
    -- right side: the speed-measure pairing
    have hR1 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (1 - lam * ∫ p, survivalIntegral lam
          (ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) p) ∂K x) *
          (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (ρ x * φ.toH1Function.toFun x - ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      rw [aux_torsion_bound_speed_integral M H omega N _ hQm, ← hρdef]
      refine integral_congr_ae ?_
      filter_upwards [hu0S] with x hx
      have hw : (w : SobolevData (centeredCube z r hr)).1 x = φ.toH1Function.toFun x := by
        have := congrFun hφv x
        exact this.symm
      have hS' : (∫ p, survivalIntegral lam (ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) p) ∂K x) = S x := by rw [hSdef]
      rw [hw, hS', ← hx]
      ring
    have hφL2 : MemLp φ.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      φ.toH1Function.memL2
    have hu0L2 : MemLp u0.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      u0.toH1Function.memL2
    have hρm : AEStronglyMeasurable ρ
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hρc.aestronglyMeasurable
    have hi1 : Integrable (fun x => ρ x * φ.toH1Function.toFun x)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      Integrable.bdd_mul (hφL2.integrable one_le_two) hρm
        (by filter_upwards [hρb] with x hx; rwa [Real.norm_eq_abs])
    have hi2 : Integrable (fun x => ρ x * (u0.toH1Function.toFun x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ _ _ Cρ hρm hρb hu0L2 hφL2
    have hi2' : Integrable (fun x => ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hi2.congr (ae_of_all _ (fun x => by ring))
    have hRHS := hR1.trans (integral_sub hi1 hi2')
    simp only [mul_one] at heq
    have hsrc : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ρ x * lam * φ.toH1Function.toFun x) =
        lam * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * φ.toH1Function.toFun x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun x => by ring))
    rw [hsrc] at heq
    have hv : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
        lam * ((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * φ.toH1Function.toFun x) -
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      linarith
    exact hL1.trans ((congrArg (fun y => lam⁻¹ * y) (hL2.trans hv)).trans
      ((inv_mul_cancel_left₀ hlam.ne' _).trans hRHS.symm))

end TbB

section TbC
open Set
open _root_.SubdiffusiveProcess.EllipticRegularity
/-! ### Per-sample coercivity and Hölder inputs of the oscillation engine -/

theorem aux_torsion_bound_cubeFrac_nonneg {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (v : DomainL2 (centeredCube z r hr)) :
    0 ≤ cubeFractionalSqNorm hd z r hr threeQuarterOrder v := by
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  have hV : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    centeredCube_volume_pos z hr
  positivity

/-- The two coercivity bounds of the oscillation engine, from the cube `H^{3/4}` coercivity
(`lem_as_coarse`) and the zero-extension bound (`killed_zero_extension_bound`). -/
theorem aux_torsion_bound_hcoer {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (K Cext : ℝ) (hK : 0 ≤ K)
    (hCext : 0 ≤ Cext)
    (hext : ∀ w : killedSobolevGraph (centeredCube z r hr),
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube z r hr : Set (SpatialCoordinates d))
          (fun x => ((w : SobolevData (centeredCube z r hr)).1) x)) ≤
        ENNReal.ofReal (Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (w : SobolevData (centeredCube z r hr)).1))
    (hcf : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr))) :
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ^ 2 ≤
          (K * (r ^ d + Cext)) * sobolevCoefficientForm a v.val v.val ∧
      globalFractionalSqNorm (3 / 4)
          (Set.indicator (centeredCube z r hr : Set (SpatialCoordinates d))
            (fun x => (v : SobolevData (centeredCube z r hr)).1 x)) ≤
        ENNReal.ofReal ((K * (r ^ d + Cext)) * sobolevCoefficientForm a v.val v.val) := by
  intro v
  have hE : 0 ≤ sobolevCoefficientForm a v.val v.val := sobolevCoefficientForm_nonneg a _
  have hcf0 := aux_torsion_bound_cubeFrac_nonneg hd z r hr (v : SobolevData (centeredCube z r hr)).1
  have hKE : 0 ≤ K * sobolevCoefficientForm a v.val v.val := mul_nonneg hK hE
  have hrd : 0 ≤ r ^ d := pow_nonneg hr.le d
  have hL2 := aux_torsion_bound_L2_le_cubeFractional hd z r hr threeQuarterOrder
    (v : SobolevData (centeredCube z r hr)).1
  rw [centeredCube_volume_real] at hL2
  constructor
  · calc ‖(v : SobolevData (centeredCube z r hr)).1‖ ^ 2
        ≤ r ^ d * cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 := hL2
      _ ≤ r ^ d * (K * sobolevCoefficientForm a v.val v.val) :=
          mul_le_mul_of_nonneg_left (hcf v) hrd
      _ ≤ (r ^ d + Cext) * (K * sobolevCoefficientForm a v.val v.val) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCext) hKE
      _ = (K * (r ^ d + Cext)) * sobolevCoefficientForm a v.val v.val := by ring
  · refine (hext v).trans (ENNReal.ofReal_le_ofReal ?_)
    calc Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1
        ≤ Cext * (K * sobolevCoefficientForm a v.val v.val) :=
          mul_le_mul_of_nonneg_left (hcf v) hCext
      _ ≤ (r ^ d + Cext) * (K * sobolevCoefficientForm a v.val v.val) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hrd) hKE
      _ = (K * (r ^ d + Cext)) * sobolevCoefficientForm a v.val v.val := by ring

/-- The `C²` norm of the zero function on a nonempty set vanishes. -/
theorem aux_torsion_bound_c2Norm_zero {d : ℕ} (S : Set (SpatialCoordinates d))
    (hS : S.Nonempty) : c2Norm S (fun _ => (0 : ℝ)) ≤ 0 := by
  have h1 : {v : ℝ | ∃ x ∈ S, v = |(fun _ : SpatialCoordinates d => (0 : ℝ)) x|} = {0} := by
    ext v; simp only [abs_zero, mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, hv⟩; exact hv
    · intro hv; obtain ⟨x, hx⟩ := hS; exact ⟨x, hx, hv⟩
  have hd1 : fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ)) = 0 := by
    funext x; simp
  have hd2 : fderiv ℝ (fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ))) = 0 := by
    rw [hd1]; funext x; simp
  have h2 : {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ)) x‖} =
      {0} := by
    rw [hd1]
    ext v; simp only [Pi.zero_apply, norm_zero, mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, hv⟩; exact hv
    · intro hv; obtain ⟨x, hx⟩ := hS; exact ⟨x, hx, hv⟩
  have h3 : {v : ℝ | ∃ x ∈ S,
      v = ‖fderiv ℝ (fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ))) x‖} = {0} := by
    rw [hd2]
    ext v; simp only [Pi.zero_apply, mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, hv⟩; rw [hv]; exact ContinuousLinearMap.opNorm_zero
    · intro hv; obtain ⟨x, hx⟩ := hS; exact ⟨x, hx, by rw [hv]; exact ContinuousLinearMap.opNorm_zero.symm⟩
  unfold c2Norm
  rw [h1, h2, h3, csSup_singleton]
  norm_num

/-- Euclidean distance is at most `√d` times the sup distance. -/
theorem aux_torsion_bound_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d : ℝ) * dist x y := by
  have hterm : ∀ j : Fin d, (x j - y j) ^ 2 ≤ dist x y ^ 2 := by
    intro j
    have h := dist_le_pi_dist x y j
    rw [Real.dist_eq] at h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * dist x y ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, dist x y ^ 2 :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = (d : ℝ) * dist x y ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * dist x y ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * dist x y := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq dist_nonneg]

/-- Pointwise Hölder bound from a finite `C^{1/2}` norm on a compact set. -/
theorem aux_torsion_bound_holder_pt {d : ℕ} (S : Set (SpatialCoordinates d)) (hS : IsCompact S)
    (U : SpatialCoordinates d → ℝ) (hU : Continuous U) (C : ℝ)
    (hH : IsHolderOn (1 / 2) S U) (hC : cAlphaNorm (1 / 2) S U ≤ C) :
    ∀ x ∈ S, ∀ y ∈ S,
      |U x - U y| ≤ C * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ) * dist x y ^ (1 / 2 : ℝ) := by
  intro x hx y hy
  have hA : BddAbove {v : ℝ | ∃ x ∈ S, v = |U x|} := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hU.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨w, hw, rfl⟩
    have := hB w hw
    rwa [Real.norm_eq_abs] at this
  have hA0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} :=
    (abs_nonneg (U x)).trans (le_csSup hA ⟨x, hx, rfl⟩)
  have hsemi : holderSeminorm (1 / 2) S U ≤ C := by
    unfold cAlphaNorm at hC
    linarith
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, abs_zero, dist_self, Real.zero_rpow (by norm_num), mul_zero]
  · have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      rw [Real.sqrt_pos]
      by_contra hle
      push Not at hle
      apply hxy
      funext j
      have h0 : ∑ j : Fin d, (x j - y j) ^ 2 = 0 :=
        le_antisymm hle (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - y j))).1 h0 j
        (Finset.mem_univ j)
      have h2 : x j - y j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hpos _
    have hmem : |U x - U y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) ∈
        holderRatioSet (1 / 2) S U := ⟨x, hx, y, hy, hxy, rfl⟩
    have hle : |U x - U y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) ≤
        holderSeminorm (1 / 2) S U := le_csSup hH hmem
    have hsemi0 : 0 ≤ holderSeminorm (1 / 2) S U :=
      (div_nonneg (abs_nonneg _) hden.le).trans hle
    have h1 : |U x - U y| ≤ holderSeminorm (1 / 2) S U *
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) := by
      rwa [div_le_iff₀ hden] at hle
    have h2 : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) ≤
        Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ) * dist x y ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
      exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (aux_torsion_bound_euclid_le x y)
        (by norm_num)
    have hC0 : 0 ≤ C := hsemi0.trans hsemi
    calc |U x - U y| ≤ holderSeminorm (1 / 2) S U *
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) := h1
      _ ≤ C * (Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ) * dist x y ^ (1 / 2 : ℝ)) :=
          mul_le_mul hsemi h2 (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hC0
      _ = C * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ) * dist x y ^ (1 / 2 : ℝ) := by ring

/-- The closure of the open cube is the closed cube. -/
theorem aux_torsion_bound_closure_cube {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
  exact closure_ball z (half_pos hr).ne'

/-- The Hölder input of the oscillation engine from the Dirichlet `C^{1/2}` estimate and the
vanishing of continuous killed representatives on the boundary. -/
theorem aux_torsion_bound_hHol {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (K : ℝ)
    (hD : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet a F b u →
          ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K * (Kf + Cphi)) :
    ∀ (F0 : SpatialCoordinates d → ℝ), Measurable F0 → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |F0 x| ≤ MF) →
      ∀ v : killedSobolevGraph (centeredCube z r hr),
        (∀ w : killedSobolevGraph (centeredCube z r hr), sobolevCoefficientForm a v.val w.val =
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            F0 x * (w : SobolevData (centeredCube z r hr)).1 x) →
        ∃ vc : C(SpatialCoordinates d, ℝ),
          (((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc) ∧
          (∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = 0) ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
              |vc x - vc y| ≤ (K * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ)) * MF *
                dist x y ^ (1 / 2 : ℝ)) := by
  classical
  intro F0 hF0 MF hMF hF0b v hv
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨v.val, killedSobolevGraph_le_weakSobolevGraph v.property⟩
  have hsolve : SolvesDirichlet a F0 0 u := by
    refine ⟨?_, ?_⟩
    · have : ((u : SobolevData (centeredCube z r hr)) -
          ((0 : weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr))) =
          (v : SobolevData (centeredCube z r hr)) := by
        simp [u]
      rw [this]
      exact v.property
    · intro ψ
      exact hv ψ
  have hb : (((0 : weakSobolevGraph (centeredCube z r hr)) :
      SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun _ => (0 : ℝ)) := by
    have h0 : (((0 : weakSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1) = 0 := rfl
    rw [h0]
    exact Lp.coeFn_zero _ _ _
  have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (half_pos hr).le⟩
  have hres := hD F0 MF hMF hF0.aemeasurable
    (by filter_upwards [ae_restrict_mem hQm] with x hx using hF0b x hx)
    (fun _ => (0 : ℝ)) 0 contDiff_const (aux_torsion_bound_c2Norm_zero _ hne) 0 u hb hsolve
  obtain ⟨U, hUc, hUae, hUhol, hUnorm⟩ := hres
  rw [add_zero] at hUnorm
  -- the boundary values vanish
  have hbd : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
    intro x hx
    have hxc : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
      rw [← aux_torsion_bound_closure_cube z r hr]
      exact frontier_subset_closure hx
    have hxo : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [(centeredCube z r hr).isOpen.frontier_eq] at hx
      exact hx.2
    exact killed_continuous_boundary_zero d z r hr v.val v.property U hUc hUae x hxc hxo
  have hcont : Continuous (fun x => if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
      then U x else 0) := by
    refine continuous_if ?_ hUc.continuousOn continuous_const.continuousOn
    intro x hx
    exact hbd x hx
  let vc : C(SpatialCoordinates d, ℝ) := ⟨fun x => if x ∈ (centeredCube z r hr :
    Set (SpatialCoordinates d)) then U x else 0, hcont⟩
  have hvcU : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = U x := by
    intro x hx
    change (if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U x else 0) = U x
    by_cases hxQ : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
    · rw [ite_eq_left hxQ]
    · rw [ite_eq_right hxQ]
      have : x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        rw [(centeredCube z r hr).isOpen.frontier_eq]
        exact ⟨hx, hxQ⟩
      exact (hbd x this).symm
  refine ⟨vc, ?_, ?_, ?_⟩
  · filter_upwards [hUae, ae_restrict_mem hQm] with x hx hxQ
    rw [hx]
    exact (hvcU x (subset_closure hxQ)).symm
  · intro x hx
    change (if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U x else 0) = 0
    rw [ite_eq_right hx]
  · intro x hx y hy
    rw [hvcU x hx, hvcU y hy]
    have hcomp : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
      (closedCube z r hr).isCompact
    rw [aux_torsion_bound_closure_cube] at hx hy
    have h := aux_torsion_bound_holder_pt _ hcomp U hUc (K * MF) hUhol hUnorm x hx y hy
    calc |U x - U y| ≤ K * MF * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ) * dist x y ^ (1 / 2 : ℝ) := h
      _ = (K * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ)) * MF * dist x y ^ (1 / 2 : ℝ) := by ring

end TbC

section TbD
open Set
open _root_.SubdiffusiveProcess.EllipticRegularity
/-! ### Assembly of the analytic supply -/

/-- Every cube lies in the closure of an origin-centred triadic cube. -/
theorem aux_torsion_bound_support_cube {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) :
    ∃ Qs : Homogenization.TriadicCube d,
      (centeredCube z s hs : Set (SpatialCoordinates d)) ⊆
        closure (Homogenization.openCubeSet Qs) ∧
      Bornology.IsBounded (closure (Homogenization.openCubeSet Qs)) := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 * ‖z‖ + s + 1) (by norm_num : (1 : ℝ) < 3)
  let Qs : Homogenization.TriadicCube d := ⟨(m : ℤ), fun _ => 0⟩
  have hscale : Homogenization.cubeScaleFactor Qs = (3 : ℝ) ^ m := by
    change (3 : ℝ) ^ ((m : ℤ)) = (3 : ℝ) ^ m
    exact zpow_natCast 3 m
  refine ⟨Qs, ?_, ?_⟩
  · intro x hx
    apply subset_closure
    change ∀ i, (((0 : ℤ) : ℝ) - (1 / 2 : ℝ)) * Homogenization.cubeScaleFactor Qs < x i ∧
      x i < (((0 : ℤ) : ℝ) + (1 / 2 : ℝ)) * Homogenization.cubeScaleFactor Qs
    intro i
    rw [hscale]
    have hxz : dist x z < s / 2 := hx
    have h1 : |x i - z i| < s / 2 := by
      have := (dist_le_pi_dist x z i).trans_lt hxz
      rwa [Real.dist_eq] at this
    have h2 : |z i| ≤ ‖z‖ := by
      have := norm_le_pi_norm z i
      rwa [Real.norm_eq_abs] at this
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    constructor
    · have := neg_abs_le (x i - z i)
      have := neg_abs_le (z i)
      push_cast
      linarith
    · have := le_abs_self (x i - z i)
      have := le_abs_self (z i)
      push_cast
      linarith
  · refine Bornology.IsBounded.closure ?_
    refine (Homogenization.isBounded_cubeSet Qs).subset ?_
    intro x hx i
    exact ⟨(hx i).1.le, (hx i).2⟩

/-- Uniform cube mass from unit-ball growth (a fixed finite cover of the closure). -/
theorem aux_torsion_bound_cover {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) :
    ∃ V1 : ℝ, 0 ≤ V1 ∧ ∀ (μ : Measure (SpatialCoordinates d)) (Km : ℝ), 0 ≤ Km →
      (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
        μ (Metric.ball x 1) ≤ ENNReal.ofReal Km) →
      μ (centeredCube z s hs : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * Km) := by
  have hcomp : IsCompact (closure (centeredCube z s hs : Set (SpatialCoordinates d))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (centeredCube_isBounded _ hs).closure
  obtain ⟨T, hTsub, hTfin, hcover⟩ := finite_cover_balls_of_compact hcomp one_pos
  refine ⟨(hTfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro μ Km hKm hball
  have hsub : (centeredCube z s hs : Set (SpatialCoordinates d)) ⊆
      ⋃ x ∈ hTfin.toFinset, Metric.ball x 1 := by
    intro y hy
    have := hcover (subset_closure hy)
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨x, hxT, hyx⟩ := this
    exact ⟨x, hTfin.mem_toFinset.2 hxT, hyx⟩
  calc μ (centeredCube z s hs : Set (SpatialCoordinates d))
      ≤ μ (⋃ x ∈ hTfin.toFinset, Metric.ball x 1) := measure_mono hsub
    _ ≤ ∑ x ∈ hTfin.toFinset, μ (Metric.ball x 1) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ hTfin.toFinset, ENNReal.ofReal Km :=
        Finset.sum_le_sum (fun x hx => hball x (hTsub (hTfin.mem_toFinset.1 hx)))
    _ = ENNReal.ofReal ((hTfin.toFinset.card : ℝ) * Km) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- The cutoff speed measure is the weighted cutoff chaos (as in `chaos_cutoff_normalization`). -/
theorem aux_torsion_bound_speed_eq_weighted {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedMeasure M H omega N = weightedChaosCutoff M H N omega := by
  unfold cutoffSpeedMeasure weightedChaosCutoff
  congr 1
  funext x
  simp only [Function.comp_apply, cutoffSpeedDensity, cutoffPotential, fineDensity,
    finePotential]
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- The exponent comparison `r^{2(1/2-(d+2)ε)} ≤ r^{2·(1/4)}` for `0 < r ≤ 1`. -/
theorem aux_torsion_bound_rpow_quarter {d : ℕ} (epsilon : ℝ)
    (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) (1 / (8 * ((d : ℝ) + 2))))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r ^ (2 * (1 / 2 - ((d : ℝ) + 2) * epsilon)) ≤ r ^ (2 * (1 / 4 : ℝ)) := by
  have hq := aux_torsion_bound_quarter_le d epsilon hepsilon
  exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)

/-- The survival resolvent lies in `[0, λ⁻¹]`. -/
theorem aux_torsion_bound_S_bounds {d : ℕ}
    (ν : Measure (ContinuousPath (SpatialCoordinates d))) [IsProbabilityMeasure ν]
    (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ ∫ p, survivalIntegral lam (ContinuousPath.exitTime Q p) ∂ν ∧
      ∫ p, survivalIntegral lam (ContinuousPath.exitTime Q p) ∂ν ≤ lam⁻¹ := by
  refine ⟨integral_nonneg (fun p => survivalIntegral_nonneg _ _), ?_⟩
  calc (∫ p, survivalIntegral lam (ContinuousPath.exitTime Q p) ∂ν)
      ≤ ∫ _p, lam⁻¹ ∂ν :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => survivalIntegral_nonneg _ _)
          (integrable_const _)
          (Filter.Eventually.of_forall fun p => survivalIntegral_le_inv hlam _)
    _ = lam⁻¹ := by simp

/-- The zero-order source density `1 - λ S` is bounded by `1`. -/
theorem aux_torsion_bound_h_bound (S lam : ℝ) (hlam : 0 < lam) (h0 : 0 ≤ S) (h1 : S ≤ lam⁻¹) :
    |1 - lam * S| ≤ 1 := by
  have e1 : 0 ≤ lam * S := mul_nonneg hlam.le h0
  have e2 : lam * S ≤ 1 := by
    calc lam * S ≤ lam * lam⁻¹ := mul_le_mul_of_nonneg_left h1 hlam.le
      _ = 1 := mul_inv_cancel₀ hlam.ne'
  rw [abs_le]
  constructor <;> linarith

/-- Measurability of the survival resolvent in the starting point. -/
theorem aux_torsion_bound_S_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (omega : BilateralField d) (lam : ℝ) (hlam : 0 < lam) :
    Measurable (fun x => ∫ path, survivalIntegral lam
        (ContinuousPath.exitTime Q path) ∂(K (omega, x))) := by
  have hg : Measurable (fun q : SpatialCoordinates d × DiffusionPath d =>
      survivalIntegral lam (ContinuousPath.exitTime Q q.2)) :=
    (measurable_survivalIntegral hlam).comp
      ((ContinuousPath.measurable_exitTime _ hQ).comp measurable_snd)
  exact (hg.stronglyMeasurable.integral_kernel_prod_right'' (η := K) (a := omega)).measurable

/-- The Dirichlet `C^{1/2}` estimate (the form `lem_as_regularity` gives it) for one coefficient. -/
def aux_torsion_bound_DirProp {d : ℕ} (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (a : PositiveCoefficient (centeredCube z s hs)) (K : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
    AEMeasurable F (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂(volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
      ContDiff ℝ 2 phi →
      c2Norm (closedCube z s hs : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z s hs)),
        ((b : SobolevData (centeredCube z s hs)).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet a F b u →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          ((u : SobolevData (centeredCube z s hs)).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] U ∧
          IsHolderOn (1 / 2) (closedCube z s hs : Set (SpatialCoordinates d)) U ∧
          cAlphaNorm (1 / 2) (closedCube z s hs : Set (SpatialCoordinates d)) U ≤
            K * (Kf + Cphi)

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- **One sample, one cube** (`mfd:cor-finite-exit`, the mollification/Campanato step): with the
cutoff-uniform coercivity constant `K1`, Hölder constant `K2` and growth constant `Kmu` of the
fixed sample, one amplitude `A` bounds the square-mean oscillation of every zero-extended
survival resolvent, uniformly in the cutoff and the discount. -/
theorem aux_torsion_bound_fixed_supply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (epsilon : ℝ)
    (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) (1 / (8 * ((d : ℝ) + 2))))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (omega : BilateralField d)
    (hLD : ∀ N, LocalDiffusion (cutoffCoefficient M H omega N)
      (cutoffSpeedDensity M H omega N) (L N omega))
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (Qs : Homogenization.TriadicCube d)
    (hroot : (centeredCube z s hs : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qs))
    (Kmu : ℝ) (hKmu : 0 ≤ Kmu)
    (hgr : ∀ (N : ℕ) (x : SpatialCoordinates d), x ∈ closure (Homogenization.openCubeSet Qs) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        weightedChaosCutoff M H N omega (Metric.ball x r) ≤
          ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (K1 : ℝ) (hK1 : 0 ≤ K1)
    (hcf : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z s hs)),
      cubeFractionalSqNorm hd z s hs threeQuarterOrder (v : SobolevData (centeredCube z s hs)).1 ≤
        K1 * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hs)
          (v : SobolevData (centeredCube z s hs)) (v : SobolevData (centeredCube z s hs)))
    (Cext : ℝ) (hCext : 0 ≤ Cext)
    (hext : ∀ w : killedSobolevGraph (centeredCube z s hs),
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
          (fun x => ((w : SobolevData (centeredCube z s hs)).1) x)) ≤
        ENNReal.ofReal (Cext * cubeFractionalSqNorm hd z s hs threeQuarterOrder
          (w : SobolevData (centeredCube z s hs)).1))
    (K2 : ℝ) (hK2 : 0 ≤ K2)
    (hDir : ∀ N : ℕ, aux_torsion_bound_DirProp z s hs
      (cutoffPositiveCoefficient M H omega N z hs) K2)
    (V1 : ℝ) (hV1 : 0 ≤ V1)
    (hcov : ∀ (μ : Measure (SpatialCoordinates d)) (Km : ℝ), 0 ≤ Km →
      (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
        μ (Metric.ball x 1) ≤ ENNReal.ofReal Km) →
      μ (centeredCube z s hs : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * Km)) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
            (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
                  (centeredCube z s hs : Set (SpatialCoordinates d)) path)
                  ∂(KN N (omega, y))) y -
              (volume.real (Metric.ball x r))⁻¹ *
                ∫ w' in Metric.ball x r,
                  Set.indicator
                    (centeredCube z s hs : Set (SpatialCoordinates d))
                    (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
                      (centeredCube z s hs : Set (SpatialCoordinates d))
                      path) ∂(KN N (omega, y))) w') ^ 2) ≤
            A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ)) := by
  have hε0 : 0 < epsilon := hepsilon.1
  have hε1 : epsilon < 1 := by
    have h8 : (1 : ℝ) < 8 * ((d : ℝ) + 2) := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    exact hepsilon.2.trans ((div_lt_one (by linarith)).2 h8)
  have hQo : IsOpen (centeredCube z s hs : Set (SpatialCoordinates d)) :=
    (centeredCube z s hs).isOpen
  have hQm : MeasurableSet (centeredCube z s hs : Set (SpatialCoordinates d)) := hQo.measurableSet
  have hclQ : closure (centeredCube z s hs : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Qs) :=
    closure_minimal hroot isClosed_closure
  -- growth of the actual speed measures, uniform in the cutoff
  have hgS : ∀ (N : ℕ), ∀ x ∈ closure (Homogenization.openCubeSet Qs), ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ 1 → cutoffSpeedMeasure M H omega N (Metric.ball x ρ) ≤
        ENNReal.ofReal (Kmu * ρ ^ ((d : ℝ) - epsilon)) := by
    intro N x hx ρ hρ hρ1
    rw [aux_torsion_bound_speed_eq_weighted]
    exact hgr N x hx ρ hρ hρ1
  have hgQ : ∀ (N : ℕ), ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → cutoffSpeedMeasure M H omega N (Metric.ball x ρ) ≤
        ENNReal.ofReal (Kmu * ρ ^ ((d : ℝ) - epsilon)) :=
    fun N x hx => hgS N x (hclQ hx)
  have hV : ∀ N : ℕ, cutoffSpeedMeasure M H omega N
      (centeredCube z s hs : Set (SpatialCoordinates d)) ≤ ENNReal.ofReal (V1 * Kmu) := by
    intro N
    refine hcov _ Kmu hKmu (fun x hx => ?_)
    have h := hgQ N x hx 1 one_pos le_rfl
    rwa [Real.one_rpow, mul_one] at h
  have hV0 : 0 ≤ V1 * Kmu := mul_nonneg hV1 hKmu
  have hKc : 0 ≤ K1 * (s ^ d + Cext) := mul_nonneg hK1 (add_nonneg (pow_nonneg hs.le d) hCext)
  have hKh : 0 ≤ K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ) :=
    mul_nonneg hK2 (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨|aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s Kmu (V1 * Kmu)
      (K1 * (s ^ d + Cext)) (K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ))|, abs_nonneg _, ?_⟩
  intro N lam hlam
  have := hKN N
  let K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)) :=
    (KN N).comap (fun x => (omega, x)) (measurable_const.prodMk measurable_id)
  have hKmk : IsMarkovKernel K := by infer_instance
  have hLK : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = L N omega x :=
    fun x => hL N omega x
  have hid := aux_torsion_bound_ident M H omega N K (L N omega) hLK (hLD N) z s hs lam hlam
  rcases hid with ⟨u, hu_ae, hu_fin⟩
  have hSm := aux_torsion_bound_S_measurable (centeredCube z s hs : Set (SpatialCoordinates d))
    hQo (KN N) omega lam hlam
  have hhm : AEStronglyMeasurable (fun y => 1 - lam * ∫ p, survivalIntegral lam
      (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) p) ∂K y)
      ((cutoffSpeedMeasure M H omega N).restrict
        (centeredCube z s hs : Set (SpatialCoordinates d))) :=
    (measurable_const.sub (measurable_const.mul hSm)).aestronglyMeasurable
  have hhb : ∀ᵐ y ∂((cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z s hs : Set (SpatialCoordinates d))),
      |1 - lam * ∫ p, survivalIntegral lam
        (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) p) ∂K y| ≤ 1 := by
    refine ae_of_all _ (fun y => ?_)
    have hb := aux_torsion_bound_S_bounds (K y)
      (centeredCube z s hs : Set (SpatialCoordinates d)) lam hlam
    exact aux_torsion_bound_h_bound _ lam hlam hb.1 hb.2
  have hac : (cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z s hs : Set (SpatialCoordinates d)) ≪ volume :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (withDensity_absolutelyContinuous _ _)
  have hbd : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      (∫ y in Metric.ball x r,
        (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
            (fun y => (u : SobolevData (centeredCube z s hs)).1 y) y -
          (volume.real (Metric.ball x r))⁻¹ *
            ∫ w' in Metric.ball x r,
              Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                (fun y => (u : SobolevData (centeredCube z s hs)).1 y) w') ^ 2) ≤
        |aux_prop_uniform_resolvent_cutoff_oscillation_Kinst d epsilon s Kmu (V1 * Kmu)
          (K1 * (s ^ d + Cext)) (K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ))| ^ 2 *
          volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ)) := by
    intro x r hr0 hr1
    have hins := aux_torsion_bound_osc_instance hd epsilon hε0 hε1 Qs z s hs hroot
      (cutoffSpeedMeasure M H omega N) hac Kmu (V1 * Kmu) (K1 * (s ^ d + Cext))
      (K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ)) hKmu hV0 hKc hKh (hgQ N) (hgS N) (hV N)
      (cutoffPositiveCoefficient M H omega N z hs)
      (aux_torsion_bound_hcoer hd z s hs _ K1 Cext hK1 hCext hext (hcf N))
      (aux_torsion_bound_hHol z s hs _ K2 (hDir N)) u
      (fun y => 1 - lam * ∫ p, survivalIntegral lam
        (ContinuousPath.exitTime (centeredCube z s hs : Set (SpatialCoordinates d)) p) ∂K y)
      hhm 1 zero_le_one hhb hu_fin
      (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
        (fun y => (u : SobolevData (centeredCube z s hs)).1 y)) (fun _ => rfl) x r hr0 hr1
    refine hins.trans ?_
    rw [mul_one, ← sq_abs]
    have hvol : 0 ≤ volume.real (Metric.ball x r) := measureReal_nonneg
    exact mul_le_mul_of_nonneg_left (aux_torsion_bound_rpow_quarter epsilon hepsilon r hr0 hr1)
      (mul_nonneg (sq_nonneg _) hvol)
  intro x r hr0 hr1
  exact aux_torsion_bound_osc_congr (centeredCube z s hs : Set (SpatialCoordinates d)) hQm
    (fun y => (u : SobolevData (centeredCube z s hs)).1 y)
    (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
      (centeredCube z s hs : Set (SpatialCoordinates d)) path) ∂(KN N (omega, y)))
    hu_ae _ (1 / 4) hbd x r hr0 hr1

/-- Analytic supply (`mfd:cor-finite-exit`): the mollified-source oscillation estimate for the
zero-extended finite-cutoff survival resolvents, with one amplitude for every cutoff and every
discount, at every sample of one event and every cube of the family. -/
theorem aux_torsion_bound_supply
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (epsilon : ℝ)
    (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ)
      (1 / (8 * ((d : ℝ) + 2)))) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
        (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
        (hQtriadic : ∀ n : ℕ, ∃ k : ℤ, Qr n = (3 : ℝ) ^ k)
        (hgrowth : ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ Kmu omega ∧
              ∀ N x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon))),
        ∀ n : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ A : ℝ, 0 ≤ A ∧
          ∀ (N : ℕ) (lam : ℝ), 0 < lam →
            ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                (Set.indicator (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))
                    (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
                      (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path)
                      ∂(KN N (omega, y))) y -
                  (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w' in Metric.ball x r,
                      Set.indicator
                        (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))
                        (fun y => ∫ path, survivalIntegral lam (ContinuousPath.exitTime
                          (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))
                          path) ∂(KN N (omega, y))) w') ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * (1 / 4 : ℝ)) := by
  have hAC := lem_as_coarse d hd E _P _X _S _W _Cp D hES Step Dbase Interp 1 (3 / 4) ⟨one_pos, le_rfl⟩
    ⟨by norm_num, by norm_num⟩
  rcases hAC with ⟨δ1, hδ1, hco⟩
  have hAR := lem_as_regularity d hd E _P _X _W D _Cp _S Step Dbase Interp (1 / 2) (3 / 4) ((d : ℝ) - 3 / 4)
    ((d : ℝ) - 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith)
    (by linarith)
  rcases hAR with ⟨δ2, hδ2, hreg⟩
  refine ⟨min 1 (min δ1 δ2), lt_min one_pos (lt_min hδ1 hδ2), ?_⟩
  intro M _Rm Sreg _It hM H hH PN KN hKN hin L hL hLlocal hLstrong Qc Qr hQr hQtriadic hgrowth n
  have hM1 : M.delta ≤ min 1 δ1 :=
    le_min (hM.trans (min_le_left _ _)) (hM.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hM2 : M.delta ≤ min 1 δ2 :=
    le_min (hM.trans (min_le_left _ _)) (hM.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsc := aux_torsion_bound_support_cube (Qc n) (Qr n) (hQr n)
  rcases hsc with ⟨Qs, hroot, hQsb⟩
  have hze := killed_zero_extension_bound hd _S (Qc n) (Qr n) (hQr n)
  rcases hze with ⟨Cext, hCext, hext, -⟩
  have hcv := aux_torsion_bound_cover (Qc n) (Qr n) (hQr n)
  rcases hcv with ⟨V1, hV1, hcov⟩
  have e1 := hco M _Rm Sreg _It H hH hM1 (Qc n) (Qr n) (hQr n) (hQtriadic n)
  have e2 := hreg M _Rm Sreg _It H hH hM2 (Qc n) (Qr n) (hQr n)
  have e3 := hgrowth _ hQsb
  rcases e3 with ⟨Kmu, hKmu⟩
  filter_upwards [e1, e2, hKmu, hLlocal] with omega h1 h2 h3 h4
  rcases h1 with ⟨K1, hK1, hK1c⟩
  rcases h2 with ⟨K2, hK2, hK2c⟩
  exact aux_torsion_bound_fixed_supply hd epsilon hepsilon M H KN hKN L hL omega h4
    (Qc n) (Qr n) (hQr n) Qs hroot (Kmu omega) h3.1
    (fun N x hx r hr0 hr1 => h3.2 N x hx r hr0 hr1) K1 hK1.le
    (fun N v => (hK1c true).2.1 N v) Cext hCext.le hext K2 hK2.le
    (fun N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol =>
      ((hK2c N).1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol).2)
    V1 hV1 hcov

end TbD



theorem torsion_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (epsilon : ℝ)
    (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ)
      (1 / (8 * ((d : ℝ) + 2)))) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
      (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
      (hL : ∀ N omega x,
        Measure.map MarkovProcess.LifetimePath.ofContinuousPath
          (KN N (omega, x)) = L N omega x)
      (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (L N omega))
      (hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
        (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
        (hQexh : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
          ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) :
            Set (SpatialCoordinates d)))
        (hQtriadic : ∀ n : ℕ, ∃ k : ℤ, Qr n = (3 : ℝ) ^ k)
        (hgrowth : ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ Kmu omega ∧
              ∀ N x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)))
        (_hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
              (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
              LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
              (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
              (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                (∫ y in Metric.ball x r,
                    (u y - (volume.real (Metric.ball x r))⁻¹ *
                      ∫ w in Metric.ball x r, u w) ^ 2) ≤
                  A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
              ∃ v : SpatialCoordinates d → ℝ,
                v =ᵐ[volume] u ∧
                (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                  |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
                ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ,
            ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
              ∫⁻ path, ContinuousPath.exitTime (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path
                ∂(KN N (omega, x)) ≤ ENNReal.ofReal Cw := by
  obtain ⟨delta0, hdelta0, hsup⟩ :=
    aux_torsion_bound_supply hd E _P _X _W _Cp D _S hES Step Dbase Interp epsilon hepsilon
  refine ⟨delta0, hdelta0, ?_⟩
  intro M _Rm Sreg _It hM H hH PN KN hKN hin L hL hLlocal hLstrong Qc Qr hQr hQexh hQtriadic
    hgrowth hcamp
  have hbounds := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLlocal
  have hstart := in_cutoff_start_continuity hd M H hH PN KN hKN hin hbounds
  exact aux_torsion_bound_core_path hd M H KN hKN L hL hLlocal hLstrong hstart Qc Qr hQr hcamp
    (hsup M _Rm Sreg _It hM H hH PN KN hKN hin L hL hLlocal hLstrong Qc Qr hQr hQtriadic hgrowth)

end SubdiffusiveProcess.Paper

