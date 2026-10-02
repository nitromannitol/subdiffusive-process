import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.SemigroupSymmetric
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.HasStrongMarkovRestart
import SubdiffusiveProcess.Main.HasFiniteMeanExits
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import SubdiffusiveProcess.Main.PhysicalRescaledPath
import SubdiffusiveProcess.Main.PhysicalTimeFactor
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Main.MeasureTraceCharacterization
import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.Main.HalfFractionalOrder
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Sobolev.MeasureTraceSmoothDensity
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane2.KilledInverse
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Probability.CubeMassMartingale
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Inputs.MarkovProcesses
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.Frozen.Vocab.Ahom
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import SubdiffusiveProcess.Paper.in_killed_energy
import SubdiffusiveProcess.Paper.limiting_local_energy
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_19
import SubdiffusiveProcess.Paper.prop_chaos_growth
import SubdiffusiveProcess.Paper.speed_trace_completion
import SubdiffusiveProcess.Paper.killed_zero_extension_bound
import SubdiffusiveProcess.Paper.conv_represented_sequence

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open Homogenization
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

noncomputable section
namespace Paper

/-- Three-epsilon approximation for real sequences. -/
theorem aux_lem_varying_trace_three_eps
    (x : ℕ → ℝ) (y : ℝ) (z : ℕ → ℕ → ℝ) (zl : ℕ → ℝ) (e dN : ℕ → ℝ) (B : ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hdN : Tendsto dN atTop (𝓝 0))
    (hz : ∀ n, Tendsto (z n) atTop (𝓝 (zl n)))
    (hxz : ∀ n N, |x N - z n N| ≤ B * (dN N + e n))
    (hzy : ∀ n, |zl n - y| ≤ B * e n) :
    Tendsto x atTop (𝓝 y) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hBe : Tendsto (fun n => B * e n) atTop (𝓝 0) := by
    simpa using he.const_mul B
  have hBd : Tendsto (fun N => B * dN N) atTop (𝓝 0) := by
    simpa using hdN.const_mul B
  obtain ⟨n, hn⟩ :=
    (hBe.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists
  obtain ⟨N0, hN0⟩ :=
    eventually_atTop.1 (hBd.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4)))
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 (hz n) (ε / 4) (by positivity)
  refine ⟨max N0 N1, fun N hN => ?_⟩
  have h0 := hN0 N (le_of_max_le_left hN)
  have h1 := hN1 N (le_of_max_le_right hN)
  rw [Real.dist_eq] at h1 ⊢
  have h2 := hxz n N
  have h3 := hzy n
  have htri : |x N - y| ≤ |x N - z n N| + |z n N - zl n| + |zl n - y| := by
    calc |x N - y| ≤ |x N - z n N| + |z n N - y| := abs_sub_le _ _ _
      _ ≤ |x N - z n N| + (|z n N - zl n| + |zl n - y|) := by
          gcongr; exact abs_sub_le _ _ _
      _ = _ := by ring
  rw [mul_add] at h2
  linarith

/-- The square integral of an `L²` class is its squared norm. -/
theorem aux_lem_varying_trace_integral_sq {d : ℕ} {ν : Measure (SpatialCoordinates d)}
    (a : Lp ℝ 2 ν) : ∫ x, (a x) ^ 2 ∂ν = ‖a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]

/-- The norm of `toLp f` is the square root of `∫ f²`. -/
theorem aux_lem_varying_trace_norm_toLp {d : ℕ} {ν : Measure (SpatialCoordinates d)}
    (f : SpatialCoordinates d → ℝ) (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, (f x) ^ 2 ∂ν) := by
  have h1 := aux_lem_varying_trace_integral_sq (hf.toLp f)
  have h2 : ∫ x, ((hf.toLp f) x) ^ 2 ∂ν = ∫ x, (f x) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [← h2, h1, Real.sqrt_sq (norm_nonneg _)]

/-- Linear functionals `g ↦ ∫ f g` against a bounded continuous `f` are Lipschitz on `L²`
of a finite measure. -/
theorem aux_lem_varying_trace_linear_bound {d : ℕ} {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasure ν] (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (a b : Lp ℝ 2 ν) :
    |∫ x, f x * a x ∂ν - ∫ x, f x * b x ∂ν| ≤
      (ν Set.univ).toReal ^ (1 / 2 : ℝ) * ‖f‖ * ‖a - b‖ := by
  have hF : MemLp (fun x => f x) 2 ν :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  have hint : ∀ g : Lp ℝ 2 ν, ∫ x, f x * g x ∂ν = inner ℝ (hF.toLp (fun x => f x)) g := by
    intro g
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    simp [RCLike.inner_apply, hx, mul_comm]
  rw [hint a, hint b, ← inner_sub_right]
  have hFn : ‖hF.toLp (fun x => f x)‖ ≤ (ν Set.univ).toReal ^ (1 / 2 : ℝ) * ‖f‖ := by
    have := Lp.norm_le_of_ae_bound (f := hF.toLp (fun x => f x)) (norm_nonneg f)
      (by filter_upwards [hF.coeFn_toLp] with x hx; rw [hx]; exact f.norm_coe_le_norm x)
    simpa [measureUnivNNReal, one_div] using this
  calc |inner ℝ (hF.toLp (fun x => f x)) (a - b)|
      ≤ ‖hF.toLp (fun x => f x)‖ * ‖a - b‖ := abs_real_inner_le_norm _ _
    _ ≤ ((ν Set.univ).toReal ^ (1 / 2 : ℝ) * ‖f‖) * ‖a - b‖ := by
        gcongr

/-- Local weak convergence of measures supported on a compact set passes to all continuous
integrands. -/
theorem aux_lem_varying_trace_cc_tendsto {d : ℕ}
    (μN : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hconv : MeasuresConvergeLocally μN μ)
    {S : Set (SpatialCoordinates d)} (hS : IsCompact S)
    (hN : ∀ N, μN N Sᶜ = 0) (h : μ Sᶜ = 0)
    (g : SpatialCoordinates d → ℝ) (hg : Continuous g) :
    Tendsto (fun N => ∫ x, g x ∂μN N) atTop (𝓝 (∫ x, g x ∂μ)) := by
  obtain ⟨χ, hχ1, -, hχc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hS isClosed_empty (Set.disjoint_empty S)
  let G : C_c(SpatialCoordinates d, ℝ) :=
    ⟨⟨fun x => χ x * g x, χ.continuous.mul hg⟩, hχc.mul_right⟩
  have key : ∀ ν : Measure (SpatialCoordinates d), ν Sᶜ = 0 →
      ∫ x, G x ∂ν = ∫ x, g x ∂ν := by
    intro ν hν
    apply integral_congr_ae
    have hae : ∀ᵐ x ∂ν, x ∈ S := mem_ae_iff.2 hν
    filter_upwards [hae] with x hx
    simp [G, hχ1 hx]
  have hG := hconv G
  rw [key μ h] at hG
  simpa only [key _ (hN _)] using hG

theorem aux_lem_varying_trace_norm_nonneg {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := k) hd z r hr s) :
    0 ≤ cubeFractionalL2Norm hd z r hr s f := by
  unfold cubeFractionalL2Norm
  exact add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (Real.rpow_nonneg hr.le _)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

theorem aux_lem_varying_trace_finite {d : ℕ} (ν : Measure (SpatialCoordinates d))
    (S : Set (SpatialCoordinates d)) (Mbar : ℝ≥0∞) (hM : Mbar ≠ ∞) (hS : ν S ≤ Mbar)
    (hc : ν Sᶜ = 0) :
    IsFiniteMeasure ν ∧ (ν Set.univ).toReal ≤ Mbar.toReal := by
  have huniv : ν Set.univ ≤ Mbar := by
    calc ν Set.univ = ν (S ∪ Sᶜ) := by rw [Set.union_compl_self]
      _ ≤ ν S + ν Sᶜ := measure_union_le _ _
      _ = ν S := by rw [hc, add_zero]
      _ ≤ Mbar := hS
  exact ⟨⟨lt_of_le_of_lt huniv hM.lt_top⟩, ENNReal.toReal_mono hM huniv⟩

/-- The common trace estimate `eq:mfd-19` as a Lipschitz bound. -/
theorem aux_lem_varying_trace_trace_lip {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal) ≤ L ^ 2)
    (u v w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (hw : w.val 0 = u.val 0 - v.val 0) :
    ‖T u - T v‖ ≤ L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder w := by
  have h := hT.2.1 u v w hw
  have hn := aux_lem_varying_trace_norm_nonneg hd (Homogenization.cubeCenter Q)
    (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder w
  have hsq : ‖T u - T v‖ ^ 2 ≤ (L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder w) ^ 2 := by
    calc ‖T u - T v‖ ^ 2 ≤ _ := h
      _ ≤ L ^ 2 * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder w) ^ 2 :=
          mul_le_mul_of_nonneg_right hL (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hL0 hn) two_ne_zero).1 hsq

/-- Assembly: the `H^{1/2}` differences vanish, the trace estimate is common, and the fixed
limit is approximated by smooth functions (`eq:mfd-40`). -/
theorem aux_lem_varying_trace_core {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (μN : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hconv : MeasuresConvergeLocally μN μ)
    (hsuppN : ∀ N, μN N (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (hsupp : μ (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (TN : (N : ℕ) → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 (μN N))
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 μ)
    (KN : ℕ → ℝ) (K C : ℝ)
    (hTN : ∀ N, MeasureTraceCharacterization hd Q hr (μN N) (KN N) C (TN N))
    (hT : MeasureTraceCharacterization hd Q hr μ K C T)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hLN : ∀ N, C * (KN N + (μN N (closure (Homogenization.openCubeSet Q))).toReal) ≤ L ^ 2)
    (hL : C * (K + (μ (closure (Homogenization.openCubeSet Q))).toReal) ≤ L ^ 2)
    (Mbar : ℝ≥0∞) (hMbar : Mbar ≠ ∞)
    (hmuNM : ∀ N, μN N (closure (Homogenization.openCubeSet Q)) ≤ Mbar)
    (hmuM : μ (closure (Homogenization.openCubeSet Q)) ≤ Mbar)
    (uN : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (uHalf : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (diff : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (hdiffval : ∀ N, (diff N).val 0 = (uN N).val 0 - uHalf.val 0)
    (hdifflim : Tendsto (fun N => cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (diff N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ x, (TN N (uN N)) x ^ 2 ∂(μN N)) atTop
        (nhds (∫ x, (T uHalf) x ^ 2 ∂μ)) ∧
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Tendsto (fun N : ℕ => ∫ x, f x * (TN N (uN N)) x ∂(μN N)) atTop
          (nhds (∫ x, f x * (T uHalf) x ∂μ)) := by
  have hfinN : ∀ N, IsFiniteMeasure (μN N) ∧ ((μN N) Set.univ).toReal ≤ Mbar.toReal :=
    fun N => aux_lem_varying_trace_finite (μN N) _ Mbar hMbar (hmuNM N) (hsuppN N)
  have hfin : IsFiniteMeasure μ ∧ (μ Set.univ).toReal ≤ Mbar.toReal :=
    aux_lem_varying_trace_finite μ _ Mbar hMbar hmuM hsupp
  haveI : IsFiniteMeasure μ := hfin.1
  have hcpt : IsCompact (closure (Homogenization.openCubeSet Q)) := by
    rw [← centeredCube_eq_openCubeSet Q hr]
    exact (centeredCube_isBounded (Homogenization.cubeCenter Q) hr).isCompact_closure
  have hdense := measureTrace_hdense_of_finiteMeasure_supported hd Q hr μ hsupp uHalf
  rcases hdense with ⟨a, fs, ws, hfs, hfsmu, hfsae, hwsval, hwslim⟩
  have hfsN : ∀ n N, MemLp (fs n) 2 (μN N) := by
    intro n N
    haveI := (hfinN N).1
    exact contDiff_memLp_of_finiteMeasure_supported_closure Q hr (μN N) (hsuppN N) (fs n)
      (hfs n)
  have hTNa : ∀ n N, TN N (a n) = (hfsN n N).toLp (fs n) := fun n N =>
    (hTN N).2.2 (fs n) (hfs n) (a n) (hfsae n) (hfsN n N)
  have hTa : ∀ n, T (a n) = (hfsmu n).toLp (fs n) := fun n =>
    hT.2.2 (fs n) (hfs n) (a n) (hfsae n) (hfsmu n)
  have hA : ∀ N, ‖TN N (uN N) - TN N uHalf‖ ≤
      L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (diff N) := fun N =>
    aux_lem_varying_trace_trace_lip hd Q hr (μN N) (KN N) C (TN N) (hTN N) L hL0 (hLN N)
      _ _ _ (hdiffval N)
  have hB : ∀ n N, ‖TN N uHalf - TN N (a n)‖ ≤
      L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (ws n) := fun n N =>
    aux_lem_varying_trace_trace_lip hd Q hr (μN N) (KN N) C (TN N) (hTN N) L hL0 (hLN N)
      _ _ _ (hwsval n)
  have hB' : ∀ n, ‖T uHalf - T (a n)‖ ≤
      L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (ws n) := fun n =>
    aux_lem_varying_trace_trace_lip hd Q hr μ K C T hT L hL0 hL _ _ _ (hwsval n)
  have hAB : ∀ n N, ‖TN N (uN N) - TN N (a n)‖ ≤
      L * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (diff N) +
        cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (ws n)) := by
    intro n N
    rw [mul_add]
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hA N) (hB n N))
  constructor
  · have hnorm : Tendsto (fun N => ‖TN N (uN N)‖) atTop (𝓝 ‖T uHalf‖) := by
      refine aux_lem_varying_trace_three_eps _ _ (fun n N => ‖TN N (a n)‖)
        (fun n => ‖T (a n)‖) _ _ L hwslim hdifflim ?_ ?_ ?_
      · intro n
        have heqN : (fun N => ‖TN N (a n)‖) =
            fun N => Real.sqrt (∫ x, (fs n x) ^ 2 ∂μN N) := by
          funext N
          rw [hTNa n N, aux_lem_varying_trace_norm_toLp]
        have heq : ‖T (a n)‖ = Real.sqrt (∫ x, (fs n x) ^ 2 ∂μ) := by
          rw [hTa n, aux_lem_varying_trace_norm_toLp]
        beta_reduce
        rw [heqN, heq]
        exact (Real.continuous_sqrt.tendsto _).comp
          (aux_lem_varying_trace_cc_tendsto μN μ hconv hcpt hsuppN hsupp
            (fun x => (fs n x) ^ 2) ((hfs n).continuous.pow 2))
      · intro n N
        exact (abs_norm_sub_norm_le _ _).trans (hAB n N)
      · intro n
        refine (abs_norm_sub_norm_le _ _).trans ?_
        rw [norm_sub_rev]
        exact hB' n
    have hsq := hnorm.pow 2
    simpa only [aux_lem_varying_trace_integral_sq] using hsq
  · intro f
    have hBf0 : 0 ≤ Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖ :=
      mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (norm_nonneg f)
    have hlin : ∀ (ν : Measure (SpatialCoordinates d)), IsFiniteMeasure ν →
        (ν Set.univ).toReal ≤ Mbar.toReal → ∀ (g h : Lp ℝ 2 ν),
        |∫ x, f x * g x ∂ν - ∫ x, f x * h x ∂ν| ≤
          (Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖) * ‖g - h‖ := by
      intro ν hν hνM g h
      refine (aux_lem_varying_trace_linear_bound f g h).trans ?_
      gcongr
    refine aux_lem_varying_trace_three_eps _ _
      (fun n N => ∫ x, f x * (TN N (a n)) x ∂μN N)
      (fun n => ∫ x, f x * (T (a n)) x ∂μ) _ _
      ((Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖) * L) hwslim hdifflim ?_ ?_ ?_
    · intro n
      have heqN : (fun N => ∫ x, f x * (TN N (a n)) x ∂μN N) =
          fun N => ∫ x, f x * fs n x ∂μN N := by
        funext N
        rw [hTNa n N]
        apply integral_congr_ae
        filter_upwards [(hfsN n N).coeFn_toLp] with x hx
        rw [hx]
      have heq : ∫ x, f x * (T (a n)) x ∂μ = ∫ x, f x * fs n x ∂μ := by
        rw [hTa n]
        apply integral_congr_ae
        filter_upwards [(hfsmu n).coeFn_toLp] with x hx
        rw [hx]
      beta_reduce
      rw [heqN, heq]
      exact aux_lem_varying_trace_cc_tendsto μN μ hconv hcpt hsuppN hsupp
        (fun x => f x * fs n x) (f.continuous.mul (hfs n).continuous)
    · intro n N
      haveI := (hfinN N).1
      calc _ ≤ (Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖) * ‖TN N (uN N) - TN N (a n)‖ :=
            hlin (μN N) (hfinN N).1 (hfinN N).2 _ _
        _ ≤ (Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖) * (L * _) :=
            mul_le_mul_of_nonneg_left (hAB n N) hBf0
        _ = _ := by ring
    · intro n
      rw [abs_sub_comm]
      calc _ ≤ (Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖) * ‖T uHalf - T (a n)‖ :=
            hlin μ hfin.1 hfin.2 _ _
        _ ≤ (Mbar.toReal ^ (1 / 2 : ℝ) * ‖f‖) * (L * _) :=
            mul_le_mul_of_nonneg_left (hB' n) hBf0
        _ = _ := by ring



theorem lem_varying_trace
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q) :
    let U : TopologicalSpace.Opens (SpatialCoordinates d) :=
      centeredCube (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (HI : InfraredCharacterization M H)
      (cutoff : ℕ → ℕ)
      (hcutoff : StrictMono cutoff)
      (omegaN : ℕ → BilateralField d)
      (muN : ℕ → Measure (SpatialCoordinates d))
      (mu : Measure (SpatialCoordinates d))
      (muFull : Measure (SpatialCoordinates d)),
      (∀ (N : ℕ),
        muN N = (cutoffSpeedMeasure M H (omegaN N) (cutoff N)).restrict
          (closure U)) →
      mu = muFull.restrict (closure U) →
      MeasuresConvergeLocally
        (fun N => cutoffSpeedMeasure M H (omegaN N) (cutoff N)) muFull →
      muFull (frontier U) = 0 →
      MeasuresConvergeLocally muN mu →
      mu (frontier (Homogenization.openCubeSet Q)) = 0 →
      (∀ (N : ℕ), muN N (closure (Homogenization.openCubeSet Q))ᶜ = 0) →
      mu (closure (Homogenization.openCubeSet Q))ᶜ = 0 →
      ∀ (TN : (N : ℕ) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder →
        Lp ℝ 2 (muN N))
      (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 mu)
      (KN : ℕ → ℝ) (K C : ℝ),
      (∀ (N : ℕ), 0 ≤ KN N) →
      0 ≤ K →
      0 ≤ C →
      (∀ (N : ℕ),
        MeasureTraceCharacterization hd Q hr (muN N) (KN N) C (TN N)) →
      MeasureTraceCharacterization hd Q hr mu K C T →
      ∀ (Kbar : ℝ),
      (∀ (N : ℕ), KN N ≤ Kbar) →
      K ≤ Kbar →
      ∀ (Mbar : ℝ≥0∞),
      Mbar ≠ ∞ →
      (∀ (N : ℕ), muN N (closure (Homogenization.openCubeSet Q)) ≤ Mbar) →
      mu (closure (Homogenization.openCubeSet Q)) ≤ Mbar →
      ∀ (vN : ℕ → killedSobolevGraph U)
      (uNHalf : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder),
      (∀ (N : ℕ), (uNHalf N).val 0 = (vN N : SobolevData U).1) →
      ∀ (ubar : DomainL2 U),
      Tendsto (fun N => (vN N : SobolevData U).1) atTop (nhds ubar) →
      ∀ (Ebound : ℝ),
      0 ≤ Ebound →
      (∀ (N : ℕ),
        in_killed_energy M H HI (omegaN N) (cutoff N)
          (Homogenization.cubeCenter Q) hr (vN N) (vN N) ≤ Ebound) →
      ∀ (Ccoer : ℝ),
      0 < Ccoer →
      (∀ (N : ℕ) (v : killedSobolevGraph U),
        ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr Lane4.threeQuarterOrder,
          v3.val 0 = (v : SobolevData U).1 ∧
            cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
              (Homogenization.cubeScaleFactor Q) hr
              Lane4.threeQuarterOrder v3 ^ 2 ≤
              Ccoer * in_killed_energy M H HI (omegaN N) (cutoff N)
                (Homogenization.cubeCenter Q) hr v v) →
      ∀ (SInterp : CubeFractionalInterpolationInput d hd),
      ∃ uHalf : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder,
        uHalf.val 0 = ubar ∧
        Tendsto (fun N : ℕ => ∫ x, (TN N (uNHalf N)) x ^ 2 ∂(muN N)) atTop
          (nhds (∫ x, (T uHalf) x ^ 2 ∂mu)) ∧
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Tendsto (fun N : ℕ => ∫ x, f x * (TN N (uNHalf N)) x ∂(muN N)) atTop
            (nhds (∫ x, f x * (T uHalf) x ∂mu)) := by
  intro U M H HI cutoff hcutoff omegaN muN mu muFull hmuN hmu hfull hfullfront hconv hfront
    hsuppN hsupp TN T KN K C hKN hK hC hTN hT Kbar hKNbar hKbar Mbar hMbar hmuNM hmuM vN
    uNHalf huNHalf ubar hL2 Ebound hEbound henergy Ccoer hCcoer hcoer SInterp
  -- `H^{3/4}` representatives of the killed data, bounded by the common coercivity
  choose v3 hv3val hv3bd using fun N => hcoer N (vN N)
  have hv3norm : ∀ N, cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr Lane4.threeQuarterOrder (v3 N) ≤
        Real.sqrt (Ccoer * Ebound) := by
    intro N
    have h2 : Ccoer * in_killed_energy M H HI (omegaN N) (cutoff N)
        (Homogenization.cubeCenter Q) hr (vN N) (vN N) ≤ Ccoer * Ebound :=
      mul_le_mul_of_nonneg_left (henergy N) hCcoer.le
    exact (le_abs_self _).trans (Real.abs_le_sqrt ((hv3bd N).trans h2))
  have hv3lim : Tendsto (fun N => (v3 N).val 0) atTop (𝓝 ubar) := by
    have hfun : (fun N => (v3 N).val 0) = fun N => (vN N : SobolevData U).1 := by
      funext N
      exact hv3val N
    rw [hfun]
    exact hL2
  -- `H^{1/2}` upgrade and membership of the limit (`lem_19`, interpolation step)
  have hup := lem_19_interpolation_upgrade d hd SInterp (Homogenization.cubeCenter Q)
    (Homogenization.cubeScaleFactor Q) hr Lane4.threeQuarterOrder rfl v3 ubar _ hv3norm
    hv3lim
  rcases hup with ⟨uHalf, huHalf, diff, hdiffval, hdifflim⟩
  refine ⟨uHalf, huHalf, ?_⟩
  -- the common trace constant
  have hCst : 0 ≤ C * (Kbar + Mbar.toReal) :=
    mul_nonneg hC (add_nonneg (hK.trans hKbar) ENNReal.toReal_nonneg)
  have hLsq : Real.sqrt (C * (Kbar + Mbar.toReal)) ^ 2 = C * (Kbar + Mbar.toReal) :=
    Real.sq_sqrt hCst
  have hLN : ∀ N, C * (KN N + (muN N (closure (Homogenization.openCubeSet Q))).toReal) ≤
      Real.sqrt (C * (Kbar + Mbar.toReal)) ^ 2 := by
    intro N
    rw [hLsq]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (hKNbar N) (ENNReal.toReal_mono hMbar (hmuNM N))) hC
  have hL : C * (K + (mu (closure (Homogenization.openCubeSet Q))).toReal) ≤
      Real.sqrt (C * (Kbar + Mbar.toReal)) ^ 2 := by
    rw [hLsq]
    exact mul_le_mul_of_nonneg_left (add_le_add hKbar (ENNReal.toReal_mono hMbar hmuM)) hC
  have hdiffval' : ∀ N, (diff N).val 0 = (uNHalf N).val 0 - uHalf.val 0 := by
    intro N
    rw [hdiffval N, hv3val N, huNHalf N, huHalf]
  exact aux_lem_varying_trace_core hd Q hr muN mu hconv hsuppN hsupp TN T KN K C hTN hT
    (Real.sqrt (C * (Kbar + Mbar.toReal))) (Real.sqrt_nonneg _) hLN hL Mbar hMbar hmuNM hmuM
    uNHalf uHalf diff hdiffval' hdifflim

end Paper
