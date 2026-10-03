module

public import SubdiffusiveProcess.Sobolev.MeasureTraceUniqueness
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
public import SubdiffusiveProcess.Main.MeasureTraceCharacterization
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Lane3.DirichletForm
public import SubdiffusiveProcess.Lane2.KilledInverse
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.in_killed_energy
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.speed_trace_completion
public import SubdiffusiveProcess.Paper.lem_varying_trace
public import SubdiffusiveProcess.Paper.finite_speed_resolvent_properties
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.conv_represented_sequence


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess
open SubdiffusiveProcess
open Homogenization
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

noncomputable section
namespace Paper

section PSRBridges
open scoped InnerProductSpace

/-! ### Bridges: `L²` integrals, lower semicontinuity, subsequences, trace bounds -/

theorem aux_prop_speed_resolvent_sq_integral_congr {d : ℕ}
    {ν : Measure (SpatialCoordinates d)} (J : SpatialCoordinates d → ℝ) (a : Lp ℝ 2 ν)
    (hJ : J =ᵐ[ν] ⇑a) :
    ∫ x, J x ^ 2 ∂ν = ‖a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hJ] with x hx
  rw [hx]
  simp [pow_two]

theorem aux_prop_speed_resolvent_f_integral_inner {d : ℕ}
    {ν : Measure (SpatialCoordinates d)}
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hf : MemLp (fun x => f x) 2 ν)
    (J : SpatialCoordinates d → ℝ) (a : Lp ℝ 2 ν) (hJ : J =ᵐ[ν] ⇑a) :
    ∫ x, f x * J x ∂ν = ⟪hf.toLp (fun x => f x), a⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hJ, hf.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem aux_prop_speed_resolvent_elim_lsc {d : ℕ}
    {U : TopologicalSpace.Opens (SpatialCoordinates d)}
    (G : DomainL2 U →L[ℝ] DomainL2 U) :
    LowerSemicontinuous (fun u : DomainL2 U => (limitFormEnergy G u).toENNReal) := by
  apply Continuous.comp_lowerSemicontinuous EReal.continuous_toENNReal ?_ ?_
  · unfold limitFormEnergy
    apply lowerSemicontinuous_iSup
    intro f
    apply Continuous.lowerSemicontinuous
    apply EReal.continuous_coe_iff.mpr
    fun_prop
  · intro x y h
    exact EReal.toENNReal_le_toENNReal h

theorem aux_prop_speed_resolvent_converge_comp {d : ℕ}
    (μN : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (h : MeasuresConvergeLocally μN μ) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    MeasuresConvergeLocally (fun n => μN (φ n)) μ := by
  intro f
  exact (h f).comp hφ.tendsto_atTop

theorem aux_prop_speed_resolvent_trace_bound {d : ℕ}
    {ν : Measure (SpatialCoordinates d)} (J : SpatialCoordinates d → ℝ) (a : Lp ℝ 2 ν)
    (hJ : J =ᵐ[ν] ⇑a) (Ktr : ℝ) (hKtr : 0 ≤ Ktr) (e : ℝ≥0∞) (he : e ≠ ∞)
    (h : ∫⁻ x, ENNReal.ofReal (J x ^ 2) ∂ν ≤ ENNReal.ofReal Ktr * e) :
    ‖a‖ ^ 2 ≤ Ktr * e.toReal := by
  have h1 : ‖a‖ ^ 2 = ∫ x, J x ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hnonneg : 0 ≤ᶠ[ae ν] fun x => J x ^ 2 := Eventually.of_forall fun x => sq_nonneg _
  have hmeas : AEStronglyMeasurable (fun x => J x ^ 2) ν := by
    have h' : AEStronglyMeasurable (fun x => ((↑↑a : SpatialCoordinates d → ℝ) x) ^ 2) ν :=
      (Lp.memLp a).integrable_sq.aestronglyMeasurable
    exact h'.congr (hJ.mono fun x hx => by
      show ((↑↑a : SpatialCoordinates d → ℝ) x) ^ 2 = J x ^ 2
      rw [hx])
  have h2 : ∫ x, J x ^ 2 ∂ν = (∫⁻ x, ENNReal.ofReal (J x ^ 2) ∂ν).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
  rw [h1, h2]
  calc (∫⁻ x, ENNReal.ofReal (J x ^ 2) ∂ν).toReal
      ≤ (ENNReal.ofReal Ktr * e).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top he) h
    _ = Ktr * e.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKtr]

/-- Two half-order
representatives with the same `L²` value have the same completion trace. -/
theorem aux_prop_speed_resolvent_trace_congr {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T)
    (u v : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (huv : u.val 0 = v.val 0) :
    T u = T v := by
  obtain ⟨w, hw⟩ := hT.1 u v
  have hw0 : w.val 0 = 0 := by rw [hw, huv, sub_self]
  have hnorm : cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder w = 0 := by
    unfold cubeFractionalL2Norm cubeFractionalL2Seminorm
    simp only [Fin.sum_univ_one]
    have hg : (fun x => (w.val 0).val.cast x) =ᵐ[
        volume.restrict (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))] 0 := by
      have h := Lp.coeFn_zero (E := ℝ) (p := 2)
        (μ := volume.restrict (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)))
      rw [← hw0] at h
      exact h
    have hint : (∫⁻ x in (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (((w.val 0).val.cast x - (w.val 0).val.cast y) ^ (2:ℕ)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2:ℕ)))) ^
              ((d:ℝ) + 2 * (halfFractionalOrder : ℝ))) = 0 := by
      rw [show (0:ℝ≥0∞) = ∫⁻ x in (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)),
          (0:ℝ≥0∞) from by simp]
      apply lintegral_congr_ae
      filter_upwards [hg] with x hx
      apply lintegral_congr_ae
      filter_upwards [hg] with y hy
      simp [hx, hy]
    rw [hint, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)]
    simp only [ENNReal.toReal_zero, zero_add]
    rw [hw0]
    simp
  have h := hT.2.1 u v w hw
  rw [hnorm] at h
  have h2 : ‖T u - T v‖ ^ 2 ≤ 0 := by
    calc ‖T u - T v‖ ^ 2
        ≤ C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal) * (0:ℝ)^2 := h
      _ = 0 := by ring
  have h0 : ‖T u - T v‖ = 0 := by
    nlinarith [norm_nonneg (T u - T v), h2]
  exact norm_sub_eq_zero_iff.mp h0

/-- Lower bound of the variational functional (completing the square). -/
theorem aux_prop_speed_resolvent_bdd_below
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W) (g : W) (lam : ℝ) (hlam : 0 < lam) (w : V) :
    -(‖g‖ ^ 2 / lam) ≤ (E w).toReal + lam * ‖A w‖ ^ 2 - 2 * ⟪g, A w⟫_ℝ := by
  have h1 : ⟪g, A w⟫_ℝ ≤ ‖g‖ * ‖A w‖ := real_inner_le_norm g (A w)
  have h2 : 0 ≤ (E w).toReal := ENNReal.toReal_nonneg
  have h3 : 0 ≤ (lam * ‖A w‖ - ‖g‖) ^ 2 / lam := div_nonneg (sq_nonneg _) hlam.le
  have h4 : (lam * ‖A w‖ - ‖g‖) ^ 2 / lam =
      lam * ‖A w‖ ^ 2 - 2 * (‖g‖ * ‖A w‖) + ‖g‖ ^ 2 / lam := by
    field_simp
    ring
  have h5 : -(‖g‖ ^ 2 / lam) ≤ lam * ‖A w‖ ^ 2 - 2 * (‖g‖ * ‖A w‖) := by linarith
  linarith

/-- Midpoint identity: for `a, b` of finite energy,
`F((a+b)/2) = (F a + F b)/2 - Q((a-b)/2)` with `Q = E.toReal + lam ‖A ·‖²`. -/
theorem aux_prop_speed_resolvent_midpoint
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W) (g : W) (lam : ℝ)
    (hE0 : E 0 = 0)
    (hclosed : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ → E (c • w1 + w2) ≠ ∞)
    (hpara : ∀ w1 w2 : V, E w1 ≠ ∞ → E w2 ≠ ∞ →
      (E (w1 + w2)).toReal + (E (w1 - w2)).toReal =
        2 * (E w1).toReal + 2 * (E w2).toReal)
    (hscale : ∀ (c : ℝ) (u : V), E u ≠ ∞ → E (c • u) = ENNReal.ofReal (c ^ 2) * E u)
    (hAlin : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ →
      A (c • w1 + w2) = c • A w1 + A w2)
    (a b : V) (ha : E a ≠ ∞) (hb : E b ≠ ∞) :
    (E ((1 / 2 : ℝ) • (a + b))).toReal + lam * ‖A ((1 / 2 : ℝ) • (a + b))‖ ^ 2 -
        2 * ⟪g, A ((1 / 2 : ℝ) • (a + b))⟫_ℝ =
      ((E a).toReal + lam * ‖A a‖ ^ 2 - 2 * ⟪g, A a⟫_ℝ +
          ((E b).toReal + lam * ‖A b‖ ^ 2 - 2 * ⟪g, A b⟫_ℝ)) / 2 -
        ((E ((1 / 2 : ℝ) • (a - b))).toReal +
          lam * ‖A ((1 / 2 : ℝ) • (a - b))‖ ^ 2) := by
  have hE0ne : E (0:V) ≠ ∞ := by rw [hE0]; exact ENNReal.zero_ne_top
  have hA0 : A 0 = 0 := by
    have h := hAlin 1 0 0 hE0ne hE0ne
    simp only [one_smul, zero_add] at h
    exact (add_left_cancel (show A 0 + 0 = A 0 + A 0 by rw [add_zero]; exact h)).symm
  have hsmul : ∀ x : V, E x ≠ ∞ → A ((1/2:ℝ) • x) = (1/2:ℝ) • A x := by
    intro x hx
    have h := hAlin (1/2) x 0 hx hE0ne
    simp only [add_zero, hA0] at h
    exact h
  have hEab : E (a + b) ≠ ∞ := by simpa using hclosed 1 a b ha hb
  have hEabm : E (a - b) ≠ ∞ := by
    have h := hclosed (-1) b a hb ha
    rw [neg_one_smul ℝ b, neg_add_eq_sub b a] at h
    exact h
  have hsum : A (a + b) = A a + A b := by
    have h := hAlin 1 a b ha hb
    simpa using h
  have hdiff : A (a - b) = A a - A b := by
    have h := hAlin (-1) b a hb ha
    rw [neg_one_smul ℝ b, neg_add_eq_sub b a, neg_one_smul ℝ (A b),
        neg_add_eq_sub (A b) (A a)] at h
    exact h
  have hssum : A ((1/2:ℝ) • (a + b)) = (1/2:ℝ) • (A a + A b) := by
    rw [hsmul (a+b) hEab, hsum]
  have hsdiff : A ((1/2:ℝ) • (a - b)) = (1/2:ℝ) • (A a - A b) := by
    rw [hsmul (a-b) hEabm, hdiff]
  have hn1 : ‖(1/2:ℝ) • (A a + A b)‖^2 = (1/4:ℝ) * ‖A a + A b‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    ring
  have hn2 : ‖(1/2:ℝ) • (A a - A b)‖^2 = (1/4:ℝ) * ‖A a - A b‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    ring
  have hEsm : (E ((1/2:ℝ) • (a + b))).toReal = (1/4:ℝ) * (E (a + b)).toReal := by
    rw [hscale (1/2) (a + b) hEab, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1/2:ℝ)^2)]
    ring
  have hEsm' : (E ((1/2:ℝ) • (a - b))).toReal = (1/4:ℝ) * (E (a - b)).toReal := by
    rw [hscale (1/2) (a - b) hEabm, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1/2:ℝ)^2)]
    ring
  have hEfinal : (E ((1/2:ℝ) • (a + b))).toReal =
      ((E a).toReal + (E b).toReal) / 2 - (E ((1/2:ℝ) • (a - b))).toReal := by
    rw [hEsm, hEsm']
    have hp := hpara a b ha hb
    linarith
  have hAfinal : lam * ‖A ((1/2:ℝ) • (a + b))‖^2 =
      (lam * ‖A a‖^2 + lam * ‖A b‖^2) / 2 - lam * ‖A ((1/2:ℝ) • (a - b))‖^2 := by
    rw [hssum, hsdiff, hn1, hn2]
    have hp : ‖A a + A b‖^2 + ‖A a - A b‖^2 = 2 * (‖A a‖^2 + ‖A b‖^2) := by
      simpa only [sq] using parallelogram_law_with_norm ℝ (A a) (A b)
    have hp' : ‖A a + A b‖^2 = 2 * (‖A a‖^2 + ‖A b‖^2) - ‖A a - A b‖^2 := by
      linarith
    rw [hp']
    ring
  have hInner : ⟪g, A ((1/2:ℝ) • (a + b))⟫_ℝ = (⟪g, A a⟫_ℝ + ⟪g, A b⟫_ℝ) / 2 := by
    rw [hssum, real_inner_smul_right, inner_add_right]
    ring
  rw [hEfinal, hAfinal, hInner]
  ring

theorem aux_prop_speed_resolvent_E_neg
    {V : Type*} [NormedAddCommGroup V] [Module ℝ V] (E : V → ℝ≥0∞)
    (hscale : ∀ (c : ℝ) (u : V), E u ≠ ∞ → E (c • u) = ENNReal.ofReal (c ^ 2) * E u)
    {x : V} (hx : E x ≠ ∞) : E (-x) ≠ ∞ := by
  have h := hscale (-1) x hx
  rw [neg_one_smul] at h
  rw [h, show ((-1:ℝ)) ^ 2 = 1 by norm_num, ENNReal.ofReal_one, one_mul]
  exact hx

/-- Uniqueness of the minimizer (strict convexity through the midpoint
identity and coercivity; no injectivity of `A` is used). -/
theorem aux_prop_speed_resolvent_uniq
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W) (g : W) (lam : ℝ) (hlam : 0 < lam)
    (hE0 : E 0 = 0)
    (hclosed : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ → E (c • w1 + w2) ≠ ∞)
    (hpara : ∀ w1 w2 : V, E w1 ≠ ∞ → E w2 ≠ ∞ →
      (E (w1 + w2)).toReal + (E (w1 - w2)).toReal =
        2 * (E w1).toReal + 2 * (E w2).toReal)
    (hscale : ∀ (c : ℝ) (u : V), E u ≠ ∞ → E (c • u) = ENNReal.ofReal (c ^ 2) * E u)
    (hAlin : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ →
      A (c • w1 + w2) = c • A w1 + A w2)
    (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : V, ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * E w)
    (w u : V) (hw : E w ≠ ∞) (hu : E u ≠ ∞)
    (hwmin : ∀ v : V, E v ≠ ∞ →
      (E w).toReal + lam * ‖A w‖ ^ 2 - 2 * ⟪g, A w⟫_ℝ ≤
        (E v).toReal + lam * ‖A v‖ ^ 2 - 2 * ⟪g, A v⟫_ℝ)
    (humin : ∀ v : V, E v ≠ ∞ →
      (E u).toReal + lam * ‖A u‖ ^ 2 - 2 * ⟪g, A u⟫_ℝ ≤
        (E v).toReal + lam * ‖A v‖ ^ 2 - 2 * ⟪g, A v⟫_ℝ) :
    w = u := by
  obtain ⟨Ccoer, hCpos, hC⟩ := hcoer
  have hE0ne : E 0 ≠ ∞ := by rw [hE0]; exact ENNReal.zero_ne_top
  have hwu : E (w + u) ≠ ∞ := by
    have h := hclosed (1:ℝ) w u hw hu
    simp only [one_smul] at h
    exact h
  have hm : E ((1/2:ℝ) • (w + u)) ≠ ∞ := by
    have h := hclosed (1/2) (w + u) 0 hwu hE0ne
    rwa [add_zero] at h
  have hnu : E (-u) ≠ ∞ := aux_prop_speed_resolvent_E_neg E hscale hu
  have hwmu : E (w - u) ≠ ∞ := by
    have h := hclosed (1:ℝ) w (-u) hw hnu
    simp only [one_smul] at h
    rw [← sub_eq_add_neg] at h
    exact h
  have hd : E ((1/2:ℝ) • (w - u)) ≠ ∞ := by
    have h := hclosed (1/2) (w - u) 0 hwmu hE0ne
    rwa [add_zero] at h
  have hmid := aux_prop_speed_resolvent_midpoint E A g lam hE0 hclosed hpara hscale hAlin w u hw hu
  have hwm := hwmin ((1/2:ℝ) • (w + u)) hm
  have hum := humin ((1/2:ℝ) • (w + u)) hm
  have hQd : (E ((1/2:ℝ) • (w - u))).toReal + lam * ‖A ((1/2:ℝ) • (w - u))‖ ^ 2 ≤ 0 := by
    linarith [hwm, hum, hmid]
  have hEd0 : (E ((1/2:ℝ) • (w - u))).toReal = 0 := by
    have h1 : 0 ≤ (E ((1/2:ℝ) • (w - u))).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ lam * ‖A ((1/2:ℝ) • (w - u))‖ ^ 2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    linarith
  have hEd : E ((1/2:ℝ) • (w - u)) = 0 := by
    have h := ENNReal.ofReal_toReal hd
    rw [hEd0, ENNReal.ofReal_zero] at h
    exact h.symm
  have hcoerce : ENNReal.ofReal (‖(1/2:ℝ) • (w - u)‖ ^ 2) ≤ 0 := by
    have h := hC ((1/2:ℝ) • (w - u))
    rwa [hEd, mul_zero] at h
  have hnorm : ‖(1/2:ℝ) • (w - u)‖ = 0 := by
    have hle : ENNReal.ofReal (‖(1/2:ℝ) • (w - u)‖ ^ 2) = 0 :=
      le_antisymm hcoerce zero_le
    have hle2 : ‖(1/2:ℝ) • (w - u)‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hle
    have h2 : ‖(1/2:ℝ) • (w - u)‖ ^ 2 = 0 := le_antisymm hle2 (sq_nonneg _)
    exact (sq_eq_zero_iff).mp h2
  have hd0 : (1/2:ℝ) • (w - u) = 0 := by
    rwa [norm_eq_zero] at hnorm
  have hsub : w - u = 0 := by
    rcases smul_eq_zero.mp hd0 with h | h
    · norm_num at h
    · exact h
  exact sub_eq_zero.mp hsub

/-- A `1/(n+1)`-minimizing sequence is Cauchy for the energy. -/
theorem aux_prop_speed_resolvent_cauchy_bound
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W) (g : W) (lam : ℝ) (hlam : 0 < lam)
    (hE0 : E 0 = 0)
    (hclosed : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ → E (c • w1 + w2) ≠ ∞)
    (hpara : ∀ w1 w2 : V, E w1 ≠ ∞ → E w2 ≠ ∞ →
      (E (w1 + w2)).toReal + (E (w1 - w2)).toReal =
        2 * (E w1).toReal + 2 * (E w2).toReal)
    (hscale : ∀ (c : ℝ) (u : V), E u ≠ ∞ → E (c • u) = ENNReal.ofReal (c ^ 2) * E u)
    (hAlin : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ →
      A (c • w1 + w2) = c • A w1 + A w2)
    (m : ℝ)
    (hm : ∀ v : V, E v ≠ ∞ → m ≤ (E v).toReal + lam * ‖A v‖ ^ 2 - 2 * ⟪g, A v⟫_ℝ)
    (u : ℕ → V) (hu : ∀ n, E (u n) ≠ ∞)
    (huF : ∀ n : ℕ,
      (E (u n)).toReal + lam * ‖A (u n)‖ ^ 2 - 2 * ⟪g, A (u n)⟫_ℝ ≤
        m + 1 / ((n : ℝ) + 1))
    (p q : ℕ) :
    (E (u p - u q)).toReal ≤ 2 / ((p : ℝ) + 1) + 2 / ((q : ℝ) + 1) := by
  have hp : E (u p) ≠ ∞ := hu p
  have hq : E (u q) ≠ ∞ := hu q
  have h0 : E (0:V) ≠ ∞ := by rw [hE0]; exact ENNReal.zero_ne_top
  have hsfin : E ((1/2:ℝ) • (u p + u q)) ≠ ∞ := by
    have hab : E (u p + u q) ≠ ∞ := by simpa using hclosed 1 (u p) (u q) hp hq
    have h := hclosed (1/2) (u p + u q) 0 hab h0
    simpa using h
  have hmid := aux_prop_speed_resolvent_midpoint E A g lam hE0 hclosed hpara hscale hAlin (u p) (u q) hp hq
  have hm_s := hm ((1/2:ℝ) • (u p + u q)) hsfin
  have hQd : (E ((1/2:ℝ) • (u p - u q))).toReal + lam * ‖A ((1/2:ℝ) • (u p - u q))‖ ^ 2
      ≤ (1 / ((p:ℝ)+1) + 1 / ((q:ℝ)+1)) / 2 := by
    linarith [hmid, hm_s, huF p, huF q]
  have hEd_le : (E ((1/2:ℝ) • (u p - u q))).toReal
      ≤ (E ((1/2:ℝ) • (u p - u q))).toReal + lam * ‖A ((1/2:ℝ) • (u p - u q))‖ ^ 2 := by
    have hnn : 0 ≤ lam * ‖A ((1/2:ℝ) • (u p - u q))‖ ^ 2 := mul_nonneg hlam.le (sq_nonneg _)
    linarith
  have hEd : (E ((1/2:ℝ) • (u p - u q))).toReal
      ≤ (1 / ((p:ℝ)+1) + 1 / ((q:ℝ)+1)) / 2 := le_trans hEd_le hQd
  have hab' : E (u p - u q) ≠ ∞ := by
    have h := hclosed (-1) (u q) (u p) hq hp
    have e : (-1:ℝ) • u q + u p = u p - u q := by rw [neg_one_smul]; abel
    rw [e] at h
    exact h
  have hsc : (E ((1/2:ℝ) • (u p - u q))).toReal = (1/4) * (E (u p - u q)).toReal := by
    rw [hscale (1/2) (u p - u q) hab', ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    ring
  have hfour : (E (u p - u q)).toReal = 4 * (E ((1/2:ℝ) • (u p - u q))).toReal := by linarith
  rw [hfour]
  have h2 : (2:ℝ) / ((p:ℝ)+1) + 2 / ((q:ℝ)+1) = 4 * ((1 / ((p:ℝ)+1) + 1 / ((q:ℝ)+1)) / 2) := by ring
  rw [h2]
  linarith

/-- An energy-Cauchy sequence converges in `V` to a finite-energy limit, with the
energy of the differences controlled (coercivity + completeness + lower semicontinuity). -/
theorem aux_prop_speed_resolvent_complete_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (E : V → ℝ≥0∞) (hlsc : LowerSemicontinuous E)
    (hclosed : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ → E (c • w1 + w2) ≠ ∞)
    (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : V, ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * E w)
    (u : ℕ → V) (hu : ∀ n, E (u n) ≠ ∞)
    (hcau : ∀ p q : ℕ, (E (u p - u q)).toReal ≤ 2 / ((p : ℝ) + 1) + 2 / ((q : ℝ) + 1)) :
    ∃ ulim : V, E ulim ≠ ∞ ∧ Tendsto u atTop (𝓝 ulim) ∧
      ∀ p : ℕ, (E (u p - ulim)).toReal ≤ 2 / ((p : ℝ) + 1) := by
  obtain ⟨Ccoer, hCpos, hcoer⟩ := hcoer
  have hE0 : E 0 ≠ ⊤ := by
    have h := hclosed (-1) (u 0) (u 0) (hu 0) (hu 0)
    simpa using h
  have hneg : ∀ q, E (-u q) ≠ ⊤ := by
    intro q
    have h := hclosed (-1) (u q) 0 (hu q) hE0
    simpa using h
  have hdiff : ∀ p q, E (u p - u q) ≠ ⊤ := by
    intro p q
    have h := hclosed (1:ℝ) (u p) (-u q) (hu p) (hneg q)
    simpa [sub_eq_add_neg] using h
  have hbound : ∀ p q, ‖u p - u q‖ ^ 2 ≤ Ccoer * (E (u p - u q)).toReal := by
    intro p q
    have h := hcoer (u p - u q)
    have hb : ENNReal.ofReal Ccoer * E (u p - u q) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hdiff p q)
    have h' := (ENNReal.ofReal_le_iff_le_toReal hb).mp h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le] at h'
  have hcauchy : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt ((4 * Ccoer) * (1 / ((N : ℝ) + 1))))
    · intro n m N hNn hNm
      have hpq : ‖u n - u m‖ ^ 2 ≤ Ccoer * (2 / ((n : ℝ) + 1) + 2 / ((m : ℝ) + 1)) := by
        have h1 := hbound n m
        have h2 := hcau n m
        have h3 : Ccoer * (E (u n - u m)).toReal ≤ Ccoer * (2 / ((n : ℝ) + 1) + 2 / ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h2 hCpos.le
        linarith
      have hkey : 2 / ((n : ℝ) + 1) + 2 / ((m : ℝ) + 1) ≤ 4 / ((N : ℝ) + 1) := by
        have hNn1 : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
          linarith
        have hNm1 : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by
          have : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hNm
          linarith
        have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have ha : 2 / ((n : ℝ) + 1) ≤ 2 / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_left (by norm_num) hNpos hNn1
        have hb : 2 / ((m : ℝ) + 1) ≤ 2 / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_left (by norm_num) hNpos hNm1
        have h2 : 2 / ((N : ℝ) + 1) + 2 / ((N : ℝ) + 1) = 4 / ((N : ℝ) + 1) := by ring
        linarith [ha, hb, h2]
      have hfin : Ccoer * (2 / ((n : ℝ) + 1) + 2 / ((m : ℝ) + 1)) ≤ Ccoer * (4 / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hkey hCpos.le
      have hnn : ‖u n - u m‖ ^ 2 ≤ Ccoer * (4 / ((N : ℝ) + 1)) := le_trans hpq hfin
      have hs : ‖u n - u m‖ ≤ Real.sqrt (Ccoer * (4 / ((N : ℝ) + 1))) := by
        have := Real.sqrt_le_sqrt hnn
        rwa [Real.sqrt_sq (norm_nonneg _)] at this
      have hrw : Ccoer * (4 / ((N : ℝ) + 1)) = (4 * Ccoer) * (1 / ((N : ℝ) + 1)) := by ring
      rw [hrw] at hs
      simpa [dist_eq_norm] using hs
    · have h1 : Tendsto (fun _ : ℕ => (4 * Ccoer)) atTop (𝓝 (4 * Ccoer)) := tendsto_const_nhds
      have h2 : Tendsto (fun N : ℕ => (4 * Ccoer) * (1 / ((N : ℝ) + 1))) atTop (𝓝 ((4 * Ccoer) * 0)) :=
        h1.mul tendsto_one_div_add_atTop_nhds_zero_nat
      rw [mul_zero] at h2
      have h3 : Tendsto (fun N : ℕ => Real.sqrt ((4 * Ccoer) * (1 / ((N : ℝ) + 1)))) atTop (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp h2
      simpa [Real.sqrt_zero] using h3
  obtain ⟨ulim, hulim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hboundE : ∀ p, E (u p - ulim) ≤ ENNReal.ofReal (2 / ((p : ℝ) + 1)) := by
    intro p
    have hg : Tendsto (fun q : ℕ => u p - u q) atTop (𝓝 (u p - ulim)) :=
      tendsto_const_nhds.sub hulim
    have step1 : E (u p - ulim) ≤ liminf E (𝓝 (u p - ulim)) := hlsc.le_liminf _
    have step2 : liminf E (𝓝 (u p - ulim)) ≤
        liminf (fun q : ℕ => E (u p - u q)) atTop := by
      change (Filter.map E (𝓝 (u p - ulim))).limsInf ≤
        (Filter.map (fun q : ℕ => E (u p - u q)) atTop).limsInf
      have hm : Filter.map (fun q : ℕ => E (u p - u q)) atTop ≤
          Filter.map E (𝓝 (u p - ulim)) := by
        have h2 := Filter.map_mono (m := E) hg
        rwa [Filter.map_map] at h2
      exact limsInf_le_limsInf_of_le hm
    have step3 : liminf (fun q : ℕ => E (u p - u q)) atTop ≤
        ENNReal.ofReal (2 / ((p : ℝ) + 1)) := by
      have hev : ∀ᶠ q in atTop,
          E (u p - u q) ≤ ENNReal.ofReal (2 / ((p : ℝ) + 1) + 2 / ((q : ℝ) + 1)) :=
        Filter.Eventually.of_forall (fun q => by
          rw [← ENNReal.ofReal_toReal (hdiff p q)]
          exact ENNReal.ofReal_le_ofReal (hcau p q))
      have hlim : Tendsto (fun q : ℕ => ENNReal.ofReal (2 / ((p : ℝ) + 1) + 2 / ((q : ℝ) + 1)))
          atTop (𝓝 (ENNReal.ofReal (2 / ((p : ℝ) + 1)))) := by
        have hc : Tendsto (fun _ : ℕ => (2 : ℝ) / ((p : ℝ) + 1)) atTop
            (𝓝 ((2 : ℝ) / ((p : ℝ) + 1))) := tendsto_const_nhds
        have hq : Tendsto (fun q : ℕ => (2 : ℝ) / ((q : ℝ) + 1)) atTop (𝓝 0) := by
          have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
          have hfun : (fun q : ℕ => (2 : ℝ) / ((q : ℝ) + 1)) =
              fun q : ℕ => (2 : ℝ) * (1 / ((q : ℝ) + 1)) := by
            funext q
            rw [mul_one_div]
          rw [hfun]
          simpa only [mul_zero] using h
        have hsum : Tendsto (fun q : ℕ => (2 : ℝ) / ((p : ℝ) + 1) + 2 / ((q : ℝ) + 1))
            atTop (𝓝 ((2 : ℝ) / ((p : ℝ) + 1))) := by
          have h0 := hc.add hq
          simpa only [add_zero] using h0
        exact ENNReal.tendsto_ofReal hsum
      have h4 := liminf_le_liminf hev
      rw [hlim.liminf_eq] at h4
      exact h4
    exact le_trans step1 (le_trans step2 step3)
  have hbound_lim : ∀ p, (E (u p - ulim)).toReal ≤ 2 / ((p : ℝ) + 1) := fun p =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hboundE p)
  refine ⟨ulim, ?_, hulim, hbound_lim⟩
  have h0 : E (u 0 - ulim) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hboundE 0)
  have h := hclosed (-1) (u 0 - ulim) (u 0) h0 (hu 0)
  have hkey : (-1 : ℝ) • (u 0 - ulim) + u 0 = ulim := by simp
  rwa [hkey] at h

/-- Passage to the limit: the value at the limit of a minimizing sequence is at most
the infimum (lower semicontinuity of `E`, continuity of the trace part). -/
theorem aux_prop_speed_resolvent_passage
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W) (g : W) (lam : ℝ) (hlam : 0 < lam)
    (hlsc : LowerSemicontinuous E)
    (hclosed : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ → E (c • w1 + w2) ≠ ∞)
    (hAlin : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ →
      A (c • w1 + w2) = c • A w1 + A w2)
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hAbd : ∀ w : V, E w ≠ ∞ → ‖A w‖ ^ 2 ≤ Ktr * (E w).toReal)
    (m : ℝ) (u : ℕ → V) (ulim : V) (hu : ∀ n, E (u n) ≠ ∞) (hulim : E ulim ≠ ∞)
    (hconv : Tendsto u atTop (𝓝 ulim))
    (hEdiff : Tendsto (fun p => (E (u p - ulim)).toReal) atTop (𝓝 0))
    (hF : Tendsto (fun p => (E (u p)).toReal + lam * ‖A (u p)‖ ^ 2 -
      2 * ⟪g, A (u p)⟫_ℝ) atTop (𝓝 m)) :
    (E ulim).toReal + lam * ‖A ulim‖ ^ 2 - 2 * ⟪g, A ulim⟫_ℝ ≤ m := by
  have hE_diff_ne_top (p : ℕ) : E (u p - ulim) ≠ ∞ := by
    have h := hclosed (-1) ulim (u p) hulim (hu p)
    rw [show (-1 : ℝ) • ulim + u p = u p - ulim from by rw [neg_one_smul]; abel] at h
    exact h
  have hA_sub (p : ℕ) : A (u p - ulim) = A (u p) - A ulim := by
    have h := hAlin (-1) ulim (u p) hulim (hu p)
    simp only [neg_one_smul] at h
    rw [show -ulim + u p = u p - ulim from by abel] at h
    rw [h]
    abel
  have hA_norm_sq_tendsto : Tendsto (fun p : ℕ => ‖A (u p) - A ulim‖ ^ 2) atTop (𝓝 0) := by
    have h_bound (p : ℕ) : ‖A (u p) - A ulim‖ ^ 2 ≤ Ktr * (E (u p - ulim)).toReal := by
      calc
        ‖A (u p) - A ulim‖ ^ 2 = ‖A (u p - ulim)‖ ^ 2 := by rw [hA_sub p]
        _ ≤ Ktr * (E (u p - ulim)).toReal := hAbd (u p - ulim) (hE_diff_ne_top p)
    have hh : Tendsto (fun p : ℕ => Ktr * (E (u p - ulim)).toReal) atTop (𝓝 0) := by
      have := hEdiff.const_mul Ktr
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
      (fun p => by positivity) h_bound
  have hA_norm_tendsto : Tendsto (fun p : ℕ => ‖A (u p) - A ulim‖) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun p => Real.sqrt (‖A (u p) - A ulim‖ ^ 2)) atTop
        (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hA_norm_sq_tendsto
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt.congr (fun p => Real.sqrt_sq (norm_nonneg _))
  have hA_tendsto : Tendsto (fun p => A (u p)) atTop (𝓝 (A ulim)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hA_norm_tendsto
  have hnormsq_tendsto : Tendsto (fun p => ‖A (u p)‖ ^ 2) atTop (𝓝 (‖A ulim‖ ^ 2)) := by
    have := (hA_tendsto.norm).pow 2
    simpa using this
  have hinner_tendsto : Tendsto (fun p => (⟪g, A (u p)⟫_ℝ : ℝ)) atTop (𝓝 (⟪g, A ulim⟫_ℝ : ℝ)) :=
    Filter.Tendsto.inner tendsto_const_nhds hA_tendsto
  set L : ℝ := m - (lam * ‖A ulim‖ ^ 2 - 2 * ⟪g, A ulim⟫_ℝ) with hLdef
  have hEreal_tendsto : Tendsto (fun p => (E (u p)).toReal) atTop (𝓝 L) := by
    have hrhs : Tendsto (fun p => lam * ‖A (u p)‖ ^ 2 - 2 * ⟪g, A (u p)⟫_ℝ) atTop
        (𝓝 (lam * ‖A ulim‖ ^ 2 - 2 * ⟪g, A ulim⟫_ℝ)) :=
      (hnormsq_tendsto.const_mul lam).sub (hinner_tendsto.const_mul 2)
    have hsub := hF.sub hrhs
    have heq : ∀ p, (E (u p)).toReal + lam * ‖A (u p)‖ ^ 2 - 2 * ⟪g, A (u p)⟫_ℝ -
        (lam * ‖A (u p)‖ ^ 2 - 2 * ⟪g, A (u p)⟫_ℝ) = (E (u p)).toReal := fun p => by ring
    exact hsub.congr heq
  have hL_nonneg : 0 ≤ L := ge_of_tendsto' hEreal_tendsto (fun p => ENNReal.toReal_nonneg)
  have hE_ofReal_tendsto : Tendsto (fun p => E (u p)) atTop (𝓝 (ENNReal.ofReal L)) := by
    have h1 : Tendsto (fun p => ENNReal.ofReal ((E (u p)).toReal)) atTop
        (𝓝 (ENNReal.ofReal L)) :=
      (ENNReal.continuous_ofReal.tendsto L).comp hEreal_tendsto
    exact h1.congr (fun p => ENNReal.ofReal_toReal (hu p))
  have hliminf_eq : liminf (fun p => E (u p)) atTop = ENNReal.ofReal L :=
    hE_ofReal_tendsto.liminf_eq
  have hliminf_le : liminf E (𝓝 ulim) ≤ liminf E (map u atTop) :=
    liminf_le_liminf_of_le hconv
  have hcomp : liminf E (map u atTop) = liminf (fun p => E (u p)) atTop :=
    (liminf_comp E u atTop).symm
  have hE_le : E ulim ≤ ENNReal.ofReal L := by
    calc E ulim ≤ liminf E (𝓝 ulim) := hlsc.le_liminf ulim
      _ ≤ liminf E (map u atTop) := hliminf_le
      _ = liminf (fun p => E (u p)) atTop := hcomp
      _ = ENNReal.ofReal L := hliminf_eq
  have hE_toReal_le : (E ulim).toReal ≤ L := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE_le
    rwa [ENNReal.toReal_ofReal hL_nonneg] at h1
  rw [hLdef] at hE_toReal_le
  linarith

/-- Abstract variational Riesz step (paper 4895-4904): existence, minimality and
uniqueness of the minimizer of `E + lam ‖A ·‖² - 2 ⟪g, A ·⟫` on the finite-energy domain. -/
theorem aux_prop_speed_resolvent_abstract_min
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W) (g : W) (lam : ℝ) (hlam : 0 < lam)
    (hlsc : LowerSemicontinuous E)
    (hE0 : E 0 = 0)
    (hclosed : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ → E (c • w1 + w2) ≠ ∞)
    (hpara : ∀ w1 w2 : V, E w1 ≠ ∞ → E w2 ≠ ∞ →
      (E (w1 + w2)).toReal + (E (w1 - w2)).toReal =
        2 * (E w1).toReal + 2 * (E w2).toReal)
    (hscale : ∀ (c : ℝ) (u : V), E u ≠ ∞ → E (c • u) = ENNReal.ofReal (c ^ 2) * E u)
    (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : V, ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * E w)
    (hAlin : ∀ (c : ℝ) (w1 w2 : V), E w1 ≠ ∞ → E w2 ≠ ∞ →
      A (c • w1 + w2) = c • A w1 + A w2)
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hAbd : ∀ w : V, E w ≠ ∞ → ‖A w‖ ^ 2 ≤ Ktr * (E w).toReal) :
    ∃ ustar : V, E ustar ≠ ∞ ∧
      (∀ w : V, E w ≠ ∞ →
        (E ustar).toReal + lam * ‖A ustar‖ ^ 2 - 2 * ⟪g, A ustar⟫_ℝ ≤
          (E w).toReal + lam * ‖A w‖ ^ 2 - 2 * ⟪g, A w⟫_ℝ) ∧
      (∀ w : V, E w ≠ ∞ →
        (∀ v : V, E v ≠ ∞ →
          (E w).toReal + lam * ‖A w‖ ^ 2 - 2 * ⟪g, A w⟫_ℝ ≤
            (E v).toReal + lam * ‖A v‖ ^ 2 - 2 * ⟪g, A v⟫_ℝ) →
        w = ustar) := by
  set F : V → ℝ := fun w => (E w).toReal + lam * ‖A w‖ ^ 2 - 2 * ⟪g, A w⟫_ℝ with hFdef
  set S : Set ℝ := F '' {w : V | E w ≠ ∞} with hSdef
  have hne : S.Nonempty := ⟨F 0, 0, by simp [hE0], rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨-(‖g‖ ^ 2 / lam), ?_⟩
    rintro _ ⟨w, -, rfl⟩
    exact aux_prop_speed_resolvent_bdd_below E A g lam hlam w
  set m : ℝ := sInf S with hmdef
  have hm : ∀ v : V, E v ≠ ∞ → m ≤ F v := fun v hv => csInf_le hbdd ⟨v, hv, rfl⟩
  have hseq : ∀ n : ℕ, ∃ w : V, E w ≠ ∞ ∧ F w ≤ m + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt : m < m + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨w, hw, rfl⟩, hwlt⟩ := exists_lt_of_csInf_lt hne hlt
    exact ⟨w, hw, hwlt.le⟩
  choose u hu huF using hseq
  have hcau := aux_prop_speed_resolvent_cauchy_bound E A g lam hlam hE0 hclosed hpara hscale
    hAlin m hm u hu huF
  obtain ⟨ulim, hulim, hconv, hEp⟩ :=
    aux_prop_speed_resolvent_complete_limit E hlsc hclosed hcoer u hu hcau
  have hinv : Tendsto (fun p : ℕ => 1 / ((p : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hFt : Tendsto (fun p => F (u p)) atTop (𝓝 m) := by
    have hup : Tendsto (fun p : ℕ => m + 1 / ((p : ℝ) + 1)) atTop (𝓝 m) := by
      simpa using hinv.const_add m
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun p => hm (u p) (hu p)) huF
  have hEt : Tendsto (fun p => (E (u p - ulim)).toReal) atTop (𝓝 0) := by
    have hup : Tendsto (fun p : ℕ => 2 / ((p : ℝ) + 1)) atTop (𝓝 0) := by
      have h2 := hinv.const_mul 2
      simp only [mul_zero] at h2
      refine h2.congr (fun p => ?_)
      ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun p => ENNReal.toReal_nonneg) hEp
  have hle : F ulim ≤ m :=
    aux_prop_speed_resolvent_passage E A g lam hlam hlsc hclosed hAlin Ktr hKtr hAbd m u ulim
      hu hulim hconv hEt hFt
  refine ⟨ulim, hulim, fun w hw => hle.trans (hm w hw), ?_⟩
  intro w hw hwmin
  exact aux_prop_speed_resolvent_uniq E A g lam hlam hE0 hclosed hpara hscale hAlin hcoer
    w ulim hw hulim hwmin (fun v hv => hle.trans (hm v hv))


end PSRBridges

section PSRWeak
open Metric

/-- ε-sandwich for real sequences. -/
theorem aux_prop_speed_resolvent_w_sandwich (a : ℕ → ℝ) (A : ℝ)
    (L U : ℕ → ℕ → ℝ) (l u : ℕ → ℝ)
    (hL : ∀ n k, L n k ≤ a k) (hU : ∀ n k, a k ≤ U n k)
    (hLk : ∀ n, Tendsto (L n) atTop (𝓝 (l n))) (hUk : ∀ n, Tendsto (U n) atTop (𝓝 (u n)))
    (hl : Tendsto l atTop (𝓝 A)) (hu : Tendsto u atTop (𝓝 A)) :
    Tendsto a atTop (𝓝 A) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.1 hl (ε / 2) (by linarith)
  obtain ⟨n2, hn2⟩ := Metric.tendsto_atTop.1 hu (ε / 2) (by linarith)
  obtain ⟨k1, hk1⟩ := Metric.tendsto_atTop.1 (hLk (max n1 n2)) (ε / 2) (by linarith)
  obtain ⟨k2, hk2⟩ := Metric.tendsto_atTop.1 (hUk (max n1 n2)) (ε / 2) (by linarith)
  refine ⟨max k1 k2, fun k hk => ?_⟩
  have e1 := hn1 (max n1 n2) (le_max_left _ _)
  have e2 := hn2 (max n1 n2) (le_max_right _ _)
  have e3 := hk1 k (le_of_max_le_left hk)
  have e4 := hk2 k (le_of_max_le_right hk)
  have h1 := hL (max n1 n2) k
  have h2 := hU (max n1 n2) k
  rw [Real.dist_eq, abs_lt] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

/-- A continuous function vanishing off a compact set of finite measure is integrable. -/
theorem aux_prop_speed_resolvent_w_integrable_of_vanish {d : ℕ}
    (ν : Measure (SpatialCoordinates d)) (S : Set (SpatialCoordinates d))
    (hS : IsCompact S) (hνS : ν S < ∞)
    (φ : SpatialCoordinates d → ℝ) (hφ : Continuous φ) (hvan : ∀ x ∉ S, φ x = 0) :
    Integrable φ ν := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hφ.continuousOn
  have hon : IntegrableOn φ S ν := by
    refine Measure.integrableOn_of_bounded (M := C) hνS.ne hφ.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
    exact hC x hx
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro x hx
  by_contra hxS
  exact hx (hvan x hxS)

/-- A continuous function is integrable on a compact set of finite measure. -/
theorem aux_prop_speed_resolvent_w_integrableOn {d : ℕ}
    (ν : Measure (SpatialCoordinates d)) (S : Set (SpatialCoordinates d))
    (hS : IsCompact S) (hνS : ν S < ∞)
    (φ : SpatialCoordinates d → ℝ) (hφ : Continuous φ) :
    IntegrableOn φ S ν := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hφ.continuousOn
  refine Measure.integrableOn_of_bounded (M := C) hνS.ne hφ.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with x hx
  exact hC x hx

/-- Outer cutoff `max 0 (1 - infDist x K / δ)`. -/
def aux_prop_speed_resolvent_w_outer {d : ℕ} (K : Set (SpatialCoordinates d)) (δ : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  max 0 (1 - infDist x K / δ)

/-- Inner cutoff `min 1 (infDist x Uᶜ / δ)`. -/
def aux_prop_speed_resolvent_w_inner {d : ℕ} (U : Set (SpatialCoordinates d)) (δ : ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  min 1 (infDist x Uᶜ / δ)

theorem aux_prop_speed_resolvent_w_outer_continuous {d : ℕ} (K : Set (SpatialCoordinates d))
    (δ : ℝ) : Continuous (aux_prop_speed_resolvent_w_outer K δ) := by
  unfold aux_prop_speed_resolvent_w_outer
  fun_prop

theorem aux_prop_speed_resolvent_w_inner_continuous {d : ℕ} (U : Set (SpatialCoordinates d))
    (δ : ℝ) : Continuous (aux_prop_speed_resolvent_w_inner U δ) := by
  unfold aux_prop_speed_resolvent_w_inner
  fun_prop

theorem aux_prop_speed_resolvent_w_outer_nonneg {d : ℕ} (K : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) : 0 ≤ aux_prop_speed_resolvent_w_outer K δ x :=
  le_max_left _ _

theorem aux_prop_speed_resolvent_w_outer_le_one {d : ℕ} (K : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) :
    aux_prop_speed_resolvent_w_outer K δ x ≤ 1 := by
  unfold aux_prop_speed_resolvent_w_outer
  refine max_le zero_le_one ?_
  have : 0 ≤ infDist x K / δ := div_nonneg infDist_nonneg hδ.le
  linarith

theorem aux_prop_speed_resolvent_w_outer_of_mem {d : ℕ} (K : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) (hx : x ∈ K) :
    aux_prop_speed_resolvent_w_outer K δ x = 1 := by
  unfold aux_prop_speed_resolvent_w_outer
  rw [infDist_zero_of_mem hx, zero_div, sub_zero]
  exact max_eq_right zero_le_one

theorem aux_prop_speed_resolvent_w_outer_of_le {d : ℕ} (K : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) (hx : δ ≤ infDist x K) :
    aux_prop_speed_resolvent_w_outer K δ x = 0 := by
  unfold aux_prop_speed_resolvent_w_outer
  refine max_eq_left ?_
  have : 1 ≤ infDist x K / δ := by rw [le_div_iff₀ hδ]; linarith
  linarith

theorem aux_prop_speed_resolvent_w_inner_nonneg {d : ℕ} (U : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) :
    0 ≤ aux_prop_speed_resolvent_w_inner U δ x :=
  le_min zero_le_one (div_nonneg infDist_nonneg hδ.le)

theorem aux_prop_speed_resolvent_w_inner_le_one {d : ℕ} (U : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) : aux_prop_speed_resolvent_w_inner U δ x ≤ 1 :=
  min_le_left _ _

theorem aux_prop_speed_resolvent_w_inner_of_notMem {d : ℕ} (U : Set (SpatialCoordinates d))
    (δ : ℝ) (x : SpatialCoordinates d) (hx : x ∉ U) :
    aux_prop_speed_resolvent_w_inner U δ x = 0 := by
  unfold aux_prop_speed_resolvent_w_inner
  rw [infDist_zero_of_mem (show x ∈ Uᶜ from hx), zero_div]
  exact min_eq_right zero_le_one

theorem aux_prop_speed_resolvent_w_inner_of_le {d : ℕ} (U : Set (SpatialCoordinates d))
    {δ : ℝ} (hδ : 0 < δ) (x : SpatialCoordinates d) (hx : δ ≤ infDist x Uᶜ) :
    aux_prop_speed_resolvent_w_inner U δ x = 1 := by
  unfold aux_prop_speed_resolvent_w_inner
  refine min_eq_left ?_
  rw [le_div_iff₀ hδ]
  linarith

/-- Outside the closed `δ`-thickening of a nonempty compact `K`, the outer cutoff vanishes. -/
theorem aux_prop_speed_resolvent_w_outer_vanish {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (hKne : K.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (x : SpatialCoordinates d) (hx : x ∉ cthickening δ K) :
    aux_prop_speed_resolvent_w_outer K δ x = 0 := by
  apply aux_prop_speed_resolvent_w_outer_of_le K hδ
  obtain ⟨y, hyK, hy⟩ := hK.exists_infDist_eq_dist hKne x
  rw [hy]
  by_contra hlt
  exact hx (mem_cthickening_of_dist_le x y δ K hyK (le_of_lt (not_le.1 hlt)))

/-- The positive-part version of the restricted-integral convergence. -/
theorem aux_prop_speed_resolvent_w_restrict_tendsto_nonneg {d : ℕ}
    (νF : ℕ → Measure (SpatialCoordinates d)) (μF : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hUne : U.Nonempty) (hUc : (Uᶜ).Nonempty)
    (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hνfin : ∀ k, νF k (cthickening δ0 (closure U)) < ∞)
    (hμfin : μF (cthickening δ0 (closure U)) < ∞)
    (hconv : MeasuresConvergeLocally νF μF)
    (hfr : μF (frontier U) = 0)
    (h : SpatialCoordinates d → ℝ) (hh : Continuous h) (hpos : ∀ x, 0 ≤ h x) :
    Tendsto (fun k => ∫ x, h x ∂((νF k).restrict (closure U))) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict (closure U)))) := by
  set K := closure U with hKdef
  set S := cthickening δ0 K with hSdef
  have hKne : K.Nonempty := hUne.mono subset_closure
  have hKcl : IsClosed K := isClosed_closure
  have hKm : MeasurableSet K := hKcl.measurableSet
  have hScpt : IsCompact S := hK.cthickening
  have hKS : K ⊆ S := self_subset_cthickening K
  set δ : ℕ → ℝ := fun n => δ0 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => div_pos hδ0 (by positivity)
  have hδle : ∀ n, δ n ≤ δ0 := fun n => div_le_self hδ0.le (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [hδdef] using h1.const_div_atTop δ0
  -- eventually `δ n < c` for any `c > 0`
  have hδev : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, δ n < c := fun c hc =>
    (tendsto_order.1 hδlim).2 c hc
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn hh.continuousOn
  set χo : ℕ → SpatialCoordinates d → ℝ := fun n =>
    aux_prop_speed_resolvent_w_outer K (δ n) with hχo
  set χi : ℕ → SpatialCoordinates d → ℝ := fun n =>
    aux_prop_speed_resolvent_w_inner U (δ n) with hχi
  have hχo_app : ∀ n x, χo n x = aux_prop_speed_resolvent_w_outer K (δ n) x :=
    fun _ _ => rfl
  have hχi_app : ∀ n x, χi n x = aux_prop_speed_resolvent_w_inner U (δ n) x :=
    fun _ _ => rfl
  have hχo_cont : ∀ n, Continuous (χo n) := fun n =>
    aux_prop_speed_resolvent_w_outer_continuous K (δ n)
  have hχi_cont : ∀ n, Continuous (χi n) := fun n =>
    aux_prop_speed_resolvent_w_inner_continuous U (δ n)
  have hχo_van : ∀ n, ∀ x ∉ S, χo n x = 0 := by
    intro n x hx
    apply aux_prop_speed_resolvent_w_outer_vanish K hK hKne (hδpos n)
    intro hx'
    exact hx (cthickening_mono (hδle n) K hx')
  have hχi_van : ∀ n, ∀ x ∉ K, χi n x = 0 := by
    intro n x hx
    exact aux_prop_speed_resolvent_w_inner_of_notMem U (δ n) x
      (fun hxU => hx (subset_closure hxU))
  -- compactly supported test functions
  have hcs_o : ∀ n, HasCompactSupport (fun x => h x * χo n x) := by
    intro n
    refine HasCompactSupport.intro hScpt ?_
    intro x hx
    rw [hχo_van n x hx, mul_zero]
  have hcs_i : ∀ n, HasCompactSupport (fun x => h x * χi n x) := by
    intro n
    refine HasCompactSupport.intro hK ?_
    intro x hx
    rw [hχi_van n x hx, mul_zero]
  let Fo : ℕ → C_c(SpatialCoordinates d, ℝ) := fun n =>
    ⟨⟨fun x => h x * χo n x, hh.mul (hχo_cont n)⟩, hcs_o n⟩
  let Fi : ℕ → C_c(SpatialCoordinates d, ℝ) := fun n =>
    ⟨⟨fun x => h x * χi n x, hh.mul (hχi_cont n)⟩, hcs_i n⟩
  -- integrability
  have hint_o : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      Integrable (fun x => h x * χo n x) ν := by
    intro ν hν n
    exact aux_prop_speed_resolvent_w_integrable_of_vanish ν S hScpt hν _
      (hh.mul (hχo_cont n)) (fun x hx => by rw [hχo_van n x hx, mul_zero])
  have hint_i : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      Integrable (fun x => h x * χi n x) ν := by
    intro ν hν n
    refine aux_prop_speed_resolvent_w_integrable_of_vanish ν S hScpt hν _
      (hh.mul (hχi_cont n)) (fun x hx => ?_)
    rw [hχi_van n x (fun hxK => hx (hKS hxK)), mul_zero]
  have hint_K : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ →
      Integrable (K.indicator h) ν := by
    intro ν hν
    rw [integrable_indicator_iff hKm]
    exact (aux_prop_speed_resolvent_w_integrableOn ν S hScpt hν h hh).mono_set hKS
  -- sandwich inequalities
  have hupper : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      ∫ x, h x ∂(ν.restrict K) ≤ ∫ x, h x * χo n x ∂ν := by
    intro ν hν n
    rw [← integral_indicator hKm]
    refine integral_mono (hint_K ν hν) (hint_o ν hν n) (fun x => ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, hχo_app, aux_prop_speed_resolvent_w_outer_of_mem K _ x hx, mul_one]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (hpos x) (aux_prop_speed_resolvent_w_outer_nonneg K _ x)
  have hlower : ∀ (ν : Measure (SpatialCoordinates d)), ν S < ∞ → ∀ n,
      ∫ x, h x * χi n x ∂ν ≤ ∫ x, h x ∂(ν.restrict K) := by
    intro ν hν n
    rw [← integral_indicator hKm]
    refine integral_mono (hint_i ν hν n) (hint_K ν hν) (fun x => ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      calc h x * χi n x ≤ h x * 1 :=
            mul_le_mul_of_nonneg_left (aux_prop_speed_resolvent_w_inner_le_one U _ x) (hpos x)
        _ = h x := mul_one _
    · rw [indicator_of_notMem hx, hχi_van n x hx, mul_zero]
  -- limits of the cutoff integrals against μF
  have hbound_int : Integrable (S.indicator (fun _ => C)) μF := by
    rw [integrable_indicator_iff hScpt.isClosed.measurableSet]
    exact integrableOn_const hμfin.ne
  have hlim_o : Tendsto (fun n => ∫ x, h x * χo n x ∂μF) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict K))) := by
    rw [← integral_indicator hKm]
    refine tendsto_integral_of_dominated_convergence (S.indicator (fun _ => C))
      (fun n => (hh.mul (hχo_cont n)).aestronglyMeasurable) hbound_int ?_ ?_
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      by_cases hxS : x ∈ S
      · rw [indicator_of_mem hxS, Real.norm_eq_abs, abs_mul]
        have h1 : |χo n x| ≤ 1 := by
          rw [abs_of_nonneg (aux_prop_speed_resolvent_w_outer_nonneg K _ x)]
          exact aux_prop_speed_resolvent_w_outer_le_one K (hδpos n) x
        have h2 : |h x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hxS
        calc |h x| * |χo n x| ≤ C * 1 :=
              mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
          _ = C := mul_one C
      · rw [indicator_of_notMem hxS, hχo_van n x hxS, mul_zero, norm_zero]
    · refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        refine tendsto_const_nhds.congr (fun n => ?_)
        rw [hχo_app, aux_prop_speed_resolvent_w_outer_of_mem K _ x hx, mul_one]
      · rw [indicator_of_notMem hx]
        have hpos' : 0 < infDist x K :=
          (hKcl.notMem_iff_infDist_pos hKne).1 hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hδev _ hpos'] with n hn
        rw [hχo_app, aux_prop_speed_resolvent_w_outer_of_le K (hδpos n) x hn.le, mul_zero]
  have hUcl : IsClosed Uᶜ := hU.isClosed_compl
  have hlim_i : Tendsto (fun n => ∫ x, h x * χi n x ∂μF) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict K))) := by
    have hae : U.indicator h =ᵐ[μF] K.indicator h := by
      have hnull : μF {x | U.indicator h x ≠ K.indicator h x} = 0 := by
        refine measure_mono_null (fun x hx => ?_) hfr
        simp only [mem_setOf_eq] at hx
        rw [hU.frontier_eq]
        by_cases hxU : x ∈ U
        · exact absurd (by rw [indicator_of_mem hxU, indicator_of_mem (subset_closure hxU)]) hx
        · by_cases hxK : x ∈ K
          · exact ⟨hxK, hxU⟩
          · exact absurd (by rw [indicator_of_notMem hxU, indicator_of_notMem hxK]) hx
      exact hnull
    rw [← integral_indicator hKm, ← integral_congr_ae hae]
    refine tendsto_integral_of_dominated_convergence (S.indicator (fun _ => C))
      (fun n => (hh.mul (hχi_cont n)).aestronglyMeasurable) hbound_int ?_ ?_
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      by_cases hxS : x ∈ S
      · rw [indicator_of_mem hxS, Real.norm_eq_abs, abs_mul]
        have h1 : |χi n x| ≤ 1 := by
          rw [abs_of_nonneg (aux_prop_speed_resolvent_w_inner_nonneg U (hδpos n) x)]
          exact aux_prop_speed_resolvent_w_inner_le_one U _ x
        have h2 : |h x| ≤ C := by simpa [Real.norm_eq_abs] using hC x hxS
        calc |h x| * |χi n x| ≤ C * 1 :=
              mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
          _ = C := mul_one C
      · rw [indicator_of_notMem hxS, hχi_van n x (fun hxK => hxS (hKS hxK)), mul_zero,
          norm_zero]
    · refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx]
        have hpos' : 0 < infDist x Uᶜ :=
          (hUcl.notMem_iff_infDist_pos hUc).1 (fun h' => h' hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hδev _ hpos'] with n hn
        rw [hχi_app, aux_prop_speed_resolvent_w_inner_of_le U (hδpos n) x hn.le, mul_one]
      · rw [indicator_of_notMem hx]
        refine tendsto_const_nhds.congr (fun n => ?_)
        rw [hχi_app, aux_prop_speed_resolvent_w_inner_of_notMem U _ x hx, mul_zero]
  exact aux_prop_speed_resolvent_w_sandwich
    (fun k => ∫ x, h x ∂((νF k).restrict K)) (∫ x, h x ∂(μF.restrict K))
    (fun n k => ∫ x, h x * χi n x ∂(νF k)) (fun n k => ∫ x, h x * χo n x ∂(νF k))
    (fun n => ∫ x, h x * χi n x ∂μF) (fun n => ∫ x, h x * χo n x ∂μF)
    (fun n k => hlower (νF k) (hνfin k) n) (fun n k => hupper (νF k) (hνfin k) n)
    (fun n => hconv (Fi n)) (fun n => hconv (Fo n)) hlim_i hlim_o

/-- **Restricted weak convergence.** Local (vague) convergence plus a null frontier give
convergence of the integrals of every continuous function over the closed set. -/
theorem aux_prop_speed_resolvent_w_restrict_tendsto {d : ℕ}
    (νF : ℕ → Measure (SpatialCoordinates d)) (μF : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hUne : U.Nonempty) (hUc : (Uᶜ).Nonempty)
    (δ0 : ℝ) (hδ0 : 0 < δ0)
    (hνfin : ∀ k, νF k (cthickening δ0 (closure U)) < ∞)
    (hμfin : μF (cthickening δ0 (closure U)) < ∞)
    (hconv : MeasuresConvergeLocally νF μF)
    (hfr : μF (frontier U) = 0)
    (h : SpatialCoordinates d → ℝ) (hh : Continuous h) :
    Tendsto (fun k => ∫ x, h x ∂((νF k).restrict (closure U))) atTop
      (𝓝 (∫ x, h x ∂(μF.restrict (closure U)))) := by
  have hKS : closure U ⊆ cthickening δ0 (closure U) := self_subset_cthickening _
  have hfinK : ∀ (ν : Measure (SpatialCoordinates d)), ν (cthickening δ0 (closure U)) < ∞ →
      IsFiniteMeasure (ν.restrict (closure U)) := by
    intro ν hν
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hKS).trans_lt hν
  have hp : Continuous (fun x => max (h x) 0) := hh.max continuous_const
  have hm : Continuous (fun x => max (-h x) 0) := hh.neg.max continuous_const
  have hsplit : ∀ (ν : Measure (SpatialCoordinates d)), ν (cthickening δ0 (closure U)) < ∞ →
      ∫ x, h x ∂(ν.restrict (closure U)) =
        ∫ x, max (h x) 0 ∂(ν.restrict (closure U)) -
          ∫ x, max (-h x) 0 ∂(ν.restrict (closure U)) := by
    intro ν hν
    haveI := hfinK ν hν
    have hK' : IsCompact (closure U) := hK
    have i1 : Integrable (fun x => max (h x) 0) (ν.restrict (closure U)) :=
      aux_prop_speed_resolvent_w_integrableOn ν _ hK' ((measure_mono hKS).trans_lt hν) _ hp
    have i2 : Integrable (fun x => max (-h x) 0) (ν.restrict (closure U)) :=
      aux_prop_speed_resolvent_w_integrableOn ν _ hK' ((measure_mono hKS).trans_lt hν) _ hm
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    rcases le_total 0 (h x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  have t1 := aux_prop_speed_resolvent_w_restrict_tendsto_nonneg νF μF U hU hK hUne hUc δ0 hδ0
    hνfin hμfin hconv hfr _ hp (fun x => le_max_right _ _)
  have t2 := aux_prop_speed_resolvent_w_restrict_tendsto_nonneg νF μF U hU hK hUne hUc δ0 hδ0
    hνfin hμfin hconv hfr _ hm (fun x => le_max_right _ _)
  rw [hsplit μF hμfin]
  exact (t1.sub t2).congr (fun k => (hsplit (νF k) (hνfin k)).symm)


/-- Restricted convergence when the limit is infinite on the unit thickening: the limit
test integral of the outer cutoff is the junk value `0`, which forces both sides to vanish. -/
theorem aux_prop_speed_resolvent_restrict_converge_inf {d : ℕ}
    (νN : ℕ → Measure (SpatialCoordinates d)) (ν : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hUne : U.Nonempty) (hUc : (Uᶜ).Nonempty)
    (hνN : ∀ N, IsLocallyFiniteMeasure (νN N))
    (hνS : ν (closure U) ≠ ∞) (hfr : ν (frontier U) = 0)
    (h : MeasuresConvergeLocally νN ν)
    (hinf : ν (cthickening 1 (closure U)) = ∞) (f : C_c(SpatialCoordinates d, ℝ)) :
    Tendsto (fun N => ∫ x, f x ∂((νN N).restrict (closure U))) atTop
      (𝓝 (∫ x, f x ∂(ν.restrict (closure U)))) := by
  set K := closure U with hKdef
  have hKne : K.Nonempty := hUne.mono subset_closure
  have hKcl : IsClosed K := isClosed_closure
  have hKm : MeasurableSet K := hKcl.measurableSet
  have hS2 : IsCompact (cthickening 2 K) := hK.cthickening
  set χ : SpatialCoordinates d → ℝ := aux_prop_speed_resolvent_w_outer K 2 with hχdef
  have hχc : Continuous χ := aux_prop_speed_resolvent_w_outer_continuous K 2
  have hχ0 : ∀ x, 0 ≤ χ x := aux_prop_speed_resolvent_w_outer_nonneg K 2
  have hχK : ∀ x ∈ K, χ x = 1 := fun x hx => aux_prop_speed_resolvent_w_outer_of_mem K 2 x hx
  have hχvan : ∀ x ∉ cthickening 2 K, χ x = 0 :=
    aux_prop_speed_resolvent_w_outer_vanish K hK hKne two_pos
  have hχhalf : ∀ x ∈ cthickening 1 K, (1 / 2 : ℝ) ≤ χ x := by
    intro x hx
    have h1 : infDist x K ≤ 1 := by
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (mem_cthickening_iff.1 hx)
      rwa [ENNReal.toReal_ofReal zero_le_one] at h2
    show (1 / 2 : ℝ) ≤ max 0 (1 - infDist x K / 2)
    exact le_max_of_le_right (by linarith)
  have hχcs : HasCompactSupport χ := HasCompactSupport.intro hS2 hχvan
  let X : C_c(SpatialCoordinates d, ℝ) := ⟨⟨χ, hχc⟩, hχcs⟩
  have hnotint : ¬ Integrable χ ν := by
    intro hi
    have hlt := hi.hasFiniteIntegral
    have hhalf : ENNReal.ofReal (1 / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by norm_num)).ne'
    have hge : ∞ ≤ ∫⁻ x, ‖χ x‖ₑ ∂ν := by
      calc (∞ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) * ν (cthickening 1 K) := by
            rw [hinf, ENNReal.mul_top hhalf]
        _ = ∫⁻ x, (cthickening 1 K).indicator (fun _ => ENNReal.ofReal (1 / 2)) x ∂ν := by
            rw [lintegral_indicator_const isClosed_cthickening.measurableSet]
        _ ≤ ∫⁻ x, ‖χ x‖ₑ ∂ν := by
            apply lintegral_mono
            intro x
            by_cases hx : x ∈ cthickening 1 K
            · rw [indicator_of_mem hx]
              show ENNReal.ofReal (1 / 2) ≤ ‖χ x‖ₑ
              rw [Real.enorm_eq_ofReal (hχ0 x)]
              exact ENNReal.ofReal_le_ofReal (hχhalf x hx)
            · rw [indicator_of_notMem hx]
              exact zero_le
    exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)
  have hχint0 : ∫ x, χ x ∂ν = 0 := integral_undef hnotint
  have hlimχ : Tendsto (fun N => ∫ x, χ x ∂(νN N)) atTop (𝓝 0) := by
    have := h X
    rw [show (∫ x, X x ∂ν) = ∫ x, χ x ∂ν from rfl, hχint0] at this
    exact this
  have hνNK : ∀ N, (νN N).real K ≤ ∫ x, χ x ∂(νN N) := by
    intro N
    haveI := hνN N
    rw [← integral_indicator_one hKm]
    have hi1 : Integrable (K.indicator (1 : SpatialCoordinates d → ℝ)) (νN N) := by
      rw [integrable_indicator_iff hKm]
      exact integrableOn_const hK.measure_lt_top.ne
    have hi2 : Integrable χ (νN N) := hχc.integrable_of_hasCompactSupport hχcs
    refine integral_mono hi1 hi2 (fun x => ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, hχK x hx, Pi.one_apply]
    · rw [indicator_of_notMem hx]
      exact hχ0 x
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn f.continuous.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ hKne.some_mem)
  have hbdN : ∀ N, ‖∫ x, f x ∂((νN N).restrict K)‖ ≤ C * ∫ x, χ x ∂(νN N) := by
    intro N
    haveI := hνN N
    haveI : IsFiniteMeasure ((νN N).restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    have hb := norm_integral_le_of_norm_le_const (μ := (νN N).restrict K)
      (f := fun x => f x) (C := C)
      (by filter_upwards [ae_restrict_mem hKm] with x hx; exact hC x hx)
    calc ‖∫ x, f x ∂((νN N).restrict K)‖ ≤ C * ((νN N).restrict K).real univ := hb
      _ = C * (νN N).real K := by
          rw [Measure.real, Measure.real, Measure.restrict_apply_univ]
      _ ≤ C * ∫ x, χ x ∂(νN N) := mul_le_mul_of_nonneg_left (hνNK N) hC0
  -- the limit vanishes on `U`, hence on `closure U`
  have hUK : U ⊆ K := subset_closure
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set χi : ℕ → SpatialCoordinates d → ℝ := fun n => aux_prop_speed_resolvent_w_inner U (δ n)
    with hχidef
  have hχic : ∀ n, Continuous (χi n) := fun n =>
    aux_prop_speed_resolvent_w_inner_continuous U _
  have hχivan : ∀ n, ∀ x ∉ K, χi n x = 0 := fun n x hx =>
    aux_prop_speed_resolvent_w_inner_of_notMem U _ x (fun hxU => hx (subset_closure hxU))
  have hχics : ∀ n, HasCompactSupport (χi n) := fun n => HasCompactSupport.intro hK (hχivan n)
  let Xi : ℕ → C_c(SpatialCoordinates d, ℝ) := fun n => ⟨⟨χi n, hχic n⟩, hχics n⟩
  have hχi_le : ∀ n x, χi n x ≤ χ x := by
    intro n x
    by_cases hx : x ∈ K
    · rw [hχK x hx]
      exact aux_prop_speed_resolvent_w_inner_le_one U _ x
    · rw [hχivan n x hx]
      exact hχ0 x
  have hstep : ∀ n, ∫ x, χi n x ∂ν ≤ 0 := by
    intro n
    have hle : ∀ N, ∫ x, χi n x ∂(νN N) ≤ ∫ x, χ x ∂(νN N) := by
      intro N
      haveI := hνN N
      exact integral_mono ((hχic n).integrable_of_hasCompactSupport (hχics n))
        (hχc.integrable_of_hasCompactSupport hχcs) (hχi_le n)
    exact le_of_tendsto_of_tendsto' (h (Xi n)) hlimχ hle
  have hlimi : Tendsto (fun n => ∫ x, χi n x ∂ν) atTop (𝓝 (ν.real U)) := by
    rw [← integral_indicator_one hU.measurableSet]
    refine tendsto_integral_of_dominated_convergence (K.indicator 1)
      (fun n => (hχic n).aestronglyMeasurable) ?_ ?_ ?_
    · rw [integrable_indicator_iff hKm]
      exact integrableOn_const hνS
    · intro n
      refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, Pi.one_apply, Real.norm_eq_abs,
          abs_of_nonneg (aux_prop_speed_resolvent_w_inner_nonneg U (hδpos n) x)]
        exact aux_prop_speed_resolvent_w_inner_le_one U _ x
      · rw [indicator_of_notMem hx, hχivan n x hx, norm_zero]
    · refine Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx, Pi.one_apply]
        have hpos' : 0 < infDist x Uᶜ :=
          (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h' => h' hx)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [(tendsto_order.1 hδlim).2 _ hpos'] with n hn
        exact (aux_prop_speed_resolvent_w_inner_of_le U (hδpos n) x hn.le).symm
      · rw [indicator_of_notMem hx]
        refine tendsto_const_nhds.congr (fun n => ?_)
        exact (aux_prop_speed_resolvent_w_inner_of_notMem U _ x hx).symm
  have hνU : ν.real U ≤ 0 := le_of_tendsto' hlimi hstep
  have hfinU : ν U ≠ ∞ := ne_top_of_le_ne_top hνS (measure_mono hUK)
  have hνU0 : ν U = 0 := by
    have h0 : (ν U).toReal = 0 := le_antisymm hνU ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h' | h'
    · exact h'
    · exact absurd h' hfinU
  have hνK0 : ν K = 0 := by
    apply le_antisymm _ zero_le
    calc ν K = ν (U ∪ frontier U) := by rw [hKdef, closure_eq_self_union_frontier]
      _ ≤ ν U + ν (frontier U) := measure_union_le _ _
      _ = 0 := by rw [hνU0, hfr, add_zero]
  have htarget : ∫ x, f x ∂(ν.restrict K) = 0 := by
    rw [Measure.restrict_eq_zero.2 hνK0, integral_zero_measure]
  rw [htarget]
  refine squeeze_zero_norm hbdN ?_
  simpa using hlimχ.const_mul C

/-- Restriction to the closure of an open set with null frontier preserves local
convergence (vague portmanteau; no local finiteness of the limit off the set is needed). -/
theorem aux_prop_speed_resolvent_restrict_converge {d : ℕ}
    (νN : ℕ → Measure (SpatialCoordinates d)) (ν : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hK : IsCompact (closure U))
    (hUne : U.Nonempty) (hUc : (Uᶜ).Nonempty)
    (hνN : ∀ N, IsLocallyFiniteMeasure (νN N))
    (hνS : ν (closure U) ≠ ∞) (hfr : ν (frontier U) = 0)
    (h : MeasuresConvergeLocally νN ν) :
    MeasuresConvergeLocally (fun N => (νN N).restrict (closure U))
      (ν.restrict (closure U)) := by
  intro f
  by_cases hA : ν (cthickening 1 (closure U)) < ∞
  · exact aux_prop_speed_resolvent_w_restrict_tendsto νN ν U hU hK hUne hUc 1 one_pos
      (fun k => by haveI := hνN k; exact hK.cthickening.measure_lt_top) hA h hfr
      (fun x => f x) f.continuous
  · exact aux_prop_speed_resolvent_restrict_converge_inf νN ν U hU hK hUne hUc hνN hνS hfr h
      (top_le_iff.1 (not_lt.1 hA)) f

end PSRWeak

section PSRMosco

/-! ### Mosco along subsequences; the real-analysis cluster step -/

/-- Mosco lower bound along a subsequence (extend `y` to the full sequence by `x`). -/
theorem aux_prop_speed_resolvent_subseq_liminf {X : Type*} [NormedAddCommGroup X]
    (EN : ℕ → X → ℝ≥0∞) (Elim : X → ℝ≥0∞) (hlim : Lane3.MoscoLiminf EN Elim)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (y : ℕ → X) (x : X)
    (hy : Tendsto y atTop (𝓝 x)) :
    Elim x ≤ liminf (fun n => EN (phi n) (y n)) atTop := by
  classical
  let z : ℕ → X := fun N => if h : ∃ n, phi n = N then y (Classical.choose h) else x
  have hz : ∀ n, z (phi n) = y n := by
    intro n
    have h : ∃ m, phi m = phi n := ⟨n, rfl⟩
    simp only [z, dif_pos h]
    rw [hphi.injective (Classical.choose_spec h)]
  have hzt : Tendsto z atTop (𝓝 x) := by
    rw [tendsto_nhds]
    intro s hs hxs
    obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hy.eventually (hs.mem_nhds hxs))
    refine eventually_atTop.2 ⟨phi n0, fun N hN => ?_⟩
    by_cases h : ∃ n, phi n = N
    · simp only [z, dif_pos h]
      apply hn0
      have h1 : phi n0 ≤ phi (Classical.choose h) := by
        rw [Classical.choose_spec h]
        exact hN
      exact hphi.le_iff_le.1 h1
    · simp only [z, dif_neg h]
      exact hxs
  have h1 := hlim x z hzt
  have h2 : liminf (fun N => EN N (z N)) atTop ≤
      liminf (fun n => EN (phi n) (z (phi n))) atTop := by
    rw [show (fun n => EN (phi n) (z (phi n))) = (fun N => EN N (z N)) ∘ phi from rfl,
      liminf_comp]
    exact liminf_le_liminf_of_le hphi.tendsto_atTop
  simp only [hz] at h2
  exact h1.trans h2

/-- Mosco recovery along a subsequence. -/
theorem aux_prop_speed_resolvent_subseq_limsup {X : Type*} [NormedAddCommGroup X]
    (EN : ℕ → X → ℝ≥0∞) (Elim : X → ℝ≥0∞) (hrec : Lane3.MoscoRecovery EN Elim)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (x : X) :
    ∃ y : ℕ → X, Tendsto y atTop (𝓝 x) ∧
      limsup (fun n => EN (phi n) (y n)) atTop ≤ Elim x := by
  obtain ⟨z, hz, hzl⟩ := hrec x
  refine ⟨fun n => z (phi n), hz.comp hphi.tendsto_atTop, le_trans ?_ hzl⟩
  rw [show (fun n => EN (phi n) (z (phi n))) = (fun N => EN N (z N)) ∘ phi from rfl,
    limsup_comp]
  exact limsup_le_limsup_of_le hphi.tendsto_atTop

/-- A lower bound by a liminf of uniformly bounded values is finite. -/
theorem aux_prop_speed_resolvent_liminf_ne_top (e : ℝ≥0∞) (a : ℕ → ℝ≥0∞) (Cen : ℝ≥0∞)
    (hCen : Cen ≠ ∞) (ha : ∀ n, a n ≤ Cen) (he : e ≤ liminf a atTop) : e ≠ ∞ := by
  have hlimsup : limsup a atTop ≤ Cen := limsup_le_of_le (h := Eventually.of_forall ha)
  have hle : e ≤ Cen := he.trans ((liminf_le_limsup).trans hlimsup)
  exact (hle.trans_lt (lt_top_iff_ne_top.mpr hCen)).ne

/-- The real-analysis step of the cluster argument: liminf of the minimal
values dominates the limit functional at `ubar`, recovery values bound it at `v`. -/
theorem aux_prop_speed_resolvent_cluster_real (Eu Ev : ℕ → ℝ≥0∞) (eu ev Cen : ℝ≥0∞)
    (hCen : Cen ≠ ∞) (hEu : ∀ n, Eu n ≤ Cen) (hev : ev ≠ ∞)
    (hlow : eu ≤ liminf Eu atTop) (hup : limsup Ev atTop ≤ ev)
    (p1 p2 q1 q2 : ℕ → ℝ) (P1 P2 Q1 Q2 : ℝ)
    (hp1 : Tendsto p1 atTop (𝓝 P1)) (hp2 : Tendsto p2 atTop (𝓝 P2))
    (hq1 : Tendsto q1 atTop (𝓝 Q1)) (hq2 : Tendsto q2 atTop (𝓝 Q2))
    (hmin : ∀ n, Ev n ≠ ∞ →
      (Eu n).toReal + p1 n - p2 n ≤ (Ev n).toReal + q1 n - q2 n) :
    eu.toReal + P1 - P2 ≤ ev.toReal + Q1 - Q2 := by
  have heu : eu ≠ ∞ := aux_prop_speed_resolvent_liminf_ne_top eu Eu Cen hCen hEu hlow
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hEu_ev : ∀ᶠ n in atTop, eu.toReal - ε / 6 < (Eu n).toReal := by
    by_cases hpos : eu.toReal - ε / 6 < 0
    · exact Eventually.of_forall fun n => lt_of_lt_of_le hpos ENNReal.toReal_nonneg
    · push_neg at hpos
      have hlt : ENNReal.ofReal (eu.toReal - ε / 6) < liminf Eu atTop := by
        refine lt_of_lt_of_le ?_ hlow
        rw [ENNReal.ofReal_lt_iff_lt_toReal hpos heu]
        linarith
      filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
      exact (ENNReal.ofReal_lt_iff_lt_toReal hpos (ne_top_of_le_ne_top hCen (hEu n))).1 hn
  have hev0 : 0 ≤ ev.toReal := ENNReal.toReal_nonneg
  have hEv_ev : ∀ᶠ n in atTop, Ev n < ENNReal.ofReal (ev.toReal + ε / 6) := by
    have hlt : limsup Ev atTop < ENNReal.ofReal (ev.toReal + ε / 6) := by
      refine lt_of_le_of_lt hup ?_
      rw [ENNReal.lt_ofReal_iff_toReal_lt hev]
      linarith
    exact eventually_lt_of_limsup_lt hlt
  have e1 := (tendsto_order.1 hp1).1 (P1 - ε / 6) (by linarith)
  have e2 := (tendsto_order.1 hp2).2 (P2 + ε / 6) (by linarith)
  have e3 := (tendsto_order.1 hq1).2 (Q1 + ε / 6) (by linarith)
  have e4 := (tendsto_order.1 hq2).1 (Q2 - ε / 6) (by linarith)
  obtain ⟨n, h0, h1, h2, h3, h4, h5⟩ :=
    (hEu_ev.and (hEv_ev.and (e1.and (e2.and (e3.and e4))))).exists
  have hEvn : Ev n ≠ ∞ := ne_top_of_lt h1
  have hb : (Ev n).toReal < ev.toReal + ε / 6 := by
    have := (ENNReal.toReal_lt_toReal hEvn ENNReal.ofReal_ne_top).2 h1
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have := hmin n hEvn
  linarith

end PSRMosco

section PSRTrlin
open scoped ContDiff

theorem aux_prop_speed_resolvent_sqrt_ofReal_sq (a : ℝ) :
    ENNReal.ofReal (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = ENNReal.ofReal |a| := by
  have h1 : ENNReal.ofReal (a ^ (2 : ℕ)) = ENNReal.ofReal |a| ^ (2 : ℝ) := by
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg a), ← ENNReal.rpow_natCast,
        show (((2 : ℕ) : ℝ)) = (2 : ℝ) by norm_num]
  rw [h1, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

theorem aux_prop_speed_resolvent_rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- Weighted `L²` Minkowski inequality for the fractional double integral. -/
theorem aux_prop_speed_resolvent_weighted_minkowski {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (c : ℝ)
    (φ ψ : SpatialCoordinates d → ℝ)
    (hφ : AEMeasurable φ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hψ : AEMeasurable ψ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
       ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
         ENNReal.ofReal (((c * φ x + ψ x) - (c * φ y + ψ y)) ^ (2 : ℕ)) /
           (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ)))
      ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal |c| *
        (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
           ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
             ENNReal.ofReal ((φ x - φ y) ^ (2 : ℕ)) /
               (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ)))
        ^ (1 / 2 : ℝ) +
      (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
         ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
           ENNReal.ofReal ((ψ x - ψ y) ^ (2 : ℕ)) /
             (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ)))
      ^ (1 / 2 : ℝ) := by
  classical
  let μ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let ν : Measure (SpatialCoordinates d × SpatialCoordinates d) := μ.prod μ
  let D : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ))
  let Tφ : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((φ q.1 - φ q.2) ^ (2 : ℕ)) / D q
  let Tψ : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((ψ q.1 - ψ q.2) ^ (2 : ℕ)) / D q
  let Tc : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)) ^ (2 : ℕ)) / D q
  let Fφ : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((φ q.1 - φ q.2) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) * (D q)⁻¹ ^ (1 / 2 : ℝ)
  let Fψ : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((ψ q.1 - ψ q.2) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) * (D q)⁻¹ ^ (1 / 2 : ℝ)
  let Fc : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)
      * (D q)⁻¹ ^ (1 / 2 : ℝ)
  have hD : Measurable D := by
    dsimp only [D]
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  have hDinv : Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d => (D q)⁻¹) := hD.inv
  have hφ1 : AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d => φ q.1) ν :=
    hφ.comp_fst
  have hφ2 : AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d => φ q.2) ν :=
    hφ.comp_snd
  have hψ1 : AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d => ψ q.1) ν :=
    hψ.comp_fst
  have hψ2 : AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d => ψ q.2) ν :=
    hψ.comp_snd
  have hnumφ : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d => (φ q.1 - φ q.2) ^ (2 : ℕ)) ν :=
    (hφ1.sub hφ2).pow_const (2 : ℕ)
  have hnumψ : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d => (ψ q.1 - ψ q.2) ^ (2 : ℕ)) ν :=
    (hψ1.sub hψ2).pow_const (2 : ℕ)
  have hnumc : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)) ν :=
    ((hφ1.const_mul c).add hψ1).sub ((hφ2.const_mul c).add hψ2)
  have hTφ : AEMeasurable Tφ ν := by
    dsimp only [Tφ]
    exact hnumφ.ennreal_ofReal.div hD.aemeasurable
  have hTψ : AEMeasurable Tψ ν := by
    dsimp only [Tψ]
    exact hnumψ.ennreal_ofReal.div hD.aemeasurable
  have hTc : AEMeasurable Tc ν := by
    dsimp only [Tc]
    exact (hnumc.pow_const (2 : ℕ)).ennreal_ofReal.div hD.aemeasurable
  have hFφ : AEMeasurable Fφ ν := by
    dsimp only [Fφ]
    exact (hnumφ.ennreal_ofReal.pow_const (1 / 2)).mul (hDinv.aemeasurable.pow_const (1 / 2))
  have hFψ : AEMeasurable Fψ ν := by
    dsimp only [Fψ]
    exact (hnumψ.ennreal_ofReal.pow_const (1 / 2)).mul (hDinv.aemeasurable.pow_const (1 / 2))
  have hFc : AEMeasurable Fc ν := by
    dsimp only [Fc]
    exact ((hnumc.pow_const (2 : ℕ)).ennreal_ofReal.pow_const (1 / 2)).mul
      (hDinv.aemeasurable.pow_const (1 / 2))
  have hφsq : ∀ q, Fφ q ^ (2 : ℝ) = Tφ q := by
    intro q
    dsimp only [Fφ, Tφ]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [aux_prop_speed_resolvent_rpow_half_sq]
    rw [mul_comm, ← ENNReal.div_eq_inv_mul]
  have hψsq : ∀ q, Fψ q ^ (2 : ℝ) = Tψ q := by
    intro q
    dsimp only [Fψ, Tψ]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [aux_prop_speed_resolvent_rpow_half_sq]
    rw [mul_comm, ← ENNReal.div_eq_inv_mul]
  have hcsq : ∀ q, Fc q ^ (2 : ℝ) = Tc q := by
    intro q
    dsimp only [Fc, Tc]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [aux_prop_speed_resolvent_rpow_half_sq]
    rw [mul_comm, ← ENNReal.div_eq_inv_mul]
  have hcle : ∀ q, Fc q ≤ ENNReal.ofReal |c| * Fφ q + Fψ q := by
    intro q
    have habs : |(c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)|
        ≤ |c| * |φ q.1 - φ q.2| + |ψ q.1 - ψ q.2| := by
      have h : (c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)
          = c * (φ q.1 - φ q.2) + (ψ q.1 - ψ q.2) := by ring
      calc |(c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)|
          = |c * (φ q.1 - φ q.2) + (ψ q.1 - ψ q.2)| := by rw [h]
        _ ≤ |c * (φ q.1 - φ q.2)| + |ψ q.1 - ψ q.2| := by
            rw [abs_le]
            exact ⟨by linarith [neg_abs_le (c * (φ q.1 - φ q.2)), neg_abs_le (ψ q.1 - ψ q.2)],
                   by linarith [le_abs_self (c * (φ q.1 - φ q.2)), le_abs_self (ψ q.1 - ψ q.2)]⟩
        _ = |c| * |φ q.1 - φ q.2| + |ψ q.1 - ψ q.2| := by rw [abs_mul]
    have hofR : ENNReal.ofReal |(c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)|
        ≤ ENNReal.ofReal |c| * ENNReal.ofReal |φ q.1 - φ q.2|
          + ENNReal.ofReal |ψ q.1 - ψ q.2| := by
      calc ENNReal.ofReal |(c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)|
          ≤ ENNReal.ofReal (|c| * |φ q.1 - φ q.2| + |ψ q.1 - ψ q.2|) :=
            ENNReal.ofReal_le_ofReal habs
        _ = ENNReal.ofReal (|c| * |φ q.1 - φ q.2|) + ENNReal.ofReal |ψ q.1 - ψ q.2| := by
            rw [ENNReal.ofReal_add (mul_nonneg (abs_nonneg c) (abs_nonneg _)) (abs_nonneg _)]
        _ = ENNReal.ofReal |c| * ENNReal.ofReal |φ q.1 - φ q.2|
            + ENNReal.ofReal |ψ q.1 - ψ q.2| := by
            rw [ENNReal.ofReal_mul (abs_nonneg c)]
    dsimp only [Fc, Fφ, Fψ]
    simp only [aux_prop_speed_resolvent_sqrt_ofReal_sq]
    calc ENNReal.ofReal |(c * φ q.1 + ψ q.1) - (c * φ q.2 + ψ q.2)| * (D q)⁻¹ ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal |c| * ENNReal.ofReal |φ q.1 - φ q.2|
            + ENNReal.ofReal |ψ q.1 - ψ q.2|) * (D q)⁻¹ ^ (1 / 2 : ℝ) :=
          mul_le_mul' hofR le_rfl
      _ = ENNReal.ofReal |c| * (ENNReal.ofReal |φ q.1 - φ q.2| * (D q)⁻¹ ^ (1 / 2 : ℝ))
            + ENNReal.ofReal |ψ q.1 - ψ q.2| * (D q)⁻¹ ^ (1 / 2 : ℝ) := by
          rw [add_mul, mul_assoc]
  have hMin := ENNReal.lintegral_Lp_add_le (p := 2)
      (f := fun q => ENNReal.ofReal |c| * Fφ q) (g := Fψ)
      (hFφ.const_mul (ENNReal.ofReal |c|)) hFψ (by norm_num : (1 : ℝ) ≤ 2)
  have hstep1 : (∫⁻ q, (Fc q) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ q, (ENNReal.ofReal |c| * Fφ q + Fψ q) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow
      (lintegral_mono (μ := ν) (fun q => ENNReal.rpow_le_rpow (hcle q) (by norm_num : (0 : ℝ) ≤ 2)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hconst : (∫⁻ q, (ENNReal.ofReal |c| * Fφ q) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal |c| * (∫⁻ q, (Fφ q) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
    have h1 : (∫⁻ q, (ENNReal.ofReal |c| * Fφ q) ^ (2 : ℝ) ∂ν)
        = ENNReal.ofReal |c| ^ (2 : ℝ) * (∫⁻ q, (Fφ q) ^ (2 : ℝ) ∂ν) := by
      rw [lintegral_congr (fun q => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2))]
      rw [lintegral_const_mul'' (ENNReal.ofReal |c| ^ (2 : ℝ)) (hFφ.pow_const (2 : ℝ))]
    rw [h1]
    rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal |c| ^ (2 : ℝ))
          (∫⁻ q, (Fφ q) ^ (2 : ℝ) ∂ν) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (ENNReal.ofReal |c| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ENNReal.ofReal |c| from by
          rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]]
  have hcore := hstep1.trans (hMin.trans (le_of_eq (by rw [hconst])))
  have hgoalC : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (((c * φ x + ψ x) - (c * φ y + ψ y)) ^ (2 : ℕ)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ)))
      = (∫⁻ q, (Fc q) ^ (2 : ℝ) ∂ν) := by
    rw [← lintegral_prod Tc hTc]
    apply lintegral_congr
    intro q
    exact (hcsq q).symm
  have hgoalF : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((φ x - φ y) ^ (2 : ℕ)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ)))
      = (∫⁻ q, (Fφ q) ^ (2 : ℝ) ∂ν) := by
    rw [← lintegral_prod Tφ hTφ]
    apply lintegral_congr
    intro q
    exact (hφsq q).symm
  have hgoalG : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((ψ x - ψ y) ^ (2 : ℕ)) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ)))
      = (∫⁻ q, (Fψ q) ^ (2 : ℝ) ∂ν) := by
    rw [← lintegral_prod Tψ hTψ]
    apply lintegral_congr
    intro q
    exact (hψsq q).symm
  rw [hgoalC, hgoalF, hgoalG]
  exact hcore

/-- Minkowski for the scalar Gagliardo seminorm. -/
theorem aux_prop_speed_resolvent_seminorm_lincomb_le {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (c : ℝ)
    (f g : Fin 1 → DomainL2 (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s (fun i => c • f i + g i) ≤
      ENNReal.ofReal |c| * cubeFractionalL2Seminorm hd z r hr s f +
        cubeFractionalL2Seminorm hd z r hr s g := by
  classical
  simp only [cubeFractionalL2Seminorm, Fin.sum_univ_one]
  let P : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))
  let vf : SpatialCoordinates d → ℝ := fun x => (f 0 : DomainL2 (centeredCube z r hr)) x
  let vg : SpatialCoordinates d → ℝ := fun x => (g 0 : DomainL2 (centeredCube z r hr)) x
  let hw : SpatialCoordinates d → ℝ := fun x => c * vf x + vg x
  let w : SpatialCoordinates d → ℝ := fun x => (c • f 0 + g 0 : DomainL2 (centeredCube z r hr)) x
  let κ : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ (2 : ℕ)))) ^ ((d : ℝ) + 2 * (s : ℝ))
  let core : (SpatialCoordinates d → ℝ) → ℝ≥0∞ := fun h =>
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((h x - h y) ^ (2 : ℕ)) / κ x y
  change (P * core w) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal |c| * (P * core vf) ^ (1 / 2 : ℝ)
      + (P * core vg) ^ (1 / 2 : ℝ)
  have hae : w =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] hw := by
    dsimp only [w, hw, vf, vg]
    filter_upwards [Lp.coeFn_add (c • f 0) (g 0), Lp.coeFn_smul c (f 0)] with x hx hx'
    rw [hx, Pi.add_apply, hx', Pi.smul_apply, smul_eq_mul]
  have hcore_eq : core w = core hw := by
    dsimp only [core]
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    rw [hx, hy]
  have hvf : AEMeasurable vf (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable (f 0)).aemeasurable
  have hvg : AEMeasurable vg (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable (g 0)).aemeasurable
  have haux := aux_prop_speed_resolvent_weighted_minkowski z r hr s c vf vg hvf hvg
  rw [hcore_eq]
  rw [ENNReal.mul_rpow_of_nonneg P (core hw) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg P (core vf) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg P (core vg) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc P ^ (1 / 2 : ℝ) * (core hw) ^ (1 / 2 : ℝ)
      ≤ P ^ (1 / 2 : ℝ) * (ENNReal.ofReal |c| * (core vf) ^ (1 / 2 : ℝ)
          + (core vg) ^ (1 / 2 : ℝ)) := mul_le_mul' le_rfl haux
    _ = ENNReal.ofReal |c| * (P ^ (1 / 2 : ℝ) * (core vf) ^ (1 / 2 : ℝ))
          + P ^ (1 / 2 : ℝ) * (core vg) ^ (1 / 2 : ℝ) := by
        rw [mul_add, ← mul_assoc, mul_comm (P ^ (1 / 2 : ℝ)) (ENNReal.ofReal |c|), mul_assoc]

/-- On smooth representatives the trace is the restriction, hence linear. -/
theorem aux_prop_speed_resolvent_trace_smooth_lin {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T) (c : ℝ)
    (a b e : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (f g : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ha : (a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr :
        Set (SpatialCoordinates d))] f)
    (hb : (b.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr :
        Set (SpatialCoordinates d))] g)
    (he : (e.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr :
        Set (SpatialCoordinates d))] fun x => c * f x + g x) :
    T e = c • T a + T b := by
  have hfm := contDiff_memLp_of_finiteMeasure_supported_closure Q hr ν hsupp f hf
  have hgm := contDiff_memLp_of_finiteMeasure_supported_closure Q hr ν hsupp g hg
  have hsm : ContDiff ℝ ∞ (fun x => c * f x + g x) := (contDiff_const.mul hf).add hg
  have hem := contDiff_memLp_of_finiteMeasure_supported_closure Q hr ν hsupp _ hsm
  rw [hT.2.2 f hf a ha hfm, hT.2.2 g hg b hb hgm, hT.2.2 _ hsm e he hem,
    ← MemLp.toLp_const_smul c hfm, ← MemLp.toLp_add (hfm.const_smul c) hgm]
  exact MemLp.toLp_congr hem _ (Eventually.of_forall fun x => by simp)

/-- Linear combinations stay in the fractional carrier, with the norm bound. -/
theorem aux_prop_speed_resolvent_frac_lincomb {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (c : ℝ)
    (x y : CubeFractionalL2 (k := 1) hd z r hr s) :
    ∃ σ : CubeFractionalL2 (k := 1) hd z r hr s,
      σ.val 0 = c • x.val 0 + y.val 0 ∧
        cubeFractionalL2Norm hd z r hr s σ ≤
          |c| * cubeFractionalL2Norm hd z r hr s x + cubeFractionalL2Norm hd z r hr s y := by
  have hle := aux_prop_speed_resolvent_seminorm_lincomb_le hd z r hr s c x.val y.val
  have hx : cubeFractionalL2Seminorm hd z r hr s x.val < ⊤ := x.property
  have hy : cubeFractionalL2Seminorm hd z r hr s y.val < ⊤ := y.property
  have hxy : ENNReal.ofReal |c| * cubeFractionalL2Seminorm hd z r hr s x.val +
      cubeFractionalL2Seminorm hd z r hr s y.val ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.ne, hy.ne⟩
  have hlt : cubeFractionalL2Seminorm hd z r hr s (fun i => c • x.val i + y.val i) < ⊤ :=
    lt_of_le_of_lt hle (lt_top_iff_ne_top.2 hxy)
  refine ⟨⟨fun i => c • x.val i + y.val i, hlt⟩, rfl, ?_⟩
  have hsemi : (cubeFractionalL2Seminorm hd z r hr s (fun i => c • x.val i + y.val i)).toReal ≤
      |c| * (cubeFractionalL2Seminorm hd z r hr s x.val).toReal +
        (cubeFractionalL2Seminorm hd z r hr s y.val).toReal := by
    have h1 := ENNReal.toReal_mono hxy hle
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.ne) hy.ne,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg c)] at h1
  have hL2 : ‖c • x.val 0 + y.val 0‖ ≤ |c| * ‖x.val 0‖ + ‖y.val 0‖ := by
    calc ‖c • x.val 0 + y.val 0‖ ≤ ‖c • x.val 0‖ + ‖y.val 0‖ := norm_add_le _ _
      _ = |c| * ‖x.val 0‖ + ‖y.val 0‖ := by rw [norm_smul, Real.norm_eq_abs]
  set V := Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) with hV
  set R := r ^ (-(s : ℝ)) with hR
  have hv : 0 ≤ V := Real.sqrt_nonneg _
  have hr0 : 0 ≤ R := Real.rpow_nonneg hr.le _
  have h1 : R * (‖c • x.val 0 + y.val 0‖ / V) ≤ R * ((|c| * ‖x.val 0‖ + ‖y.val 0‖) / V) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL2 hv) hr0
  have h2 : R * ((|c| * ‖x.val 0‖ + ‖y.val 0‖) / V) =
      |c| * (R * (‖x.val 0‖ / V)) + R * (‖y.val 0‖ / V) := by ring
  show (cubeFractionalL2Seminorm hd z r hr s (fun i => c • x.val i + y.val i)).toReal +
      R * (Real.sqrt (∑ i : Fin 1, ‖c • x.val i + y.val i‖ ^ 2) / V) ≤
    |c| * ((cubeFractionalL2Seminorm hd z r hr s x.val).toReal +
      R * (Real.sqrt (∑ i : Fin 1, ‖x.val i‖ ^ 2) / V)) +
    ((cubeFractionalL2Seminorm hd z r hr s y.val).toReal +
      R * (Real.sqrt (∑ i : Fin 1, ‖y.val i‖ ^ 2) / V))
  simp only [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
  rw [mul_add]
  linarith

/-- `cubeFractionalL2Norm` is nonnegative. -/
theorem aux_prop_speed_resolvent_norm_nonneg {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := k) hd z r hr s) :
    0 ≤ cubeFractionalL2Norm hd z r hr s f := by
  unfold cubeFractionalL2Norm
  exact add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (Real.rpow_nonneg hr.le _)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- Traces converge along a sequence whose differences vanish in the half-order norm. -/
theorem aux_prop_speed_resolvent_trace_tendsto {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T)
    (x : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (y δ : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (hδ : ∀ n, (δ n).val 0 = x.val 0 - (y n).val 0)
    (hlim : Tendsto (fun n => cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (δ n)) atTop (𝓝 0)) :
    Tendsto (fun n => T (y n)) atTop (𝓝 (T x)) := by
  set Lc := C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal) with hLc
  set L := max 1 Lc with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLL : Lc ≤ L ^ 2 := by
    have : L ≤ L ^ 2 := by nlinarith
    exact (le_max_right _ _).trans this
  have hbd : ∀ n, ‖T (y n) - T x‖ ≤ L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (δ n) := by
    intro n
    have hN := aux_prop_speed_resolvent_norm_nonneg hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (δ n)
    have h := hT.2.1 x (y n) (δ n) (hδ n)
    have hsq : ‖T x - T (y n)‖ ^ 2 ≤ (L * cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (δ n)) ^ 2 := by
      calc ‖T x - T (y n)‖ ^ 2 ≤ _ := h
        _ ≤ L ^ 2 * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (δ n)) ^ 2 :=
            mul_le_mul_of_nonneg_right hLL (sq_nonneg _)
        _ = _ := by ring
    rw [norm_sub_rev]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (by linarith) hN) two_ne_zero).1 hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hbd ?_
  simpa using hlim.const_mul L

/-- Linearity of the completion trace (density of smooth functions plus the common
Lipschitz bound). -/
theorem aux_prop_speed_resolvent_trace_linear {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T) (c : ℝ)
    (u v w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (hw : w.val 0 = c • u.val 0 + v.val 0) :
    T w = c • T u + T v := by
  obtain ⟨a, f, wa, hf, -, hfa, hwa, hwalim⟩ :=
    measureTrace_hdense_of_finiteMeasure_supported hd Q hr ν hsupp u
  obtain ⟨b, g, wb, hg, -, hgb, hwb, hwblim⟩ :=
    measureTrace_hdense_of_finiteMeasure_supported hd Q hr ν hsupp v
  choose e he1 he2 using fun n => aux_prop_speed_resolvent_frac_lincomb hd
    (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder
    c (a n) (b n)
  have hTe : ∀ n, T (e n) = c • T (a n) + T (b n) := by
    intro n
    refine aux_prop_speed_resolvent_trace_smooth_lin hd Q hr ν hsupp K C T hT c (a n) (b n) (e n)
      (f n) (g n) (hf n) (hg n) (hfa n) (hgb n) ?_
    rw [he1 n]
    filter_upwards [Lp.coeFn_add (c • (a n).val 0) ((b n).val 0),
      Lp.coeFn_smul c ((a n).val 0), hfa n, hgb n] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  choose dd hdd1 hdd2 using fun n => aux_prop_speed_resolvent_frac_lincomb hd
    (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder
    c (wa n) (wb n)
  have hddv : ∀ n, (dd n).val 0 = w.val 0 - (e n).val 0 := by
    intro n
    rw [hdd1 n, hwa n, hwb n, hw, he1 n, smul_sub]
    abel
  have hddlim : Tendsto (fun n => cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (dd n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => aux_prop_speed_resolvent_norm_nonneg hd _ _ hr _ (dd n))
      hdd2 ?_
    simpa using (hwalim.const_mul |c|).add hwblim
  have hL1 := aux_prop_speed_resolvent_trace_tendsto hd Q hr ν K C T hT u a wa hwa hwalim
  have hL2 := aux_prop_speed_resolvent_trace_tendsto hd Q hr ν K C T hT v b wb hwb hwblim
  have hL3 := aux_prop_speed_resolvent_trace_tendsto hd Q hr ν K C T hT w e dd hddv hddlim
  have hlim2 : Tendsto (fun n => T (e n)) atTop (𝓝 (c • T u + T v)) := by
    simp_rw [hTe]
    exact (hL1.const_smul c).add hL2
  exact tendsto_nhds_unique hL3 hlim2

open Classical in
/-- The finite-energy trace `A w = T (i w hw)` is linear on the energy domain:
the `hAlin` input of `aux_prop_speed_resolvent_abstract_min`. -/
theorem aux_prop_speed_resolvent_A_lin {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasure ν]
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT : MeasureTraceCharacterization hd Q hr ν K C T)
    (E : DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr) → ℝ≥0∞)
    (hclosed : ∀ (c : ℝ) (w1 w2 : DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr)), E w1 ≠ ⊤ → E w2 ≠ ⊤ → E (c • w1 + w2) ≠ ⊤)
    (i : (u : DomainL2 (centeredCube (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr)) → E u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
    (hi0 : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr)) (hu : E u ≠ ⊤), (i u hu).val 0 = u)
    (c : ℝ) (w1 w2 : DomainL2 (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr)) (h1 : E w1 ≠ ⊤) (h2 : E w2 ≠ ⊤) :
    (if h : E (c • w1 + w2) ≠ ⊤ then T (i (c • w1 + w2) h) else 0) =
      c • (if h : E w1 ≠ ⊤ then T (i w1 h) else 0) +
        (if h : E w2 ≠ ⊤ then T (i w2 h) else 0) := by
  rw [dif_pos (hclosed c w1 w2 h1 h2), dif_pos h1, dif_pos h2]
  exact aux_prop_speed_resolvent_trace_linear hd Q hr ν hsupp K C T hT c _ _ _
    (by rw [hi0, hi0, hi0])

end PSRTrlin

section PSRAssembly
open scoped InnerProductSpace

/-! ### Parts A/B: existence, minimality, uniqueness (paper 4895-4909) -/

open Classical in
/-- Conjuncts 1-3 of `prop_speed_resolvent`: the abstract minimization applied with
`A w = T (i w hw)` and `g = f` in `L²(μ)`. -/
theorem aux_prop_speed_resolvent_parts_AB {d : ℕ} (hd : 2 ≤ d)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < cubeScaleFactor Qtri)
    (G : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
    (Elim : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hElim : ∀ u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
      Elim u = (limitFormEnergy G u).toENNReal)
    (mu muFull : Measure (SpatialCoordinates d))
    (hmu : mu = muFull.restrict
      (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d))))
    (hmufin : mu univ < ∞) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri) (cubeScaleFactor Qtri) hr
      halfFractionalOrder → Lp ℝ 2 mu)
    (hT : MeasureTraceCharacterization hd Qtri hr mu K C T)
    (i : (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)) →
      Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri) (cubeScaleFactor Qtri) hr
        halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) →
      SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞), (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
        ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * Elim w)
    (hE0 : Elim 0 = 0)
    (hclosed : ∀ (c : ℝ)
      (w1 w2 : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      Elim w1 ≠ ∞ → Elim w2 ≠ ∞ → Elim (c • w1 + w2) ≠ ∞)
    (hpara : ∀ (w1 w2 : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      Elim w1 ≠ ∞ → Elim w2 ≠ ∞ →
      (Elim (w1 + w2)).toReal + (Elim (w1 - w2)).toReal =
        2 * (Elim w1).toReal + 2 * (Elim w2).toReal)
    (hscale : ∀ (c : ℝ)
      (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      Elim u ≠ ∞ → Elim (c • u) = ENNReal.ofReal (c ^ 2) * Elim u)
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hJtr : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞),
      (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤ ENNReal.ofReal Ktr * Elim u)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ ustar : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
      Elim ustar ≠ ∞ ∧
      (∀ w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
        Elim w ≠ ∞ →
        (Elim ustar).toReal + lam * (∫ x, J ustar x ^ 2 ∂mu) -
            2 * ∫ x, f x * J ustar x ∂mu ≤
          (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
            2 * ∫ x, f x * J w x ∂mu) ∧
      (∀ w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
        Elim w ≠ ∞ →
        (∀ v : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
          Elim v ≠ ∞ →
          (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
              2 * ∫ x, f x * J w x ∂mu ≤
            (Elim v).toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
              2 * ∫ x, f x * J v x ∂mu) →
        w = ustar) := by
  haveI : IsFiniteMeasure mu := ⟨hmufin⟩
  have hsupp : mu (closure (Homogenization.openCubeSet Qtri))ᶜ = 0 := by
    rw [hmu, Measure.restrict_apply isClosed_closure.measurableSet.compl,
      centeredCube_eq_openCubeSet Qtri hr, Set.compl_inter_self, measure_empty]
  have hfm : MemLp (fun x => f x) 2 mu :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  let A : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) → Lp ℝ 2 mu :=
    fun w => if h : Elim w ≠ ⊤ then T (i w h) else 0
  have hAw : ∀ (w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hw : Elim w ≠ ∞), A w = T (i w hw) := fun w hw => dif_pos hw
  have hlsc : LowerSemicontinuous Elim := by
    have hE : Elim = fun u => (limitFormEnergy G u).toENNReal := funext hElim
    rw [hE]
    exact aux_prop_speed_resolvent_elim_lsc G
  have hAlin : ∀ (c : ℝ)
      (w1 w2 : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      Elim w1 ≠ ∞ → Elim w2 ≠ ∞ → A (c • w1 + w2) = c • A w1 + A w2 :=
    fun c w1 w2 h1 h2 =>
      aux_prop_speed_resolvent_A_lin hd Qtri hr mu hsupp K C T hT Elim hclosed i hi c w1 w2 h1 h2
  have hAbd : ∀ w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
      Elim w ≠ ∞ → ‖A w‖ ^ 2 ≤ Ktr * (Elim w).toReal := by
    intro w hw
    rw [hAw w hw]
    exact aux_prop_speed_resolvent_trace_bound (J w) _ (hJ w hw) Ktr hKtr _ hw (hJtr w hw)
  obtain ⟨ustar, hus, hmin, huniq⟩ :=
    aux_prop_speed_resolvent_abstract_min Elim A (hfm.toLp (fun x => f x)) lam hlam hlsc hE0
      hclosed hpara hscale hcoer hAlin Ktr hKtr hAbd
  have key : ∀ (w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hw : Elim w ≠ ∞),
      (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) - 2 * ∫ x, f x * J w x ∂mu =
        (Elim w).toReal + lam * ‖A w‖ ^ 2 -
          2 * ⟪hfm.toLp (fun x => f x), A w⟫_ℝ := by
    intro w hw
    have hJA : J w =ᵐ[mu] ⇑(A w) := by
      rw [hAw w hw]
      exact hJ w hw
    rw [aux_prop_speed_resolvent_sq_integral_congr (J w) (A w) hJA,
      aux_prop_speed_resolvent_f_integral_inner f hfm (J w) (A w) hJA]
  refine ⟨ustar, hus, fun w hw => ?_, fun w hw hwmin => ?_⟩
  · rw [key ustar hus, key w hw]
    exact hmin w hw
  · exact huniq w hw (fun v hv => by
      rw [← key w hw, ← key v hv]
      exact hwmin v hv)

/-! ### Part C: cluster points (paper 4909-4918) -/

/-- The cutoff speed measures are locally finite. -/
theorem aux_prop_speed_resolvent_cutoff_locfin {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    IsLocallyFiniteMeasure (cutoffSpeedMeasure M H omega N) := by
  rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
  exact weightedChaosCutoff_isLocallyFinite M H N omega


/-- The open cube contains its center. -/
theorem aux_prop_speed_resolvent_cube_nonempty {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) : (centeredCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
  ⟨z, Metric.mem_ball_self (half_pos hr)⟩

/-- The complement of the open cube is nonempty (`d ≥ 1`). -/
theorem aux_prop_speed_resolvent_cube_compl_nonempty {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ((centeredCube z r hr : Set (SpatialCoordinates d))ᶜ).Nonempty := by
  refine ⟨fun i => z i + r, fun hx => ?_⟩
  have hx' : dist (fun i => z i + r) z < r / 2 := Metric.mem_ball.1 hx
  have h1 := dist_le_pi_dist (fun i => z i + r) z ⟨0, by omega⟩
  simp only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hr] at h1
  linarith

/-- Trace passage along a subsequence of eventually bounded-energy
elements (application of `lem_varying_trace` to the `phi`-subsequence, after a finite
shift, with near-infimum killed representatives). -/
theorem aux_prop_speed_resolvent_trace_passage
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < cubeScaleFactor Qtri)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H)
    (cutoff : ℕ → ℕ) (hcutoff : StrictMono cutoff)
    (omegaN : ℕ → BilateralField d)
    (EN : ℕ → DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (Elim : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hEN : ∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      EN N u = ⨅ v : {v : killedSobolevGraph
          (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) //
        (v : SobolevData (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)).1 = u},
        ENNReal.ofReal
          (in_killed_energy M H HI (omegaN N) (cutoff N)
            (cubeCenter Qtri) hr v.val v.val))
    (muN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d))
    (muFull : Measure (SpatialCoordinates d))
    (hmuN : ∀ (N : ℕ),
      muN N = (cutoffSpeedMeasure M H (omegaN N) (cutoff N)).restrict
        (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
          Set (SpatialCoordinates d))))
    (hmu : mu = muFull.restrict
      (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d))))
    (hconv : MeasuresConvergeLocally
      (fun N => cutoffSpeedMeasure M H (omegaN N) (cutoff N)) muFull)
    (hfront : muFull (frontier (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) = 0)
    (hloc : MeasuresConvergeLocally muN mu)
    (TN : (N : ℕ) →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder →
      Lp ℝ 2 (muN N))
    (T : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
      (cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 mu)
    (KN : ℕ → ℝ) (K C : ℝ)
    (hKN : ∀ (N : ℕ), 0 ≤ KN N) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hTN : ∀ (N : ℕ),
      MeasureTraceCharacterization hd Qtri hr (muN N) (KN N) C (TN N))
    (hT : MeasureTraceCharacterization hd Qtri hr mu K C T)
    (Kbar : ℝ) (hKNbar : ∀ (N : ℕ), KN N ≤ Kbar) (hKbar : K ≤ Kbar)
    (Mbar : ℝ≥0∞) (hMbar : Mbar ≠ ∞)
    (hmuNM : ∀ (N : ℕ), muN N (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) ≤ Mbar)
    (hmuM : mu (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) ≤ Mbar)
    (iN : (N : ℕ) → (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)) →
      EN N u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder)
    (i : (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)) →
      Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hiN : ∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : EN N u ≠ ∞), (iN N u hu).val 0 = u)
    (hi : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (JN : ℕ → DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) →
      SpatialCoordinates d → ℝ)
    (J : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) →
      SpatialCoordinates d → ℝ)
    (hJN : ∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : EN N u ≠ ∞),
      (JN N u) =ᵐ[muN N] (TN N (iN N u hu) : SpatialCoordinates d → ℝ))
    (hJ : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞),
      (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (hH3N : ∃ C3 : ℝ, 0 < C3 ∧
      (∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
        EN N u ≠ ∞ →
        ∃ v : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
            (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder,
          v.val 0 = u ∧
            cubeFractionalL2Norm hd (cubeCenter Qtri)
              (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder v ^ 2 ≤
              C3 * (EN N u).toReal))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (wN : ℕ → DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
    (w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
    (Cen : ℝ≥0∞) (hCen : Cen ≠ ∞)
    (hbd : ∀ᶠ n in atTop, EN (phi n) (wN n) ≤ Cen)
    (hw : Tendsto wN atTop (𝓝 w)) (hwE : Elim w ≠ ∞) :
    Tendsto (fun n => ∫ x, JN (phi n) (wN n) x ^ 2 ∂(muN (phi n))) atTop
        (𝓝 (∫ x, J w x ^ 2 ∂mu)) ∧
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Tendsto (fun n => ∫ x, f x * JN (phi n) (wN n) x ∂(muN (phi n))) atTop
          (𝓝 (∫ x, f x * J w x ∂mu)) := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hbd
  obtain ⟨C3, hC3, hH3⟩ := hH3N
  have hψ : StrictMono (fun n : ℕ => phi (n + n0)) :=
    hphi.comp (fun a b hab => Nat.add_lt_add_right hab n0)
  have hfin : ∀ n, EN (phi (n + n0)) (wN (n + n0)) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top hCen (hn0 _ (Nat.le_add_left _ _))
  have hCen1 : Cen + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hCen, ENNReal.one_ne_top⟩
  have hrep : ∀ n, ∃ v : killedSobolevGraph
      (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr),
      (v : SobolevData (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)).1 =
        wN (n + n0) ∧
      in_killed_energy M H HI (omegaN (phi (n + n0))) (cutoff (phi (n + n0)))
        (cubeCenter Qtri) hr v v ≤ (Cen + 1).toReal := by
    intro n
    have hlt : EN (phi (n + n0)) (wN (n + n0)) < Cen + 1 :=
      lt_of_le_of_lt (hn0 _ (Nat.le_add_left _ _)) (ENNReal.lt_add_right hCen one_ne_zero)
    rw [hEN] at hlt
    obtain ⟨v, hv⟩ := iInf_lt_iff.1 hlt
    exact ⟨v.val, v.property, (ENNReal.ofReal_le_iff_le_toReal hCen1).1 hv.le⟩
  choose vN hvN1 hvN2 using hrep
  have hcoer : ∀ (N : ℕ) (v : killedSobolevGraph
      (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
          (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (cubeCenter Qtri)
          (cubeScaleFactor Qtri) hr)).1 ∧
          cubeFractionalL2Norm hd (cubeCenter Qtri)
            (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder v3 ^ 2 ≤
            C3 * in_killed_energy M H HI (omegaN (phi (N + n0))) (cutoff (phi (N + n0)))
              (cubeCenter Qtri) hr v v := by
    intro N v
    have hle : EN (phi (N + n0)) (v : SobolevData (centeredCube (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr)).1 ≤
        ENNReal.ofReal (in_killed_energy M H HI (omegaN (phi (N + n0)))
          (cutoff (phi (N + n0))) (cubeCenter Qtri) hr v v) := by
      rw [hEN]
      exact iInf_le (fun v' : {v' : killedSobolevGraph
          (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) //
          (v' : SobolevData (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)).1 =
            (v : SobolevData (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)).1} =>
        ENNReal.ofReal (in_killed_energy M H HI (omegaN (phi (N + n0)))
          (cutoff (phi (N + n0))) (cubeCenter Qtri) hr v'.val v'.val)) ⟨v, rfl⟩
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    obtain ⟨v3, hv3, hv3b⟩ := hH3 (phi (N + n0)) _ hne
    refine ⟨v3, hv3, hv3b.trans (mul_le_mul_of_nonneg_left ?_ hC3.le)⟩
    have hnn : 0 ≤ in_killed_energy M H HI (omegaN (phi (N + n0))) (cutoff (phi (N + n0)))
        (cubeCenter Qtri) hr v v := by
      unfold in_killed_energy
      exact sobolevCoefficientForm_nonneg _ _
    calc (EN (phi (N + n0)) _).toReal ≤ (ENNReal.ofReal (in_killed_energy M H HI
          (omegaN (phi (N + n0))) (cutoff (phi (N + n0))) (cubeCenter Qtri) hr v v)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = _ := ENNReal.toReal_ofReal hnn
  have hsuppN : ∀ N, muN (phi (N + n0)) (closure (Homogenization.openCubeSet Qtri))ᶜ = 0 := by
    intro N
    rw [hmuN, Measure.restrict_apply isClosed_closure.measurableSet.compl,
      centeredCube_eq_openCubeSet Qtri hr, Set.compl_inter_self, measure_empty]
  have hsupp : mu (closure (Homogenization.openCubeSet Qtri))ᶜ = 0 := by
    rw [hmu, Measure.restrict_apply isClosed_closure.measurableSet.compl,
      centeredCube_eq_openCubeSet Qtri hr, Set.compl_inter_self, measure_empty]
  have hfrontQ : mu (frontier (Homogenization.openCubeSet Qtri)) = 0 := by
    rw [← centeredCube_eq_openCubeSet Qtri hr, hmu]
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq hfront)) zero_le
  have hmuNM' : ∀ N, muN (phi (N + n0)) (closure (Homogenization.openCubeSet Qtri)) ≤ Mbar := by
    intro N
    rw [← centeredCube_eq_openCubeSet Qtri hr]
    exact hmuNM _
  have hmuM' : mu (closure (Homogenization.openCubeSet Qtri)) ≤ Mbar := by
    rw [← centeredCube_eq_openCubeSet Qtri hr]
    exact hmuM
  have hvconv : Tendsto (fun N => (vN N : SobolevData (centeredCube (cubeCenter Qtri)
      (cubeScaleFactor Qtri) hr)).1) atTop (𝓝 w) :=
    (hw.comp (tendsto_add_atTop_nat n0)).congr (fun n => (hvN1 n).symm)
  obtain ⟨uHalf, huH, hsq, hlin⟩ := lem_varying_trace hd Qtri hr M H HI
    (fun N => cutoff (phi (N + n0))) (hcutoff.comp hψ) (fun N => omegaN (phi (N + n0)))
    (fun N => muN (phi (N + n0))) mu muFull (fun N => hmuN (phi (N + n0))) hmu
    (aux_prop_speed_resolvent_converge_comp _ _ hconv _ hψ) hfront
    (aux_prop_speed_resolvent_converge_comp _ _ hloc _ hψ) hfrontQ hsuppN hsupp
    (fun N => TN (phi (N + n0))) T (fun N => KN (phi (N + n0))) K C (fun N => hKN _) hK hC
    (fun N => hTN _) hT Kbar (fun N => hKNbar _) hKbar Mbar hMbar hmuNM' hmuM'
    vN (fun N => iN (phi (N + n0)) (wN (N + n0)) (hfin N))
    (fun N => by rw [hiN, hvN1]) w hvconv (Cen + 1).toReal ENNReal.toReal_nonneg hvN2
    C3 hC3 hcoer SInterp
  have hTu : T uHalf = T (i w hwE) :=
    aux_prop_speed_resolvent_trace_congr hd Qtri hr mu K C T hT uHalf (i w hwE)
      (by rw [huH, hi])
  have hJNe : ∀ n, JN (phi (n + n0)) (wN (n + n0)) =ᵐ[muN (phi (n + n0))]
      (TN (phi (n + n0)) (iN (phi (n + n0)) (wN (n + n0)) (hfin n)) :
        SpatialCoordinates d → ℝ) := fun n => hJN _ _ (hfin n)
  have hJe : J w =ᵐ[mu] (T uHalf : SpatialCoordinates d → ℝ) := by
    rw [hTu]
    exact hJ w hwE
  have hJsq : ∫ x, J w x ^ 2 ∂mu = ∫ x, (T uHalf : SpatialCoordinates d → ℝ) x ^ 2 ∂mu :=
    integral_congr_ae (hJe.mono fun x hx => by simp only [hx])
  have hJf : ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∫ x, f x * J w x ∂mu = ∫ x, f x * (T uHalf : SpatialCoordinates d → ℝ) x ∂mu :=
    fun f => integral_congr_ae (hJe.mono fun x hx => by simp only [hx])
  refine ⟨?_, fun f => ?_⟩
  · rw [← tendsto_add_atTop_iff_nat n0, hJsq]
    exact hsq.congr (fun n => integral_congr_ae ((hJNe n).mono fun x hx => by simp only [hx]))
  · rw [← tendsto_add_atTop_iff_nat n0, hJf f]
    exact (hlin f).congr
      (fun n => integral_congr_ae ((hJNe n).mono fun x hx => by simp only [hx]))

/-- Part C of `prop_speed_resolvent`: every `L²` cluster point of the finite-cutoff minimizers
has finite limit energy and minimizes the limit functional (paper 4909-4918). -/
theorem aux_prop_speed_resolvent_cluster_min
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < cubeScaleFactor Qtri)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H)
    (cutoff : ℕ → ℕ) (hcutoff : StrictMono cutoff)
    (omegaN : ℕ → BilateralField d)
    (EN : ℕ → DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (Elim : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hEN : ∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
      EN N u = ⨅ v : {v : killedSobolevGraph
          (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) //
        (v : SobolevData (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)).1 = u},
        ENNReal.ofReal
          (in_killed_energy M H HI (omegaN N) (cutoff N)
            (cubeCenter Qtri) hr v.val v.val))
    (muN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d))
    (muFull : Measure (SpatialCoordinates d))
    (hmuN : ∀ (N : ℕ),
      muN N = (cutoffSpeedMeasure M H (omegaN N) (cutoff N)).restrict
        (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
          Set (SpatialCoordinates d))))
    (hmu : mu = muFull.restrict
      (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d))))
    (hconv : MeasuresConvergeLocally
      (fun N => cutoffSpeedMeasure M H (omegaN N) (cutoff N)) muFull)
    (hfront : muFull (frontier (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) = 0)
    (hmufin : mu univ < ∞)
    (TN : (N : ℕ) →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder →
      Lp ℝ 2 (muN N))
    (T : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
      (cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 mu)
    (KN : ℕ → ℝ) (K C : ℝ)
    (hKN : ∀ (N : ℕ), 0 ≤ KN N) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hTN : ∀ (N : ℕ),
      MeasureTraceCharacterization hd Qtri hr (muN N) (KN N) C (TN N))
    (hT : MeasureTraceCharacterization hd Qtri hr mu K C T)
    (Kbar : ℝ) (hKNbar : ∀ (N : ℕ), KN N ≤ Kbar) (hKbar : K ≤ Kbar)
    (Mbar : ℝ≥0∞) (hMbar : Mbar ≠ ∞)
    (hmuNM : ∀ (N : ℕ), muN N (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) ≤ Mbar)
    (hmuM : mu (closure (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) ≤ Mbar)
    (iN : (N : ℕ) → (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)) →
      EN N u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder)
    (i : (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)) →
      Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hiN : ∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : EN N u ≠ ∞), (iN N u hu).val 0 = u)
    (hi : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (JN : ℕ → DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) →
      SpatialCoordinates d → ℝ)
    (J : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) →
      SpatialCoordinates d → ℝ)
    (hJN : ∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : EN N u ≠ ∞),
      (JN N u) =ᵐ[muN N] (TN N (iN N u hu) : SpatialCoordinates d → ℝ))
    (hJ : ∀ (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
      (hu : Elim u ≠ ∞),
      (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (hH3N : ∃ C3 : ℝ, 0 < C3 ∧
      (∀ (N : ℕ) (u : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)),
        EN N u ≠ ∞ →
        ∃ v : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
            (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder,
          v.val 0 = u ∧
            cubeFractionalL2Norm hd (cubeCenter Qtri)
              (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder v ^ 2 ≤
              C3 * (EN N u).toReal))
    (hmosco : Lane3.MoscoLiminf EN Elim ∧ Lane3.MoscoRecovery EN Elim)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (uN : ℕ → DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr)) (ubar : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hfin : ∀ n : ℕ, EN n (uN n) ≠ ∞)
    (hbd : ∃ Cen : ℝ≥0∞, Cen ≠ ∞ ∧ ∀ n : ℕ, EN n (uN n) ≤ Cen)
    (hNmin : ∀ n : ℕ, ∀ w : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr), EN n w ≠ ∞ →
      (EN n (uN n)).toReal +
          lam * (∫ x, JN n (uN n) x ^ 2 ∂(muN n)) -
          2 * ∫ x, f x * JN n (uN n) x ∂(muN n) ≤
        (EN n w).toReal +
          lam * (∫ x, JN n w x ^ 2 ∂(muN n)) -
          2 * ∫ x, f x * JN n w x ∂(muN n))
    (hlim : Tendsto (fun n => uN (phi n)) atTop (𝓝 ubar)) :
    Elim ubar ≠ ∞ ∧
      ∀ v : DomainL2 (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr), Elim v ≠ ∞ →
        (Elim ubar).toReal + lam * (∫ x, J ubar x ^ 2 ∂mu) -
          2 * ∫ x, f x * J ubar x ∂mu ≤
        (Elim v).toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
          2 * ∫ x, f x * J v x ∂mu := by
  obtain ⟨Cen, hCen, hCenb⟩ := hbd
  have hloc : MeasuresConvergeLocally muN mu := by
    have hS : muFull (closure ((centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) ≠ ∞ := by
      rw [hmu, Measure.restrict_apply_univ] at hmufin
      exact hmufin.ne
    have h := aux_prop_speed_resolvent_restrict_converge
      (fun N => cutoffSpeedMeasure M H (omegaN N) (cutoff N)) muFull
      ((centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))
      (centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr).isOpen
      (centeredCube_isBounded (cubeCenter Qtri) hr).isCompact_closure
      (aux_prop_speed_resolvent_cube_nonempty (cubeCenter Qtri) hr)
      (aux_prop_speed_resolvent_cube_compl_nonempty hd (cubeCenter Qtri) hr)
      (fun N => aux_prop_speed_resolvent_cutoff_locfin M H (omegaN N) (cutoff N)) hS hfront hconv
    have e : muN = fun N => (cutoffSpeedMeasure M H (omegaN N) (cutoff N)).restrict
        (closure ((centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) := funext hmuN
    rw [e, hmu]
    exact h
  have hEu := aux_prop_speed_resolvent_subseq_liminf EN Elim hmosco.1 phi hphi
    (fun n => uN (phi n)) ubar hlim
  have hubar : Elim ubar ≠ ∞ :=
    aux_prop_speed_resolvent_liminf_ne_top _ _ Cen hCen (fun n => hCenb (phi n)) hEu
  refine ⟨hubar, fun v hv => ?_⟩
  obtain ⟨y, hy, hylim⟩ := aux_prop_speed_resolvent_subseq_limsup EN Elim hmosco.2 phi hphi v
  have hU := aux_prop_speed_resolvent_trace_passage hd Qtri hr M H HI cutoff hcutoff omegaN
    EN Elim hEN muN mu muFull hmuN hmu hconv hfront hloc TN T KN K C hKN hK hC hTN hT
    Kbar hKNbar hKbar Mbar hMbar hmuNM hmuM iN i hiN hi JN J hJN hJ hH3N SInterp phi hphi
    (fun n => uN (phi n)) ubar Cen hCen (Eventually.of_forall fun n => hCenb (phi n)) hlim hubar
  have hev : ∀ᶠ n in atTop, EN (phi n) (y n) ≤ Elim v + 1 := by
    have hlt : limsup (fun n => EN (phi n) (y n)) atTop < Elim v + 1 :=
      hylim.trans_lt (ENNReal.lt_add_right hv one_ne_zero)
    exact (eventually_lt_of_limsup_lt hlt).mono fun n hn => hn.le
  have hV := aux_prop_speed_resolvent_trace_passage hd Qtri hr M H HI cutoff hcutoff omegaN
    EN Elim hEN muN mu muFull hmuN hmu hconv hfront hloc TN T KN K C hKN hK hC hTN hT
    Kbar hKNbar hKbar Mbar hMbar hmuNM hmuM iN i hiN hi JN J hJN hJ hH3N SInterp phi hphi
    y v (Elim v + 1) (ENNReal.add_ne_top.2 ⟨hv, ENNReal.one_ne_top⟩) hev hy hv
  exact aux_prop_speed_resolvent_cluster_real (fun n => EN (phi n) (uN (phi n)))
    (fun n => EN (phi n) (y n)) (Elim ubar) (Elim v) Cen hCen (fun n => hCenb (phi n)) hv
    hEu hylim _ _ _ _ _ _ _ _ (hU.1.const_mul lam) ((hU.2 f).const_mul 2)
    (hV.1.const_mul lam) ((hV.2 f).const_mul 2) (fun n hn => hNmin (phi n) (y n) hn)

end PSRAssembly



theorem prop_speed_resolvent
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < cubeScaleFactor Qtri) :
    let U : TopologicalSpace.Opens (SpatialCoordinates d) :=
      centeredCube (cubeCenter Qtri) (cubeScaleFactor Qtri) hr
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (HI : InfraredCharacterization M H)
      (cutoff : ℕ → ℕ)
      (hcutoff : StrictMono cutoff)
      (omegaN : ℕ → BilateralField d)
      (EN : ℕ → DomainL2 U → ℝ≥0∞)
      (G : DomainL2 U →L[ℝ] DomainL2 U)
      (Elim : DomainL2 U → ℝ≥0∞),
      (∀ (N : ℕ) (u : DomainL2 U),
        EN N u = ⨅ v : {v : killedSobolevGraph U //
          (v : SobolevData U).1 = u},
          ENNReal.ofReal
            (in_killed_energy M H HI (omegaN N) (cutoff N)
              (cubeCenter Qtri) hr v.val v.val)) →
      (∀ (u : DomainL2 U),
        Elim u = (limitFormEnergy G u).toENNReal) →
      ∀ (muN : ℕ → Measure (SpatialCoordinates d))
        (mu : Measure (SpatialCoordinates d))
        (muFull : Measure (SpatialCoordinates d)),
      (∀ (N : ℕ),
        muN N = (cutoffSpeedMeasure M H (omegaN N) (cutoff N)).restrict
          (closure U)) →
      mu = muFull.restrict (closure U) →
      MeasuresConvergeLocally
        (fun N => cutoffSpeedMeasure M H (omegaN N) (cutoff N)) muFull →
      muFull (frontier U) = 0 →
      (∀ (N : ℕ), muN N univ < ∞) →
      mu univ < ∞ →
      ∀ (TN : (N : ℕ) →
        CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
          (cubeScaleFactor Qtri) hr halfFractionalOrder →
        Lp ℝ 2 (muN N))
      (T : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
        (cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 mu)
      (KN : ℕ → ℝ) (K C : ℝ),
      (∀ (N : ℕ), 0 ≤ KN N) →
      0 ≤ K →
      0 ≤ C →
      (∀ (N : ℕ),
        MeasureTraceCharacterization hd Qtri hr (muN N) (KN N) C (TN N)) →
      MeasureTraceCharacterization hd Qtri hr mu K C T →
      ∀ (Kbar : ℝ),
      (∀ (N : ℕ), KN N ≤ Kbar) →
      K ≤ Kbar →
      ∀ (Mbar : ℝ≥0∞),
      Mbar ≠ ∞ →
      (∀ (N : ℕ), muN N (closure U) ≤ Mbar) →
      mu (closure U) ≤ Mbar →
      ∀ (iN : (N : ℕ) → (u : DomainL2 U) → EN N u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
          (cubeScaleFactor Qtri) hr halfFractionalOrder)
      (i : (u : DomainL2 U) → Elim u ≠ ∞ →
        CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
          (cubeScaleFactor Qtri) hr halfFractionalOrder),
      (∀ (N : ℕ) (u : DomainL2 U) (hu : EN N u ≠ ∞),
        (iN N u hu).val 0 = u) →
      (∀ (u : DomainL2 U) (hu : Elim u ≠ ∞),
        (i u hu).val 0 = u) →
      ∀ (JN : ℕ → DomainL2 U → SpatialCoordinates d → ℝ)
      (J : DomainL2 U → SpatialCoordinates d → ℝ),
      (∀ (N : ℕ) (u : DomainL2 U) (hu : EN N u ≠ ∞),
        (JN N u) =ᵐ[muN N]
          (TN N (iN N u hu) : SpatialCoordinates d → ℝ)) →
      (∀ (u : DomainL2 U) (hu : Elim u ≠ ∞),
        (J u) =ᵐ[mu]
          (T (i u hu) : SpatialCoordinates d → ℝ)) →
      (hmosco : Lane3.MoscoLiminf EN Elim ∧
        Lane3.MoscoRecovery EN Elim) →
      (hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
        ∀ w : DomainL2 U,
          ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * Elim w) →
      Elim 0 = 0 →
      (∀ (c : ℝ) (w1 w2 : DomainL2 U),
        Elim w1 ≠ ∞ → Elim w2 ≠ ∞ →
        Elim (c • w1 + w2) ≠ ∞) →
      (∀ (w1 w2 : DomainL2 U), Elim w1 ≠ ∞ → Elim w2 ≠ ∞ →
        (Elim (w1 + w2)).toReal + (Elim (w1 - w2)).toReal =
          2 * (Elim w1).toReal + 2 * (Elim w2).toReal) →
      (∀ (u : ℕ → DomainL2 U), (∀ n : ℕ, Elim (u n) ≠ ∞) →
        (∀ eps : ℝ, 0 < eps →
          ∃ Nn : ℕ, ∀ m n : ℕ, Nn ≤ m → Nn ≤ n →
            (Elim (u m - u n)).toReal < eps) →
        ∃ ulim : DomainL2 U, Elim ulim ≠ ∞ ∧
          Tendsto (fun n => (Elim (u n - ulim)).toReal) atTop (nhds 0)) →
      (∀ (c : ℝ) (u : DomainL2 U), Elim u ≠ ∞ →
        Elim (c • u) = ENNReal.ofReal (c ^ 2) * Elim u) →
      ∀ (Ktr : ℝ),
      0 ≤ Ktr →
      (∀ (N : ℕ) (u : DomainL2 U) (hu : EN N u ≠ ∞),
        (∫⁻ x, ENNReal.ofReal (JN N u x ^ 2) ∂(muN N)) ≤
          ENNReal.ofReal Ktr * EN N u) →
      (∀ (u : DomainL2 U) (hu : Elim u ≠ ∞),
        (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤
          ENNReal.ofReal Ktr * Elim u) →
      (∃ C3 : ℝ, 0 < C3 ∧
        (∀ (N : ℕ) (u : DomainL2 U), EN N u ≠ ∞ →
          ∃ v : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
              (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder,
            v.val 0 = u ∧
              cubeFractionalL2Norm hd (cubeCenter Qtri)
                (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder v ^ 2 ≤
                C3 * (EN N u).toReal)) →
      (∃ C3 : ℝ, 0 < C3 ∧
        (∀ (u : DomainL2 U), Elim u ≠ ∞ →
          ∃ v : CubeFractionalL2 (k := 1) hd (cubeCenter Qtri)
              (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder,
            v.val 0 = u ∧
              cubeFractionalL2Norm hd (cubeCenter Qtri)
                (cubeScaleFactor Qtri) hr Lane4.threeQuarterOrder v ^ 2 ≤
                C3 * (Elim u).toReal)) →
      ∀ (SInterp : CubeFractionalInterpolationInput d hd)
        (lam : ℝ) (hlam : 0 < lam)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      ∃ ustar : DomainL2 U, Elim ustar ≠ ∞ ∧
        (∀ w : DomainL2 U, Elim w ≠ ∞ →
          (Elim ustar).toReal + lam * (∫ x, J ustar x ^ 2 ∂mu) -
              2 * ∫ x, f x * J ustar x ∂mu ≤
            (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
              2 * ∫ x, f x * J w x ∂mu) ∧
        (∀ w : DomainL2 U, Elim w ≠ ∞ →
          (∀ v : DomainL2 U, Elim v ≠ ∞ →
            (Elim w).toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
                2 * ∫ x, f x * J w x ∂mu ≤
              (Elim v).toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
                2 * ∫ x, f x * J v x ∂mu) →
          w = ustar) ∧
        ∀ (uN : ℕ → DomainL2 U) (ubar : DomainL2 U)
          (phi : ℕ → ℕ),
          StrictMono phi →
          (∀ n : ℕ, EN n (uN n) ≠ ∞) →
          (∃ Cen : ℝ≥0∞, Cen ≠ ∞ ∧
            ∀ n : ℕ, EN n (uN n) ≤ Cen) →
          (∀ n : ℕ, ∀ w : DomainL2 U, EN n w ≠ ∞ →
            (EN n (uN n)).toReal +
                lam * (∫ x, JN n (uN n) x ^ 2 ∂(muN n)) -
                2 * ∫ x, f x * JN n (uN n) x ∂(muN n) ≤
              (EN n w).toReal +
                lam * (∫ x, JN n w x ^ 2 ∂(muN n)) -
                2 * ∫ x, f x * JN n w x ∂(muN n)) →
          Tendsto (fun n => uN (phi n)) atTop (nhds ubar) →
          ubar = ustar := by
  intro U M H HI cutoff hcutoff omegaN EN G Elim hEN hElim muN mu muFull hmuN hmu hconv hfront
    hmuNfin hmufin TN T KN K C hKN hK hC hTN hT Kbar hKNbar hKbar Mbar hMbar hmuNM hmuM iN i
    hiN hi JN J hJN hJ hmosco hcoer hE0 hclosed hpara hcomplete hscale Ktr hKtr hJNtr hJtr
    hH3N hH3 SInterp lam hlam f
  obtain ⟨ustar, hus, hmin, huniq⟩ := aux_prop_speed_resolvent_parts_AB hd Qtri hr G Elim hElim
    mu muFull hmu hmufin K C T hT i hi J hJ hcoer hE0 hclosed hpara hscale Ktr hKtr hJtr
    lam hlam f
  refine ⟨ustar, hus, hmin, huniq, ?_⟩
  intro uN ubar phi hphi hfin hbd hNmin hlim
  obtain ⟨hubar, hubar_min⟩ := aux_prop_speed_resolvent_cluster_min hd Qtri hr M H HI cutoff
    hcutoff omegaN EN Elim hEN muN mu muFull hmuN hmu hconv hfront hmufin TN T KN K C hKN hK hC
    hTN hT Kbar hKNbar hKbar Mbar hMbar hmuNM hmuM iN i hiN hi JN J hJN hJ hH3N hmosco SInterp
    lam f uN ubar phi hphi hfin hbd hNmin hlim
  exact huniq ubar hubar hubar_min

end Paper
