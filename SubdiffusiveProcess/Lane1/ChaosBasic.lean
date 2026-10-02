import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Probability.ChaosCutoffLocalFinite
import SubdiffusiveProcess.Probability.WeightedChaosMass
import SubdiffusiveProcess.Probability.WeightedChaosAdapted
import SubdiffusiveProcess.Probability.CubeMassMartingale
import SubdiffusiveProcess.Probability.CubeMassConvergence
import SubdiffusiveProcess.Probability.WeightedFineDensityMartingale
import SubdiffusiveProcess.Probability.WeightedFineDensityIntegrable
import SubdiffusiveProcess.Probability.FineDensityMultipointCutoffMoment
import SubdiffusiveProcess.Probability.FineDensityMean
import SubdiffusiveProcess.Probability.MartingaleMaximalMoment
import SubdiffusiveProcess.Probability.MartingalePowers
import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem continuous_fineDensity
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) :
    Continuous (fineDensity M N omega) := by
  unfold fineDensity finePotential
  fun_prop

theorem chaosCutoff_eq_weightedChaosCutoff_zero
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) :
    chaosCutoff M N omega = weightedChaosCutoff M (fun _ ↦ 0) N omega := by
  unfold chaosCutoff weightedChaosCutoff
  aesop

theorem integral_pow_eq_integral_pi
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SigmaFinite mu]
    (f : X → ℝ) (p : ℕ) :
    (∫ x, f x ∂mu) ^ p =
      ∫ y : Fin p → X, ∏ i, f (y i) ∂(Measure.pi fun _ : Fin p ↦ mu) := by
  simpa using (integral_fintype_prod_eq_pow (ι := Fin p) (𝕜 := ℝ)
    (E := X) (μ := mu) f).symm

theorem fineDensity_pos
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    0 < fineDensity M N omega x := by
  unfold fineDensity
  positivity

theorem weightedFineDensity_pos
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    0 < Real.exp (H omega x) * fineDensity M N omega x := by
  unfold fineDensity
  positivity

theorem centeredCube_volume_ne_top
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ∞ := by
  unfold centeredCube
  aesop

theorem exp_apply_le_exp_norm_restrict
    {d : ℕ} (g : C(SpatialCoordinates d, ℝ))
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (x : SpatialCoordinates d) (hx : x ∈ (K : Set (SpatialCoordinates d))) :
    Real.exp (g x) ≤ Real.exp ‖g.restrict (K : Set (SpatialCoordinates d))‖ := by
  apply Real.exp_le_exp.mpr
  calc
    g x = (g.restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩ := rfl
    _ ≤ ‖(g.restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩‖ := Real.le_norm_self _
    _ ≤ ‖g.restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm _ _

theorem centeredCube_coe_eq_ball
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := by
  unfold centeredCube
  aesop

theorem volume_ball_spatial
    {d : ℕ} (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s) :
    volume (Metric.ball z s) = ENNReal.ofReal ((2 * s) ^ d) := by
  have h2 : (0 : ℝ) < 2 * s := by linarith
  have hdiv : (2 * s) / 2 = s := by ring
  have hball : Metric.ball z s = ↑(centeredCube z (2 * s) h2) := by
    rw [centeredCube_eq_pi z h2]
    simp_rw [hdiv]
    ext y
    simp only [Metric.mem_ball, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    rw [dist_pi_lt_iff hs]
    constructor
    · intro h i
      have hi := h i
      rw [Real.dist_eq, abs_lt] at hi
      rcases hi with ⟨hi1, hi2⟩
      constructor <;> linarith
    · intro h i
      have hi := h i
      rcases hi with ⟨hi1, hi2⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
  rw [hball]
  exact centeredCube_volume z h2

theorem integrable_and_integral_le_of_lintegral_ofReal_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (g : Omega → ℝ) (hg : Measurable g) (hg0 : ∀ w, 0 ≤ g w)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (∫⁻ w, ENNReal.ofReal (g w) ∂mu) ≤ ENNReal.ofReal C) :
    Integrable g mu ∧ (∫ w, g w ∂mu) ≤ C := by
  have hg_ae : 0 ≤ᵐ[mu] g := MeasureTheory.ae_of_all mu hg0
  have hfin : HasFiniteIntegral g mu := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hg_ae]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hint : Integrable g mu := ⟨hg.aestronglyMeasurable, hfin⟩
  constructor
  · exact hint
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hg_ae hg.aestronglyMeasurable]
    have hlt : (∫⁻ w, ENNReal.ofReal (g w) ∂mu) < ⊤ :=
      lt_of_le_of_lt h ENNReal.ofReal_lt_top
    have hne : (∫⁻ w, ENNReal.ofReal (g w) ∂mu) ≠ ⊤ := ne_of_lt hlt
    have hle : (∫⁻ w, ENNReal.ofReal (g w) ∂mu).toReal ≤ (ENNReal.ofReal C).toReal :=
      (ENNReal.toReal_le_toReal hne ENNReal.ofReal_ne_top).2 h
    simpa [ENNReal.toReal_ofReal hC] using hle

theorem weightedChaosCutoff_centeredCube_toReal_nonneg
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 ≤ ((weightedChaosCutoff M H N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  aesop

theorem exp_norm_restrict_pow_integrable
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d)) (p : ℕ) :
    Integrable (fun omega ↦ Real.exp
      ((p : ℝ) * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure := by
  exact exists_compactExponentialMoment_of_infraredCharacterization hd M H hH K (p : ℝ) (Nat.cast_nonneg p)

theorem weightedChaosCutoff_isLocallyFinite
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d) :
    IsLocallyFiniteMeasure (weightedChaosCutoff M H N omega) := by
  haveI : IsLocallyFiniteMeasure (chaosCutoff M N omega) :=
    chaosCutoff_isLocallyFinite M N omega
  unfold weightedChaosCutoff
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  apply Continuous.mul
  · exact Real.continuous_exp.comp (ContinuousMap.continuous (H omega))
  · unfold fineDensity finePotential
    fun_prop

theorem chaosCutoff_centeredCube_toReal_eq_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((chaosCutoff M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        fineDensity M N omega x := by
  rw [chaosCutoff_eq_weightedChaosCutoff_zero]
  rw [weightedChaosCutoff_centeredCube_toReal_eq_integral]
  simp [ContinuousMap.zero_apply]

theorem weightedChaosCutoff_centeredCube_toReal_pow_eq_pi_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    ((weightedChaosCutoff M H N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p =
      ∫ y : Fin p → SpatialCoordinates d,
        ∏ i, (Real.exp (H omega (y i)) * fineDensity M N omega (y i))
        ∂(Measure.pi fun _ : Fin p ↦
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  rw [weightedChaosCutoff_centeredCube_toReal_eq_integral M H N omega z r hr]
  exact integral_pow_eq_integral_pi
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
    (fun x => Real.exp (H omega x) * fineDensity M N omega x) p

theorem prod_exp_apply_le_exp_nsmul_norm_restrict
    {d : ℕ} (g : C(SpatialCoordinates d, ℝ))
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (p : ℕ) (y : Fin p → SpatialCoordinates d)
    (hy : ∀ i, y i ∈ (K : Set (SpatialCoordinates d))) :
    ∏ i, Real.exp (g (y i)) ≤
      Real.exp ((p : ℝ) * ‖g.restrict (K : Set (SpatialCoordinates d))‖) := by
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      0 ≤ Real.exp (g (y i)) := fun i _ => (Real.exp_pos _).le
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      Real.exp (g (y i)) ≤ Real.exp ‖g.restrict (K : Set (SpatialCoordinates d))‖ :=
    fun i _ => exp_apply_le_exp_norm_restrict g K (y i) (hy i)
  calc
    ∏ i, Real.exp (g (y i))
        ≤ ∏ _i : Fin p, Real.exp ‖g.restrict (K : Set (SpatialCoordinates d))‖ :=
      Finset.prod_le_prod h1 h2
    _ = (Real.exp ‖g.restrict (K : Set (SpatialCoordinates d))‖) ^ p := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = Real.exp ((p : ℝ) * ‖g.restrict (K : Set (SpatialCoordinates d))‖) := by
      rw [Real.exp_nat_mul]

theorem volume_ball_inter_le
    {d : ℕ} (x : SpatialCoordinates d) (R s : ℝ) (hs : 0 < s)
    (hvol : volume (Metric.ball x s) = ENNReal.ofReal ((2 * s) ^ d)) :
    volume (Metric.ball x R ∩ Metric.ball x s) ≤ ENNReal.ofReal ((2 * s) ^ d) := by
  calc
    volume (Metric.ball x R ∩ Metric.ball x s) ≤ volume (Metric.ball x s) :=
      measure_mono Set.inter_subset_right
    _ = ENNReal.ofReal ((2 * s) ^ d) := hvol

theorem prod_mul_eq_prod_mul_prod
    {X : Type*} (p : ℕ) (a b : X → ℝ) (y : Fin p → X) :
    ∏ i, (a (y i) * b (y i)) = (∏ i, a (y i)) * ∏ i, b (y i) :=
  Finset.prod_mul_distrib


theorem chaosCutoff_centeredCube_toReal_pow_eq_pi_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    ((chaosCutoff M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p =
      ∫ y : Fin p → SpatialCoordinates d,
        ∏ i, fineDensity M N omega (y i)
        ∂(Measure.pi fun _ : Fin p ↦
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  rw [chaosCutoff_centeredCube_toReal_eq_integral M N omega z r hr]
  exact integral_pow_eq_integral_pi _ _ p

theorem prod_weighted_le_exp_mul_prod_fineDensity
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (p : ℕ) (y : Fin p → SpatialCoordinates d)
    (hy : ∀ i, y i ∈ (K : Set (SpatialCoordinates d))) :
    ∏ i, (Real.exp (H omega (y i)) * fineDensity M N omega (y i)) ≤
      Real.exp ((p : ℝ) * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖) *
        ∏ i, fineDensity M N omega (y i) := by
  rw [prod_mul_eq_prod_mul_prod p (fun x => Real.exp (H omega x))
    (fun x => fineDensity M N omega x) y]
  have h1 := prod_exp_apply_le_exp_nsmul_norm_restrict (H omega) K p y hy
  have h2 : 0 ≤ ∏ i, fineDensity M N omega (y i) :=
    Finset.prod_nonneg (fun i _ => (fineDensity_pos M N omega (y i)).le)
  exact mul_le_mul_of_nonneg_right h1 h2


theorem fineDensity_integrableOn_centeredCube
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fineDensity M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d)) volume := by
  have hc := continuous_fineDensity M N omega
  have h := (hc.locallyIntegrable (μ := (volume : Measure (SpatialCoordinates d)))
    ).integrableOn_isCompact (isCompact_closedBall z (r / 2))
  refine h.mono_set ?_
  rw [centeredCube_coe_eq_ball]
  exact Metric.ball_subset_closedBall

theorem integrable_prod_fineDensity_pi
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    Integrable (fun y : Fin p → SpatialCoordinates d ↦
        ∏ i, fineDensity M N omega (y i))
      (Measure.pi fun _ : Fin p ↦
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
  Integrable.fintype_prod
    (fun _ => fineDensity_integrableOn_centeredCube M N omega z r hr)

theorem ofReal_chaosCutoff_pow_eq_pi_lintegral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p) =
      ∫⁻ y : Fin p → SpatialCoordinates d,
        ENNReal.ofReal (∏ i, fineDensity M N omega (y i))
        ∂(Measure.pi fun _ : Fin p ↦
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  rw [chaosCutoff_centeredCube_toReal_pow_eq_pi_integral M N omega z r hr p]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_prod_fineDensity_pi M N omega z r hr p)
    (ae_of_all _ (fun y =>
      Finset.prod_nonneg (fun i _ => (fineDensity_pos M N omega (y i)).le)))

theorem measurable_prod_fineDensity_uncurry
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (p : ℕ) :
    Measurable (fun q : BilateralField d × (Fin p → SpatialCoordinates d) ↦
      ENNReal.ofReal (∏ i, fineDensity M N q.1 (q.2 i))) := by
  have hg : Measurable (fun q : BilateralField d × SpatialCoordinates d =>
      fineDensity M N q.1 q.2) := by
    unfold fineDensity finePotential
    fun_prop
  refine Measurable.ennreal_ofReal ?_
  refine Finset.measurable_prod _ (fun i _ => ?_)
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem lintegral_lintegral_swap_prod_fineDensity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    (∫⁻ omega, ∫⁻ y : Fin p → SpatialCoordinates d,
        ENNReal.ofReal (∏ i, fineDensity M N omega (y i))
        ∂(Measure.pi fun _ : Fin p ↦
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ y : Fin p → SpatialCoordinates d, ∫⁻ omega,
        ENNReal.ofReal (∏ i, fineDensity M N omega (y i))
        ∂(chaosSampleLaw M).toMeasure
      ∂(Measure.pi fun _ : Fin p ↦
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
  lintegral_lintegral_swap (measurable_prod_fineDensity_uncurry M N p).aemeasurable

theorem lintegral_ofReal_prod_fineDensity_eq_ofReal_integral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N : ℕ)
    (y : Fin p → SpatialCoordinates d) (hpdelta : (p : ℝ) * M.delta ≤ 1) :
    (∫⁻ omega, ENNReal.ofReal (∏ k, fineDensity M N omega (y k))
        ∂(chaosSampleLaw M).toMeasure) =
      ENNReal.ofReal (∫ omega, ∏ k, fineDensity M N omega (y k)
        ∂(chaosSampleLaw M).toMeasure) :=
  (ofReal_integral_eq_lintegral_ofReal
    (fineDensity_multiPoint_prod_exp_moment_le M p hp N y hpdelta).1
    (ae_of_all _ (fun omega =>
      Finset.prod_nonneg (fun k _ => (fineDensity_pos M N omega (y k)).le)))).symm

/-- Paper D:46–48 combined with D:49–60: the `p`-point expansion of the cube
mass, with the layer-moment bound inserted pointwise.  `bound` is the
pointwise bound on the `p`-point moment; the conclusion is the `ω`-integral
of the `p`-th power of the cube mass, bounded by the integral of `bound` over
the `p`-fold cube. -/
theorem lintegral_ofReal_chaosCutoff_pow_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : ℕ) (hp : 1 ≤ p) (N : ℕ)
    (hpdelta : (p : ℝ) * M.delta ≤ 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (bound : (Fin p → SpatialCoordinates d) → ℝ)
    (hb : ∀ y : Fin p → SpatialCoordinates d,
      (∫ omega, ∏ k, fineDensity M N omega (y k)
        ∂(chaosSampleLaw M).toMeasure) ≤ bound y) :
    (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      ∂(chaosSampleLaw M).toMeasure) ≤
      ∫⁻ y : Fin p → SpatialCoordinates d, ENNReal.ofReal (bound y)
        ∂(Measure.pi fun _ : Fin p ↦
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hstep : (∫⁻ omega, ENNReal.ofReal (((chaosCutoff M N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p)
      ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ y : Fin p → SpatialCoordinates d, ∫⁻ omega,
        ENNReal.ofReal (∏ i, fineDensity M N omega (y i))
        ∂(chaosSampleLaw M).toMeasure
      ∂(Measure.pi fun _ : Fin p ↦
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [← lintegral_lintegral_swap_prod_fineDensity M N z r hr p]
    apply lintegral_congr
    intro omega
    exact ofReal_chaosCutoff_pow_eq_pi_lintegral M N omega z r hr p
  rw [hstep]
  refine lintegral_mono ?_
  intro y
  exact le_trans
    (le_of_eq (lintegral_ofReal_prod_fineDensity_eq_ofReal_integral M p hp N y hpdelta))
    (ENNReal.ofReal_le_ofReal (hb y))


theorem continuous_weightedFineDensity
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d) :
    Continuous (fun x ↦ Real.exp (H omega x) * fineDensity M N omega x) :=
  ((Real.continuous_exp.comp (H omega).continuous)).mul
    (continuous_fineDensity M N omega)

theorem weightedFineDensity_integrableOn_centeredCube
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x ↦ Real.exp (H omega x) * fineDensity M N omega x)
      (centeredCube z r hr : Set (SpatialCoordinates d)) volume := by
  have hc := continuous_weightedFineDensity M H N omega
  have h := (hc.locallyIntegrable (μ := (volume : Measure (SpatialCoordinates d)))
    ).integrableOn_isCompact (isCompact_closedBall z (r / 2))
  refine h.mono_set ?_
  rw [centeredCube_coe_eq_ball]
  exact Metric.ball_subset_closedBall

theorem integrable_prod_weightedFineDensity_pi
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    Integrable (fun y : Fin p → SpatialCoordinates d ↦
        ∏ i, (Real.exp (H omega (y i)) * fineDensity M N omega (y i)))
      (Measure.pi fun _ : Fin p ↦
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
  Integrable.fintype_prod
    (fun _ => weightedFineDensity_integrableOn_centeredCube M H N omega z r hr)

/-- Almost every point of the `p`-fold restricted product lies coordinatewise
in the cube. -/
theorem ae_pi_mem_centeredCube
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ) :
    ∀ᵐ y : Fin p → SpatialCoordinates d
      ∂(Measure.pi fun _ : Fin p ↦
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      ∀ i, y i ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hmeas : MeasurableSet
      (Set.univ.pi fun _ : Fin p ↦
        (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    MeasurableSet.univ_pi
      (fun _ => (centeredCube z r hr).isOpen.measurableSet)
  have hrw : (Measure.pi fun _ : Fin p ↦
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) =
      (Measure.pi fun _ : Fin p ↦ (volume : Measure (SpatialCoordinates d))).restrict
        (Set.univ.pi fun _ : Fin p ↦
          (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Measure.restrict_pi_pi _
      (fun _ : Fin p => (centeredCube z r hr : Set (SpatialCoordinates d)))).symm
  rw [hrw]
  filter_upwards [ae_restrict_mem hmeas] with y hy i
  exact hy i (Set.mem_univ i)

/-- Paper D:40–44: on a bounded region the weight contributes the single
factor `e^{p·sup_K H}`, pointwise in the environment. -/
theorem weightedChaosCutoff_pow_le_exp_mul_chaosCutoff_pow
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : ℕ)
    (hQK : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (K : Set (SpatialCoordinates d))) :
    ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p ≤
      Real.exp ((p : ℝ) * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖) *
        ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ^ p := by
  rw [weightedChaosCutoff_centeredCube_toReal_pow_eq_pi_integral M H N omega z r hr p,
    chaosCutoff_centeredCube_toReal_pow_eq_pi_integral M N omega z r hr p,
    ← integral_const_mul]
  refine integral_mono_ae (integrable_prod_weightedFineDensity_pi M H N omega z r hr p)
    ((integrable_prod_fineDensity_pi M N omega z r hr p).const_mul _) ?_
  filter_upwards [ae_pi_mem_centeredCube z r hr p] with y hy
  exact prod_weighted_le_exp_mul_prod_fineDensity M H N omega K p y
    (fun i => hQK (hy i))

end SubdiffusiveProcess
