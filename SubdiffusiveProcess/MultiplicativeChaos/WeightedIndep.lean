module

public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Probability.InfraredWholePrefixIndependence
public import SubdiffusiveProcess.Probability.FineDensityMartingale
public import SubdiffusiveProcess.Probability.WeightedFineDensityIntegrable
public import SubdiffusiveProcess.Probability.FineDensityMean
public import SubdiffusiveProcess.Main.FineDensity
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import SubdiffusiveProcess.Probability.WeightedChaosMass
public import SubdiffusiveProcess.Probability.WeightedChaosAdapted
public import SubdiffusiveProcess.Probability.WeightedFineDensityMartingale
public import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- Paper D:39–40: `H` is independent of the fine layers `j ≥ 0`, so the
weight `exp (H · x)` is independent of the fine density at `x`.  Extracted
from the proof of `weightedFineDensity_integrable`. -/
theorem indepFun_exp_H_fineDensity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ)
    (x : SpatialCoordinates d)
    (hH : InfraredCharacterization M H) :
    IndepFun (fun omega : BilateralField d => Real.exp (H omega x))
      (fun omega : BilateralField d => fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure := by
  classical
  let φ : C(SpatialCoordinates d, ℝ) → ℝ := fun f => Real.exp (f x)
  let ψ : ((j : Fin (N + 1)) → C(SpatialCoordinates d, ℝ)) → ℝ :=
    fun y => Real.exp (∑ j : Fin (N + 1), (y j) x -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hφmeas : Measurable φ :=
    (Real.continuous_exp.comp (continuous_eval_const x)).measurable
  have hψmeas : Measurable ψ := by
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j hj =>
        (continuous_eval_const x).measurable.comp (measurable_pi_apply j))
    · exact measurable_const
  have hindep := infraredCharacterization_indepFun_H_finePrefix M H N hH
  have hcomp := hindep.comp hφmeas hψmeas
  have hleft : (φ ∘ H) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d => Real.exp (H omega x)) := by
    filter_upwards [] with omega
    rfl
  have hright : (ψ ∘ (fun omega : BilateralField d =>
      fun j : Fin (N + 1) => omega (-(Int.ofNat j)))) =ᵐ[(chaosSampleLaw M).toMeasure]
      (fun omega : BilateralField d => fineDensity M N omega x) := by
    filter_upwards [] with omega
    show Real.exp (∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x -
        (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) = fineDensity M N omega x
    unfold fineDensity finePotential
    have hs : (∑ j : Fin (N + 1), (omega (-(Int.ofNat j))) x) =
        ∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) x := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (omega (-(Int.ofNat j))) x) (N + 1))
    rw [hs]
  exact hcomp.congr hleft hright


/-- Paper D:40–44: on a bounded region the weight `exp (H · x)` has all
exponential moments, uniformly for `x` in a compact set. -/
theorem integrable_exp_H_apply
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (K : Compacts (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (hxK : x ∈ (K : Set (SpatialCoordinates d))) :
    Integrable (fun omega : BilateralField d => Real.exp (H omega x))
      (chaosSampleLaw M).toMeasure := by
  have hExpMeas : Measurable (fun omega : BilateralField d => Real.exp (H omega x)) :=
    ((Real.continuous_exp.comp (continuous_eval_const x)).measurable).comp hH.1
  have hDomInt : Integrable (fun omega : BilateralField d =>
      Real.exp (1 * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure :=
    exists_compactExponentialMoment_of_infraredCharacterization hd M H hH K 1 (by norm_num)
  apply hDomInt.mono' hExpMeas.aestronglyMeasurable
  filter_upwards with omega
  have hb : |H omega x| ≤ ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖ := by
    have h0 := ((H omega).restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm
      ⟨x, hxK⟩
    have hb0 : ‖H omega x‖ ≤ ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖ := h0
    simpa only [Real.norm_eq_abs] using hb0
  have hfin : H omega x ≤ ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖ :=
    (abs_le.mp hb).2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr hfin

/-- Paper D:37–40: the layers have mean one, so the pointwise weighted mean is
the mean of the weight alone. -/
theorem integral_weightedFineDensity_eq_integral_exp
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ)
    (K : Compacts (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (hxK : x ∈ (K : Set (SpatialCoordinates d))) :
    (∫ omega, Real.exp (H omega x) * fineDensity M N omega x
        ∂(chaosSampleLaw M).toMeasure) =
      ∫ omega, Real.exp (H omega x) ∂(chaosSampleLaw M).toMeasure := by
  have hind := indepFun_exp_H_fineDensity M H N x hH
  have hExpInt := integrable_exp_H_apply hd M H hH K x hxK
  have hDenInt : Integrable (fun omega : BilateralField d => fineDensity M N omega x)
      (chaosSampleLaw M).toMeasure :=
    (conditionalFineFiltration_zero_eq_restrict_and_fineDensity_martingale M x).2.integrable N
  rw [hind.integral_fun_mul_eq_mul_integral hExpInt.aestronglyMeasurable
    hDenInt.aestronglyMeasurable, integral_fineDensity_chaosSampleLaw, mul_one]

/-- Paper D:41–42: `E e^{sup_K H} < ∞` bounds the pointwise weighted mean
uniformly over the compact set `K`. -/
theorem integral_weightedFineDensity_le
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ)
    (K : Compacts (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (hxK : x ∈ (K : Set (SpatialCoordinates d))) :
    (∫ omega, Real.exp (H omega x) * fineDensity M N omega x
        ∂(chaosSampleLaw M).toMeasure) ≤
      ∫ omega, Real.exp (1 * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure := by
  rw [integral_weightedFineDensity_eq_integral_exp hd M H hH N K x hxK]
  refine integral_mono (integrable_exp_H_apply hd M H hH K x hxK)
    (exists_compactExponentialMoment_of_infraredCharacterization hd M H hH K 1
      (by norm_num)) ?_
  intro omega
  have hb : |H omega x| ≤ ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖ := by
    have h0 := ((H omega).restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm
      ⟨x, hxK⟩
    have hb0 : ‖H omega x‖ ≤ ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖ := h0
    simpa only [Real.norm_eq_abs] using hb0
  have hfin : H omega x ≤ ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖ :=
    (abs_le.mp hb).2
  simp only [one_mul]
  exact Real.exp_le_exp.mpr hfin

/-- Joint measurability of the weighted density in the pair `(omega, x)`. -/
theorem stronglyMeasurable_weightedFineDensity_uncurry
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) :
    StronglyMeasurable (fun q : BilateralField d × SpatialCoordinates d =>
      Real.exp (H q.1 q.2) * fineDensity M N q.1 q.2) := by
  have hev : Continuous
      (fun p : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d => p.1 p.2) :=
    continuous_eval
  have hHj : Measurable (fun q : BilateralField d × SpatialCoordinates d => H q.1 q.2) :=
    hev.measurable.comp ((hH.comp measurable_fst).prodMk measurable_snd)
  have hfine : StronglyMeasurable
      (fun q : BilateralField d × SpatialCoordinates d =>
        fineDensity M N q.1 q.2) := by
    unfold fineDensity finePotential
    fun_prop
  exact (hHj.exp.stronglyMeasurable).mul hfine


/-- Joint integrability of the weighted density on `Omega × q`, the Fubini
input for the weighted cube-mass martingale (paper D:32–33, D:39–40). -/
theorem weightedFineDensity_joint_integrable
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Integrable (fun q : BilateralField d × SpatialCoordinates d =>
        Real.exp (H q.1 q.2) * fineDensity M N q.1 q.2)
      ((chaosSampleLaw M).toMeasure.prod
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  classical
  set P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQdef
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall z (r / 2), isCompact_closedBall _ _⟩
  have hQK : Q ⊆ (K : Set (SpatialCoordinates d)) := Metric.ball_subset_closedBall
  have hQmeas : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  have hQfin : volume Q ≠ ∞ := by
    rw [hQdef, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hjoint := stronglyMeasurable_weightedFineDensity_uncurry M H hH.1 N
  rw [integrable_prod_iff' hjoint.aestronglyMeasurable]
  refine ⟨ae_of_all _ (fun x => weightedFineDensity_integrable hd M H N x hH), ?_⟩
  have hmeasx : StronglyMeasurable (fun x : SpatialCoordinates d =>
      ∫ omega, ‖Real.exp (H omega x) * fineDensity M N omega x‖ ∂P) := by
    have hsw : StronglyMeasurable
        (fun q : SpatialCoordinates d × BilateralField d =>
          ‖Real.exp (H q.2 q.1) * fineDensity M N q.2 q.1‖) :=
      (hjoint.comp_measurable measurable_swap).norm
    exact hsw.integral_prod_right'
  have hfinm : IsFiniteMeasure (volume.restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hQfin
  set cK : ℝ :=
    ∫ omega, Real.exp (1 * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖) ∂P
    with hcKdef
  have hconst : Integrable (fun _ : SpatialCoordinates d => cK) (volume.restrict Q) :=
    integrable_const cK
  refine Integrable.mono' (g := fun _ : SpatialCoordinates d => cK)
    hconst hmeasx.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hQmeas] with x hx
  have hx' : x ∈ (K : Set (SpatialCoordinates d)) := hQK hx
  have h1 : (∫ omega, ‖Real.exp (H omega x) * fineDensity M N omega x‖ ∂P) =
      ∫ omega, Real.exp (H omega x) * fineDensity M N omega x ∂P := by
    apply integral_congr_ae
    filter_upwards with omega
    refine Real.norm_of_nonneg ?_
    unfold fineDensity
    positivity
  have h3 : 0 ≤ ∫ omega, ‖Real.exp (H omega x) * fineDensity M N omega x‖ ∂P :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg h3, h1]
  exact integral_weightedFineDensity_le hd M H hH N K x hx'

/-- The weighted cube mass is integrable at every cutoff. -/
theorem weightedChaosCutoff_centeredCube_integrable
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Integrable (fun omega : BilateralField d =>
        ((weightedChaosCutoff M H N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      (chaosSampleLaw M).toMeasure := by
  have hmass := (weightedFineDensity_joint_integrable hd M H hH N z r hr).integral_prod_left
  have heq : (fun omega : BilateralField d =>
      ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) =
      (fun omega : BilateralField d =>
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          Real.exp (H omega x) * fineDensity M N omega x) := by
    funext omega
    exact weightedChaosCutoff_centeredCube_toReal_eq_integral M H N omega z r hr
  rw [heq]
  exact hmass

/-- Paper D:32–33 (the weighted half): `mu_N(q)` is a nonnegative martingale
conditionally on `H`.  This is block (E) of the frozen
`chaos_positive_moments_and_martingales`. -/
theorem weightedChaosCutoff_centeredCube_martingale_nonnegative
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      Martingale
        (fun N omega ↦ ((weightedChaosCutoff M H N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        (conditionalFineFiltration H hH.1) (chaosSampleLaw M).toMeasure ∧
      (∀ N omega, 0 ≤ ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  classical
  intro z r hr
  refine ⟨?_, fun N omega => ENNReal.toReal_nonneg⟩
  set P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP
  have hadp := weightedChaosCutoff_centeredCube_adapted M H hH.1 z r hr
  have hint : ∀ N, Integrable (fun omega : BilateralField d =>
      ((weightedChaosCutoff M H N omega) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) P :=
    fun N => weightedChaosCutoff_centeredCube_integrable hd M H hH N z r hr
  refine martingale_of_setIntegral_eq_succ hadp.stronglyAdapted hint ?_
  intro N S hS
  have hprodS : ∀ m : ℕ, Integrable
      (fun q : BilateralField d × SpatialCoordinates d =>
        Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2)
      ((P.restrict S).prod (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
    intro m
    have hfull := weightedFineDensity_joint_integrable hd M H hH m z r hr
    have hQfull : Integrable
        (fun q : BilateralField d × SpatialCoordinates d =>
          Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2)
        ((P.prod volume).restrict (Set.univ ×ˢ (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
      rw [← Measure.prod_restrict (Set.univ : Set (BilateralField d)) (centeredCube z r hr : Set (SpatialCoordinates d)),
        Measure.restrict_univ]
      exact hfull
    have hSQ : Integrable
        (fun q : BilateralField d × SpatialCoordinates d =>
          Real.exp (H q.1 q.2) * fineDensity M m q.1 q.2)
        ((P.prod volume).restrict (S ×ˢ (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
      have hrestricted := hQfull.restrict (s := S ×ˢ (centeredCube z r hr : Set (SpatialCoordinates d)))
      rw [Measure.restrict_restrict_of_subset] at hrestricted
      · exact hrestricted
      · intro q hq
        exact ⟨Set.mem_univ _, hq.2⟩
    rw [Measure.prod_restrict S (centeredCube z r hr : Set (SpatialCoordinates d))]
    exact hSQ
  have hswap : ∀ m : ℕ,
      (∫ omega in S, ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), Real.exp (H omega x) * fineDensity M m omega x ∂volume ∂P) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ∫ omega in S, Real.exp (H omega x) * fineDensity M m omega x ∂P ∂volume := by
    intro m
    simpa using integral_integral_swap
      (f := fun omega x => Real.exp (H omega x) * fineDensity M m omega x) (hprodS m)
  have hpoint : ∀ x : SpatialCoordinates d,
      (∫ omega in S, Real.exp (H omega x) * fineDensity M N omega x ∂P) =
        ∫ omega in S, Real.exp (H omega x) * fineDensity M (N + 1) omega x ∂P := by
    intro x
    exact Martingale.setIntegral_eq
      (infraredWeightedFineDensity_martingale hd M H hH x) (Nat.le_succ N) hS
  have hspatial :
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ∫ omega in S, Real.exp (H omega x) * fineDensity M N omega x ∂P ∂volume) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ∫ omega in S,
          Real.exp (H omega x) * fineDensity M (N + 1) omega x ∂P ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    exact hpoint x
  simp_rw [weightedChaosCutoff_centeredCube_toReal_eq_integral M H N _ z r hr,
    weightedChaosCutoff_centeredCube_toReal_eq_integral M H (N + 1) _ z r hr]
  rw [hswap N, hspatial, ← hswap (N + 1)]

end SubdiffusiveProcess
