module

public import SubdiffusiveProcess.Section10.ChaosCarrier
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Probability.StrongLaw
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper
/-- Fix 9, L:278–282. Pool order `astra10r2_0927_root_eval_stationary`, independently accepted. -/
theorem aux_lim_measure_root_eval_stationary
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    (chaosRootFieldLaw M).toMeasure.map (fun f => f x) =
      (chaosRootFieldLaw M).toMeasure.map (fun f => f 0) := by
  let shift : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun y => y + x, continuous_id.add continuous_const⟩
  have hstat := gmc_zero_field_law_stationary M x
  have htrans : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f.comp shift) := hstat.measurable
  have hmap : Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp shift)
      (chaosRootFieldLaw M).toMeasure = (chaosRootFieldLaw M).toMeasure := hstat.map_eq
  have heval : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f 0) :=
    (ContinuousEvalConst.continuous_eval_const (0 : SpatialCoordinates d)).measurable
  calc
    Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f x) (chaosRootFieldLaw M).toMeasure
        = Measure.map ((fun f : C(SpatialCoordinates d, ℝ) => f 0) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp shift))
            (chaosRootFieldLaw M).toMeasure := by
          congr 1
          funext f
          simp only [Function.comp_apply, ContinuousMap.comp_apply]
          show f x = f ((0 : SpatialCoordinates d) + x)
          rw [zero_add]
    _ = Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f 0)
          (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp shift)
            (chaosRootFieldLaw M).toMeasure) := (Measure.map_map heval htrans).symm
    _ = Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f 0)
          (chaosRootFieldLaw M).toMeasure := by rw [hmap]


/-- Fix 9, L:278–282. Pool order `astra10r2_0927_root_eval_moments`, independently accepted. -/
theorem aux_lim_measure_root_eval_moments
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    Integrable (fun f => f x) (chaosRootFieldLaw M).toMeasure ∧
    (∫ f, f x ∂(chaosRootFieldLaw M).toMeasure) = 0 := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  have hmap : (chaosRootFieldLaw M).toMeasure =
      Measure.map forget (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := rfl
  have hmapμ : (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => ω 0)
        M.P.toMeasure := by
    rw [SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw,
      SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]
  constructor
  · rw [hmap, hmapμ]
    rw [integrable_map_measure
      ((continuous_eval_const x).measurable.aestronglyMeasurable)
      forget.continuous.measurable.aemeasurable]
    rw [integrable_map_measure
      (((continuous_eval_const x).comp forget.continuous).measurable.aestronglyMeasurable)
      (measurable_pi_apply 0).aemeasurable]
    exact M.G1.integrable x
  · rw [hmap, hmapμ]
    rw [integral_map forget.continuous.measurable.aemeasurable
      ((continuous_eval_const x).measurable.aestronglyMeasurable)]
    rw [integral_map (measurable_pi_apply 0).aemeasurable
      (((continuous_eval_const x).comp forget.continuous).measurable.aestronglyMeasurable)]
    exact M.G1.mean_zero x


/-- Fix 9, L:278–282. Pool order `astra10r2_0927_fine_eval_independent`, independently accepted. -/
theorem aux_lim_measure_fine_eval_independent
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    iIndepFun (fun n : ℕ => fun omega : BilateralField d => omega (-(n : ℤ)) x)
      (chaosSampleLaw M).toMeasure := by
  rw [SubdiffusiveProcess.chaosSampleLaw, SubdiffusiveProcess.commonScaleLaw,
    ProbabilityMeasure.coe_mk]
  have hbase :
      iIndepFun (fun (i : ℤ) (ω : ℤ → C(SpatialCoordinates d, ℝ)) => ω i)
        (Measure.infinitePi fun j : ℤ =>
          (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hcomp :
      iIndepFun (fun (i : ℤ) (ω : ℤ → C(SpatialCoordinates d, ℝ)) => (ω i) x)
        (Measure.infinitePi fun j : ℤ =>
          (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure) :=
    hbase.comp (fun _ => fun g : C(SpatialCoordinates d, ℝ) => g x)
      (fun _ => (ContinuousEvalConst.continuous_eval_const x).measurable)
  exact hcomp.precomp (g := fun n : ℕ => -(n : ℤ))
    (by intro a b h; exact Int.ofNat_inj.mp (neg_inj.mp h))


/-- Fix 9, L:278–282. Pool order `astra10r2_0927_negative_drift`, independently accepted. -/
theorem aux_lim_measure_negative_drift
    (a : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (ha : Tendsto (fun n => a n / ((n : ℝ) + 1)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.exp (a n - ((n : ℝ) + 1) * c)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => a n / ((n : ℝ) + 1) - c) atTop (𝓝 (0 - c)) :=
    ha.sub_const c
  have hneg : (0 - c) < 0 := by linarith
  have hf : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (a n / ((n : ℝ) + 1) - c))
      atTop atBot :=
    Filter.Tendsto.atTop_mul_neg hneg hf hshift
  have hinner : Tendsto (fun n : ℕ => a n - ((n : ℝ) + 1) * c) atTop atBot := by
    refine Tendsto.congr' ?_ hmain
    filter_upwards with n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  exact Real.tendsto_exp_atBot.comp hinner


theorem aux_lim_measure_scaled_eval_map
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (j : ℤ) (x : SpatialCoordinates d) :
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure.map (fun f => f x) =
      (chaosRootFieldLaw M).toMeasure.map (fun f => f ((3 : ℝ) ^ (-j) • x)) := by
  change Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f x)
    (Measure.map (layerScaling d j) (chaosRootFieldLaw M).toMeasure) = _
  rw [Measure.map_map (continuous_eval_const x).measurable
    (layerScaling d j).continuous.measurable]
  rfl

theorem aux_lim_measure_layer_eval_map
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (j : ℤ) (x : SpatialCoordinates d) :
    (chaosSampleLaw M).toMeasure.map (fun omega => omega j x) =
      (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure.map (fun f => f x) := by
  have hmap := Measure.map_map (μ := (chaosSampleLaw M).toMeasure)
    (g := fun f : C(SpatialCoordinates d, ℝ) => f x)
    (f := fun omega : BilateralField d => omega j)
    (continuous_eval_const x).measurable (measurable_pi_apply j)
  exact hmap.symm.trans (congrArg
    (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f x))
    (Measure.infinitePi_map_eval
      (fun k => (scaledLayerLaw d (chaosRootFieldLaw M) k).toMeasure) j))
/-- Fix 9, L:278–282. Pool order `astra10r2_0927_fine_eval_identDistrib`, independently accepted. -/
theorem aux_lim_measure_fine_eval_identDistrib
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (x : SpatialCoordinates d) :
    IdentDistrib (fun omega : BilateralField d => omega (-(n : ℤ)) x)
      (fun f : C(SpatialCoordinates d, ℝ) => f 0)
      (chaosSampleLaw M).toMeasure (chaosRootFieldLaw M).toMeasure := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((continuous_eval_const x).measurable.comp (measurable_pi_apply (-(n : ℤ)))).aemeasurable
  · exact (continuous_eval_const (0 : SpatialCoordinates d)).measurable.aemeasurable
  · calc
      Measure.map (fun omega : BilateralField d => omega (-(n : ℤ)) x) (chaosSampleLaw M).toMeasure
          = Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f x)
              (scaledLayerLaw d (chaosRootFieldLaw M) (-(n : ℤ))).toMeasure :=
            aux_lim_measure_layer_eval_map M (-(n : ℤ)) x
      _ = Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f ((3 : ℝ) ^ (-(-(n : ℤ))) • x))
              (chaosRootFieldLaw M).toMeasure :=
            aux_lim_measure_scaled_eval_map M (-(n : ℤ)) x
      _ = Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f 0)
              (chaosRootFieldLaw M).toMeasure :=
            aux_lim_measure_root_eval_stationary M ((3 : ℝ) ^ (-(-(n : ℤ))) • x)


/-- Fix 9, L:278–282. Pool order `astra10r2_0927_fine_average`, independently accepted. -/
theorem aux_lim_measure_fine_average
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun N => finePotential N omega x / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    obtain ⟨hint_root, hint0_root⟩ := aux_lim_measure_root_eval_moments M 0
    let X : ℕ → BilateralField d → ℝ := fun n omega => omega (-(n : ℤ)) x
    have hid : iIndepFun X (chaosSampleLaw M).toMeasure :=
      aux_lim_measure_fine_eval_independent M x
    have hident0 : IdentDistrib (X 0) (fun f : C(SpatialCoordinates d, ℝ) => f 0)
        (chaosSampleLaw M).toMeasure (chaosRootFieldLaw M).toMeasure :=
      aux_lim_measure_fine_eval_identDistrib M 0 x
    have hidentd : ∀ n, IdentDistrib (X n) (X 0)
        (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
      fun n => (aux_lim_measure_fine_eval_identDistrib M n x).trans hident0.symm
    have hint : Integrable (X 0) (chaosSampleLaw M).toMeasure := hident0.integrable_iff.mpr hint_root
    have hint0 : ∫ omega, X 0 omega ∂(chaosSampleLaw M).toMeasure = 0 :=
      hident0.integral_eq.trans hint0_root
    have hsl := strong_law_ae_real X hint (fun i j hij => hid.indepFun hij) hidentd
    rw [hint0] at hsl
    filter_upwards [hsl] with omega hom
    refine (hom.comp (tendsto_add_atTop_nat 1)).congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply, X, finePotential, Nat.cast_add, Nat.cast_one, Int.ofNat_eq_natCast]


/-- Fix 9, L:278–282: the actual fine density tends to zero at each fixed point. -/
theorem aux_lim_measure_fineDensity_zero
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (x : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun N => fineDensity M N omega x) atTop (𝓝 0) := by
  filter_upwards [aux_lim_measure_fine_average M x] with omega homega
  exact aux_lim_measure_negative_drift (fun N => finePotential N omega x)
    (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) M.G4.tauSq_pos homega

/-- Fix 9, L:278–282: ONE measurable density-zero carrier is Lebesgue conull. -/
theorem aux_lim_measure_fineDensity_zero_ae
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
        Tendsto (fun N => fineDensity M N omega x) atTop (𝓝 0) := by
  exact (Measure.ae_ae_comm (aux_lim_measure_measurable_zero_carrier M)).mpr
    (Filter.Eventually.of_forall (aux_lim_measure_fineDensity_zero M))

end Paper
