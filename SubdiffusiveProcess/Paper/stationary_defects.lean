module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Probability.FineDensityMean
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.MeasurabilityProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators Topology

namespace Paper

theorem aux_stationary_defects_negate_chaos_law
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Measure.map (fun omega : BilateralField d => fun j => -omega j)
        (chaosSampleLaw model).toMeasure =
      (chaosSampleLaw model).toMeasure := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
    chaosRootFieldLaw model
  let neg : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
    fun f => -f
  have hnegcont : Continuous neg := by
    exact continuous_neg
  have hν : Measure.map neg ν.toMeasure = ν.toMeasure := by
    change Measure.map neg
        (Measure.map forget
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure) = _
    have hzero := congrArg ProbabilityMeasure.toMeasure model.G3.negation
    change Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure = _ at hzero
    calc
      Measure.map neg (Measure.map forget
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure) =
          Measure.map (neg ∘ forget)
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure :=
        Measure.map_map hnegcont.measurable forget.continuous.measurable
      _ = Measure.map (forget ∘ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate)
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure := by
        congr 1
        funext g
        apply ContinuousMap.ext
        intro x
        change -(g.1.1 x) = (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate g).1.1 x
        exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate_apply g x).symm
      _ = Measure.map forget
            (Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure) :=
        (Measure.map_map forget.continuous.measurable
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_negate).symm
      _ = Measure.map forget
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw model.P).toMeasure := by
        rw [hzero]
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  have hlaw : ∀ j : ℤ, Measure.map neg (laws j) = laws j := by
    intro j
    change Measure.map neg
        (Measure.map (layerScaling d j) ν.toMeasure) = _
    calc
      Measure.map neg (Measure.map (layerScaling d j) ν.toMeasure) =
          Measure.map (neg ∘ layerScaling d j) ν.toMeasure :=
        Measure.map_map hnegcont.measurable
          (layerScaling d j).continuous.measurable
      _ = Measure.map (layerScaling d j ∘ neg) ν.toMeasure := by
        congr 1
      _ = Measure.map (layerScaling d j)
          (Measure.map neg ν.toMeasure) :=
        (Measure.map_map (layerScaling d j).continuous.measurable
          hnegcont.measurable).symm
      _ = laws j := by simpa [laws] using! congrArg (Measure.map (layerScaling d j)) hν
  have hmap :
      Measure.map (fun omega : BilateralField d => fun j => -omega j)
        (Measure.infinitePi laws) = Measure.infinitePi laws := by
    rw [Measure.infinitePi_map_pi
      (μ := laws) (f := fun _ f => neg f)
      (fun _ => hnegcont.measurable)]
    congr 1
    funext j
    exact hlaw j
  simpa [chaosSampleLaw, commonScaleLaw, ν, laws] using! hmap

theorem aux_stationary_defects_fineDensity_integrable
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (x : SpatialCoordinates d) :
    Integrable (fun omega : BilateralField d => fineDensity model N omega x)
      (chaosSampleLaw model).toMeasure := by
  apply integrable_of_integral_eq_one
  exact integral_fineDensity_chaosSampleLaw model N x

theorem aux_stationary_defects_invFineDensity_integrable
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (x : SpatialCoordinates d) :
    Integrable (fun omega : BilateralField d => (fineDensity model N omega x)⁻¹)
      (chaosSampleLaw model).toMeasure := by
  let negB : BilateralField d → BilateralField d :=
    fun omega j => -omega j
  have hnegB : Measurable negB := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply j).neg
  have hfd : Measurable (fun omega : BilateralField d => fineDensity model N omega x) := by
    unfold fineDensity finePotential
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j _ =>
        (continuous_eval_const x).measurable.comp (measurable_pi_apply _))
    · exact measurable_const
  have hpoint : ∀ omega : BilateralField d,
      (fineDensity model N omega x)⁻¹ =
        Real.exp (2 * (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          fineDensity model N (negB omega) x := by
    intro omega
    unfold fineDensity finePotential negB
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    simp only [Pi.neg_apply, ContinuousMap.neg_apply]
    rw [Finset.sum_neg_distrib]
    ring_nf
  have hcomp : Integrable
      (fun omega => fineDensity model N (negB omega) x)
      (chaosSampleLaw model).toMeasure := by
    let hmp : MeasurePreserving negB
        (chaosSampleLaw model).toMeasure
        (chaosSampleLaw model).toMeasure :=
      ⟨hnegB, aux_stationary_defects_negate_chaos_law model⟩
    simpa [Function.comp_def] using
      hmp.integrable_comp_of_integrable
        (aux_stationary_defects_fineDensity_integrable model N x)
  have hmul : Integrable
      (fun omega => Real.exp (2 * (N + 1 : ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        fineDensity model N (negB omega) x)
      (chaosSampleLaw model).toMeasure :=
    hcomp.const_mul _
  exact (hmul.congr (Filter.Eventually.of_forall fun omega => (hpoint omega).symm))

theorem aux_stationary_defects_invFineDensity_integral
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (x : SpatialCoordinates d) :
    ∫ omega, (fineDensity model N omega x)⁻¹
      ∂(chaosSampleLaw model).toMeasure =
      Real.exp (2 * (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
  let negB : BilateralField d → BilateralField d :=
    fun omega j => -omega j
  have hnegB : Measurable negB := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply j).neg
  have hfd : Measurable (fun omega : BilateralField d => fineDensity model N omega x) := by
    unfold fineDensity finePotential
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j _ =>
        (continuous_eval_const x).measurable.comp (measurable_pi_apply _))
    · exact measurable_const
  have hpoint : ∀ omega : BilateralField d,
      (fineDensity model N omega x)⁻¹ =
        Real.exp (2 * (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          fineDensity model N (negB omega) x := by
    intro omega
    unfold fineDensity finePotential negB
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    simp only [Pi.neg_apply, ContinuousMap.neg_apply]
    rw [Finset.sum_neg_distrib]
    ring_nf
  have hmp : MeasurePreserving negB
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure :=
    ⟨hnegB, aux_stationary_defects_negate_chaos_law model⟩
  calc
    ∫ omega, (fineDensity model N omega x)⁻¹
        ∂(chaosSampleLaw model).toMeasure =
        ∫ omega, Real.exp (2 * (N + 1 : ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          fineDensity model N (negB omega) x
          ∂(chaosSampleLaw model).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with omega
      exact hpoint omega
    _ = Real.exp (2 * (N + 1 : ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        ∫ omega, fineDensity model N (negB omega) x
          ∂(chaosSampleLaw model).toMeasure := by
      rw [integral_const_mul]
    _ = Real.exp (2 * (N + 1 : ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        ∫ omega, fineDensity model N omega x
          ∂Measure.map negB (chaosSampleLaw model).toMeasure := by
      congr 1
      symm
      exact integral_map hnegB.aemeasurable hfd.aestronglyMeasurable
    _ = Real.exp (2 * (N + 1 : ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        ∫ omega, fineDensity model N omega x
          ∂(chaosSampleLaw model).toMeasure := by
      rw [aux_stationary_defects_negate_chaos_law model]
    _ = Real.exp (2 * (N + 1 : ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
      rw [integral_fineDensity_chaosSampleLaw]
      ring

theorem aux_stationary_defects_fineDensity_average_integrable
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (U : Homogenization.Book.Ch02.Domain d) :
    Integrable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.average U (fun x => fineDensity model N omega x))
      (chaosSampleLaw model).toMeasure := by
  let hEvalSwap : Measurable
      (Function.uncurry fun x : SpatialCoordinates d =>
        fun f : C(SpatialCoordinates d, ℝ) => f x) := by
    exact measurable_uncurry_of_continuous_of_measurable
      (ι := SpatialCoordinates d) (α := C(SpatialCoordinates d, ℝ)) (β := ℝ)
      (fun f => f.continuous)
      (fun x => (continuous_eval_const x).measurable)
  let hEval : Measurable
      (fun z : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d => z.1 z.2) :=
    hEvalSwap.comp measurable_swap
  have hJoint : Measurable
      (fun z : BilateralField d × SpatialCoordinates d =>
        fineDensity model N z.1 z.2) := by
    unfold fineDensity finePotential
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j _ => by
        have hj : Measurable (fun z : BilateralField d × SpatialCoordinates d =>
            (z.1 (-(j : ℤ)), z.2)) := by
          exact ((measurable_pi_apply (-(j : ℤ))).comp measurable_fst).prodMk
            measurable_snd
        simpa [Function.comp_def] using! hEval.comp hj)
    · exact measurable_const
  have hProd : Integrable
      (fun z : BilateralField d × SpatialCoordinates d =>
        fineDensity model N z.1 z.2)
      ((chaosSampleLaw model).toMeasure.prod
        (volumeMeasureOn (U : Set (SpatialCoordinates d)))) := by
    apply (integrable_prod_iff' hJoint.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with x
      exact aux_stationary_defects_fineDensity_integrable model N x
    · have hnorm : (fun x : SpatialCoordinates d =>
          ∫ omega, ‖fineDensity model N omega x‖
            ∂(chaosSampleLaw model).toMeasure) = fun _ => (1 : ℝ) := by
        funext x
        rw [show (fun omega => ‖fineDensity model N omega x‖) =
            fun omega => fineDensity model N omega x by
          funext omega
          exact Real.norm_of_nonneg (Real.exp_pos _).le]
        exact integral_fineDensity_chaosSampleLaw model N x
      rw [hnorm]
      exact integrable_const 1
  have hscaled := hProd.integral_prod_left.const_mul
    (volume (U : Set (SpatialCoordinates d))).toReal⁻¹
  simpa [Homogenization.Book.Ch02.average] using! hscaled

theorem aux_stationary_defects_invFineDensity_average_integrable
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (U : Homogenization.Book.Ch02.Domain d) :
    Integrable (fun omega : BilateralField d =>
      Homogenization.Book.Ch02.average U
        (fun x => (fineDensity model N omega x)⁻¹))
      (chaosSampleLaw model).toMeasure := by
  let hEvalSwap : Measurable
      (Function.uncurry fun x : SpatialCoordinates d =>
        fun f : C(SpatialCoordinates d, ℝ) => f x) := by
    exact measurable_uncurry_of_continuous_of_measurable
      (ι := SpatialCoordinates d) (α := C(SpatialCoordinates d, ℝ)) (β := ℝ)
      (fun f => f.continuous)
      (fun x => (continuous_eval_const x).measurable)
  let hEval : Measurable
      (fun z : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d => z.1 z.2) :=
    hEvalSwap.comp measurable_swap
  have hfdJoint : Measurable
      (fun z : BilateralField d × SpatialCoordinates d =>
        fineDensity model N z.1 z.2) := by
    unfold fineDensity finePotential
    apply Measurable.exp
    apply Measurable.sub
    · exact Finset.measurable_fun_sum _ (fun j _ => by
        have hj : Measurable (fun z : BilateralField d × SpatialCoordinates d =>
            (z.1 (-(j : ℤ)), z.2)) := by
          exact ((measurable_pi_apply (-(j : ℤ))).comp measurable_fst).prodMk
            measurable_snd
        simpa [Function.comp_def] using! hEval.comp hj)
    · exact measurable_const
  have hJoint : Measurable
      (fun z : BilateralField d × SpatialCoordinates d =>
        (fineDensity model N z.1 z.2)⁻¹) := hfdJoint.inv
  have hProd : Integrable
      (fun z : BilateralField d × SpatialCoordinates d =>
        (fineDensity model N z.1 z.2)⁻¹)
      ((chaosSampleLaw model).toMeasure.prod
        (volumeMeasureOn (U : Set (SpatialCoordinates d)))) := by
    apply (integrable_prod_iff' hJoint.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with x
      exact aux_stationary_defects_invFineDensity_integrable model N x
    · have hnorm : (fun x : SpatialCoordinates d =>
          ∫ omega, ‖(fineDensity model N omega x)⁻¹‖
            ∂(chaosSampleLaw model).toMeasure) = fun _ =>
              Real.exp (2 * (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
        funext x
        rw [show (fun omega => ‖(fineDensity model N omega x)⁻¹‖) =
            fun omega => (fineDensity model N omega x)⁻¹ by
          funext omega
          exact Real.norm_of_nonneg (inv_nonneg.mpr (Real.exp_pos _).le)]
        exact aux_stationary_defects_invFineDensity_integral model N x
      rw [hnorm]
      exact integrable_const _
  have hscaled := hProd.integral_prod_left.const_mul
    (volume (U : Set (SpatialCoordinates d))).toReal⁻¹
  simpa [Homogenization.Book.Ch02.average] using! hscaled

theorem aux_stationary_defects_measurable_blockEnergyAverage
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → Homogenization.Vec d → ℝ)
    (hF : Measurable (fun z : Ω × Homogenization.Vec d => F z.1 z.2))
    (hFpos : ∀ omega x, 0 < F omega x)
    (U : Homogenization.Book.Ch02.Domain d) (X : Homogenization.BlockState d)
    (hX : Homogenization.MemBlockL2
      (U : Set (Homogenization.Vec d)) X.eval) :
    Measurable (fun omega =>
      Homogenization.blockEnergyAverage (U : Set (Homogenization.Vec d))
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) X) := by
  have hXL2 : Homogenization.MemBlockL2 (U : Set (Homogenization.Vec d)) X.eval :=
    hX
  have hPotentialL2 : Homogenization.MemVectorL2
      (U : Set (Homogenization.Vec d)) X.potential := by
    simpa [Homogenization.BlockState.eval] using
      Homogenization.memVectorL2_fst_of_memBlockL2
        (U := (U : Set (Homogenization.Vec d))) hXL2
  have hFluxL2 : Homogenization.MemVectorL2
      (U : Set (Homogenization.Vec d)) X.flux := by
    simpa [Homogenization.BlockState.eval] using
      Homogenization.memVectorL2_snd_of_memBlockL2
        (U := (U : Set (Homogenization.Vec d))) hXL2
  let f : Homogenization.Vec d → Homogenization.Vec d :=
    hPotentialL2.aestronglyMeasurable.mk X.potential
  let g : Homogenization.Vec d → Homogenization.Vec d :=
    hFluxL2.aestronglyMeasurable.mk X.flux
  have hf : Measurable f := hPotentialL2.aestronglyMeasurable.measurable_mk
  have hg : Measurable g := hFluxL2.aestronglyMeasurable.measurable_mk
  have measurable_vecDot_self {v : Ω × Homogenization.Vec d → Homogenization.Vec d}
      (hv : Measurable v) :
      Measurable (fun z => Homogenization.vecDot (v z) (v z)) := by
    simp only [Homogenization.vecDot]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hv)
  have hPotential : Measurable
      (fun z : Ω × Homogenization.Vec d =>
        F z.1 z.2 * Homogenization.vecDot (f z.2) (f z.2)) := by
    exact hF.mul (measurable_vecDot_self (hf.comp measurable_snd))
  have hFlux : Measurable
      (fun z : Ω × Homogenization.Vec d =>
        (F z.1 z.2)⁻¹ * Homogenization.vecDot (g z.2) (g z.2)) := by
    exact hF.inv.mul (measurable_vecDot_self (hg.comp measurable_snd))
  have hIntegral : StronglyMeasurable
      (fun omega : Ω =>
        ∫ x, (1 / 2 : ℝ) *
          (F omega x * Homogenization.vecDot (f x) (f x) +
            (F omega x)⁻¹ * Homogenization.vecDot (g x) (g x))
          ∂volumeMeasureOn (U : Set (Homogenization.Vec d))) :=
    (measurable_const.mul (hPotential.add hFlux)).stronglyMeasurable.integral_prod_right'
  have hEq :
      (fun omega : Ω =>
        Homogenization.blockEnergyAverage (U : Set (Homogenization.Vec d))
          (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) X) =
      fun omega => (volume (U : Set (Homogenization.Vec d))).toReal⁻¹ *
        ∫ x, (1 / 2 : ℝ) *
          (F omega x * Homogenization.vecDot (f x) (f x) +
            (F omega x)⁻¹ * Homogenization.vecDot (g x) (g x))
          ∂volumeMeasureOn (U : Set (Homogenization.Vec d)) := by
    funext omega
    rw [Homogenization.blockEnergyAverage, Homogenization.volumeAverage]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hPotentialL2.aestronglyMeasurable.ae_eq_mk,
      hFluxL2.aestronglyMeasurable.ae_eq_mk] with x hfx hgx
    simpa [f, g, hfx, hgx] using
      SubdiffusiveProcess.CoarseGrainingVocab.blockEnergyDensity_scalarCoeffField_of_pos
        (F omega) (hFpos omega) X x
  rw [hEq]
  exact measurable_const.mul hIntegral.measurable

theorem aux_stationary_defects_scalar_elliptic
    {d : ℕ} {Ω : Type*} (F : Ω → Homogenization.Vec d → ℝ)
    (hFcont : ∀ omega, Continuous (F omega))
    (hFpos : ∀ omega x, 0 < F omega x)
    (U : Homogenization.Book.Ch02.Domain d) :
    ∀ omega, ∃ lam Lam : ℝ,
      Homogenization.IsEllipticFieldOn lam Lam (U : Set (Homogenization.Vec d))
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) := by
  intro omega
  let a : Homogenization.Vec d → ℝ := F omega
  have hcompact : IsCompact (closure (U : Set (Homogenization.Vec d))) :=
    U.isBoundedDomain.isBounded.isCompact_closure
  have hnonempty : (closure (U : Set (Homogenization.Vec d))).Nonempty :=
    U.nonempty.closure
  obtain ⟨xMin, hxMin, hMin⟩ :=
    hcompact.exists_isMinOn hnonempty (hFcont omega).continuousOn
  obtain ⟨xMax, hxMax, hMax⟩ :=
    hcompact.exists_isMaxOn hnonempty (hFcont omega).continuousOn
  refine ⟨a xMin, a xMax, ?_⟩
  constructor
  · rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    have hEntry : Measurable
        (fun x : Homogenization.Vec d =>
          SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField a x i j) := by
      have hMatrix : Continuous
          (fun x : Homogenization.Vec d =>
            SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField a x) :=
        (hFcont omega).smul continuous_const
      exact ((continuous_apply j).comp ((continuous_apply i).comp hMatrix)).measurable
    exact hEntry.piecewise U.measurableSet measurable_const
  · intro x hx
    exact (Homogenization.isEllipticMatrix_scalarMatrix (hFpos omega x)).mono
      (hFpos omega xMin) (hMin (subset_closure hx)) (hMax (subset_closure hx))

theorem aux_stationary_defects_mu_eq
    {d : ℕ} [NeZero d]
    (U : Homogenization.Book.Ch02.Domain d)
    (a : Homogenization.CoeffField d)
    {lam Lam : ℝ}
    (hEll : Homogenization.IsEllipticFieldOn lam Lam
      (U : Set (Homogenization.Vec d)) a)
    (P : Homogenization.BlockVec d) :
    let R :=
      Homogenization.potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
        (Homogenization.PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
          U.isDomain)
    let Rc := R.toMuCorrectionSpaceRecoveryData
    let system := R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U)
    Homogenization.Mu (U : Set (Homogenization.Vec d)) P a =
      (system.toMuOperatorRealization.toMuHilbertRealization
        Rc.toMuCorrectionSpaceData).muCandidate P := by
  dsimp only
  let Uset : Set (Homogenization.Vec d) := (U : Set (Homogenization.Vec d))
  let R : Homogenization.PotentialSolenoidalL2RecoveryData Uset :=
    Homogenization.potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
      (Homogenization.PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
        U.isDomain)
  let Rc : Homogenization.MuCorrectionSpaceRecoveryData Uset :=
    R.toMuCorrectionSpaceRecoveryData
  have hvol : 0 < (volume Uset).toReal := by
    simpa [Uset] using! Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  let system : Homogenization.MuOperatorSystemData Uset a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn (by simpa [Uset] using! hEll) hvol
  have hCandidateLe : ∀ X : Homogenization.BlockState d,
      Homogenization.IsBlockMuAdmissible Uset P X →
        (system.toMuOperatorRealization.toMuHilbertRealization
          Rc.toMuCorrectionSpaceData).muCandidate P ≤
          Homogenization.blockEnergyAverage Uset a X := by
    intro X hX
    let Y : Homogenization.CorrectionFieldData Uset :=
      hX.toCorrectionFieldDataOfAdmissible
    have hXmem : Homogenization.MemBlockL2 Uset X.eval := hX.memBlockL2_eval
    have hcorr : Y.toHilbertBlockL2 ∈
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace :=
      R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
        Y.potential_memL2 Y.flux_memL2 Y.isPotentialZeroTrace
        Y.isSolenoidalZeroNormalTrace
    have hsplit :
        Homogenization.toHilbertBlockL2OfBlockField (U := Uset) hXmem =
          Homogenization.blockVecToHilbertBlockL2Const (U := Uset) P +
            Y.toHilbertBlockL2 := by
      simpa [Y] using
        hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    have hcorr_mem :
        Homogenization.toHilbertBlockL2OfBlockField (U := Uset) hXmem -
            (system.toMuOperatorRealization.toMuHilbertRealization
              Rc.toMuCorrectionSpaceData).constantField P ∈
          (system.toMuOperatorRealization.toMuHilbertRealization
            Rc.toMuCorrectionSpaceData).correctionSpace.correctionSpace := by
      rw [hsplit]
      simpa [Rc, R, system,
        Homogenization.PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        Homogenization.MuOperatorSystemData.toMuHilbertRealization,
        Homogenization.MuOperatorRealization.toMuHilbertRealization,
        Homogenization.MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hcorr
    have hMin :
        (system.toMuOperatorRealization.toMuHilbertRealization
          Rc.toMuCorrectionSpaceData).muCandidate P ≤
          Homogenization.quadraticEnergy
            (Homogenization.energyBilinOfOperator
              system.toMuOperatorRealization.operator)
            (Homogenization.toHilbertBlockL2OfBlockField (U := Uset) hXmem) := by
      simpa [Rc, R, system,
        Homogenization.PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        Homogenization.MuOperatorSystemData.toMuHilbertRealization,
        Homogenization.MuOperatorRealization.toMuHilbertRealization,
        Homogenization.MuHilbertRealization.ofOperator] using
        (system.toMuOperatorRealization.toMuHilbertRealization
          Rc.toMuCorrectionSpaceData).muCandidate_le_quadraticEnergy P
          (Homogenization.toHilbertBlockL2OfBlockField (U := Uset) hXmem) hcorr_mem
    calc
      (system.toMuOperatorRealization.toMuHilbertRealization
        Rc.toMuCorrectionSpaceData).muCandidate P ≤
          Homogenization.quadraticEnergy
            (Homogenization.energyBilinOfOperator
              system.toMuOperatorRealization.operator)
            (Homogenization.toHilbertBlockL2OfBlockField (U := Uset) hXmem) := hMin
      _ = Homogenization.blockEnergyAverage Uset a X :=
        system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState hXmem
  have hrecEnergy :
      Homogenization.blockEnergyAverage Uset a
          (Rc.recoveredField system P) =
        (system.toMuOperatorRealization.toMuHilbertRealization
          Rc.toMuCorrectionSpaceData).muCandidate P := by
    exact Rc.blockEnergyAverage_affineField_correctionPart_eq_muCandidate system P
  have hBddBelow : BddBelow (Homogenization.muValueSet Uset P a) := by
    refine ⟨Homogenization.vecDot P.1 P.2, ?_⟩
    intro value hvalue
    rcases hvalue with ⟨X, hX, rfl⟩
    exact hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
      (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn hEll) hEll
      (by simpa [sub_eq_add_neg] using
        (Homogenization.IsPotentialZeroTraceOn.integral_eq_zero
          hX.isPotentialZeroTrace))
      (by simpa [sub_eq_add_neg] using
        (Homogenization.IsSolenoidalZeroNormalTraceOn.integral_eq_zero
          U.isDomain.isSobolevRegularDomain hX.isSolenoidalZeroNormalTrace))
      hvol.ne'
  have hUpper :
      Homogenization.Mu Uset P a ≤
          (system.toMuOperatorRealization.toMuHilbertRealization
            Rc.toMuCorrectionSpaceData).muCandidate P := by
    let Xrec : Homogenization.BlockState d := Rc.recoveredField system P
    have hAdm : Homogenization.IsBlockMuAdmissible Uset P Xrec := by
      simpa [Xrec] using! Rc.recoveredField_admissible system P
    calc
      Homogenization.Mu Uset P a ≤ Homogenization.blockEnergyAverage Uset a Xrec :=
        csInf_le hBddBelow (Homogenization.muValueSet_mem hAdm)
      _ = (system.toMuOperatorRealization.toMuHilbertRealization
          Rc.toMuCorrectionSpaceData).muCandidate P := hrecEnergy
  have hLower :
      (system.toMuOperatorRealization.toMuHilbertRealization
        Rc.toMuCorrectionSpaceData).muCandidate P ≤
        Homogenization.Mu Uset P a := by
    apply Homogenization.le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    exact hCandidateLe X hX
  have hmain :
      Homogenization.Mu Uset P a =
          (system.toMuOperatorRealization.toMuHilbertRealization
            Rc.toMuCorrectionSpaceData).muCandidate P :=
    le_antisymm hUpper hLower
  simpa [Uset, R, Rc, system,
    Homogenization.PotentialSolenoidalL2RecoveryData.toMuHilbertRealization] using! hmain

theorem aux_stationary_defects_measurable_mu
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → Homogenization.Vec d → ℝ)
    (hF : Measurable (fun z : Ω × Homogenization.Vec d => F z.1 z.2))
    (hFcont : ∀ omega, Continuous (F omega))
    (hFpos : ∀ omega x, 0 < F omega x)
    (U : Homogenization.Book.Ch02.Domain d)
    (P : Homogenization.BlockVec d) :
    Measurable (fun omega =>
      Homogenization.Mu (U : Set (Homogenization.Vec d)) P
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega))) := by
  let Uset : Set (Homogenization.Vec d) := (U : Set (Homogenization.Vec d))
  let R : Homogenization.PotentialSolenoidalL2RecoveryData Uset :=
    Homogenization.potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
      (Homogenization.PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
        U.isDomain)
  let Rc : Homogenization.MuCorrectionSpaceRecoveryData Uset :=
    R.toMuCorrectionSpaceRecoveryData
  have hvol : 0 < (volume Uset).toReal := by
    simpa [Uset] using! Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hEllExists := aux_stationary_defects_scalar_elliptic F hFcont hFpos U
  let lam : Ω → ℝ := fun omega => Classical.choose (hEllExists omega)
  have hLam : ∀ omega, ∃ Lam : ℝ,
      Homogenization.IsEllipticFieldOn (lam omega) Lam Uset
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) := by
    intro omega
    simpa [lam, Uset] using! Classical.choose_spec (hEllExists omega)
  let Lam : Ω → ℝ := fun omega => Classical.choose (hLam omega)
  have hEll : ∀ omega,
      Homogenization.IsEllipticFieldOn (lam omega) (Lam omega) Uset
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) := by
    intro omega
    exact Classical.choose_spec (hLam omega)
  let system : ∀ omega : Ω,
      Homogenization.MuOperatorSystemData Uset
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) := fun omega =>
    R.toMuOperatorSystemDataOfIsEllipticFieldOn (hEll omega) hvol
  have hMuEq : ∀ omega : Ω, ∀ Q : Homogenization.BlockVec d,
      Homogenization.Mu Uset Q
          (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega)) =
        ((system omega).toMuOperatorRealization.toMuHilbertRealization
          Rc.toMuCorrectionSpaceData).muCandidate Q := by
    intro omega Q
    simpa [Rc, R, Uset, system] using
      aux_stationary_defects_mu_eq U
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega))
        (by simpa [Uset] using! hEll omega) Q
  letI : TopologicalSpace.SeparableSpace ↥Rc.correctionSpace := by
    letI : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
    letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    dsimp [Rc, R]
    infer_instance
  apply Homogenization.measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq
    (A := fun omega => SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (F omega))
    Rc system hMuEq P
  intro n
  exact aux_stationary_defects_measurable_blockEnergyAverage F hF hFpos U
    (Rc.affineField P (TopologicalSpace.denseSeq ↥Rc.correctionSpace n))
    (Rc.affineField_memBlockL2 P (TopologicalSpace.denseSeq ↥Rc.correctionSpace n))

theorem aux_stationary_defects_scalar_coefficient_identity
    {d : ℕ}
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    ((Real.exp (((N : ℝ) + 1) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
      Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
        (1 : Homogenization.Mat d) =
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField
        (fun y => (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          fineDensity model N omega y) x := by
  ext i j
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
    Homogenization.scalarMatrix, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    unfold fineDensity finePotential
    rw [Real.exp_sub]
    field_simp [ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)]
    congr 1
  · simp [hij]

theorem aux_stationary_defects_average_ratio
    {d : ℕ}
    (F : BilateralField d → Homogenization.Vec d → ℝ)
    (hFcont : ∀ omega, Continuous (F omega))
    (hFpos : ∀ omega x, 0 < F omega x)
    (U : Homogenization.Book.Ch02.Domain d) (alpha : ℝ) (halpha : 0 < alpha) :
    ∀ omega, Homogenization.Book.Ch02.average U
        (fun x => F omega x / alpha + alpha / F omega x - 2) =
      alpha⁻¹ * Homogenization.Book.Ch02.average U (F omega) +
        alpha * Homogenization.Book.Ch02.average U
          (fun x => (F omega x)⁻¹) - 2 := by
  intro omega
  let W : Set (Homogenization.Vec d) := (U : Set (Homogenization.Vec d))
  have hcompact : IsCompact (closure W) := U.isBoundedDomain.isBounded.isCompact_closure
  have hsub : W ⊆ closure W := subset_closure
  have hFint : IntegrableOn (F omega) W :=
    (ContinuousOn.integrableOn_compact hcompact (hFcont omega).continuousOn).mono_set hsub
  have hInvCont : Continuous (fun x => (F omega x)⁻¹) :=
    (hFcont omega).inv₀ (fun x => (hFpos omega x).ne')
  have hInvint : IntegrableOn (fun x => (F omega x)⁻¹) W :=
    (ContinuousOn.integrableOn_compact hcompact hInvCont.continuousOn).mono_set hsub
  have hDiv : IntegrableOn (fun x => F omega x / alpha) W := by
    simpa [div_eq_mul_inv, mul_comm] using! hFint.const_mul alpha⁻¹
  have hInvDiv : IntegrableOn (fun x => alpha / F omega x) W := by
    simpa [div_eq_mul_inv, mul_comm] using! hInvint.const_mul alpha
  have hWfinite : volume W ≠ ⊤ := by
    exact ne_of_lt (by simpa [W] using! U.isDomain.volume_lt_top)
  have hTwo : IntegrableOn (fun _ : Homogenization.Vec d => (2 : ℝ)) W :=
    integrableOn_const hWfinite
  have hSum : IntegrableOn
      (fun x => F omega x / alpha + alpha / F omega x) W := hDiv.add hInvDiv
  have hInt :
      ∫ x in W, F omega x / alpha + alpha / F omega x - 2 ∂volume =
        (alpha⁻¹) * (∫ x in W, F omega x ∂volume) +
          alpha * (∫ x in W, (F omega x)⁻¹ ∂volume) -
            (2 : ℝ) * (volume W).toReal := by
    rw [integral_sub hSum hTwo, integral_add hDiv hInvDiv]
    have hdivfun : (fun x => F omega x / alpha) =
        (fun x => alpha⁻¹ * F omega x) := by
      funext x
      ring
    have hinvfun : (fun x => alpha / F omega x) =
        (fun x => alpha * (F omega x)⁻¹) := by
      funext x
      ring
    rw [hdivfun, hinvfun, integral_const_mul, integral_const_mul]
    have htwoint : ∫ x in W, (2 : ℝ) ∂volume =
        (2 : ℝ) * (volume W).toReal := by
      rw [integral_const]
      simp only [smul_eq_mul]
      change ((volume.restrict W) Set.univ).toReal * 2 =
        2 * (volume W).toReal
      rw [Measure.restrict_apply_univ]
      ring
    rw [htwoint]
  unfold Homogenization.Book.Ch02.average
  rw [hInt]
  have hvol : 0 < (volume W).toReal := by
    simpa [W] using! Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hne : (volume W).toReal ≠ 0 := hvol.ne'
  have hneU : (volume (U : Set (Homogenization.Vec d))).toReal ≠ 0 := by
    simpa [W] using! hne
  simp only [W, Measure.real]
  field_simp [hneU]



theorem stationary_defects
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (U : ℕ → Homogenization.Book.Ch02.Domain d)
    (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)))
    (a0 : (N k : ℕ) → BilateralField d → Homogenization.Book.Ch02.CoeffOn (U k))
    (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
      ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
        (1 : Homogenization.Mat d))
    (hJ : Paper.in_J d) :
    let Pm := fun N k omega => Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega)
    let Rm := fun N k omega => Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega)
    let f := fun N k => (1 / 2 : ℝ) *
      (∫ omega, Matrix.trace (Pm N k omega + Rm N k omega -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ)) ∂(chaosSampleLaw model).toMeasure)
    ∀ N k, f N k = ∑ j : Fin d,
      ∫ omega, Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
        (Pi.single j 1) (Pi.single j 1) ∂(chaosSampleLaw model).toMeasure := by
  dsimp only
  intro N k
  have hsym : ∀ omega : BilateralField d,
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric (a0 N k omega) := by
    intro omega
    rw [Homogenization.Book.Ch02.CoeffOn.IsSymmetric]
    filter_upwards [] with x
    rw [ha0 N k omega x]
    exact Homogenization.scalarMatrix_isSymm _
  have hquad : ∀ (A : Homogenization.Mat d) (j : Fin d),
      Homogenization.vecDot (Pi.single j 1)
          (Homogenization.matVecMul A (Pi.single j 1)) = A j j := by
    intro A j
    unfold Homogenization.vecDot Homogenization.matVecMul
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, one_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _hi hij
        simp [hij]
      · simp
    · intro i _hi hij
      simp [Pi.single_apply, hij]
    · simp
  have hresp : ∀ (omega : BilateralField d) (j : Fin d),
      Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1) =
        (1 / 2 : ℝ) *
            Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) j j +
          (1 / 2 : ℝ) *
            Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) j j - 1 := by
    intro omega j
    have h := hJ.responseJ_split (U k) (a0 N k omega) (hsym omega)
      (Pi.single j 1) (Pi.single j 1)
    rw [hquad, hquad] at h
    have hdot : Homogenization.vecDot (Pi.single j 1) (Pi.single j 1) = 1 := by
      unfold Homogenization.vecDot
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _hi hij
        simp [Pi.single_apply, hij]
      · simp
    rw [hdot] at h
    exact h
  have hpoint : ∀ omega : BilateralField d,
      (1 / 2 : ℝ) * Matrix.trace
        (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) +
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) -
          2 • (1 : Matrix (Fin d) (Fin d) ℝ)) =
        ∑ j : Fin d,
          Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
            (Pi.single j 1) (Pi.single j 1) := by
    intro omega
    calc
      (1 / 2 : ℝ) * Matrix.trace
          (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) +
            Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) -
            2 • (1 : Matrix (Fin d) (Fin d) ℝ)) =
          (1 / 2 : ℝ) * ∑ j : Fin d,
            (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) j j +
              Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) j j - 2) := by
        congr 1
        unfold Matrix.trace
        apply Finset.sum_congr rfl
        intro j hj
        simp [Matrix.add_apply, Matrix.sub_apply, two_smul, Matrix.one_apply_eq]
        norm_num
      _ = ∑ j : Fin d,
          ((1 / 2 : ℝ) *
              Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) j j +
            (1 / 2 : ℝ) *
              Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) j j - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j : Fin d,
          Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
            (Pi.single j 1) (Pi.single j 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hresp omega j]
  have hint : ∀ j : Fin d, Integrable
      (fun omega => Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
        (Pi.single j 1) (Pi.single j 1))
      (chaosSampleLaw model).toMeasure := by
    letI : NeZero d := ⟨by omega⟩
    intro j
    let alpha : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
    have halpha : 0 < alpha := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
    let F : BilateralField d → Homogenization.Vec d → ℝ :=
      fun omega x => fineDensity model N omega x
    let B : BilateralField d → Homogenization.Vec d → ℝ :=
      fun omega x => alpha⁻¹ * F omega x
    have hFjoint : Measurable
        (fun z : BilateralField d × Homogenization.Vec d => F z.1 z.2) := by
      dsimp [F]
      unfold fineDensity finePotential
      apply Measurable.exp
      apply Measurable.sub
      · exact Finset.measurable_fun_sum _ (fun m _ => by
          have hm : Measurable (fun z : BilateralField d × Homogenization.Vec d =>
              (z.1 (-(m : ℤ)), z.2)) := by
            exact ((measurable_pi_apply (-(m : ℤ))).comp measurable_fst).prodMk
              measurable_snd
          have heval : Measurable
              (fun z : C(SpatialCoordinates d, ℝ) × SpatialCoordinates d => z.1 z.2) := by
            exact (measurable_uncurry_of_continuous_of_measurable
              (ι := SpatialCoordinates d) (α := C(SpatialCoordinates d, ℝ)) (β := ℝ)
              (fun f => f.continuous) (fun x => (continuous_eval_const x).measurable)).comp
              measurable_swap
          exact heval.comp hm)
      · exact measurable_const
    have hBjoint : Measurable
        (fun z : BilateralField d × Homogenization.Vec d => B z.1 z.2) := by
      simpa [B] using! measurable_const.mul hFjoint
    have hFcont : ∀ omega : BilateralField d, Continuous (F omega) := by
      intro omega
      dsimp [F]
      unfold fineDensity finePotential
      fun_prop
    have hBcont : ∀ omega : BilateralField d, Continuous (B omega) := by
      intro omega
      exact continuous_const.mul (hFcont omega)
    have hFpos : ∀ omega : BilateralField d, ∀ x, 0 < F omega x := by
      intro omega x
      dsimp [F]
      unfold fineDensity
      positivity
    have hBpos : ∀ omega : BilateralField d, ∀ x, 0 < B omega x := by
      intro omega x
      exact mul_pos (inv_pos.mpr halpha) (hFpos omega x)
    have hMu := aux_stationary_defects_measurable_mu B hBjoint hBcont hBpos
      (U k) ((-Pi.single j 1), Pi.single j 1)
    have hcoeff : ∀ omega : BilateralField d, ∀ x : SpatialCoordinates d,
        (a0 N k omega).toCoeffField x =
          SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (B omega) x := by
      intro omega x
      rw [ha0 N k omega x]
      simpa [B, F, alpha] using
        aux_stationary_defects_scalar_coefficient_identity model N omega x
    have hrespEq :
        (fun omega : BilateralField d =>
          Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
            (Pi.single j 1) (Pi.single j 1)) =
        (fun omega =>
          Homogenization.Mu (U k : Set (Homogenization.Vec d))
            (-Pi.single j 1, Pi.single j 1)
            (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (B omega)) -
            Homogenization.vecDot (Pi.single j 1) (Pi.single j 1)) := by
      funext omega
      calc
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
              (Pi.single j 1) (Pi.single j 1) =
            Homogenization.Book.Ch02.doubledMu (U k) (a0 N k omega)
              (-Pi.single j 1, Pi.single j 1) -
              Homogenization.vecDot (Pi.single j 1) (Pi.single j 1) := by
          exact Homogenization.Book.Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot
            (U k) (a0 N k omega) (Pi.single j 1) (Pi.single j 1)
        _ = Homogenization.Mu (U k : Set (Homogenization.Vec d))
              (-Pi.single j 1, Pi.single j 1) (a0 N k omega).toCoeffField -
              Homogenization.vecDot (Pi.single j 1) (Pi.single j 1) := by
          rw [Homogenization.Book.Ch02.doubledMu_eq_Mu]
        _ = Homogenization.Mu (U k : Set (Homogenization.Vec d))
              (-Pi.single j 1, Pi.single j 1)
              (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (B omega)) -
              Homogenization.vecDot (Pi.single j 1) (Pi.single j 1) := by
          congr 2
          funext x
          exact hcoeff omega x
    have hrespmeas : Measurable (fun omega : BilateralField d =>
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1)) := by
      rw [hrespEq]
      exact hMu.sub measurable_const
    let avgF : BilateralField d → ℝ := fun omega =>
      Homogenization.Book.Ch02.average (U k) (F omega)
    let avgInv : BilateralField d → ℝ := fun omega =>
      Homogenization.Book.Ch02.average (U k) (fun x => (F omega x)⁻¹)
    have havgF : Integrable avgF (chaosSampleLaw model).toMeasure := by
      simpa [avgF, F] using
        aux_stationary_defects_fineDensity_average_integrable model N (U k)
    have havgInv : Integrable avgInv (chaosSampleLaw model).toMeasure := by
      simpa [avgInv, F] using
        aux_stationary_defects_invFineDensity_average_integrable model N (U k)
    have hratio : ∀ omega,
        Homogenization.Book.Ch02.average (U k)
            (fun x => F omega x / alpha + alpha / F omega x - 2) =
          alpha⁻¹ * avgF omega + alpha * avgInv omega - 2 := by
      intro omega
      exact aux_stationary_defects_average_ratio F hFcont hFpos (U k) alpha halpha omega
    have hmajor : Integrable
        (fun omega => (1 / 2 : ℝ) *
          (alpha⁻¹ * avgF omega + alpha * avgInv omega - 2))
        (chaosSampleLaw model).toMeasure := by
      have hinner : Integrable
          (fun omega => alpha⁻¹ * avgF omega + alpha * avgInv omega - 2)
          (chaosSampleLaw model).toMeasure := by
        exact (havgF.const_mul alpha⁻¹).add
          (havgInv.const_mul alpha) |>.sub (integrable_const 2)
      exact hinner.const_mul _
    let dataF : ∀ omega : BilateralField d,
        SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData (U k) (F omega) :=
      fun omega => SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
        (hFcont omega) (hFpos omega) (U k)
    let dataB : ∀ omega : BilateralField d,
        SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData (U k) (B omega) :=
      fun omega => SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
        (hBcont omega) (hBpos omega) (U k)
    have hBA : ∀ omega, (dataB omega).toCoeffOn.AEEq (a0 N k omega) := by
      intro omega
      filter_upwards [] with x
      exact (hcoeff omega x).symm
    have hrel : ∀ omega x,
        (dataB omega).toCoeffOn.toCoeffField x =
          alpha⁻¹ • (dataF omega).toCoeffOn.toCoeffField x := by
      intro omega x
      ext r s
      by_cases hrs : r = s
      · subst s
        simp [dataB, dataF, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
          SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField, B,
          Homogenization.scalarMatrix]
      · simp [dataB, dataF, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
          SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField, B,
          Homogenization.scalarMatrix, hrs]
    have he : Homogenization.vecNormSq (Pi.single j 1) = 1 := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _hi hij
        simp [Pi.single_apply, hij]
      · simp
    have hbound : ∀ omega,
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
            (Pi.single j 1) (Pi.single j 1) ≤
          (1 / 2 : ℝ) * Homogenization.Book.Ch02.average (U k)
            (fun x => F omega x / alpha + alpha / F omega x - 2) := by
      intro omega
      calc
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
              (Pi.single j 1) (Pi.single j 1) =
            Homogenization.Book.Ch02.responseJ (U k) (dataB omega).toCoeffOn
              (Pi.single j 1) (Pi.single j 1) :=
          (Homogenization.Book.Ch02.responseJ_eq_ofAEEq (hBA omega)
            (Pi.single j 1) (Pi.single j 1)).symm
        _ = Homogenization.Book.Ch02.responseJ (U k) (dataF omega).toCoeffOn
              ((Real.sqrt alpha)⁻¹ • Pi.single j 1)
              (Real.sqrt alpha • Pi.single j 1) :=
          (hJ.responseJ_scalar_hom (U k) (dataF omega).toCoeffOn
            (dataB omega).toCoeffOn alpha halpha (hrel omega) (Pi.single j 1)).symm
        _ ≤ (1 / 2 : ℝ) * Homogenization.Book.Ch02.average (U k)
              (fun x => F omega x / alpha + alpha / F omega x - 2) :=
          SubdiffusiveProcess.CoarseGrainingVocab.responseJ_le_half_scalar_ratio (U k)
            (dataF omega) halpha (hFpos omega) (Pi.single j 1) he
    have hnorm : ∀ omega,
        ‖Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
            (Pi.single j 1) (Pi.single j 1)‖ ≤
          (1 / 2 : ℝ) *
            (alpha⁻¹ * avgF omega + alpha * avgInv omega - 2) := by
      intro omega
      rw [Real.norm_of_nonneg
        (Homogenization.Book.Ch02.responseJ_nonneg (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1))]
      calc
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
              (Pi.single j 1) (Pi.single j 1) ≤
            (1 / 2 : ℝ) * Homogenization.Book.Ch02.average (U k)
              (fun x => F omega x / alpha + alpha / F omega x - 2) :=
          hbound omega
        _ = (1 / 2 : ℝ) *
            (alpha⁻¹ * avgF omega + alpha * avgInv omega - 2) := by
          rw [hratio omega]
    exact hmajor.mono' hrespmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hnorm)
  rw [← MeasureTheory.integral_const_mul]
  rw [show (fun omega => (1 / 2 : ℝ) * Matrix.trace
      (Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) +
        Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) -
        2 • (1 : Matrix (Fin d) (Fin d) ℝ))) =
      (fun omega => ∑ j : Fin d,
        Homogenization.Book.Ch02.responseJ (U k) (a0 N k omega)
          (Pi.single j 1) (Pi.single j 1)) by
        funext omega
        exact hpoint omega]
  exact MeasureTheory.integral_finset_sum Finset.univ (fun j _ => hint j)

end Paper
