

module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoRatioRow
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import SubdiffusiveProcess.Paper.lem_as_regularity_unit
public import SubdiffusiveProcess.Paper.lem_finite_source_comparison_cells
public import SubdiffusiveProcess.Lane3.LocalEnergyAux
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Lane4.InDetCampanatoHolder
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

noncomputable section
namespace Paper

/-- The finite block retained by an integer field shift has every exponential
moment. Both directions of shift are included. -/
theorem aux_lem_as_regularity_nc_retained_exp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (w : SpatialCoordinates d) (q : ℝ) :
    Integrable (fun om => Real.exp (q * aux_transport_retained m w om))
      (chaosSampleLaw M).toMeasure := by
  rcases le_or_gt 0 m with hm | hm
  · let k := m.toNat
    let ι : ℕ → ℤ := fun i => -(i : ℤ)
    have hι : Function.Injective ι := by
      intro a b hab
      dsimp [ι] at hab
      omega
    have hint := (aux_fscc_holNeuH_sum_inj M k ι hι w q).1
    have heq : (fun om => Real.exp (q * aux_transport_retained m w om)) =
        fun om => Real.exp (q * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
          Real.exp (q * (∑ j ∈ Finset.range k, om (ι j) w -
            (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
      funext om
      rw [aux_fscc_holNeuH_retained_eq_pos m hm w om, ← Real.exp_add]
      congr 1
      dsimp [k, ι]
      ring
    rw [heq]
    exact hint.const_mul _
  · let k := (-m).toNat
    let ι : ℕ → ℤ := fun i => -m - (i : ℤ)
    have hι : Function.Injective ι := by
      intro a b hab
      dsimp [ι] at hab
      omega
    have hint := (aux_fscc_holNeuH_sum_inj M k ι hι w (-q)).1
    have heq : (fun om => Real.exp (q * aux_transport_retained m w om)) =
        fun om => Real.exp (-q * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
          Real.exp (-q * (∑ j ∈ Finset.range k, om (ι j) w -
            (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
      funext om
      rw [aux_fscc_holNeuH_retained_eq_neg m hm w om, ← Real.exp_add]
      congr 1
      dsimp [k, ι]
      ring
    rw [heq]
    exact hint.const_mul _

/-- Every real exponential moment of the infrared field at the translated anchor. -/
theorem aux_lem_as_regularity_nc_infrared_exp
    {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (w : SpatialCoordinates d) (q : ℝ) :
    Integrable (fun om => Real.exp (q * H om w)) (chaosSampleLaw M).toMeasure := by
  obtain ⟨CH, hCH, hExp⟩ := exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  let Kc : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall w 1, ProperSpace.isCompact_closedBall w 1⟩
  have hwK : w ∈ (Kc : Set (SpatialCoordinates d)) := Metric.mem_closedBall_self (by norm_num)
  have hint := (hExp M H hH Kc |q| (abs_nonneg q)).1
  have hmeas : Measurable (fun om : BilateralField d => Real.exp (q * H om w)) :=
    (measurable_const.mul ((continuous_eval_const w).measurable.comp hH.1)).exp
  refine hint.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [] with om
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc q * H om w ≤ |q * H om w| := le_abs_self _
    _ = |q| * ‖H om w‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |q| * ‖(H om).restrict (Kc : Set (SpatialCoordinates d))‖ :=
      mul_le_mul_of_nonneg_left
        (((H om).restrict (Kc : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨w, hwK⟩)
        (abs_nonneg q)

/-- Integrability of an exponential of a sum, without an independence assumption. -/
theorem aux_lem_as_regularity_nc_exp_add_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (q : ℝ)
    (hfi : Integrable (fun om => Real.exp ((2 * q) * f om)) μ)
    (hgi : Integrable (fun om => Real.exp ((2 * q) * g om)) μ) :
    Integrable (fun om => Real.exp (q * (f om + g om))) μ := by
  refine (hfi.add hgi).mono'
    ((measurable_const.mul (hf.add hg)).exp.aestronglyMeasurable) ?_
  filter_upwards [] with om
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hf2 : Real.exp (q * f om) ^ 2 = Real.exp ((2 * q) * f om) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hg2 : Real.exp (q * g om) ^ 2 = Real.exp ((2 * q) * g om) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  change Real.exp (q * (f om + g om)) ≤
    Real.exp ((2 * q) * f om) + Real.exp ((2 * q) * g om)
  rw [mul_add, Real.exp_add]
  nlinarith [sq_nonneg (Real.exp (q * f om) - Real.exp (q * g om)),
    Real.exp_pos ((2 * q) * f om), Real.exp_pos ((2 * q) * g om)]

/-- The inverse random reference has every finite positive moment, uniformly
in the cutoff over the exact covariance range. The common dominating function
contains just the fixed anchor field and the finitely many retained layers. -/
theorem aux_lem_as_regularity_nc_reference_moment
    {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (w : SpatialCoordinates d) (m : ℤ)
    (p : ℝ) (hp : 0 < p) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧ ∀ N : ℕ, m ≤ (N : ℤ) →
      MemLp (fun om => (aux_transport_reference M H N m w om)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (aux_transport_reference M H N m w om)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cref := by
  let μ := (chaosSampleLaw M).toMeasure
  let f : BilateralField d → ℝ := fun om => H om w
  let g : BilateralField d → ℝ := fun om => aux_transport_retained m w om
  have hf : Measurable f := (continuous_eval_const w).measurable.comp hH.1
  have hg : Measurable g := aux_fscc_holNeuH_retained_measurable m w
  have hint : Integrable (fun om => Real.exp (-p * (f om + g om))) μ :=
    aux_lem_as_regularity_nc_exp_add_integrable μ f g hf hg (-p)
      (aux_lem_as_regularity_nc_infrared_exp hd M H hH w _) 
      (aux_lem_as_regularity_nc_retained_exp M m w _)
  let B : BilateralField d → ℝ := fun om => Real.exp (-(f om + g om))
  have hBmeas : Measurable B := (hf.add hg).neg.exp
  have hBmem : MemLp B (ENNReal.ofReal p) μ := by
    refine (integrable_norm_rpow_iff hBmeas.aestronglyMeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top).1 ?_
    refine hint.congr (Filter.Eventually.of_forall fun om => ?_)
    rw [ENNReal.toReal_ofReal hp.le]
    change Real.exp (-p * (f om + g om)) = ‖Real.exp (-(f om + g om))‖ ^ p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul]
    congr 1
    ring
  let C : ℝ := Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  let G : BilateralField d → ℝ := fun om => C * B om
  have hGmem : MemLp G (ENNReal.ofReal p) μ := hBmem.const_mul C
  refine ⟨(eLpNorm G (ENNReal.ofReal p) μ).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro N hmN
  have hratio := (aux_fscc_holNeuH_kappa_ratio_bound M m N hmN).1
  have hratio' : Real.exp (-((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ≤
      aux_transport_kappa M ((N : ℤ) - m).toNat / aux_transport_kappa M N := by
    simpa only [neg_mul] using hratio
  have hkinv : (aux_transport_kappa M ((N : ℤ) - m).toNat / aux_transport_kappa M N)⁻¹ ≤ C := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hratio'
    simpa only [one_div, ← Real.exp_neg, neg_neg, C] using h
  have hmeas : Measurable (fun om => (aux_transport_reference M H N m w om)⁻¹) := by
    unfold aux_transport_reference
    exact (measurable_const.mul ((hf.add hg).exp)).inv
  have hdom : ∀ᵐ om ∂μ, ‖(aux_transport_reference M H N m w om)⁻¹‖ ≤ G om := by
    filter_upwards [] with om
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (aux_transport_reference_pos M H N m w om))]
    change ((_ * Real.exp (f om + g om))⁻¹) ≤ C * B om
    rw [mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_right hkinv (Real.exp_pos _).le
  refine ⟨hGmem.mono' hmeas.aestronglyMeasurable hdom, ?_⟩
  calc eLpNorm (fun om => (aux_transport_reference M H N m w om)⁻¹) (ENNReal.ofReal p) μ
      ≤ eLpNorm G (ENNReal.ofReal p) μ := eLpNorm_mono_ae_real hmeas.aestronglyMeasurable hdom
    _ = ENNReal.ofReal (eLpNorm G (ENNReal.ofReal p) μ).toReal :=
      (ENNReal.ofReal_toReal hGmem.eLpNorm_lt_top.ne).symm

/-- A scalar multiple of a product consumes the doubled moment orders. -/
theorem aux_lem_as_regularity_nc_product_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p A Cb Cr : ℝ) (hA : 0 ≤ A) (hCb : 0 ≤ Cb)
    (f g : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal (2 * p)) μ)
    (hg : MemLp g (ENNReal.ofReal (2 * p)) μ)
    (hfn : eLpNorm f (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal Cb)
    (hgn : eLpNorm g (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal Cr) :
    MemLp (fun om => A * (f om * g om)) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun om => A * (f om * g om)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (A * (Cb * Cr)) := by
  have hmuln : eLpNorm (fun om => f om * g om) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal Cb * ENNReal.ofReal Cr :=
    (aux_aux_macro_moment_bank_product_moment μ p f g hf.aestronglyMeasurable hg.aestronglyMeasurable).trans
      (mul_le_mul' hfn hgn)
  have hbound : eLpNorm (fun om => A * (f om * g om)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (A * (Cb * Cr)) := by
    calc _ ≤ ‖A‖ₑ * eLpNorm (fun om => f om * g om) (ENNReal.ofReal p) μ := by
            simpa only [Pi.smul_apply, smul_eq_mul] using!
              (eLpNorm_const_smul_le (c := A) (f := fun om => f om * g om)
                (p := ENNReal.ofReal p) (μ := μ))
      _ ≤ ‖A‖ₑ * (ENNReal.ofReal Cb * ENNReal.ofReal Cr) := mul_le_mul_right hmuln _
      _ = ENNReal.ofReal (A * (Cb * Cr)) := by
          rw [Real.enorm_eq_ofReal hA, ← ENNReal.ofReal_mul hCb, ← ENNReal.ofReal_mul hA]
  exact ⟨hbound.trans_lt ENNReal.ofReal_lt_top, hbound⟩

/-- A uniform moment bound after a chaos-law-preserving scale and translation
shift, including the inverse random reference from covariance. -/
theorem aux_lem_as_regularity_nc_transport_moment
    {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (w : SpatialCoordinates d) (m : ℤ)
    (p A Cb : ℝ) (hp : 0 < p) (hA : 0 ≤ A) (hCb : 0 ≤ Cb)
    (Kcor : ℕ → BilateralField d → ℝ)
    (hmem : ∀ N, MemLp (Kcor N) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure)
    (hnorm : ∀ N, eLpNorm (Kcor N) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cb) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧ ∀ N : ℕ, m ≤ (N : ℤ) →
      MemLp (fun om => A * Kcor (((N : ℤ) - m).toNat) (aux_transport_S m w om) /
          aux_transport_reference M H N m w om)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => A * Kcor (((N : ℤ) - m).toNat) (aux_transport_S m w om) /
          aux_transport_reference M H N m w om)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cref := by
  obtain ⟨Cr, hCr, hr⟩ := aux_lem_as_regularity_nc_reference_moment hd M H hH w m (2 * p)
    (mul_pos (by norm_num) hp)
  refine ⟨A * (Cb * Cr), mul_nonneg hA (mul_nonneg hCb hCr), ?_⟩
  intro N hmN
  let n := ((N : ℤ) - m).toNat
  let f : BilateralField d → ℝ := fun om => Kcor n (aux_transport_S m w om)
  let g : BilateralField d → ℝ := fun om => (aux_transport_reference M H N m w om)⁻¹
  have hS := aux_transport_S_measurePreserving M m w
  have hf : MemLp f (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure :=
    (hmem n).comp_measurePreserving hS
  obtain ⟨hg, hgn⟩ := hr N hmN
  have hfn : eLpNorm f (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cb := by
    calc eLpNorm f (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure
        = eLpNorm (Kcor n) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure := by
          exact eLpNorm_comp_measurePreserving (hmem n).aestronglyMeasurable hS
      _ ≤ ENNReal.ofReal Cb := hnorm n
  have heq : (fun om => A * Kcor (((N : ℤ) - m).toNat) (aux_transport_S m w om) /
        aux_transport_reference M H N m w om) = fun om => A * (f om * g om) := by
    funext om
    simp only [f, g, n, div_eq_mul_inv, mul_assoc]
  rw [heq]
  exact aux_lem_as_regularity_nc_product_moment (chaosSampleLaw M).toMeasure
    p A Cb Cr hA hCb f g hf hg hfn hgn


theorem aux_lem_as_regularity_nc_localGradientEnergy_scale {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (c : ℝ) (hc : 0 < c) (a : PositiveCoefficient Ω)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (g : HilbertGradient Ω) :
    localGradientEnergy (scalePositiveCoefficient c hc a) hs g =
      c * localGradientEnergy a hs g := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoef : ∀ᵐ x ∂ (volume.restrict (Ω : Set (SpatialCoordinates d))).restrict s,
      (scalePositiveCoefficient c hc a).val x = c * a.val x :=
    ae_restrict_of_ae (scalePositiveCoefficient_coeFn c hc a)
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hcoef] with x hx
  rw [hx]
  ring

/-- Unit-cube local energy bounds extend to every positive radius, since the
whole unit cube lies in the radius-one ball about any of its interior points. -/
theorem aux_lem_as_regularity_nc_energy_all_radii {d : ℕ}
    (z0 : SpatialCoordinates d) (a : PositiveCoefficient (centeredCube z0 1 one_pos))
    (g : HilbertGradient (centeredCube z0 1 one_pos))
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ centeredCube z0 1 one_pos, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet) g ≤
        B * rad ^ t) :
    ∀ x ∈ centeredCube z0 1 one_pos, ∀ rad : ℝ, 0 < rad →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet) g ≤
        B * rad ^ t := by
  intro x hx rad hrad
  by_cases hrad1 : rad ≤ 1
  · exact hbound x hx rad hrad hrad1
  · have hsub : Metric.ball x rad ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)) ⊆
        Metric.ball x 1 ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)) := by
      rintro y ⟨_, hy⟩
      refine ⟨?_, hy⟩
      change dist y x < 1
      have hy0 : dist y z0 < 1 / 2 := hy
      have hx0 : dist x z0 < 1 / 2 := hx
      have htri := dist_triangle y z0 x
      rw [dist_comm z0 x] at htri
      linarith
    calc
      _ ≤ localGradientEnergy a
          (s := Metric.ball x 1 ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet) g :=
        Lane3.localGradientEnergy_mono a _ _ hsub g
      _ ≤ B * (1 : ℝ) ^ t := hbound x hx 1 zero_lt_one le_rfl
      _ ≤ B * rad ^ t := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by norm_num) (lt_of_not_ge hrad1).le ht) hB

/-- Transport the complete Hölder norm, retaining its supremum term. -/
theorem aux_lem_as_regularity_nc_cAlpha_transport {d : ℕ}
    (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {alpha A : ℝ} (halpha : 0 ≤ alpha) (hA : 0 ≤ A)
    (U1 : SpatialCoordinates d → ℝ) (hU1c : Continuous U1)
    (hU1h : IsHolderOn alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U1)
    (hU1n : cAlphaNorm alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U1 ≤ A) :
    let U : SpatialCoordinates d → ℝ := fun y => U1 (cubeDilation z0 z r⁻¹ y)
    Continuous U ∧ IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        (1 + r ^ (-alpha)) * A := by
  intro U
  obtain ⟨_, hUH, hsemi⟩ := aux_fscc_holNeuH_holder_transport z z0 hr halpha U1
    hU1c.continuousOn hU1h
  have hsemi1 : holderSeminorm alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U1 ≤ A :=
    (aux_lem_finite_source_comparison_cells_holderSeminorm_le _ _ U1).trans hU1n
  have hsemi0 := aux_lem_finite_source_comparison_cells_holderSeminorm_nonneg alpha
    (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U1
  have hsup1 : sSup {v : ℝ | ∃ x ∈ (closedCube z0 1 one_pos : Set (SpatialCoordinates d)),
      v = |U1 x|} ≤ A := by
    unfold cAlphaNorm at hU1n
    linarith
  have hbdd : BddAbove {v : ℝ | ∃ x ∈ (closedCube z0 1 one_pos : Set (SpatialCoordinates d)),
      v = |U1 x|} := aux_lem_as_regularity_affine_transport_sup_bdd _
        (closedCube z0 1 one_pos).isCompact (fun x => |U1 x|) (continuous_abs.comp hU1c)
  have hsup : sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |U x|} ≤ A := by
    apply Real.sSup_le _ hA
    rintro v ⟨x, hx, rfl⟩
    apply (le_csSup hbdd ?_).trans hsup1
    exact ⟨cubeDilation z0 z r⁻¹ x,
      aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z z0 hr one_pos hr
        (by ring) hx, rfl⟩
  refine ⟨hU1c.comp (continuous_cubeDilation z0 z r⁻¹), hUH, ?_⟩
  calc cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U
      ≤ A + r ^ (-alpha) * A := add_le_add hsup
        (hsemi.trans (mul_le_mul_of_nonneg_left hsemi1 (Real.rpow_nonneg hr.le _)))
    _ = (1 + r ^ (-alpha)) * A := by ring

/-- Pull a representative back from the unit cube using its exact value tie. -/
theorem aux_lem_as_regularity_nc_representative {d : ℕ}
    (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (v : SobolevData (centeredCube z r hr))
    (v1 : SobolevData (centeredCube z0 1 one_pos))
    (U1 : SpatialCoordinates d → ℝ)
    (hv1 : (v1.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))]
      fun x => v.1 (cubeDilation z z0 r x))
    (hU1 : (v1.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] U1) :
    (v.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun y => U1 (cubeDilation z0 z r⁻¹ y) := by
  apply aux_prop_growth_large_root_ae_root_of_ae_unit z z0 hr
  filter_upwards [hv1, hU1] with x hx hUx
  rw [aux_prop_growth_large_root_cubeDilation_inv_right z z0 hr, ← hx, hUx]

/-- The scalar identity in the energy transport. The source is multiplied by
r squared and divided by the reference coefficient; the energy Jacobian is r^(d-2). -/
theorem aux_lem_as_regularity_nc_energy_algebra
    (r c K Kf rad D t : ℝ) (hr : 0 < r) (hc : 0 < c) (hrad : 0 < rad) :
    r ^ (D - 2) * (c * (K * (r ^ 2 * Kf / c) ^ 2 * (rad / r) ^ t)) =
      (r ^ (D + 2 - t) * K / c) * Kf ^ 2 * rad ^ t := by
  have hp : r ^ (D - 2) * (r ^ (2 : ℕ)) ^ 2 / r ^ t = r ^ (D + 2 - t) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hr, ← Real.rpow_sub hr]
    congr 1
    norm_num
    ring
  rw [Real.div_rpow hrad.le hr.le]
  calc _ = (r ^ (D - 2) * (r ^ (2 : ℕ)) ^ 2 / r ^ t) * K / c * Kf ^ 2 * rad ^ t := by
          field_simp
    _ = _ := by rw [hp]

/-- The two estimates for a fixed Sobolev datum; used only to keep the transport
proof's elaboration context small. -/
def aux_lem_as_regularity_nc_bound {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (v : SobolevData (centeredCube z r hr)) (t alpha K Kf : ℝ) : Prop :=
  (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
    IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
    (v.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
    cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K * Kf) ∧
  (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
    localGradientEnergy a
      (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
      (sobolevGradient v) ≤ K * Kf ^ 2 * rad ^ t)

/-- All bounded-source Neumann estimates on a fixed coefficient. -/
def aux_lem_as_regularity_nc_estimate {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (t alpha K : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
    AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
    (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ v : meanZeroSobolevGraph (centeredCube z r hr), SolvesNeumann a F v →
      aux_lem_as_regularity_nc_bound z r hr a v t alpha K Kf

/-- Explicit deterministic constant for the simultaneous norm and energy transport. -/
def aux_lem_as_regularity_nc_factor (d : ℕ) (r t alpha : ℝ) : ℝ :=
  (1 + r ^ (-alpha)) * r ^ 2 + r ^ ((d : ℝ) + 2 - t)

/-- Transport one Neumann datum, with no restriction on the cube side or on
rad/r. The source scale and coefficient scale are both accounted for. -/
theorem aux_lem_as_regularity_nc_transfer_data {d : ℕ}
    (z z0 : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t alpha K c : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ alpha) (hK : 0 ≤ K) (hc : 0 < c)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a1 a2 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (hcoef : a1 = scalePositiveCoefficient c hc a2)
    (hest : aux_lem_as_regularity_nc_estimate z0 1 one_pos a2 t alpha K)
    (v : SobolevData (centeredCube z r hr))
    (v1 : meanZeroSobolevGraph (centeredCube z0 1 one_pos))
    (F1 : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F1 (volume.restrict
      (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      |F1 x| ≤ r ^ 2 * Kf)
    (hFz : (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F1 x) = 0)
    (hsol : SolvesNeumann a1 F1 v1)
    (hv1 : ((v1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))]
      fun x => v.1 (cubeDilation z z0 r x))
    (henergy : ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho →
      localGradientEnergy a1
        (s := Metric.ball x rho ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos))) =
      r ^ ((2 : ℝ) - (d : ℝ)) *
        localGradientEnergy a
          (s := Metric.ball (cubeDilation z z0 r x) (r * rho) ∩
            (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient v)) :
    aux_lem_as_regularity_nc_bound z r hr a v t alpha
      (aux_lem_as_regularity_nc_factor d r t alpha * K / c) Kf := by
  have hsolve2 := aux_fscc_holNeuH_solvesNeumann_unscale c hc a1 a2 hcoef F1 v1 hsol
  have hFdiv : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      |F1 x / c| ≤ r ^ 2 * Kf / c := by
    filter_upwards [hFb] with x hx
    rw [abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right hx hc.le
  have hFdivz : (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F1 x / c) = 0 := by
    rw [integral_div, hFz, zero_div]
  obtain ⟨hHolder, hEn⟩ := hest (fun x => F1 x / c) (r ^ 2 * Kf / c)
    (by positivity) (hFm.div_const c) hFdiv hFdivz v1 hsolve2
  have hCH : (1 + r ^ (-alpha)) * r ^ 2 * K / c ≤
      aux_lem_as_regularity_nc_factor d r t alpha * K / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    apply mul_le_mul_of_nonneg_right _ hK
    exact le_add_of_nonneg_right (Real.rpow_nonneg hr.le _)
  have hCE : r ^ ((d : ℝ) + 2 - t) * K / c ≤
      aux_lem_as_regularity_nc_factor d r t alpha * K / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    apply mul_le_mul_of_nonneg_right _ hK
    exact le_add_of_nonneg_left (by positivity)
  constructor
  · obtain ⟨U1, hU1c, hU1h, hU1ae, hU1n⟩ := hHolder
    obtain ⟨hUc, hUh, hUn⟩ := aux_lem_as_regularity_nc_cAlpha_transport z z0 hr ha
      (show 0 ≤ K * (r ^ 2 * Kf / c) by positivity) U1 hU1c hU1h hU1n
    refine ⟨fun y => U1 (cubeDilation z0 z r⁻¹ y), hUc, hUh,
      aux_lem_as_regularity_nc_representative z z0 hr v v1 U1 hv1 hU1ae, ?_⟩
    calc _ ≤ (1 + r ^ (-alpha)) * (K * (r ^ 2 * Kf / c)) := hUn
      _ = ((1 + r ^ (-alpha)) * r ^ 2 * K / c) * Kf := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCH hKf
  · intro x rad hx hrad _
    let x1 := cubeDilation z0 z r⁻¹ x
    have hx1 : x1 ∈ centeredCube z0 1 one_pos :=
      aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube z z0 hr hx
    have hEall := aux_lem_as_regularity_nc_energy_all_radii z0 a2
      (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos))) t
      (K * (r ^ 2 * Kf / c) ^ 2) ht (by positivity)
      (fun y hy rad h0 h1 => hEn y rad hy h0 h1) x1 hx1 (rad / r) (div_pos hrad hr)
    have hE := henergy x1 (rad / r) (div_pos hrad hr)
    rw [hcoef, aux_lem_as_regularity_nc_localGradientEnergy_scale] at hE
    have hTx : cubeDilation z z0 r x1 = x :=
      aux_prop_growth_large_root_cubeDilation_inv_left z z0 hr x
    have hrr : r * (rad / r) = rad := mul_div_cancel₀ rad hr.ne'
    rw [hTx, hrr] at hE
    have hinv : r ^ ((d : ℝ) - 2) * r ^ ((2 : ℝ) - (d : ℝ)) = 1 := by
      rw [← Real.rpow_add hr]
      rw [show (d : ℝ) - 2 + (2 - (d : ℝ)) = 0 by ring, Real.rpow_zero]
    have hroot := congrArg (fun a : ℝ => r ^ ((d : ℝ) - 2) * a) hE
    calc _ = r ^ ((d : ℝ) - 2) * (c * localGradientEnergy a2
          (s := Metric.ball x1 (rad / r) ∩
            (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
          (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos)))) := by
            simpa only [← mul_assoc, hinv, one_mul] using hroot.symm
      _ ≤ r ^ ((d : ℝ) - 2) * (c * (K * (r ^ 2 * Kf / c) ^ 2 * (rad / r) ^ t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEall hc.le)
          (Real.rpow_nonneg hr.le _)
      _ = (r ^ ((d : ℝ) + 2 - t) * K / c) * Kf ^ 2 * rad ^ t :=
        aux_lem_as_regularity_nc_energy_algebra r c K Kf rad d t hr hc hrad
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCE (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le _)

def aux_lem_as_regularity_nc_rho_tie {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (a1 : PositiveCoefficient (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) : Prop :=
  ∀ᵐ x ∂ volume.restrict
      (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
    (a1.val : SpatialCoordinates d → ℝ) x =
      (cutoffPositiveCoefficient M H omega N (0 : SpatialCoordinates d) hrho).val
        (cubeDilation (0 : SpatialCoordinates d) (fun _ : Fin d => (1 / 2 : ℝ)) rho x)


/-- The coefficient identity at the residual scale, derived from the field
identity and the two exact affine pullbacks. -/
theorem aux_lem_as_regularity_nc_coeff_ident {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (m : ℤ) (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hreq : r = (3 : ℝ) ^ (-m) * rho)
    (N : ℕ) (omega : BilateralField d)
    (homega : ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H omega N (z + (3 : ℝ) ^ (-m) • y) =
        aux_transport_reference M H N m z omega *
          cutoffCoefficient M H (aux_transport_S m z omega) (((N : ℤ) - m).toNat) y)
    (a1 a1rho : PositiveCoefficient (unitNeumannCube d))
    (ha1 : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a1.val x = (cutoffPositiveCoefficient M H omega N z hr).val
        (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x))
    (ha1rho : aux_lem_as_regularity_nc_rho_tie M H (aux_transport_S m z omega)
      (((N : ℤ) - m).toNat) rho hrho a1rho) :
    a1 = scalePositiveCoefficient (aux_transport_reference M H N m z omega)
      (aux_transport_reference_pos M H N m z omega) a1rho := by
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  have hval1 := aux_fscc_holNeuH_cutoffPos_val M H omega N z hr
  have hval2 := aux_fscc_holNeuH_cutoffPos_val M H (aux_transport_S m z omega)
    (((N : ℤ) - m).toNat) 0 hrho
  have hqmp1 := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
  have hqmp2 := lane4_dilation_quasi_measure_preserving d 0 z0 rho hrho one_pos
  have hpt (x : SpatialCoordinates d) :
      z + (3 : ℝ) ^ (-m) • cubeDilation (0 : SpatialCoordinates d) z0 rho x =
        cubeDilation z z0 r x := by
    funext i
    simp only [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [hreq]
    ring
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [ha1, ha1rho,
    scalePositiveCoefficient_coeFn (aux_transport_reference M H N m z omega)
      (aux_transport_reference_pos M H N m z omega) a1rho,
    hqmp1.ae hval1, hqmp2.ae hval2] with x hx1 hx2 hx3 hx4 hx5
  erw [hx1, hx4, ← hpt x, homega, ← hx5, ← hx2, hx3]
  rfl

/-- Deterministic completion of the residual-scale Neumann reduction. The
residual-scale estimate remains an explicit supplier, and the resulting
constant is explicit so that its moments can be estimated separately. -/
theorem aux_lem_as_regularity_nc_core {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (m : ℤ) (r rho : ℝ) (hr : 0 < r) (hrho : 0 < rho)
    (hreq : r = (3 : ℝ) ^ (-m) * rho) (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ alpha)
    (N : ℕ) (omega : BilateralField d)
    (homega : ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H omega N (z + (3 : ℝ) ^ (-m) • y) =
        aux_transport_reference M H N m z omega *
          cutoffCoefficient M H (aux_transport_S m z omega) (((N : ℤ) - m).toNat) y)
    (Kcor : ℝ) (hKcor : 0 ≤ Kcor)
    (hcorS : ∀ a1 : PositiveCoefficient (unitNeumannCube d),
      aux_lem_as_regularity_nc_rho_tie M H (aux_transport_S m z omega)
        (((N : ℤ) - m).toNat) rho hrho a1 →
      aux_lem_as_regularity_nc_estimate (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        a1 t alpha Kcor) :
    aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H omega N z hr)
      t alpha (aux_lem_as_regularity_nc_factor d r t alpha * Kcor /
        aux_transport_reference M H N m z omega) := by
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  obtain ⟨a1, ha1, _, hNeumannPart⟩ := lem_as_regularity_affine_transport d M H omega N z r hr
  obtain ⟨a1rho, ha1rho⟩ := lane4_dilation_coefficient_transport d 0 z0 rho hrho one_pos
    (cutoffPositiveCoefficient M H (aux_transport_S m z omega) (((N : ℤ) - m).toNat) 0 hrho)
  have hcoef := aux_lem_as_regularity_nc_coeff_ident M H z m r rho hr hrho hreq N omega
    homega a1 a1rho ha1 ha1rho
  have hest := hcorS a1rho ha1rho
  intro F Kf hKf hFm hFb hFz v hsol
  obtain ⟨F1, v1, _, hF1m, hF1b, hF1z, hsol1, hv1, _, henergy⟩ :=
    hNeumannPart F Kf hKf hFm hFb hFz v hsol
  exact aux_lem_as_regularity_nc_transfer_data z z0 r hr t alpha Kcor
    (aux_transport_reference M H N m z omega) ht ha hKcor
    (aux_transport_reference_pos M H N m z omega) _ a1 a1rho hcoef hest
    v v1 F1 Kf hKf hF1m hF1b hF1z hsol1 hv1 henergy

/-- First moments of the transported random constant, using the proved
second moment of the inverse reference scalar and a doubled supplier moment. -/
theorem aux_lem_as_regularity_nc_transport_moment_one
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ)
    (Kcor : ℕ → BilateralField d → ℝ) (Cb2 : ℝ) (hCb0 : 0 ≤ Cb2)
    (hmemK2 : ∀ N, MemLp (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure)
    (hnormK2 : ∀ N, eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb2)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (w : SpatialCoordinates d) (A : ℝ) (hA : 0 ≤ A) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧
      ∀ J : ℕ, m ≤ (J : ℤ) →
        MemLp (fun omega => A * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) /
              aux_transport_reference model H J m w omega)
            (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ∧
          eLpNorm (fun omega => A * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) /
              aux_transport_reference model H J m w omega)
            (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cref := by
  obtain ⟨CrefG, hCrefG0, hRef⟩ := aux_fscc_holNeuH_ref_inv_moment d hd model H hH w m
  let c : ℝ := A
  have hc0 : 0 ≤ c := hA
  refine ⟨c * (Cb2 * CrefG), by positivity, ?_⟩
  intro J hmJ
  set N : ℕ := ((J : ℤ) - m).toNat with hNdef
  have hSmp := aux_transport_S_measurePreserving model m w
  have hf2 : MemLp (fun omega => Kcor N (aux_transport_S m w omega))
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure :=
    (hmemK2 N).comp_measurePreserving hSmp
  have hf2norm : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega))
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cb2 := by
    have heq : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega)) (ENNReal.ofReal 2)
        (chaosSampleLaw model).toMeasure =
        eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure := by
      simpa [Function.comp_def] using
        eLpNorm_comp_measurePreserving (p := ENNReal.ofReal 2)
          (hmemK2 N).aestronglyMeasurable hSmp
    rw [heq]
    exact hnormK2 N
  obtain ⟨hg2, hg2norm⟩ := hRef J hmJ
  have hp2 : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by norm_num
  have hp1 : (ENNReal.ofReal (1 : ℝ)) = (1 : ℝ≥0∞) := ENNReal.ofReal_one
  rw [hp2] at hf2 hf2norm hg2 hg2norm
  have hmul : MemLp (fun omega => Kcor N (aux_transport_S m w omega) *
      (aux_transport_reference model H J m w omega)⁻¹)
      (1 : ℝ≥0∞) (chaosSampleLaw model).toMeasure := by
    have hraw := MemLp.mul' (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun omega => (aux_transport_reference model H J m w omega)⁻¹)
      (φ := fun omega => Kcor N (aux_transport_S m w omega)) hf2 hg2
    simpa using hraw
  have hmulnorm : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
      (aux_transport_reference model H J m w omega)⁻¹)
      (1 : ℝ≥0∞) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG := by
    have hle := eLpNorm_smul_le_mul_eLpNorm (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun omega => (aux_transport_reference model H J m w omega)⁻¹)
      (φ := fun omega => Kcor N (aux_transport_S m w omega)) hf2.aestronglyMeasurable hg2.aestronglyMeasurable
    simp only [smul_eq_mul] at hle
    calc eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
          (aux_transport_reference model H J m w omega)⁻¹) (1 : ℝ≥0∞)
          (chaosSampleLaw model).toMeasure
        ≤ eLpNorm (fun omega => Kcor N (aux_transport_S m w omega)) (2 : ℝ≥0∞)
            (chaosSampleLaw model).toMeasure *
          eLpNorm (fun omega => (aux_transport_reference model H J m w omega)⁻¹) (2 : ℝ≥0∞)
            (chaosSampleLaw model).toMeasure := hle
      _ ≤ ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG := mul_le_mul' hf2norm hg2norm
  have hgoalfun : (fun omega => A * Kcor N (aux_transport_S m w omega) /
        aux_transport_reference model H J m w omega) =
      fun omega => c * (Kcor N (aux_transport_S m w omega) *
        (aux_transport_reference model H J m w omega)⁻¹) := by
    funext omega
    simp only [c, div_eq_mul_inv, mul_assoc]
  rw [hgoalfun, hp1]
  refine ⟨hmul.const_mul c, ?_⟩
  calc eLpNorm (fun omega => c * (Kcor N (aux_transport_S m w omega) *
        (aux_transport_reference model H J m w omega)⁻¹)) (1 : ℝ≥0∞)
        (chaosSampleLaw model).toMeasure
      ≤ ‖c‖ₑ * eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
          (aux_transport_reference model H J m w omega)⁻¹) (1 : ℝ≥0∞)
          (chaosSampleLaw model).toMeasure := by
        simpa [Pi.smul_apply, smul_eq_mul] using!
          (eLpNorm_const_smul_le (c := c)
            (f := fun omega => Kcor N (aux_transport_S m w omega) *
              (aux_transport_reference model H J m w omega)⁻¹) (p := (1 : ℝ≥0∞))
            (μ := (chaosSampleLaw model).toMeasure))
    _ ≤ ‖c‖ₑ * (ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG) := mul_le_mul_right hmulnorm _
    _ = ENNReal.ofReal (c * (Cb2 * CrefG)) := by
        rw [Real.enorm_eq_ofReal hc0, ← ENNReal.ofReal_mul hCb0, ← ENNReal.ofReal_mul hc0]


/-- Monotonicity of the coefficient in the actual two Neumann estimates. -/
theorem aux_lem_as_regularity_nc_estimate_mono {d : ℕ}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {a : PositiveCoefficient (centeredCube z r hr)} {t alpha K L : ℝ}
    (hKL : K ≤ L) (h : aux_lem_as_regularity_nc_estimate z r hr a t alpha K) :
    aux_lem_as_regularity_nc_estimate z r hr a t alpha L := by
  intro F Kf hKf hFm hFb hFz v hsol
  obtain ⟨⟨U, hUc, hUH, hUae, hUn⟩, hEn⟩ := h F Kf hKf hFm hFb hFz v hsol
  refine ⟨⟨U, hUc, hUH, hUae, hUn.trans (mul_le_mul_of_nonneg_right hKL hKf)⟩, ?_⟩
  intro x rad hx hrad hrad1
  exact (hEn x rad hx hrad hrad1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKL (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le _))

/-- Exact covariance transfers the unit-cube Neumann estimates on every triadic
cube at every cutoff for which the shifted cutoff is nonnegative. -/
theorem aux_lem_as_regularity_nc_triadic_sample {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (m : ℤ) (r : ℝ) (hr : 0 < r)
    (hrm : r = (3 : ℝ) ^ (-m)) (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ alpha)
    (Kcor : ℕ → BilateralField d → ℝ) (hKcor : ∀ N om, 0 ≤ Kcor N om)
    (hcor : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      aux_lem_as_regularity_nc_estimate (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        t alpha (Kcor N om)) (N : ℕ) (hmN : m ≤ (N : ℤ)) :
    let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
        t alpha (aux_lem_as_regularity_nc_factor d r t alpha *
          Kcor (((N : ℤ) - m).toNat) (aux_transport_S m w om) /
            aux_transport_reference M H N m w om) := by
  intro w
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  have hTeq (x : SpatialCoordinates d) :
      cubeDilation z z0 r x = w + (3 : ℝ) ^ (-m) • x := by
    funext i
    simp only [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hrm]
    dsimp [w, z0]
    ring
  have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
  filter_upwards [aux_fscc_holNeuH_coeff_ident M H hH m w N hmN z0,
      (aux_transport_S_measurePreserving M m w).quasiMeasurePreserving.ae hcor]
    with om hcoef hunit
  obtain ⟨a1, ha1, _, hNeumannPart⟩ := lem_as_regularity_affine_transport d M H om N z r hr
  have ha1' : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      a1.val x = cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • x) := by
    filter_upwards [ha1, hq.ae (aux_fscc_holNeuH_cutoffPos_val M H om N z hr)]
      with x hx1 hx2
    rw [hx1, hx2, hTeq]
  have hident := hcoef a1 ha1'
  intro F Kf hKf hFm hFb hFz v hsol
  obtain ⟨F1, v1, _, hF1m, hF1b, hF1z, hsol1, hv1, _, henergy⟩ :=
    hNeumannPart F Kf hKf hFm hFb hFz v hsol
  exact aux_lem_as_regularity_nc_transfer_data z z0 r hr t alpha
    (Kcor (((N : ℤ) - m).toNat) (aux_transport_S m w om))
    (aux_transport_reference M H N m w om) ht ha (hKcor _ _)
    (aux_transport_reference_pos M H N m w om) _ a1 _ hident
    (hunit (((N : ℤ) - m).toNat)) v v1 F1 Kf hKf hF1m hF1b hF1z hsol1 hv1 henergy

/-- A first-moment Neumann bank on arbitrary triadic cubes, including large
cubes, for the entire range of cutoffs covered by scale covariance. The
remaining finitely many cutoffs on cubes smaller than one are stated explicitly. -/
theorem aux_lem_as_regularity_nc_triadic_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ), r = (3 : ℝ) ^ j →
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ N, MemLp (K N) 1 (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (K N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, -j ≤ (N : ℤ) →
            aux_lem_as_regularity_nc_estimate z r hr
              (cutoffPositiveCoefficient M H om N z hr) t alpha (K N om) := by
  obtain ⟨delta0, hdelta0, hCor⟩ := cor_neumann_source d hd E Pc Xc W D Cp t alpha
    1 (fun _ => 2) ht1 ht2 ha0 ha1 (fun _ => by norm_num)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta z r hr j hj
  obtain ⟨Kcor, Cb, hmem, hnorm, hcor⟩ := hCor M Rm Sreg It H hH hdelta
  let Ka : ℕ → BilateralField d → ℝ := fun N om => |Kcor N om|
  have hKa0 : ∀ N om, 0 ≤ Ka N om := fun N om => abs_nonneg _
  have hKamem : ∀ N, MemLp (Ka N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
    intro N
    simpa only [Ka, Real.norm_eq_abs] using (hmem 0 N).norm
  have hKanorm : ∀ N, eLpNorm (Ka N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal |Cb 0| := by
    intro N
    have heq : eLpNorm (Ka N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure =
        eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
      simpa only [Ka, Real.norm_eq_abs] using eLpNorm_norm (f := Kcor N)
        (p := ENNReal.ofReal 2) (μ := (chaosSampleLaw M).toMeasure) (hmem 0 N).aestronglyMeasurable
    rw [heq]
    exact (hnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hcor' : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      aux_lem_as_regularity_nc_estimate (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        t alpha (Ka N om) := by
    filter_upwards [hcor] with om hom N
    exact aux_lem_as_regularity_nc_estimate_mono (le_abs_self _) (hom N)
  let m : ℤ := -j
  let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
  have hfac0 : 0 ≤ aux_lem_as_regularity_nc_factor d r t alpha := by
    unfold aux_lem_as_regularity_nc_factor
    positivity
  obtain ⟨Cref, hCref, hRef⟩ := aux_lem_as_regularity_nc_transport_moment_one hd M m
    Ka |Cb 0| (abs_nonneg _) hKamem hKanorm H hH w
    (aux_lem_as_regularity_nc_factor d r t alpha) hfac0
  let K : ℕ → BilateralField d → ℝ := fun N om =>
    if m ≤ (N : ℤ) then aux_lem_as_regularity_nc_factor d r t alpha *
      Ka (((N : ℤ) - m).toNat) (aux_transport_S m w om) /
        aux_transport_reference M H N m w om else 0
  refine ⟨K, Cref, ?_, ?_, ?_, ?_⟩
  · intro N om
    dsimp [K]
    split_ifs
    · exact div_nonneg (mul_nonneg hfac0 (hKa0 _ _))
        (aux_transport_reference_pos M H N m w om).le
    · exact le_rfl
  · intro N
    by_cases hN : m ≤ (N : ℤ)
    · simpa only [K, if_pos hN, ENNReal.ofReal_one] using (hRef N hN).1
    · simpa only [K, if_neg hN] using (memLp_const (0 : ℝ) :
        MemLp (fun _ : BilateralField d => (0 : ℝ)) 1 (chaosSampleLaw M).toMeasure)
  · intro N
    by_cases hN : m ≤ (N : ℤ)
    · simpa only [K, if_pos hN, ENNReal.ofReal_one] using (hRef N hN).2
    · simp only [K, if_neg hN, eLpNorm_zero', zero_le]
  · have ht : 0 ≤ t := by
      have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hrm : r = (3 : ℝ) ^ (-m) := by simpa only [m, neg_neg] using hj
    have hEvent := fun (N : ℕ) (hN : m ≤ (N : ℤ)) =>
      aux_lem_as_regularity_nc_triadic_sample M H hH z m r hr hrm t alpha ht ha0.le
        Ka hKa0 hcor' N hN
    filter_upwards [(ae_all_iff.mpr fun N => ae_all_iff.mpr fun hN => hEvent N hN)]
      with om hom
    intro N hN
    have hN' : m ≤ (N : ℤ) := hN
    simpa only [K, if_pos hN', w] using hom N hN'

/-- One Neumann bank serves an arbitrary finite list of moment orders on
triadic cubes. The estimates cover precisely the nonnegative shifted cutoffs;
no assertion is made here for the finitely many lower cutoffs on small cubes. -/
theorem aux_lem_as_regularity_nc_triadic_finite_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ), r = (3 : ℝ) ^ j →
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, -j ≤ (N : ℤ) →
            aux_lem_as_regularity_nc_estimate z r hr
              (cutoffPositiveCoefficient M H om N z hr) t alpha (K N om) := by
  obtain ⟨delta0, hdelta0, hCor⟩ := cor_neumann_source d hd E Pc Xc W D Cp t alpha
    k (fun i => 2 * ps i) ht1 ht2 ha0 ha1 (fun i => by linarith [hps i])
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta z r hr j hj
  obtain ⟨Kcor, Cb, hmem, hnorm, hcor⟩ := hCor M Rm Sreg It H hH hdelta
  let Ka : ℕ → BilateralField d → ℝ := fun N om => |Kcor N om|
  have hKa0 : ∀ N om, 0 ≤ Ka N om := fun N om => abs_nonneg _
  have hKamem : ∀ i N, MemLp (Ka N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure := by
    intro i N
    simpa only [Ka, Real.norm_eq_abs] using (hmem i N).norm
  have hKanorm : ∀ i N, eLpNorm (Ka N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal |Cb i| := by
    intro i N
    have heq : eLpNorm (Ka N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure =
        eLpNorm (Kcor N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure := by
      simpa only [Ka, Real.norm_eq_abs] using eLpNorm_norm (f := Kcor N)
        (p := ENNReal.ofReal (2 * ps i)) (μ := (chaosSampleLaw M).toMeasure) (hmem i N).aestronglyMeasurable
    rw [heq]
    exact (hnorm i N).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hcor' : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      aux_lem_as_regularity_nc_estimate (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        t alpha (Ka N om) := by
    filter_upwards [hcor] with om hom N
    exact aux_lem_as_regularity_nc_estimate_mono (le_abs_self _) (hom N)
  let m : ℤ := -j
  let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
  have hfac0 : 0 ≤ aux_lem_as_regularity_nc_factor d r t alpha := by
    unfold aux_lem_as_regularity_nc_factor
    positivity
  have hmom := fun i => aux_lem_as_regularity_nc_transport_moment hd M H hH w m
    (ps i) (aux_lem_as_regularity_nc_factor d r t alpha) |Cb i|
    (lt_of_lt_of_le zero_lt_one (hps i)) hfac0 (abs_nonneg _)
    Ka (hKamem i) (hKanorm i)
  choose Cref hCref hRef using hmom
  let K : ℕ → BilateralField d → ℝ := fun N om =>
    if m ≤ (N : ℤ) then aux_lem_as_regularity_nc_factor d r t alpha *
      Ka (((N : ℤ) - m).toNat) (aux_transport_S m w om) /
        aux_transport_reference M H N m w om else 0
  refine ⟨K, Cref, ?_, ?_, ?_, ?_⟩
  · intro N om
    dsimp [K]
    split_ifs
    · exact div_nonneg (mul_nonneg hfac0 (hKa0 _ _))
        (aux_transport_reference_pos M H N m w om).le
    · exact le_rfl
  · intro i N
    by_cases hN : m ≤ (N : ℤ)
    · simpa only [K, if_pos hN, ENNReal.ofReal_one] using (hRef i N hN).1
    · simpa only [K, if_neg hN] using (memLp_const (0 : ℝ) :
        MemLp (fun _ : BilateralField d => (0 : ℝ)) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure)
  · intro i N
    by_cases hN : m ≤ (N : ℤ)
    · simpa only [K, if_pos hN, ENNReal.ofReal_one] using (hRef i N hN).2
    · simp only [K, if_neg hN, eLpNorm_zero', zero_le]
  · have ht : 0 ≤ t := by
      have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hrm : r = (3 : ℝ) ^ (-m) := by simpa only [m, neg_neg] using hj
    have hEvent := fun (N : ℕ) (hN : m ≤ (N : ℤ)) =>
      aux_lem_as_regularity_nc_triadic_sample M H hH z m r hr hrm t alpha ht ha0.le
        Ka hKa0 hcor' N hN
    filter_upwards [(ae_all_iff.mpr fun N => ae_all_iff.mpr fun hN => hEvent N hN)]
      with om hom
    intro N hN
    have hN' : m ≤ (N : ℤ) := hN
    simpa only [K, if_pos hN', w] using hom N hN'





/-- The side `rho * 3^{-j}` of a depth-`j` cell of the `rho`-cube. -/
def aux_lem_as_regularity_macro_rho_side (rho : ℝ) (j : ℕ) : ℝ :=
  rho * aux_prop_growth_holder_macro_campanato_side j

theorem aux_lem_as_regularity_macro_rho_side_pos {rho : ℝ} (hrho : 0 < rho) (j : ℕ) :
    0 < aux_lem_as_regularity_macro_rho_side rho j :=
  mul_pos hrho (aux_prop_growth_holder_macro_campanato_side_pos j)

theorem aux_lem_as_regularity_macro_rho_side_mul_pow (rho : ℝ) (j : ℕ) :
    aux_lem_as_regularity_macro_rho_side rho j * (3 : ℝ) ^ j = rho := by
  unfold aux_lem_as_regularity_macro_rho_side
  rw [mul_assoc, aux_prop_growth_holder_macro_campanato_side_mul_pow, mul_one]

/-- The centre of the depth-`j` cell with index `k`, in the `rho`-cube centred at `0`. -/
def aux_lem_as_regularity_macro_rho_center {d : ℕ} (rho : ℝ) (j : ℕ) (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => aux_lem_as_regularity_macro_rho_side rho j * (k i : ℝ)

/-- The open depth-`j` cell with index `k`, in the `rho`-cube centred at `0`. -/
def aux_lem_as_regularity_macro_rho_cell {d : ℕ} (rho : ℝ) (j : ℕ) (k : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  ball (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j / 2)

theorem aux_lem_as_regularity_macro_rho_cell_measurable {d : ℕ} (rho : ℝ) (j : ℕ) (k : Fin d → ℤ) :
    MeasurableSet (aux_lem_as_regularity_macro_rho_cell (d := d) rho j k) := measurableSet_ball

/-- **Admissible cells of the `rho`-scaled system fit inside the `rho`-cube**, via the SAME
admissibility predicate `aux_prop_growth_holder_macro_campanato_Adm` used for the unit cube (the
`rho` factor cancels, see the header comment). Proved via the coordinatewise `Ioo` description of
both cubes (`centeredCube_eq_pi`), avoiding any ball-subset lemma name dependency. -/
theorem aux_lem_as_regularity_macro_rho_cell_sub {d : ℕ} {rho : ℝ} (hrho : 0 < rho) {j : ℕ} {k : Fin d → ℤ}
    (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_lem_as_regularity_macro_rho_cell rho j k ⊆
      (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)) := by
  have hside0 : 0 < aux_prop_growth_holder_macro_campanato_side j :=
    aux_prop_growth_holder_macro_campanato_side_pos j
  have hhalf : 0 < aux_lem_as_regularity_macro_rho_side rho j / 2 := by
    have := aux_lem_as_regularity_macro_rho_side_pos hrho j; linarith
  rw [centeredCube_eq_pi]
  intro x hx0
  have hx : x ∈ ball (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j / 2) := hx0
  rw [mem_ball, dist_pi_lt_iff hhalf] at hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  intro i
  have hxi : dist (x i) (aux_lem_as_regularity_macro_rho_center rho j k i) < aux_lem_as_regularity_macro_rho_side rho j / 2 := hx i
  rw [Real.dist_eq] at hxi
  have hcenter : aux_lem_as_regularity_macro_rho_center rho j k i = aux_lem_as_regularity_macro_rho_side rho j * (k i : ℝ) := rfl
  have hk' : (2 * |k i| + 1 : ℤ) ≤ (3 : ℤ) ^ j := hk i
  have hk'' : (2 * |(k i : ℝ)| + 1 : ℝ) ≤ (3 : ℝ) ^ j := by exact_mod_cast hk'
  have hAdm : aux_prop_growth_holder_macro_campanato_side j * (2 * |(k i : ℝ)| + 1) ≤ 1 := by
    have h3 : (aux_prop_growth_holder_macro_campanato_side j) * (3 : ℝ) ^ j = 1 :=
      aux_prop_growth_holder_macro_campanato_side_mul_pow j
    nlinarith [mul_le_mul_of_nonneg_left hk'' hside0.le]
  have hbound : rho * aux_prop_growth_holder_macro_campanato_side j *
      (2 * |(k i : ℝ)| + 1) ≤ rho := by
    have := mul_le_mul_of_nonneg_left hAdm hrho.le
    linarith [this]
  have habs : |x i - aux_lem_as_regularity_macro_rho_center rho j k i| < aux_lem_as_regularity_macro_rho_side rho j / 2 := hxi
  rw [hcenter] at habs
  have habs1 := (abs_lt.mp habs).1
  have habs2 := (abs_lt.mp habs).2
  have hknn : -|(k i : ℝ)| ≤ (k i : ℝ) := neg_abs_le (k i : ℝ)
  have hkle : (k i : ℝ) ≤ |(k i : ℝ)| := le_abs_self (k i : ℝ)
  unfold aux_lem_as_regularity_macro_rho_side at habs1 habs2 hbound
  simp only [Pi.zero_apply]
  constructor <;> nlinarith [habs1, habs2, hbound, hknn, hkle]




/-- `rho * 3^{-j} * 3^{-m} = rho * 3^{-(j+m)}`, the `rho`-scaled analogue of
`aux_cor_neumann_source_side_mul`. -/
theorem aux_lem_as_regularity_macro_rho_side_mul (rho : ℝ) (j m : ℕ) :
    aux_lem_as_regularity_macro_rho_side rho j * (3 : ℝ) ^ (-(m : ℤ)) = rho * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by
  unfold aux_lem_as_regularity_macro_rho_side
  have h := aux_cor_neumann_source_side_mul j m
  calc rho * aux_prop_growth_holder_macro_campanato_side j * (3 : ℝ) ^ (-(m : ℤ))
      = rho * (aux_prop_growth_holder_macro_campanato_side j * (3 : ℝ) ^ (-(m : ℤ))) := by ring
    _ = rho * (1 * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ))) := by rw [h]
    _ = rho * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by ring

/-- The `rho`-scaled analogue of `aux_cor_neumann_source_center_eq`: the depth-`m` descendant
centre of an admissible depth-`j` cell of the `rho`-cube (centred at `0`) coincides with the
depth-`(j+m)` descendant centre of the `rho`-cube itself. -/
theorem aux_lem_as_regularity_macro_rho_center_eq {d : ℕ} (rho : ℝ) (j m : ℕ) (k v : Fin d → ℤ) :
    aux_lem_as_coarse_ms_cellCenter (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j) m v =
      aux_lem_as_coarse_ms_cellCenter (0 : SpatialCoordinates d) rho (j + m)
        (fun i => 3 ^ m * k i + v i) := by
  funext i
  simp only [aux_lem_as_coarse_ms_cellCenter, aux_lem_as_regularity_macro_rho_center, aux_lem_as_regularity_macro_rho_side,
    aux_prop_growth_holder_macro_campanato_side, Pi.zero_apply, zero_add,
    zpow_neg, zpow_natCast, pow_add]
  push_cast
  have h3j : ((3 : ℝ) ^ j) ≠ 0 := by positivity
  have h3m : ((3 : ℝ) ^ m) ≠ 0 := by positivity
  field_simp

/-- **Chart domination, `rho`-native.** The depth-`m` descendant maximum of `|σ_*⁻¹|` in the
chart of an admissible depth-`j` cell of the `rho`-cube (centred at `0`) is at most the
depth-`(j+m)` descendant maximum in the `rho`-cube's own root chart. Exact port of
`aux_cor_neumann_source_chart_dom` with `((1/2,...), 1, one_pos)` replaced by `(0, rho, hrho)`
throughout and `aux_lem_as_regularity_macro_rho_center_eq`/`_side_mul` in place of the unit versions. -/
theorem aux_lem_as_regularity_macro_rho_chart_dom {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (rho : ℝ) (hrho : 0 < rho)
    (j m : ℕ) (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(m : ℤ))
        (E.chart (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j)
          (aux_lem_as_regularity_macro_rho_side_pos hrho j)
          (cutoffPositiveCoefficient M H om N
            (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side_pos hrho j))
          (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j)) ≤
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-((j + m : ℕ) : ℤ))
        (E.chart (0 : SpatialCoordinates d) rho hrho
          (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
          (0 : SpatialCoordinates d) rho) := by
  set c := aux_lem_as_regularity_macro_rho_center rho j k with hc
  set s := aux_lem_as_regularity_macro_rho_side rho j with hs
  have hs0 : 0 < s := aux_lem_as_regularity_macro_rho_side_pos hrho j
  have hne : (Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      (-(m : ℤ))).Nonempty :=
    Homogenization.descendantsAtScale_nonempty _ (by simp [Homogenization.originCube])
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    Homogenization.Book.Ch02.finsetSupReal
  refine csSup_le ?_ ?_
  · obtain ⟨R, hR⟩ := hne
    exact ⟨_, R, hR, rfl⟩
  rintro _ ⟨R', hR', rfl⟩
  have hsc : (Homogenization.originCube d 0).scale - (m : ℤ) = -(m : ℤ) := by
    simp [Homogenization.originCube]
  have hR'' : R' ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (m : ℤ)) := by rw [hsc]; exact hR'
  have ht1 := (aux_lem_as_coarse_ms_chart_transport E M H om N c s hs0 m hR'').2
  have hRmem := aux_cor_neumann_source_desc_compose hk hR'
  set R : Homogenization.TriadicCube d :=
    ⟨-((j + m : ℕ) : ℤ), fun i => 3 ^ m * k i + R'.index i⟩ with hRdef
  have ht2 := (aux_lem_as_coarse_ms_chart_transport E M H om N (0 : SpatialCoordinates d) rho hrho
    (j + m) hRmem).2
  have hw : aux_lem_as_coarse_ms_cellCenter c s m R'.index =
      aux_lem_as_coarse_ms_cellCenter (0 : SpatialCoordinates d) rho (j + m) R.index :=
    aux_lem_as_regularity_macro_rho_center_eq rho j m k R'.index
  have hrr : s * (3 : ℝ) ^ (-(m : ℤ)) = rho * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) :=
    aux_lem_as_regularity_macro_rho_side_mul rho j m
  have hr1 : 0 < s * (3 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hr2 : 0 < rho * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by positivity
  have hsub1 := aux_lem_as_coarse_ms_cell_sub c s hs0 m hR'' hr1
  have hsub2 := aux_lem_as_coarse_ms_cell_sub (0 : SpatialCoordinates d) rho hrho (j + m) hRmem hr2
  rw [aux_cor_neumann_source_cube_congr hr1 hr2 hw hrr] at hsub1
  have hcross := aux_cor_neumann_source_sigma_cross E M H om N c s hs0
    (0 : SpatialCoordinates d) rho hrho _ _ hr2 hsub1 hsub2
  have hRmem' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      (-((j + m : ℕ) : ℤ)) := by
    have : (Homogenization.originCube d 0).scale - ((j + m : ℕ) : ℤ) = -((j + m : ℕ) : ℤ) := by
      simp [Homogenization.originCube]
    rw [← this]; exact hRmem
  calc Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R'
        (E.chart c s hs0 (cutoffPositiveCoefficient M H om N c hs0) c s)
      = _ := ht1
    _ = _ := by rw [hw, hrr]; exact hcross
    _ = _ := ht2.symm
    _ ≤ _ := Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
          _ hRmem'




/-- `aux_cor_neumann_source_weight_term`'s `rho`-scaled analogue: the unit-scale bound already
carries an extra factor `rho ^ e ≤ 1` (`0 < rho ≤ 1`, `e > 0`), which only tightens the estimate. -/
theorem aux_lem_as_regularity_macro_rho_weight_term (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (e e' : ℝ) (j m : ℕ) (he' : 0 < e') (hee : e' ≤ e) (he1 : e' ≤ 1) (y : ℝ) (hy : 0 ≤ y) :
    aux_lem_as_regularity_macro_rho_side rho j ^ e *
        (Homogenization.Book.Ch02.geometricWeight 1 1 m * y) ≤
      ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
        (Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) * y) := by
  have he : 0 < e := lt_of_lt_of_le he' hee
  have horig := aux_cor_neumann_source_weight_term e e' j m he' hee he1 y hy
  have hrhoe : rho ^ e ≤ 1 := Real.rpow_le_one hrho0.le hrho1 he.le
  have hrhoe0 : 0 ≤ rho ^ e := Real.rpow_nonneg hrho0.le e
  unfold aux_lem_as_regularity_macro_rho_side
  rw [Real.mul_rpow hrho0.le (aux_prop_growth_holder_macro_campanato_side_pos j).le]
  have hRHSnn : 0 ≤ ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
      (Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) * y) := by
    have h1 : 0 ≤ Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) :=
      (aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 (m + j)
    have h2 : (0:ℝ) ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) := by
      have hq1 : (3 : ℝ) ^ (-e') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hc1 : (0:ℝ) ≤ 1 - (3 : ℝ) ^ (-(1 : ℝ)) := by
        have : (3 : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
        linarith
      exact div_nonneg hc1 (by linarith)
    exact mul_nonneg h2 (mul_nonneg h1 hy)
  calc rho ^ e * aux_prop_growth_holder_macro_campanato_side j ^ e *
        (Homogenization.Book.Ch02.geometricWeight 1 1 m * y)
      = rho ^ e * (aux_prop_growth_holder_macro_campanato_side j ^ e *
          (Homogenization.Book.Ch02.geometricWeight 1 1 m * y)) := by ring
    _ ≤ rho ^ e * (((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
          (Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) * y)) :=
        mul_le_mul_of_nonneg_left horig hrhoe0
    _ ≤ 1 * (((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
          (Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) * y)) :=
        mul_le_mul_of_nonneg_right hrhoe hRHSnn
    _ = ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
          (Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) * y) := by ring

/-- **Cell ellipticity bound, `rho`-native.** For an admissible depth-`j` cell of the `rho`-cube
(centred at `0`), `side_j^e λ_{1,1}⁻¹` of the cell's own chart is dominated by the `rho`-cube's own
root discounted series. Exact port of `aux_cor_neumann_source_lam_cell`. -/
theorem aux_lem_as_regularity_macro_rho_lam_cell {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (j : ℕ) (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    (e e' : ℝ) (he' : 0 < e') (hee : e' ≤ e) (he1 : e' ≤ 1)
    (hsum : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (0 : SpatialCoordinates d) rho hrho
          (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
          (0 : SpatialCoordinates d) rho))) :
    aux_lem_as_regularity_macro_rho_side rho j ^ e *
        (E.lam (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j)
          (aux_lem_as_regularity_macro_rho_side_pos hrho j)
          (cutoffPositiveCoefficient M H om N
            (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side_pos hrho j))
          (aux_lem_as_regularity_macro_rho_center rho j k) (aux_lem_as_regularity_macro_rho_side rho j) 1 1)⁻¹ ≤
      ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
        ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
          Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            (Homogenization.originCube d 0) (-(n : ℤ))
            (E.chart (0 : SpatialCoordinates d) rho hrho
              (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
              (0 : SpatialCoordinates d) rho) := by
  set c := aux_lem_as_regularity_macro_rho_center rho j k with hc
  set s := aux_lem_as_regularity_macro_rho_side rho j with hsdef
  have hs0 : 0 < s := aux_lem_as_regularity_macro_rho_side_pos hrho j
  obtain ⟨Ssum, _hS0, hsq, hSeq, hinv⟩ := aux_lane4_lambda_inv_moments_lam_inv_eq E c s hs0
    (cutoffPositiveCoefficient M H om N c hs0) 1 one_pos le_rfl
  set YT : ℕ → ℝ := fun m => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    (Homogenization.originCube d 0) (-(m : ℤ))
    (E.chart c s hs0 (cutoffPositiveCoefficient M H om N c hs0) c s) with hYT
  set Y : ℕ → ℝ := fun n => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    (Homogenization.originCube d 0) (-(n : ℤ))
    (E.chart (0 : SpatialCoordinates d) rho hrho
      (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
      (0 : SpatialCoordinates d) rho) with hY
  set w1 : ℕ → ℝ := Homogenization.Book.Ch02.geometricWeight 1 1 with hw1def
  set w' : ℕ → ℝ := Homogenization.Book.Ch02.geometricWeight e' 1 with hw'def
  set Cg : ℝ := (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) with hCg
  have hYT0 : ∀ m, 0 ≤ YT m := fun m => aux_lane4_lambda_inv_moments_Y_nonneg _ _
  have hY0 : ∀ n, 0 ≤ Y n := fun n => aux_lane4_lambda_inv_moments_Y_nonneg _ _
  have hdom : ∀ m, YT m ≤ Y (m + j) := fun m => by
    rw [add_comm m j]; exact aux_lem_as_regularity_macro_rho_chart_dom E M H om N rho hrho j m k hk
  have hw1 : ∀ m, 0 ≤ w1 m := (aux_lane4_lambda_inv_moments_weight_sum 1 one_pos).2.2
  have hsp : 0 < s ^ e := Real.rpow_pos_of_pos hs0 e
  have hq1 : (3 : ℝ) ^ (-e') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hCg0 : 0 ≤ Cg := by
    have : (3 : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact div_nonneg (by linarith) (by linarith)
  have hterm : ∀ m, s ^ e * (w1 m * Y (m + j)) ≤ Cg * (w' (m + j) * Y (m + j)) := fun m =>
    aux_lem_as_regularity_macro_rho_weight_term rho hrho hrho1 e e' j m he' hee he1 (Y (m + j)) (hY0 _)
  have hshift : Summable (fun m => w' (m + j) * Y (m + j)) := (summable_nat_add_iff j).mpr hsum
  have hsumA : Summable (fun m => w1 m * Y (m + j)) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hw1 m) (hY0 _)) (fun m => ?_)
      (hshift.mul_left (Cg / s ^ e))
    have h := hterm m
    rw [div_mul_eq_mul_div, le_div_iff₀ hsp]
    linarith
  have hsumT : Summable (fun m => w1 m * YT m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hw1 m) (hYT0 m))
      (fun m => mul_le_mul_of_nonneg_left (hdom m) (hw1 m)) hsumA
  have hcs := aux_lane4_lambda_inv_moments_cs one_pos 0 YT hYT0 (by simpa using hsq)
    (by simpa using hsumT)
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.add_zero] at hcs
  have hshift_le : ∑' m, w' (m + j) * Y (m + j) ≤ ∑' n, w' n * Y n := by
    rw [← hsum.sum_add_tsum_nat_add j]
    have : 0 ≤ ∑ i ∈ Finset.range j, w' i * Y i :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 i) (hY0 i)
    linarith
  calc s ^ e * (E.lam c s hs0 (cutoffPositiveCoefficient M H om N c hs0) c s 1 1)⁻¹
      = s ^ e * Ssum ^ 2 := by rw [hinv]
    _ ≤ s ^ e * ∑' m, w1 m * YT m := by
        rw [hSeq]; exact mul_le_mul_of_nonneg_left hcs hsp.le
    _ ≤ s ^ e * ∑' m, w1 m * Y (m + j) :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum
          (fun m => mul_le_mul_of_nonneg_left (hdom m) (hw1 m)) hsumT hsumA) hsp.le
    _ = ∑' m, s ^ e * (w1 m * Y (m + j)) := tsum_mul_left.symm
    _ ≤ ∑' m, Cg * (w' (m + j) * Y (m + j)) :=
        Summable.tsum_le_tsum hterm (hsumA.mul_left _) (hshift.mul_left _)
    _ = Cg * ∑' m, w' (m + j) * Y (m + j) := tsum_mul_left
    _ ≤ Cg * ∑' n, w' n * Y n := mul_le_mul_of_nonneg_left hshift_le hCg0




/-- **Uniform-in-`N` moments of the `rho`-cube's own root discounted series**, `rho`-native
analogue of `aux_cor_neumann_source_Z_moments`. -/
theorem aux_lem_as_regularity_macro_rho_Z_moments (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (e' Q : ℝ) (he' : 0 < e') (hQ1 : 1 ≤ Q) (hDQ : 2 * (d : ℝ) ≤ e' * Q)
    :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (rho : ℝ) (hrho : 0 < rho), rho ≤ 1 →
        ∃ CZ : ℝ, ∀ N : ℕ,
          MemLp (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(n : ℤ))
                (E.chart (0 : SpatialCoordinates d) rho hrho
                  (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
                  (0 : SpatialCoordinates d) rho))
            (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(n : ℤ))
                (E.chart (0 : SpatialCoordinates d) rho hrho
                  (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
                  (0 : SpatialCoordinates d) rho))
            (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CZ ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(n : ℤ))
                (E.chart (0 : SpatialCoordinates d) rho hrho
                  (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
                  (0 : SpatialCoordinates d) rho)) := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  obtain ⟨deltaQ, Cd, hdQ, hCd, hmain⟩ := lane4_lambda_inv_cell_moment d hd E Q hQ1
  set dA : ℝ := Real.sqrt (e' * Real.log 3 / (4 * (Cd * (Q + Q ^ 2)) + 4)) with hdA
  set dB : ℝ := min 1 (e' * Real.log 3 / (2 * Cd + 1)) with hdB
  have hQ2 : 0 < Q + Q ^ 2 := by positivity
  have hdA0 : 0 < dA := Real.sqrt_pos.2 (div_pos (mul_pos he' hlog3pos) (by positivity))
  have hdB0 : 0 < dB := lt_min one_pos (div_pos (mul_pos he' hlog3pos) (by linarith))
  refine ⟨min deltaQ (min dA dB), lt_min hdQ (lt_min hdA0 hdB0), ?_⟩
  intro M Rm H hH hδ rho hrho hrho1
  have hδQ : M.delta ≤ deltaQ := hδ.trans (min_le_left _ _)
  have hδA : M.delta ≤ dA := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδB : M.delta ≤ dB := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ0 : 0 ≤ M.delta := (M.shellPrefix.delta_pos).le
  have hδ1 : M.delta ≤ 1 := hδB.trans (min_le_left _ _)
  have hδZ : M.delta ≤ e' * Real.log 3 / (2 * Cd + 1) := hδB.trans (min_le_right _ _)
  have hdl2 : M.delta ^ 2 ≤ e' * Real.log 3 / (4 * (Cd * (Q + Q ^ 2)) + 4) := by
    have h := pow_le_pow_left₀ hδ0 hδA 2
    rwa [hdA, Real.sq_sqrt (div_nonneg (mul_nonneg he'.le hlog3pos.le) (by positivity))] at h
  have hcondA : Cd * (Q + Q ^ 2) * M.delta ^ 2 ≤ (e' / 4) * Real.log 3 := by
    have := aux_lane4_lambda_inv_moments_condA_helper (Cd * (Q + Q ^ 2)) (e' * Real.log 3)
      (M.delta ^ 2) (by positivity) (by positivity) (sq_nonneg _) hdl2
    linarith
  have hcondB : Cd * M.delta * (1 + M.delta) ≤ e' * Real.log 3 :=
    aux_lane4_lambda_inv_moments_condB_helper Cd (e' * Real.log 3) M.delta hCd.le
      (by positivity) hδ1 hδ0 hδZ
  obtain ⟨Cq, hCq, hcb⟩ := hmain M Rm H hH (0 : SpatialCoordinates d) rho hrho hrho1 hδQ
  refine ⟨(1 - (3 : ℝ) ^ (-e')) * Cq /
      (1 - Real.exp (-(e' / 2) * Real.log 3 + Cd * (Q + Q ^ 2) * M.delta ^ 2)) +
    (1 - (3 : ℝ) ^ (-e')) * Cq * (3 : ℝ) ^ (-e') / (1 - (3 : ℝ) ^ (-e')), fun N => ?_⟩
  obtain ⟨h1, h2, h3⟩ := aux_lane4_lambda_inv_moments_series_bound (chaosSampleLaw M).toMeasure
    e' (d : ℝ) Q Cd Cq M.delta N he' (Nat.cast_nonneg d) hDQ hQ1 hCd hCq hδ0 hcondA hcondB
    (fun n om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ))
      (E.chart (0 : SpatialCoordinates d) rho hrho
        (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
        (0 : SpatialCoordinates d) rho))
    (fun n om => aux_lane4_lambda_inv_moments_Y_nonneg _ _) (fun n => (hcb N n).1)
    (fun n => (hcb N n).2)
  exact ⟨h1, h2, h3⟩


/-- Below-wavelength energy estimates with the actual requested exponent. This
is the fscc microscopic argument with its fixed exponent replaced by t. -/
theorem aux_lem_as_regularity_nc_small_energy {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hrJ : (3 : ℝ) ^ J * r ≤ 1)
    (Mxv Dv : ℝ) (hMx : 0 < Mxv) (hDv : 0 ≤ Dv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient model H om J x ∧ cutoffCoefficient model H om J x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient model H om J x) - Real.log (cutoffCoefficient model H om J y)| ≤
        Dv * (3 : ℝ) ^ J * dist x y)
    (C c p1 t1 : ℝ) (hC : 0 < C) (t : ℝ) (ht0 : 0 ≤ t)
    (hbig : let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) (rr : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rr / 2} ∩
          (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * rr ^ t)) :
    0 ≤ r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
          ((1 + Dv) ^ t * P.C ^ 2 *
            (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ + Mxv) +
        r ^ ((d : ℝ) + 2) * P.C ^ 2 *
          (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ *
          ((2 : ℝ) / r) ^ t ∧
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient model H om J z hr) F v →
        ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
          localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
            (r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
                ((1 + Dv) ^ t * P.C ^ 2 *
                  (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ + Mxv) +
              r ^ ((d : ℝ) + 2) * P.C ^ 2 *
                (E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1)⁻¹ *
                ((2 : ℝ) / r) ^ t) * Kf ^ 2 * rad ^ t := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨a1, ha1, -, hNeuTransport⟩ := lem_as_regularity_affine_transport d model H om J z r hr
  obtain ⟨A1, hA1ae, hAK, hlog1⟩ := aux_prop_growth_energy_assembly_unit_coeff model H om J z r hr
    Dv Mxv 1 hDv (by simpa using hrJ) henv hlip
  have haA1 : (a1 : PositiveCoefficient (unitNeumannCube d)).val
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A1 := hA1ae a1 ha1
  set lam1 : ℝ := E.lam (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos a1
    (fun _ : Fin d => (1 / 2 : ℝ)) 1 1 1 with hlam1def
  have hlamEq : lam1 = E.lam z r hr (cutoffPositiveCoefficient model H om J z hr) z r 1 1 :=
    (E.lam_dilation z r hr (cutoffPositiveCoefficient model H om J z hr)
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos a1 ha1 1 1).symm
  clear ha1 hA1ae
  have hMxv0 : 0 ≤ Mxv := hMx.le
  have hMxvi0 : 0 < Mxv⁻¹ := inv_pos.mpr hMx
  have hlam1pos : 0 < lam1 := E.lam_pos _ _ _ _ _ _ _ _
  have hlam1i0 : 0 ≤ lam1⁻¹ := (inv_pos.mpr hlam1pos).le
  have h2rt0 : 0 ≤ ((2 : ℝ) / r) ^ t := Real.rpow_nonneg (by positivity) _
  have hDvt0 : 0 ≤ (1 + Dv) ^ t := Real.rpow_nonneg (by linarith) _
  obtain ⟨K1, hK1def⟩ : ∃ K : ℝ, K = r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
      ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv) := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K : ℝ, K = r ^ ((d : ℝ) + 2) * P.C ^ 2 * lam1⁻¹ * ((2 : ℝ) / r) ^ t :=
    ⟨_, rfl⟩
  have hrdpos : 0 ≤ r ^ ((d : ℝ) + 2) := Real.rpow_nonneg hr.le _
  have hPC2 : 0 ≤ P.C ^ 2 := sq_nonneg _
  have hK10 : 0 ≤ K1 := by
    rw [hK1def]
    have hinner : 0 ≤ (1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv :=
      add_nonneg (mul_nonneg (mul_nonneg hDvt0 hPC2) hlam1i0) hMxv0
    exact mul_nonneg (mul_nonneg (mul_nonneg hrdpos hC.le) h2rt0) hinner
  have hK20 : 0 ≤ K2 := by
    rw [hK2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hrdpos hPC2) hlam1i0) h2rt0
  rw [← hlamEq, ← hK1def, ← hK2def]
  refine ⟨add_nonneg hK10 hK20, ?_⟩
  intro F Kf hKf hFm hFb hmean v hsol x hx rad hrad hradr
  obtain ⟨F1, v1, hF1eq, hF1m, hF1b, hF1mean, hsolve1, hv1val, hv1grad, henergyid⟩ :=
    hNeuTransport F Kf hKf hFm hFb hmean v hsol
  clear hNeuTransport hv1val
  obtain ⟨Kmac1, hKmac1def⟩ : ∃ K : ℝ, K = sobolevCoefficientForm a1
      (v1 : SobolevData (unitNeumannCube d)) (v1 : SobolevData (unitNeumannCube d)) :=
    ⟨_, rfl⟩
  have hKmac1nonneg : 0 ≤ Kmac1 := by
    rw [hKmac1def]; exact sobolevCoefficientForm_nonneg a1 _
  have hKmac1bound : Kmac1 ≤ (r ^ 2 * Kf) ^ 2 * P.C ^ 2 * lam1⁻¹ := by
    rw [hKmac1def, hlam1def]
    exact aux_cor_neumann_source_global_energy_ae hd E P a1 F1 hF1m (r ^ 2 * Kf)
      (by positivity) hF1b v1 hsolve1
  -- x1 : the preimage of x on the unit cube
  obtain ⟨x1, hx1def⟩ : ∃ y : SpatialCoordinates d, y = cubeDilation (fun _ : Fin d => (1/2:ℝ)) z r⁻¹ x := ⟨_, rfl⟩
  have hTx1 : cubeDilation z (fun _ : Fin d => (1/2:ℝ)) r x1 = x := by
    rw [hx1def]; exact aux_prop_growth_energy_assembly_dilation_inv z (fun _ : Fin d => (1/2:ℝ)) hr x
  have hx1 : x1 ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    have hpre := cubeDilation_preimage_centeredCube z (fun _ : Fin d => (1/2:ℝ)) hr one_pos
    change x1 ∈ (centeredCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d))
    rw [← hpre, Set.mem_preimage, hTx1]
    exact hx
  -- global-scale instance of the transport energy identity
  have hglobal := aux_fscc_holNeuH_hSmall_global model H om J z r hr a1 v1 v x x1 hx hx1 hTx1
    Kmac1 hKmac1def henergyid
  by_cases hcase : rad ≤ r / 2
  · -- micro case: transport, clamp, apply rem_resolved_microscopic's Neumann conjunct
    obtain ⟨f1, hf1m, hf1b, hf1eq⟩ := aux_prop_growth_energy_assembly_clamp
      (unitNeumannCube d : Set (SpatialCoordinates d)) F1 hF1m (r ^ 2 * Kf) (by positivity) hF1b
    have hsolve1' : SolvesNeumann a1 f1 v1 :=
      aux_fscc_holNeuH_solvesNeumann_congr hf1eq hsolve1
    have hDNnn : (0 : ℝ) ≤ Dv := hDv
    have h1DN : (0 : ℝ) < Mxv⁻¹ := hMxvi0
    have hf1b' : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f1 y| ≤ r ^ 2 * Kf :=
      fun y _ => hf1b y
    have hcl := hbig 1 one_pos le_rfl a1 A1 haA1 Dv Mxv⁻¹ Mxv hDNnn h1DN hAK
      (by simpa using hlog1) f1 hf1m (r ^ 2 * Kf) (by positivity) hf1b'
    have hclN := (hcl v1 hsolve1').2
    clear hbig hcl
    have hprecond : ∀ x1' ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x1' i| < C * 1 / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
          A1 y * ∑ i : Fin d, ((v1 : SobolevData (unitNeumannCube d)).2 i y) ^ 2) ≤
          Kmac1 * (1 : ℝ) ^ t1 := by
      intro x1' hx1'
      simp only [mul_one, Real.one_rpow]
      rw [aux_prop_growth_energy_assembly_gamma_eq a1 A1 haA1 (v1 : SobolevData (unitNeumannCube d))
        x1' (by positivity : (0:ℝ) < C)]
      calc localGradientEnergy a1
            (s := Metric.ball x1' (C / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
          ≤ (weightedGradientForm (a1 : PositiveCoefficient (unitNeumannCube d)).val)
              (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
              (sobolevGradient (v1 : SobolevData (unitNeumannCube d))) :=
            localGradientEnergy_le a1 _ _
        _ = Kmac1 := hKmac1def ▸ rfl
    have hr' : (0 : ℝ) < 2 * rad / r := by positivity
    have hr'1 : 2 * rad / r ≤ 1 := by
      rw [div_le_one hr]; linarith
    have hfin := hclN Kmac1 hKmac1nonneg x1 hx1 (hprecond x1 hx1) (2 * rad / r) hr' hr'1
    clear hclN hprecond hr'1 hf1b' hsolve1' hf1eq hf1b hf1m f1 hDNnn h1DN
    beta_reduce at hfin
    rw [aux_prop_growth_energy_assembly_gamma_eq a1 A1 haA1 (v1 : SobolevData (unitNeumannCube d))
      x1 (show (0:ℝ) < 2 * rad / r from hr')] at hfin
    clear hr'
    simp only [Real.one_rpow, mul_one] at hfin
    have hballeq : Metric.ball x1 (2 * rad / r / 2) ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)) =
        Metric.ball x1 (rad / r) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
      have : (2 * rad / r / 2 : ℝ) = rad / r := by ring
      rw [this]
    have heq3 := aux_prop_growth_energy_assembly_lge_congr a1
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      hballeq (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
    rw [heq3] at hfin
    clear heq3 hballeq A1 haA1 hAK hlog1 hx1 hglobal
    clear c p1 t1 ht0 hd2 hd0 henv hlip hMx hrJ
    clear hMxv0 hMxvi0 hlam1pos hlam1i0 h2rt0 hK10 hrdpos hPC2 hK2def
    clear hF1eq hF1m hF1b hF1mean hsolve1 hv1grad
    clear hKf hFm hFb hmean hsol hx hradr F
    clear hKmac1def hKmac1nonneg hx1def hcase
    have hK2nn : 0 ≤ K2 * Kf ^ 2 * rad ^ t :=
      mul_nonneg (mul_nonneg hK20 (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le t)
    refine (aux_fscc_holNeuH_hSmall_micro_finish hd E P model H om J z r hr Dv Mxv C t lam1
      hC hDvt0 a1 v1 v Kmac1 Kf rad hrad hKmac1bound x x1 hTx1 K1 hK1def hfin henergyid).trans ?_
    have heq : (K1 + K2) * Kf ^ 2 * rad ^ t = K1 * Kf ^ 2 * rad ^ t + K2 * Kf ^ 2 * rad ^ t := by
      ring
    rw [heq]
    exact le_add_of_nonneg_right hK2nn
  · -- large-radius case: trivial monotonicity against the global energy
    have hradr2 : r / 2 < rad := lt_of_not_ge hcase
    exact aux_fscc_holNeuH_hSmall_large_finish model H om J z r hr v t ht0 P.C lam1 hlam1pos
      K1 K2 Kmac1 Kf rad hK10 hK2def hKmac1bound hglobal x hrad hradr2


theorem aux_lem_as_regularity_nc_small_constants (d : ℕ) (hd : 2 ≤ d) (W : SmallPerturbationInput d)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) :
    ∃ C c p1 t1 : ℝ, 0 < C ∧
      (let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := aux_fscc_holNeuH_ell c eps DN
      let gamma := aux_fscc_holNeuH_gamma A
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * rr ^ t)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨p1, hp1, hp1t⟩ := aux_prop_growth_energy_assembly_p1_choice d hd t htd
  set t1 : ℝ := (t + (d : ℝ)) / 2 with ht1def
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1def]; linarith
  obtain ⟨C, c, hC, hc, hc16, hbig, -⟩ :=
    rem_resolved_microscopic d hd W p1 t t1 hp1 ht htt1 ht1d hp1t
  refine ⟨C, c, p1, t1, hC, ?_⟩
  intro q1 eps heps heps1 a A hA DN mN MN hDN hmN hbnd hlp f hf Kf hKf hfb
  exact (hbig eps heps heps1 a A hA DN mN MN hDN hmN hbnd hlp f hf Kf hKf hfb).2.1

theorem aux_lem_as_regularity_nc_small_campanato {d : ℕ} (Cpo : ℝ) (hCpo : 0 ≤ Cpo)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cpo * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (t alpha e : ℝ) (he : 0 ≤ e) (hexp : 2 + t = 2 * alpha + d + e)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (Mx : ℝ) (hMx : 0 ≤ Mx)
    (hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * a.val y)
    (v : meanZeroSobolevGraph (centeredCube z r hr)) (K Kf : ℝ) (hK0 : 0 ≤ K) (hKf : 0 ≤ Kf)
    (hen : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
      localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
        K * Kf ^ 2 * rad ^ t) :
    ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
      ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube z r hr)).1 y - setAverage
            (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (v : SobolevData (centeredCube z r hr)).1) ^ 2
          ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        ((1 + Cpo) * (Mx + K) * r ^ (e / 2) * Kf) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  intro x hx rad hrad hradr
  set u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨(v : SobolevData (centeredCube z r hr)),
      ((mem_meanZeroSobolevGraph_iff (v : SobolevData (centeredCube z r hr))).mp v.property).1⟩
    with hudef
  have huval : (u : SobolevData (centeredCube z r hr)) = (v : SobolevData (centeredCube z r hr)) :=
    rfl
  have hpw := aux_prop_growth_holder_micro_campanato_pathwise Cpo hCpo hPoinc z hr a Mx hMx hlow u
    rad (K * Kf ^ 2 * rad ^ t) hrad
    (fun c hc => by rw [huval]; exact hen c hc rad hrad hradr) x hx
  rw [huval] at hpw
  have hV : rad ^ d ≤
      volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    aux_prop_growth_holder_micro_campanato_volume_ge z x hrad (by linarith) hx
  have hres := aux_prop_growth_holder_micro_campanato_final_alg d Cpo Mx K Kf rad r
    (volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))))
    t alpha e _
    hCpo hMx hrad hradr he hexp hV hpw
  rwa [abs_of_nonneg hK0] at hres


/-- Mean zero controls the supremum as well as the seminorm on a cube of side
at most one. The average is normalized by the actual cube volume. -/
theorem aux_lem_as_regularity_nc_mean_zero_norm {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (alpha B : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ) (hUc : Continuous U)
    (hUH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    (hUae : ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hB : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ B) :
    cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ (2 + Real.sqrt d) * B := by
  have hmean : ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
    rw [integral_congr_ae hUae.symm]
    exact ((mem_meanZeroSobolevGraph_iff (v : SobolevData (centeredCube z r hr))).mp v.property).2
  have hUint : IntegrableOn U (centeredCube z r hr : Set (SpatialCoordinates d)) volume :=
    (hUc.locallyIntegrable.integrableOn_isCompact (closedCube z r hr).isCompact).mono_set
      (centeredCube_subset_closedCube z hr)
  have hfin : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  let S := holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U
  have hS0 : 0 ≤ S := aux_prop_growth_holder_assembly_seminorm_nonneg _ _ _
  have hsup : sSup {b : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), b = |U x|} ≤
      (1 + Real.sqrt d) * S := by
    apply Real.sSup_le _ (mul_nonneg (by positivity) hS0)
    rintro b ⟨x, hx, rfl⟩
    have h := aux_in_deterministic_regularity_avg_sub_const_le hfin
      (centeredCube_volume_pos z hr) hUint (U x) ((1 + Real.sqrt d) * S)
      (fun y hy => aux_prop_growth_holder_assembly_increment z hr hr1 ha ha1 hUH
        (centeredCube_subset_closedCube z hr hy) hx)
    simpa only [hmean, mul_zero, zero_sub, abs_neg] using h
  calc cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U
      ≤ (1 + Real.sqrt d) * S + S := add_le_add hsup (le_refl S)
    _ = (2 + Real.sqrt d) * S := by ring
    _ ≤ (2 + Real.sqrt d) * B := mul_le_mul_of_nonneg_left hB (by positivity)

/-- The full Neumann Hölder norm obtained from a Campanato estimate on a
cube of any side at most one. -/
theorem aux_lem_as_regularity_nc_holder_of_campanato {d : ℕ} (Cp : CampanatoInput d)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (Kc Kf : ℝ) (hKc : 0 ≤ Kc) (hKf : 0 ≤ Kf)
    (hcamp : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ r →
      ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((v : SobolevData (centeredCube z r hr)).1 y - setAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (v : SobolevData (centeredCube z r hr)).1) ^ 2
        ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (Kc * Kf) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        ((2 + Real.sqrt d) * Cp.C alpha * Kc) * Kf := by
  obtain ⟨U, hUc, hUae, hUH, hUn⟩ := Cp.holder_of_campanato alpha ha ha1 z r hr hr1
    (v : SobolevData (centeredCube z r hr)).1 (Kc * Kf) (mul_nonneg hKc hKf) hcamp
  refine ⟨U, hUc, hUH, hUae, ?_⟩
  have h := aux_lem_as_regularity_nc_mean_zero_norm z hr hr1 alpha (Cp.C alpha * (Kc * Kf))
    ha ha1.le v U hUc hUH hUae hUn
  simpa only [mul_assoc] using h


/-- Once a ball covers its root cube, increasing its radius cannot increase
localized energy. Thus an estimate up to the side length extends to all radii. -/
theorem aux_lem_as_regularity_nc_energy_from_root_radius {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (g : HilbertGradient (centeredCube z r hr))
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet) g ≤
        B * rad ^ t) :
    ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet) g ≤
        B * rad ^ t := by
  intro x hx rad hrad
  by_cases hradr : rad ≤ r
  · exact hbound x hx rad hrad hradr
  · have hsub : Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rintro y ⟨_, hy⟩
      refine ⟨?_, hy⟩
      change dist y x < r
      have hy0 : dist y z < r / 2 := hy
      have hx0 : dist x z < r / 2 := hx
      have htri := dist_triangle y z x
      rw [dist_comm z x] at htri
      linarith
    calc _ ≤ localGradientEnergy a
          (s := Metric.ball x r ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet) g :=
        Lane3.localGradientEnergy_mono a _ _ hsub g
      _ ≤ B * r ^ t := hbound x hx r hr le_rfl
      _ ≤ B * rad ^ t := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hr.le (lt_of_not_ge hradr).le ht) hB

/-- The microscopic energy constant written as a short scalar expression. -/
def aux_lem_as_regularity_nc_small_K (d : ℕ) (r C PC t Dv Mx Lam : ℝ) : ℝ :=
  r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t * ((1 + Dv) ^ t * PC ^ 2 * Lam + Mx) +
    r ^ ((d : ℝ) + 2) * PC ^ 2 * Lam * ((2 : ℝ) / r) ^ t

theorem aux_lem_as_regularity_nc_small_K_nonneg (d : ℕ) (r C PC t Dv Mx Lam : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ Dv) (hMx : 0 ≤ Mx) (hLam : 0 ≤ Lam) :
    0 ≤ aux_lem_as_regularity_nc_small_K d r C PC t Dv Mx Lam := by
  unfold aux_lem_as_regularity_nc_small_K
  positivity

/-- Turn a microscopic energy estimate into both estimates of the Neumann
supplier, with the stronger energy exponent chosen before the disorder. -/
theorem aux_lem_as_regularity_nc_small_estimate {d : ℕ}
    (Cp : CampanatoInput d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (t t0 alpha : ℝ) (ht0 : 0 ≤ t0) (htt : t ≤ t0) (ha : 0 < alpha) (ha1 : alpha < 1)
    (he : 0 ≤ 2 + t0 - 2 * alpha - d)
    (Cpo : ℝ) (hCpo : 0 ≤ Cpo)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cpo * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (Mx K : ℝ) (hMx : 0 ≤ Mx) (hK : 0 ≤ K)
    (hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * a.val y)
    (henergy : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr), SolvesNeumann a F v →
      ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤ K * Kf ^ 2 * rad ^ t0) :
    aux_lem_as_regularity_nc_estimate z r hr a t alpha
      (K + (2 + Real.sqrt d) * Cp.C alpha * (1 + Cpo) *
        r ^ ((2 + t0 - 2 * alpha - d) / 2) * (Mx + K)) := by
  let c : ℝ := (2 + Real.sqrt d) * Cp.C alpha * (1 + Cpo) *
    r ^ ((2 + t0 - 2 * alpha - d) / 2)
  have hc : 0 ≤ c := by
    have hCp := (Cp.C_pos alpha ha ha1).le
    dsimp [c]
    positivity
  have hKc : K ≤ K + c * (Mx + K) := le_add_of_nonneg_right (by positivity)
  intro F Kf hKf hFm hFb hFz v hsol
  have hen := henergy F Kf hKf hFm hFb hFz v hsol
  have hcamp := aux_lem_as_regularity_nc_small_campanato Cpo hCpo hPoinc t0 alpha
    (2 + t0 - 2 * alpha - d) he (by ring) z hr a Mx hMx hlow v K Kf hK hKf hen
  obtain ⟨U, hUc, hUH, hUae, hUn⟩ := aux_lem_as_regularity_nc_holder_of_campanato Cp alpha ha ha1
    z hr hr1 v ((1 + Cpo) * (Mx + K) * r ^ ((2 + t0 - 2 * alpha - d) / 2)) Kf
    (by positivity) hKf hcamp
  refine ⟨⟨U, hUc, hUH, hUae, hUn.trans ?_⟩, ?_⟩
  · have hck : c * (Mx + K) ≤ K + c * (Mx + K) := le_add_of_nonneg_left hK
    have h := mul_le_mul_of_nonneg_right hck hKf
    convert h using 1 <;> dsimp [c] <;> ring
  · intro x rad hx hrad hrad1
    have h := aux_lem_as_regularity_nc_energy_from_root_radius z r hr a
      (sobolevGradient (v : SobolevData (centeredCube z r hr))) t0 (K * Kf ^ 2)
      ht0 (mul_nonneg hK (sq_nonneg Kf)) hen x hx rad hrad
    calc _ ≤ K * Kf ^ 2 * rad ^ t0 := h
      _ ≤ K * Kf ^ 2 * rad ^ t := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hrad hrad1 htt) (mul_nonneg hK (sq_nonneg Kf))
      _ ≤ (K + c * (Mx + K)) * Kf ^ 2 * rad ^ t := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKc (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le _)

/-- Finite exceptional cutoffs are combined without claiming a uniform bound
for the unrestricted sequence of their individual constants. -/
theorem aux_lem_as_regularity_nc_finite_prefix
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ → Ω → ℝ) (hK : ∀ N om, 0 ≤ K N om)
    (m k : ℕ) (ps : Fin k → ℝ)
    (hmem : ∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) μ) :
    ∃ (Ks : ℕ → Ω → ℝ) (Cs : Fin k → ℝ),
      (∀ N om, 0 ≤ Ks N om) ∧
      (∀ i N, MemLp (Ks N) (ENNReal.ofReal (ps i)) μ) ∧
      (∀ i N, eLpNorm (Ks N) (ENNReal.ofReal (ps i)) μ ≤ ENNReal.ofReal (Cs i)) ∧
      (∀ N, N < m → Ks N = K N) := by
  let Ks : ℕ → Ω → ℝ := fun N om => if N < m then K N om else 0
  let Cs : Fin k → ℝ := fun i => ∑ N ∈ Finset.range m, (eLpNorm (K N) (ENNReal.ofReal (ps i)) μ).toReal
  refine ⟨Ks, Cs, ?_, ?_, ?_, ?_⟩
  · intro N om
    dsimp [Ks]
    split_ifs
    · exact hK N om
    · exact le_rfl
  · intro i N
    by_cases hN : N < m
    · simpa only [Ks, if_pos hN] using hmem i N
    · simpa only [Ks, if_neg hN] using (memLp_const (0 : ℝ) : MemLp (fun _ : Ω => (0 : ℝ)) _ μ)
  · intro i N
    by_cases hN : N < m
    · have hle : (eLpNorm (K N) (ENNReal.ofReal (ps i)) μ).toReal ≤ Cs i :=
        Finset.single_le_sum
          (f := fun j => (eLpNorm (K j) (ENNReal.ofReal (ps i)) μ).toReal)
          (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_range.mpr hN)
      simpa only [Ks, if_pos hN, ENNReal.ofReal_toReal (hmem i N).eLpNorm_lt_top.ne] using
        (ENNReal.ofReal_le_ofReal hle)
    · simp only [Ks, if_neg hN, eLpNorm_zero', zero_le]
  · intro N hN
    funext om
    exact if_pos hN

/-- Algebraic moment calculation for the microscopic Neumann constants. -/
theorem aux_lem_as_regularity_nc_small_K_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : ℕ) (r C PC t c p : ℝ) (ht : 1 ≤ t) (hp : 0 < p)
    (D Mx Lam : Ω → ℝ) (hD : ∀ om, 0 ≤ D om)
    (hDm : MemLp D (ENNReal.ofReal (2 * p * t)) μ)
    (hMm : MemLp Mx (ENNReal.ofReal (2 * p * t)) μ)
    (hLm : MemLp Lam (ENNReal.ofReal (2 * p)) μ) :
    MemLp (fun om => aux_lem_as_regularity_nc_small_K d r C PC t (D om) (Mx om) (Lam om) +
      c * (Mx om + aux_lem_as_regularity_nc_small_K d r C PC t (D om) (Mx om) (Lam om)))
      (ENNReal.ofReal p) μ := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hDpow : MemLp (fun om => (1 + D om) ^ t) (ENNReal.ofReal (2 * p)) μ := by
    have h1 : MemLp (fun om => 1 + D om) (ENNReal.ofReal (2 * p * t)) μ :=
      (memLp_const (1 : ℝ)).add hDm
    have h2 := h1.norm_rpow_div (ENNReal.ofReal t)
    have heq : ENNReal.ofReal (2 * p * t) / ENNReal.ofReal t = ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_div_of_pos ht0]
      congr 1
      field_simp
    rw [heq, ENNReal.toReal_ofReal ht0.le] at h2
    convert h2 using 1
    funext om
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hD om])]
  haveI := aux_aux_macro_moment_bank_holderTriple p
  have hProd : MemLp (fun om => (1 + D om) ^ t * Lam om) (ENNReal.ofReal p) μ :=
    MemLp.mul' (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
      (r := ENNReal.ofReal p) hDpow hLm
  have hM : MemLp Mx (ENNReal.ofReal p) μ :=
    hMm.mono_exponent (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hL : MemLp Lam (ENNReal.ofReal p) μ :=
    hLm.mono_exponent (ENNReal.ofReal_le_ofReal (by linarith))
  have hEn : MemLp (fun om => aux_lem_as_regularity_nc_small_K d r C PC t (D om) (Mx om) (Lam om))
      (ENNReal.ofReal p) μ := by
    have h1 := ((hProd.const_mul (PC ^ 2)).add hM).const_mul (r ^ ((d : ℝ) + 2) * C * (2 / r) ^ t)
    have h2 := hL.const_mul (r ^ ((d : ℝ) + 2) * PC ^ 2 * (2 / r) ^ t)
    convert h1.add h2 using 1
    funext om
    unfold aux_lem_as_regularity_nc_small_K
    simp only [Pi.add_apply]
    ring
  exact hEn.add ((hM.add hEn).const_mul c)

/-- Isolate the microscopic input so its large type is not repeatedly
elaborated inside the probability argument. -/
theorem aux_lem_as_regularity_nc_small_energy_supplied
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (W : SmallPerturbationInput d)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
        (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (3 : ℝ) ^ N * r ≤ 1 → ∀ Mx Dv : ℝ, 0 < Mx → 0 ≤ Dv →
      (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        Mx⁻¹ ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ Mx) →
      (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
        y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
          Dv * (3 : ℝ) ^ N * dist x y) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
      SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
      ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
      localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
          aux_lem_as_regularity_nc_small_K d r C P.C t Dv Mx
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 1)⁻¹ * Kf ^ 2 * rad ^ t := by
  obtain ⟨C, c, p1, t1, hC, hbig⟩ := aux_lem_as_regularity_nc_small_constants d hd W t ht htd
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨C, hC, ?_⟩
  intro M H om N z r hr hrN Mx Dv hMx hDv henv hlip
  exact (aux_lem_as_regularity_nc_small_energy hd E P M H om N z r hr hrN Mx Dv hMx hDv
    henv hlip C c p1 t1 hC t ht0 hbig).2

/-- Complete finite-moment bank for cutoffs below the root wavelength, on
arbitrary cubes of side at most one. The finite cutoff bound is fixed after
the model and cube; the disorder threshold is fixed before them. -/
theorem aux_lem_as_regularity_nc_small_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ m : ℕ, (3 : ℝ) ^ m * r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, N < m →
          aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
            t alpha (K N om) := by
  let t0 : ℝ := (max t ((d : ℝ) - 2 + 2 * alpha) + d) / 2
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmaxd : max t ((d : ℝ) - 2 + 2 * alpha) < d := max_lt htd (by linarith)
  have htt0 : t < t0 := by dsimp [t0]; linarith [le_max_left t ((d : ℝ) - 2 + 2 * alpha)]
  have ht0d : t0 < d := by dsimp [t0]; linarith
  have ht0 : (d : ℝ) - 1 < t0 := ht.trans htt0
  have ht01 : 1 ≤ t0 := by linarith
  have he : 0 ≤ 2 + t0 - 2 * alpha - d := by
    dsimp [t0]
    linarith [le_max_right t ((d : ℝ) - 2 + 2 * alpha)]
  obtain ⟨C, hC, henergy⟩ := aux_lem_as_regularity_nc_small_energy_supplied d hd E P W t0 ht0 ht0d
  obtain ⟨Cpo, hCpo, hPoinc⟩ := aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  let pp : ℝ := 1 + ∑ i, ps i
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => (hps i).trans' zero_le_one
  have hpp : 1 ≤ pp := by dsimp [pp]; linarith
  have hpspp : ∀ i, ps i ≤ pp := by
    intro i
    have h := Finset.single_le_sum (f := ps) (fun j _ => (hps j).trans' zero_le_one)
      (Finset.mem_univ i)
    dsimp [pp]
    linarith
  have hq : 1 ≤ 2 * pp * t0 := by nlinarith
  obtain ⟨_, _, cd, _, _, hcd, hExt⟩ := aux_prop_growth_energy_assembly_root_extremes d hd
    (2 * pp * t0) hq
  obtain ⟨δL, hδL, hLam⟩ := lane4_lambda_inv_moments d hd E (1 / 8) ⟨by norm_num, by norm_num⟩
  refine ⟨min (cd / (2 * (2 * pp * t0))) (δL (2 * pp)),
    lt_min (div_pos hcd (by positivity)) (hδL _ (by linarith)), ?_⟩
  intro M Rm H hH hdelta z r hr hr1 m hrm
  obtain ⟨Dv, Mx, _, _, hDM, hAE, hMem, _, _⟩ := hExt M H hH
    (hdelta.trans (min_le_left _ _)) z r hr hr1
  obtain ⟨_, hLm, _⟩ := hLam M Rm H hH z r hr hr1 (2 * pp) (by linarith)
    (hdelta.trans (min_le_right _ _))
  let Lam : ℕ → BilateralField d → ℝ := fun N om =>
    (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹
  have hLam0 : ∀ N om, 0 ≤ Lam N om := fun N om =>
    (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le
  let KE : ℕ → BilateralField d → ℝ := fun N om =>
    aux_lem_as_regularity_nc_small_K d r C P.C t0 (Dv N om) (Mx N om) (Lam N om)
  have hKE : ∀ N om, 0 ≤ KE N om := fun N om =>
    aux_lem_as_regularity_nc_small_K_nonneg d r C P.C t0 (Dv N om) (Mx N om) (Lam N om)
      hr hC.le (hDM N om).1 (hDM N om).2 (hLam0 N om)
  let c : ℝ := (2 + Real.sqrt d) * Cp.C alpha * (1 + Cpo) *
    r ^ ((2 + t0 - 2 * alpha - d) / 2)
  have hc : 0 ≤ c := by
    have hCp := (Cp.C_pos alpha ha ha1).le
    dsimp [c]
    positivity
  let Kraw : ℕ → BilateralField d → ℝ := fun N om => KE N om + c * (Mx N om + KE N om)
  have hKraw : ∀ N om, 0 ≤ Kraw N om := fun N om =>
    add_nonneg (hKE N om) (mul_nonneg hc (add_nonneg (hDM N om).2 (hKE N om)))
  have hKrawm : ∀ i N, MemLp (Kraw N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := by
    intro i N
    have h := aux_lem_as_regularity_nc_small_K_memLp (chaosSampleLaw M).toMeasure
      d r C P.C t0 c pp ht01 (by linarith) (Dv N) (Mx N) (Lam N)
      (fun om => (hDM N om).1) (hMem N).1 (hMem N).2 (hLm N)
    exact h.mono_exponent (ENNReal.ofReal_le_ofReal (hpspp i))
  obtain ⟨K, Cbound, hK, hKm, hKb, hKeq⟩ := aux_lem_as_regularity_nc_finite_prefix
    (chaosSampleLaw M).toMeasure Kraw hKraw m k ps hKrawm
  refine ⟨K, Cbound, hK, hKm, hKb, ?_⟩
  filter_upwards [hAE] with om hom
  intro N hNm
  rw [hKeq N hNm]
  have hrN : (3 : ℝ) ^ N * r ≤ 1 :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNm.le) hr.le).trans hrm
  obtain ⟨hMx, henv, hlip⟩ := hom N
  have hDv : 0 ≤ Dv N om := (hDM N om).1
  have hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx N om * (cutoffPositiveCoefficient M H om N z hr).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hymem
    rw [hy]
    have h := mul_le_mul_of_nonneg_left (henv y (centeredCube_subset_closedCube z hr hymem)).1 hMx.le
    rwa [mul_inv_cancel₀ hMx.ne'] at h
  have hinv : (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 1)⁻¹ ≤ Lam N om :=
    inv_anti₀ (E.lam_pos _ _ _ _ _ _ _ _)
      (E.lam_mono z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 (1 / 8) 1 (by norm_num))
  have hKEle : aux_lem_as_regularity_nc_small_K d r C P.C t0 (Dv N om) (Mx N om)
      (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 1)⁻¹ ≤ KE N om := by
    dsimp [KE, aux_lem_as_regularity_nc_small_K]
    gcongr
  apply aux_lem_as_regularity_nc_small_estimate Cp z r hr hr1
    (cutoffPositiveCoefficient M H om N z hr) t t0 alpha (by linarith) htt0.le ha ha1 he
    Cpo hCpo hPoinc (Mx N om) (KE N om) hMx.le (hKE N om) hlow
  intro F Kf hKf hFm hFb hFz v hsol x hx rad hrad hradr
  exact (henergy M H om N z r hr hrN (Mx N om) (Dv N om) hMx (hDM N om).1 henv hlip
    F Kf hKf hFm hFb hFz v hsol x hx rad hrad hradr).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKEle (sq_nonneg Kf))
      (Real.rpow_nonneg hrad.le _))

/-- Scale covariance and the microscopic finite prefix together give all
cutoffs on every translated triadic cube, for the entire finite moment list. -/
theorem aux_lem_as_regularity_nc_triadic_all_cutoffs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ), r = (3 : ℝ) ^ j →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
            t alpha (K N om) := by
  obtain ⟨δH, hδH, hHbank⟩ := aux_lem_as_regularity_nc_triadic_finite_bank d hd E P X W D Cp
    t alpha k ps ht htd ha ha1 hps
  obtain ⟨δS, hδS, hSbank⟩ := aux_lem_as_regularity_nc_small_bank d hd E P W Cp t alpha
    ht htd ha ha1 k ps hps
  refine ⟨min δH δS, lt_min hδH hδS, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr j hrj
  obtain ⟨KH, CH, hKH, hKHm, hKHb, hHAE⟩ := hHbank M Rm Sreg It H hIR
    (hdelta.trans (min_le_left _ _)) z r hr j hrj
  by_cases hj : 0 ≤ j
  · refine ⟨KH, CH, hKH, hKHm, hKHb, ?_⟩
    filter_upwards [hHAE] with om hom N
    exact hom N (by omega)
  · have hj0 : j < 0 := lt_of_not_ge hj
    let m : ℕ := (-j).toNat
    have hmj : (m : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    have hrm : (3 : ℝ) ^ m * r = 1 := by
      rw [hrj, ← zpow_natCast, hmj, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp only [neg_add_cancel, zpow_zero]
    have hr1 : r ≤ 1 := by
      have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      nlinarith
    obtain ⟨KS, CS, hKS, hKSm, hKSb, hSAE⟩ := hSbank M Rm H hIR
      (hdelta.trans (min_le_right _ _)) z r hr hr1 m hrm.le
    refine ⟨fun N om => KH N om + KS N om, fun i => max (CH i) 0 + max (CS i) 0,
      fun N om => add_nonneg (hKH N om) (hKS N om),
      fun i N => (hKHm i N).add (hKSm i N), ?_, ?_⟩
    · intro i N
      have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hps i)
      calc eLpNorm (fun om => KH N om + KS N om) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure
          ≤ eLpNorm (KH N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
            eLpNorm (KS N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
              eLpNorm_add_le hp
        _ ≤ ENNReal.ofReal (max (CH i) 0) + ENNReal.ofReal (max (CS i) 0) :=
          add_le_add ((hKHb i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hKSb i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        _ = ENNReal.ofReal (max (CH i) 0 + max (CS i) 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
    · filter_upwards [hHAE, hSAE] with om hhigh hsmall N
      by_cases hN : -j ≤ (N : ℤ)
      · exact aux_lem_as_regularity_nc_estimate_mono
          (le_add_of_nonneg_right (hKS N om)) (hhigh N hN)
      · have hNm : N < m := by omega
        exact aux_lem_as_regularity_nc_estimate_mono
          (le_add_of_nonneg_left (hKH N om)) (hsmall N hNm)
/-- The residual cells are the exact images of the unit cells. -/
theorem aux_lem_as_regularity_macro_rho_cell_smul {d : ℕ} {rho : ℝ}
    (hrho : 0 < rho) (j : ℕ) (k : Fin d → ℤ) :
    aux_lem_as_regularity_macro_rho_cell rho j k =
      rho • aux_prop_growth_holder_macro_campanato_cell (0 : SpatialCoordinates d) j k := by
  unfold aux_lem_as_regularity_macro_rho_cell aux_prop_growth_holder_macro_campanato_cell
  rw [_root_.smul_ball hrho.ne', Real.norm_eq_abs, abs_of_pos hrho]
  congr 1
  · ext i
    simp only [aux_lem_as_regularity_macro_rho_center,
      aux_lem_as_regularity_macro_rho_side, aux_prop_growth_holder_macro_campanato_center,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add, mul_assoc]
  · exact mul_div_assoc _ _ _

theorem aux_lem_as_regularity_macro_rho_ball_smul {d : ℕ} {rho : ℝ}
    (hrho : 0 < rho) :
    ball (0 : SpatialCoordinates d) (rho / 2) =
      rho • ball (0 : SpatialCoordinates d) (1 / 2) := by
  rw [_root_.smul_ball hrho.ne', Real.norm_eq_abs, abs_of_pos hrho, smul_zero, mul_one_div]

theorem aux_lem_as_regularity_macro_rho_var_smul {d : ℕ} {rho : ℝ}
    (hrho : 0 < rho) (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    (v : SpatialCoordinates d → ℝ) :
    aux_prop_growth_holder_macro_campanato_var (rho • S) v =
      rho ^ d * aux_prop_growth_holder_macro_campanato_var S (fun x => v (rho • x)) := by
  apply aux_prop_growth_holder_macro_campanato_var_smul hrho S hS
  exact Filter.Eventually.of_forall fun y => by
    rw [smul_smul, mul_inv_cancel₀ hrho.ne', one_smul]

/-- Dilation algebra for a normalized variance estimate. -/
theorem aux_lem_as_regularity_macro_rho_cancel
    (D V A B : ℝ) (hD : 0 < D) (h : D * V ≤ A * (D * B)) : V ≤ A * B := by
  apply (mul_le_mul_iff_right₀ hD).mp
  calc D * V ≤ A * (D * B) := h
    _ = D * (A * B) := by ring

/-- The macroscopic chaining theorem on an arbitrary positive side. The root
variance hypothesis is normalized by the actual volume `rho^d`; its contribution
to the final Hölder constant therefore carries `rho^(-alpha)`. -/
theorem aux_lem_as_regularity_macro_rho_chaining {d : ℕ}
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ Kd : ℝ, 1 ≤ Kd ∧ ∀ (rho : ℝ) (hrho : 0 < rho)
      (v : SpatialCoordinates d → ℝ),
      MemLp (fun y => v (rho • y)) 2
        (volume.restrict (ball (0 : SpatialCoordinates d) (1 / 2))) →
      ∀ (n P0 : ℕ) (Cg X W X0 radMin : ℝ),
      0 ≤ Cg → 0 ≤ X → 0 ≤ W → 0 ≤ X0 → 0 < radMin →
      radMin ≤ aux_lem_as_regularity_macro_rho_side rho n →
      (∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm j k →
        aux_prop_growth_holder_macro_campanato_var
          (aux_lem_as_regularity_macro_rho_cell rho j k) v ≤
          (Cg * aux_lem_as_regularity_macro_rho_side rho j ^ alpha * X) ^ 2 *
            volume.real (aux_lem_as_regularity_macro_rho_cell rho j k)) →
      (∀ p ∈ ball (0 : SpatialCoordinates d) (rho / 2),
        ∀ rad : ℝ, radMin ≤ rad → rad ≤ aux_lem_as_regularity_macro_rho_side rho n →
        aux_prop_growth_holder_macro_campanato_var
          (ball p rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) v ≤
          W ^ 2 * rad ^ (2 * alpha) *
            volume.real (ball p rad ∩ ball (0 : SpatialCoordinates d) (rho / 2))) →
      aux_prop_growth_holder_macro_campanato_var
        (ball (0 : SpatialCoordinates d) (rho / 2)) v ≤ X0 ^ 2 * rho ^ d →
      ∀ x ∈ ball (0 : SpatialCoordinates d) (rho / 2), ∀ rad : ℝ,
        radMin ≤ rad → rad ≤ rho →
        aux_prop_growth_holder_macro_campanato_var
          (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) v ≤
          (Kd * (Cg * X + W +
            ((2 : ℝ) * 3 ^ P0) ^ (alpha + (d : ℝ) / 2) / rho ^ alpha * X0)) ^ 2 *
            rad ^ (2 * alpha) *
              volume.real (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) := by
  obtain ⟨Kd, hKd, hunit⟩ :=
    aux_prop_growth_holder_macro_campanato_unit (d := d) alpha ha ha1
  refine ⟨Kd, hKd, ?_⟩
  intro rho hrho v hv n P0 Cg X W X0 radMin hCg hX hW hX0 hmin hminN H1 H2 H3 x hx rad hradMin hradR
  have hrd : 0 < rho ^ d := pow_pos hrho d
  have hra : 0 < rho ^ alpha := Real.rpow_pos_of_pos hrho alpha
  have hrad : 0 < rad := hmin.trans_le hradMin
  have hball := aux_lem_as_regularity_macro_rho_ball_smul (d := d) hrho
  have hballcut (p : SpatialCoordinates d) (s : ℝ) :
      ball (rho • p) (rho * s) ∩ ball (0 : SpatialCoordinates d) (rho / 2) =
        rho • (ball p s ∩ ball (0 : SpatialCoordinates d) (1 / 2)) := by
    rw [aux_aux_macro_energy_recurrence_ball_inter_smul _ _ _ hrho, ← hball]
  have h1 : ∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      aux_prop_growth_holder_macro_campanato_var
        (aux_prop_growth_holder_macro_campanato_cell (0 : SpatialCoordinates d) j k)
        (fun y => v (rho • y)) ≤
        (Cg * aux_prop_growth_holder_macro_campanato_side j ^ alpha * (rho ^ alpha * X)) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell (0 : SpatialCoordinates d) j k) := by
    intro j hj hjn k hk
    have h := H1 j hj hjn k hk
    rw [aux_lem_as_regularity_macro_rho_cell_smul hrho,
      aux_lem_as_regularity_macro_rho_var_smul hrho _
        (aux_prop_growth_holder_macro_campanato_cell_measurable _ _ _),
      aux_aux_macro_energy_recurrence_volume_real_smul hrho] at h
    have h' := aux_lem_as_regularity_macro_rho_cancel _ _ _ _ hrd h
    unfold aux_lem_as_regularity_macro_rho_side at h'
    rw [Real.mul_rpow hrho.le (aux_prop_growth_holder_macro_campanato_side_pos j).le] at h'
    convert h' using 1 <;> ring
  have h2 : ∀ p ∈ ball (0 : SpatialCoordinates d) (1 / 2), ∀ s : ℝ,
      radMin / rho ≤ s → s ≤ aux_prop_growth_holder_macro_campanato_side n →
      aux_prop_growth_holder_macro_campanato_var
        (ball p s ∩ ball (0 : SpatialCoordinates d) (1 / 2)) (fun y => v (rho • y)) ≤
        (rho ^ alpha * W) ^ 2 * s ^ (2 * alpha) *
          volume.real (ball p s ∩ ball (0 : SpatialCoordinates d) (1 / 2)) := by
    intro p hp s hsmin hsn
    have hs : 0 < s := (div_pos hmin hrho).trans_le hsmin
    have hp' : rho • p ∈ ball (0 : SpatialCoordinates d) (rho / 2) := by
      rw [hball]
      exact Set.smul_mem_smul_set hp
    have h := H2 (rho • p) hp' (rho * s)
      (by simpa only [mul_comm] using (div_le_iff₀ hrho).mp hsmin)
      (mul_le_mul_of_nonneg_left hsn hrho.le)
    rw [hballcut, aux_lem_as_regularity_macro_rho_var_smul hrho _
      (measurableSet_ball.inter measurableSet_ball),
      aux_aux_macro_energy_recurrence_volume_real_smul hrho] at h
    have h' := aux_lem_as_regularity_macro_rho_cancel _ _ _ _ hrd h
    rw [Real.mul_rpow hrho.le hs.le] at h'
    have heq : rho ^ (2 * alpha) = (rho ^ alpha) ^ 2 := by
      rw [← Real.rpow_mul_natCast hrho.le]
      congr 1
      ring
    rw [heq] at h'
    convert h' using 1 <;> ring
  have h3 : aux_prop_growth_holder_macro_campanato_var
      (ball (0 : SpatialCoordinates d) (1 / 2)) (fun y => v (rho • y)) ≤ X0 ^ 2 := by
    rw [hball, aux_lem_as_regularity_macro_rho_var_smul hrho _ measurableSet_ball] at H3
    exact (mul_le_mul_iff_right₀ hrd).mp (by simpa only [mul_comm] using H3)
  have hx' : rho⁻¹ • x ∈ ball (0 : SpatialCoordinates d) (1 / 2) := by
    rw [hball] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [smul_smul, inv_mul_cancel₀ hrho.ne', one_smul] using hy
  have hmin' : radMin / rho ≤ aux_prop_growth_holder_macro_campanato_side n :=
    (div_le_iff₀ hrho).mpr (by simpa only [aux_lem_as_regularity_macro_rho_side, mul_comm] using hminN)
  have h := hunit 0 (fun y => v (rho • y)) hv n P0 Cg
    (rho ^ alpha * X) (rho ^ alpha * W) X0 (radMin / rho)
    hCg (mul_nonneg hra.le hX) (mul_nonneg hra.le hW) hX0 (div_pos hmin hrho) hmin'
    h1 h2 h3 (rho⁻¹ • x) hx' (rad / rho)
    (div_le_div_of_nonneg_right hradMin hrho.le) ((div_le_one hrho).mpr hradR)
  have hset : ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2) =
      rho • (ball (rho⁻¹ • x) (rad / rho) ∩ ball (0 : SpatialCoordinates d) (1 / 2)) := by
    simpa only [smul_smul, mul_inv_cancel₀ hrho.ne', one_smul, mul_div_cancel₀ _ hrho.ne']
      using hballcut (rho⁻¹ • x) (rad / rho)
  rw [hset, aux_lem_as_regularity_macro_rho_var_smul hrho _
    (measurableSet_ball.inter measurableSet_ball),
    aux_aux_macro_energy_recurrence_volume_real_smul hrho]
  refine (mul_le_mul_of_nonneg_left h hrd.le).trans_eq ?_
  rw [Real.div_rpow hrad.le hrho.le]
  have heq : rho ^ (2 * alpha) = (rho ^ alpha) ^ 2 := by
    rw [← Real.rpow_mul_natCast hrho.le]
    congr 1
    ring
  rw [heq]
  field_simp

theorem aux_lem_as_regularity_macro_rho_memLp {d : ℕ} {rho : ℝ}
    (hrho : 0 < rho) (v : DomainL2 (centeredCube (0 : SpatialCoordinates d) rho hrho)) :
    MemLp (fun y => v (rho • y)) 2
      (volume.restrict (ball (0 : SpatialCoordinates d) (1 / 2))) := by
  have hmap : MemLp (v : SpatialCoordinates d → ℝ) 2
      (Measure.map (cubeDilation 0 0 rho)
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))) := by
    rw [map_cubeDilation_restrict 0 0 hrho one_pos]
    exact (Lp.memLp v).smul_measure ENNReal.ofReal_ne_top
  have h := hmap.comp_of_map (continuous_cubeDilation 0 0 rho).measurable.aemeasurable
  have hdil : cubeDilation (0 : SpatialCoordinates d) 0 rho = fun y => rho • y := by
    funext y i
    simp only [cubeDilation, Pi.zero_apply, sub_zero, zero_add, Pi.smul_apply, smul_eq_mul]
  simpa only [hdil, Function.comp_def] using! h

theorem aux_lem_as_regularity_macro_rho_cell_volume {d : ℕ} {rho : ℝ}
    (hrho : 0 < rho) (j : ℕ) (k : Fin d → ℤ) :
    volume.real (aux_lem_as_regularity_macro_rho_cell rho j k) =
      aux_lem_as_regularity_macro_rho_side rho j ^ d := by
  rw [aux_lem_as_regularity_macro_rho_cell_smul hrho,
    aux_aux_macro_energy_recurrence_volume_real_smul hrho,
    aux_prop_growth_holder_macro_campanato_cell_volume,
    aux_lem_as_regularity_macro_rho_side, mul_pow]

/-- Coarse Poincaré and the actual residual chart's discounted series convert
the all-radius energy estimate into the cell-variance inputs of chaining. -/
theorem aux_lem_as_regularity_macro_rho_cell_variance {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (t alpha e e' K Kf : ℝ) (ht : 0 ≤ t) (he' : 0 < e') (hee : e' ≤ e)
    (he1 : e' ≤ 1) (hK : 0 ≤ K) (hexp : 2 + t = e + 2 * alpha + d)
    (hsum : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (0 : SpatialCoordinates d) rho hrho
          (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
          (0 : SpatialCoordinates d) rho)))
    (v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) rho hrho))
    (hen : ∀ x ∈ centeredCube (0 : SpatialCoordinates d) rho hrho,
      ∀ rad : ℝ, 0 < rad → rad ≤ rho →
      localGradientEnergy (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
        (s := ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
          Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter
          (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho))) ≤
        K * Kf ^ 2 * rad ^ t) :
    let Z := ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (0 : SpatialCoordinates d) rho hrho
          (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
          (0 : SpatialCoordinates d) rho)
    let Cg := (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))
    let A := max 1 (P.C ^ 2 * Cg)
    ∀ (j : ℕ) (kk : Fin d → ℤ), aux_prop_growth_holder_macro_campanato_Adm j kk →
      aux_prop_growth_holder_macro_campanato_var
        (aux_lem_as_regularity_macro_rho_cell rho j kk)
        ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1 :
          SpatialCoordinates d → ℝ) ≤
        (aux_lem_as_regularity_macro_rho_side rho j ^ alpha * ((1 + A * (K + Z)) * Kf)) ^ 2 *
          volume.real (aux_lem_as_regularity_macro_rho_cell rho j kk) := by
  intro Z Cg A j kk hkk
  set c := aux_lem_as_regularity_macro_rho_center rho j kk with hc
  set s := aux_lem_as_regularity_macro_rho_side rho j with hsdef
  have hs0 : 0 < s := aux_lem_as_regularity_macro_rho_side_pos hrho j
  have hsR : s ≤ rho := by
    exact (mul_le_mul_of_nonneg_left
      (aux_prop_growth_holder_macro_campanato_side_le_one j) hrho.le).trans_eq (mul_one _)
  have hcellT : aux_lem_as_regularity_macro_rho_cell rho j kk =
      (centeredCube c s hs0 : Set (SpatialCoordinates d)) := rfl
  have hTQ : (centeredCube c s hs0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)) :=
    aux_lem_as_regularity_macro_rho_cell_sub hrho hkk
  have hcQ : c ∈ centeredCube (0 : SpatialCoordinates d) rho hrho :=
    hTQ (mem_ball_self (half_pos hs0))
  have hcoef : ∀ᵐ y ∂volume.restrict (centeredCube c s hs0 : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N c hs0).val y =
        (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N c hs0,
      ae_restrict_of_ae_restrict_of_subset hTQ
        (aux_prop_growth_holder_micro_campanato_coeff_ae M H om N (0 : SpatialCoordinates d)
          hrho)] with y h1 h2
    rw [h1, h2]
  have hPc := aux_cor_neumann_source_cell_poincare hd E P c s hs0 hTQ
    (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
    (cutoffPositiveCoefficient M H om N c hs0) hcoef
    ⟨(v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)),
      (inf_le_left : meanZeroSobolevGraph _ ≤ weakSobolevGraph _) v.property⟩
  have hE1 := hen c hcQ (s / 2) (half_pos hs0) (by linarith)
  have hset : ball c (s / 2) ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
      Set (SpatialCoordinates d)) = (centeredCube c s hs0 : Set (SpatialCoordinates d)) :=
    Set.inter_eq_left.mpr hTQ
  have hE2 : localGradientEnergy
      (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
      (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
      (centeredCube c s hs0).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho))) ≤
        K * Kf ^ 2 * (s / 2) ^ t := by
    rw [← aux_cor_neumann_source_energy_congr _ hset
      (isOpen_ball.measurableSet.inter
        (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)]
    exact hE1
  have hlam := aux_lem_as_regularity_macro_rho_lam_cell E M H om N rho hrho hrho1
    j kk hkk e e' he' hee he1 hsum
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n =>
    mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 n)
      (aux_lane4_lambda_inv_moments_Y_nonneg _ _)
  rw [aux_lem_as_regularity_macro_rho_cell_volume hrho, hcellT]
  exact aux_cor_neumann_source_cell_alg d _ P.C s _ _ K Kf t e alpha Z Cg A hs0
    (inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le) hK hZ0 ht
    (le_max_left _ _) (le_max_right _ _) hexp hPc hE2 hlam

theorem aux_lem_as_regularity_macro_rho_micro_pathwise {d : ℕ} (CP : ℝ) (hCP0 : 0 ≤ CP)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CP * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (rho : ℝ) (hrho : 0 < rho)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) rho hrho)) (Mx : ℝ) (hMx : 0 ≤ Mx)
    (hlow : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)),
      1 ≤ Mx * a.val y)
    (v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) rho hrho))
    (K Kf t alpha e eps rad : ℝ) (hrad : 0 < rad) (hre : rad ≤ eps) (hradR : rad ≤ rho)
    (he : 0 ≤ e) (hexp : 2 + t = 2 * alpha + d + e)
    (hen : ∀ c ∈ centeredCube (0 : SpatialCoordinates d) rho hrho,
      localGradientEnergy a
          (s := Metric.ball c rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho))) ≤ K * Kf ^ 2 * rad ^ t)
    (x : SpatialCoordinates d) (hx : x ∈ centeredCube (0 : SpatialCoordinates d) rho hrho) :
    ∫ y in Metric.ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)),
        ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1 y - setAverage
          (Metric.ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)))
          (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1) ^ 2
        ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)) ≤
      ((1 + CP) * (Mx + |K|) * eps ^ (e / 2) * Kf) ^ 2 * rad ^ (2 * alpha) *
        volume.real (Metric.ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d))) := by
  have hpw := aux_prop_growth_holder_micro_campanato_pathwise (d := d) CP hCP0 hPoinc
    (0 : SpatialCoordinates d) hrho a Mx hMx hlow
    (⟨(v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)),
        (inf_le_left : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) rho hrho) ≤ weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) rho hrho))
          v.property⟩)
    rad (K * Kf ^ 2 * rad ^ t) hrad hen x hx
  have hV := aux_prop_growth_holder_micro_campanato_volume_ge (d := d)
    (0 : SpatialCoordinates d) x (R := rho / 2) hrad (by linarith) hx
  exact aux_prop_growth_holder_micro_campanato_final_alg d CP Mx K Kf rad eps
    (volume.real (ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)))) t alpha e
    (∫ y in ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)),
        ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1 y - setAverage
          (ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)))
          (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1) ^ 2
        ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)))
    hCP0 hMx hrad hre he hexp hV hpw


/-- The two physical scale ranges meet at `rho * 3^(-N)`. The root-volume
normalization cancels the inverse-scale factor in the chaining constant. -/
theorem aux_lem_as_regularity_macro_rho_join {d : ℕ}
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (rho : ℝ) (hrho : 0 < rho)
      (v : SpatialCoordinates d → ℝ),
      MemLp (fun y => v (rho • y)) 2
        (volume.restrict (ball (0 : SpatialCoordinates d) (1 / 2))) →
      ∀ (N : ℕ) (Xc Kmic Kf : ℝ), 0 ≤ Xc → 0 ≤ Kmic → 0 ≤ Kf →
      (∀ j : ℕ, j ≤ N → ∀ k : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm j k →
        aux_prop_growth_holder_macro_campanato_var
          (aux_lem_as_regularity_macro_rho_cell rho j k) v ≤
          (aux_lem_as_regularity_macro_rho_side rho j ^ alpha * (Xc * Kf)) ^ 2 *
            volume.real (aux_lem_as_regularity_macro_rho_cell rho j k)) →
      (∀ x ∈ ball (0 : SpatialCoordinates d) (rho / 2), ∀ rad : ℝ,
        0 < rad → rad ≤ aux_lem_as_regularity_macro_rho_side rho N →
        aux_prop_growth_holder_macro_campanato_var
          (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) v ≤
          (Kmic * Kf) ^ 2 * rad ^ (2 * alpha) *
            volume.real (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2))) →
      ∀ x ∈ ball (0 : SpatialCoordinates d) (rho / 2), ∀ rad : ℝ,
        0 < rad → rad ≤ rho →
        aux_prop_growth_holder_macro_campanato_var
          (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) v ≤
          ((1 + Cd * (Xc + Kmic)) * Kf) ^ 2 * rad ^ (2 * alpha) *
            volume.real (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) := by
  obtain ⟨Kd, hKd1, hchain⟩ := aux_lem_as_regularity_macro_rho_chaining (d := d) alpha ha ha1
  let Y : ℝ := ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)
  have hY : 0 ≤ Y := Real.rpow_nonneg (by norm_num) _
  have hKd : 0 ≤ Kd := zero_le_one.trans hKd1
  have hC : 1 ≤ Kd * (1 + Y) := by nlinarith
  refine ⟨Kd * (1 + Y), hC, ?_⟩
  intro rho hrho v hv N Xc Kmic Kf hX hKm hKf hcell hmic x hx rad hrad hradR
  have hXK : 0 ≤ Xc * Kf := mul_nonneg hX hKf
  have hMK : 0 ≤ Kmic * Kf := mul_nonneg hKm hKf
  have heps : 0 < aux_lem_as_regularity_macro_rho_side rho N :=
    aux_lem_as_regularity_macro_rho_side_pos hrho N
  have hmajor (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) :
      A ^ 2 * rad ^ (2 * alpha) *
          volume.real (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) ≤
        B ^ 2 * rad ^ (2 * alpha) *
          volume.real (ball x rad ∩ ball (0 : SpatialCoordinates d) (rho / 2)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB 2)
        (Real.rpow_nonneg hrad.le _)) measureReal_nonneg
  by_cases hsmall : rad ≤ aux_lem_as_regularity_macro_rho_side rho N
  · refine (hmic x hx rad hrad hsmall).trans (hmajor _ _ hMK ?_)
    apply mul_le_mul_of_nonneg_right _ hKf
    have hC0 : 0 ≤ Kd * (1 + Y) := zero_le_one.trans hC
    calc Kmic ≤ Kd * (1 + Y) * Kmic := le_mul_of_one_le_left hKm hC
      _ ≤ Kd * (1 + Y) * (Xc + Kmic) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0
      _ ≤ 1 + Kd * (1 + Y) * (Xc + Kmic) := by linarith
  · have hcell0 : aux_lem_as_regularity_macro_rho_cell rho 0 (fun _ : Fin d => 0) =
        ball (0 : SpatialCoordinates d) (rho / 2) := by
      have hc : aux_lem_as_regularity_macro_rho_center rho 0 (fun _ : Fin d => 0) = 0 := by
        ext i
        simp only [aux_lem_as_regularity_macro_rho_center, Int.cast_zero, mul_zero, Pi.zero_apply]
      simp only [aux_lem_as_regularity_macro_rho_cell, hc,
        aux_lem_as_regularity_macro_rho_side, aux_prop_growth_holder_macro_campanato_side,
        pow_zero, inv_one, mul_one]
    have hroot : aux_prop_growth_holder_macro_campanato_var
        (ball (0 : SpatialCoordinates d) (rho / 2)) v ≤
        (rho ^ alpha * (Xc * Kf)) ^ 2 * rho ^ d := by
      have h := hcell 0 (Nat.zero_le N) (fun _ => 0) (by intro i; simp)
      rw [aux_lem_as_regularity_macro_rho_cell_volume hrho, hcell0] at h
      simpa only [aux_lem_as_regularity_macro_rho_side,
        aux_prop_growth_holder_macro_campanato_side, pow_zero, inv_one, mul_one] using h
    have hra : 0 < rho ^ alpha := Real.rpow_pos_of_pos hrho alpha
    have h := hchain rho hrho v hv N 0 1 (Xc * Kf) (Kmic * Kf)
      (rho ^ alpha * (Xc * Kf)) (aux_lem_as_regularity_macro_rho_side rho N)
      zero_le_one hXK hMK (mul_nonneg hra.le hXK) heps le_rfl
      (fun j _ hj k hk => by simpa only [one_mul] using hcell j hj k hk)
      (fun p hp s hsmin hsn => hmic p hp s (heps.trans_le hsmin) hsn)
      hroot x hx rad (le_of_not_ge hsmall) hradR
    have hcoef : Kd * (1 * (Xc * Kf) + Kmic * Kf +
        ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) / rho ^ alpha *
          (rho ^ alpha * (Xc * Kf))) =
        Kd * (Xc * Kf + Kmic * Kf + Y * (Xc * Kf)) := by
      dsimp only [Y]
      field_simp
    rw [hcoef] at h
    refine h.trans (hmajor _ _ (mul_nonneg hKd
      (add_nonneg (add_nonneg hXK hMK) (mul_nonneg hY hXK))) ?_)
    simpa only [one_mul] using
      aux_cor_neumann_source_macro_arith Kd Y Xc Kmic Kf hKd hY hX hKm hKf

theorem aux_lem_as_regularity_macro_rho_micro_floor {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (Mx : ℝ) (hMx : 0 < Mx)
    (hbounds : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) rho hrho :
        Set (SpatialCoordinates d)), Mx⁻¹ ≤ cutoffCoefficient M H om N x) :
    ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho :
        Set (SpatialCoordinates d)),
      1 ≤ Mx * (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho).val y := by
  filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N 0 hrho,
    ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet]
    with y hy hyQ
  rw [hy]
  have hlo := hbounds y (centeredCube_subset_closedCube (0 : SpatialCoordinates d) hrho hyQ)
  calc (1 : ℝ) = Mx * Mx⁻¹ := (mul_inv_cancel₀ hMx.ne').symm
    _ ≤ Mx * cutoffCoefficient M H om N y := mul_le_mul_of_nonneg_left hlo hMx.le

/-- This deterministic reduction leaves only the native residual-cube energy
estimate to supply. Both radius ranges and the residual-volume factors are explicit. -/
theorem aux_lem_as_regularity_macro_rho_campanato_of_energy {d : ℕ}
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (hd : 2 ≤ d) (E : in_J d) (P : in_poincare d hd E)
      (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
      (rho : ℝ) (hrho : 0 < rho), rho ≤ 1 →
      ∀ CP : ℝ, 0 ≤ CP →
      (∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
        (w : meanZeroSobolevGraph (centeredCube c s hs)),
        ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
            ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
          CP * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
            ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2) →
      ∀ t e e' K Kf Mx : ℝ,
      0 ≤ t → 0 ≤ e → 0 < e' → e' ≤ e → e' ≤ 1 → 0 ≤ K → 0 ≤ Kf → 0 ≤ Mx →
      2 + t = e + 2 * alpha + d →
      (∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho :
          Set (SpatialCoordinates d)),
        1 ≤ Mx * (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho).val y) →
      Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (0 : SpatialCoordinates d) rho hrho
            (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
            (0 : SpatialCoordinates d) rho)) →
      ∀ v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) rho hrho),
      (∀ x ∈ centeredCube (0 : SpatialCoordinates d) rho hrho,
        ∀ rad : ℝ, 0 < rad → rad ≤ rho →
        localGradientEnergy (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
          (s := ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
            Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter
            (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho))) ≤
          K * Kf ^ 2 * rad ^ t) →
      let Z := ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (0 : SpatialCoordinates d) rho hrho
            (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
            (0 : SpatialCoordinates d) rho)
      let A := max 1 (P.C ^ 2 *
        ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))))
      let Xc := 1 + A * (K + Z)
      let Kmic := (1 + CP) * (Mx + |K|) *
        aux_lem_as_regularity_macro_rho_side rho N ^ (e / 2)
      ∀ x ∈ centeredCube (0 : SpatialCoordinates d) rho hrho, ∀ rad : ℝ,
        0 < rad → rad ≤ rho →
        ∫ y in ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
            Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1 y -
            setAverage (ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
              Set (SpatialCoordinates d)))
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1) ^ 2
            ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho :
              Set (SpatialCoordinates d)) ≤
          ((1 + Cd * (Xc + Kmic)) * Kf) ^ 2 * rad ^ (2 * alpha) *
            volume.real (ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
              Set (SpatialCoordinates d))) := by
  obtain ⟨Cd, hCd, hjoin⟩ := aux_lem_as_regularity_macro_rho_join (d := d) alpha ha ha1
  refine ⟨Cd, hCd, ?_⟩
  intro hd E P M H om N rho hrho hrho1 CP hCP hPoinc t e e' K Kf Mx ht he he' hee he1 hK hKf hMx hexp hlo hsumm v hen Z A Xc Kmic x hx rad hrad hradR
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n =>
    mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 n)
      (aux_lane4_lambda_inv_moments_Y_nonneg _ _)
  have hA : 0 ≤ A := zero_le_one.trans (le_max_left _ _)
  have hX : 0 ≤ Xc := add_nonneg zero_le_one (mul_nonneg hA (add_nonneg hK hZ0))
  have hmic : 0 ≤ Kmic := mul_nonneg
    (mul_nonneg (add_nonneg zero_le_one hCP) (add_nonneg hMx (abs_nonneg _)))
    (Real.rpow_nonneg (aux_lem_as_regularity_macro_rho_side_pos hrho N).le _)
  have hcell := aux_lem_as_regularity_macro_rho_cell_variance hd E P M H om N rho hrho hrho1
    t alpha e e' K Kf ht he' hee he1 hK hexp hsumm v hen
  have hmicro : ∀ p ∈ ball (0 : SpatialCoordinates d) (rho / 2), ∀ s : ℝ,
      0 < s → s ≤ aux_lem_as_regularity_macro_rho_side rho N →
      aux_prop_growth_holder_macro_campanato_var
        (ball p s ∩ ball (0 : SpatialCoordinates d) (rho / 2))
        ((v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1 :
          SpatialCoordinates d → ℝ) ≤
        (Kmic * Kf) ^ 2 * s ^ (2 * alpha) *
          volume.real (ball p s ∩ ball (0 : SpatialCoordinates d) (rho / 2)) := by
    intro p hp s hs hse
    have hsR : s ≤ rho := hse.trans ((mul_le_mul_of_nonneg_left
      (aux_prop_growth_holder_macro_campanato_side_le_one N) hrho.le).trans_eq (mul_one _))
    have h := aux_lem_as_regularity_macro_rho_micro_pathwise CP hCP hPoinc rho hrho
      (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho) Mx hMx hlo v
      K Kf t alpha e (aux_lem_as_regularity_macro_rho_side rho N) s hs hse hsR he
      (by linarith) (fun c hc => hen c hc s hs hsR) p hp
    rw [aux_prop_growth_holder_macro_campanato_target_eq
      (isOpen_ball.measurableSet.inter
        (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)
      Set.inter_subset_right] at h
    exact h
  rw [aux_prop_growth_holder_macro_campanato_target_eq
    (isOpen_ball.measurableSet.inter
      (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)
    Set.inter_subset_right]
  exact hjoin rho hrho _
    (aux_lem_as_regularity_macro_rho_memLp hrho
      (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)).1)
    N Xc Kmic Kf hX hmic hKf (fun j _ k hk => hcell j k hk) hmicro x hx rad hrad hradR

/-- The remaining native residual-cube energy input, with every source and
solution inside the same pathwise assertion. -/
def aux_lem_as_regularity_rho_energy_estimate {d : ℕ} (rho : ℝ) (hrho : 0 < rho)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) rho hrho))
    (t K : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
    AEMeasurable F (volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho :
      Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) rho hrho :
      Set (SpatialCoordinates d)), |F x| ≤ Kf) →
    (∫ x in (centeredCube (0 : SpatialCoordinates d) rho hrho : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) rho hrho),
    SolvesNeumann a F v →
    ∀ x ∈ centeredCube (0 : SpatialCoordinates d) rho hrho, ∀ rad : ℝ,
      0 < rad → rad ≤ rho →
      localGradientEnergy a
        (s := ball x rad ∩ (centeredCube (0 : SpatialCoordinates d) rho hrho :
          Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter
          (centeredCube (0 : SpatialCoordinates d) rho hrho).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho))) ≤
        K * Kf ^ 2 * rad ^ t

/-- Uniform finite moments of the complete native Neumann estimates follow
from the residual energy bank. The disorder threshold is chosen before the
model, side length, and energy-bank constants. No residual regularity supplier
is assumed in the Campanato or moment calculation. -/
theorem aux_lem_as_regularity_rho_bank_of_energy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (Cp : CampanatoInput d)
    (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hgap : 0 < 2 + t - 2 * alpha - d) (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (rho : ℝ) (hrho : 0 < rho), rho ≤ 1 →
        ∀ (K : ℕ → BilateralField d → ℝ) (CK : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) →
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) →
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (CK i)) →
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          aux_lem_as_regularity_rho_energy_estimate rho hrho
            (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho) t (K N om)) →
        ∃ (KH : ℕ → BilateralField d → ℝ) (CH : Fin k → ℝ),
          (∀ N om, 0 ≤ KH N om) ∧
          (∀ i N, MemLp (KH N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (KH N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CH i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
            aux_lem_as_regularity_nc_estimate (0 : SpatialCoordinates d) rho hrho
              (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
              t alpha (KH N om) := by
  let e : ℝ := 2 + t - 2 * alpha - d
  have he : 0 < e := hgap
  let ep : ℝ := min e 1
  have hep : 0 < ep := lt_min he one_pos
  have hepe : ep ≤ e := min_le_left _ _
  have hep1 : ep ≤ 1 := min_le_right _ _
  let q : ℝ := 2 * (d : ℝ) / ep + ∑ i, ps i + 1
  have hsum : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => zero_le_one.trans (hps i)
  have hdq : 0 ≤ 2 * (d : ℝ) / ep := div_nonneg (by positivity) hep.le
  have hq : 1 ≤ q := by dsimp only [q]; linarith
  have hpq : ∀ i, ps i ≤ q := by
    intro i
    have h := Finset.single_le_sum (fun j _ => zero_le_one.trans (hps j)) (Finset.mem_univ i)
    dsimp only [q]
    linarith
  have hDQ : 2 * (d : ℝ) ≤ ep * q := by
    dsimp only [q]
    rw [mul_add, mul_add, mul_div_cancel₀ _ hep.ne']
    have h := mul_nonneg hep.le hsum
    linarith
  obtain ⟨deltaZ, hdeltaZ, hZbank⟩ :=
    aux_lem_as_regularity_macro_rho_Z_moments d hd E ep q hep hq hDQ
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd q hq
  obtain ⟨CP, hCP, hPoinc⟩ :=
    aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  obtain ⟨Cc, hCc1, hcamp⟩ := aux_lem_as_regularity_macro_rho_campanato_of_energy
    (d := d) alpha ha ha1.le
  have hCc : 0 ≤ Cc := zero_le_one.trans hCc1
  let da : ℝ := min 1 ((e / 2) * Real.log 3 / (Cd + Cpe))
  have hda : 0 < da := lt_min one_pos
    (div_pos (mul_pos (half_pos he) (Real.log_pos (by norm_num))) (add_pos hCd hCpe))
  have hq0 : 0 < 2 * q := by linarith
  refine ⟨min deltaZ (min (cd / (2 * q)) da),
    lt_min hdeltaZ (lt_min (div_pos hcd hq0) hda), ?_⟩
  intro M Rm H hIR hdelta rho hrho hrho1 K CK hK0 hKL hKB henergy
  obtain ⟨CZ, hZN⟩ := hZbank M Rm H hIR (hdelta.trans (min_le_left _ _)) rho hrho hrho1
  obtain ⟨Dx, Mx, CE, hCE, hDMx, hext, hMxLp, -, hMxB⟩ :=
    hroot M H hIR (hdelta.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (0 : SpatialCoordinates d) rho hrho hrho1
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe
      M.shellPrefix.delta_pos (hdelta.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Z : ℕ → BilateralField d → ℝ := fun N om =>
    ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight ep 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (0 : SpatialCoordinates d) rho hrho
          (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho)
          (0 : SpatialCoordinates d) rho)
  have hZ0 : ∀ N om, 0 ≤ Z N om := fun N om => tsum_nonneg fun n =>
    mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum ep hep).2.2 n)
      (aux_lane4_lambda_inv_moments_Y_nonneg _ _)
  have hZL : ∀ i N, MemLp (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
    fun i N => (hZN N).1.mono_exponent (ENNReal.ofReal_le_ofReal (hpq i))
  have hZB : ∀ i N, eLpNorm (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CZ := fun i N =>
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpq i))
       ).trans (hZN N).2.1
  let A : ℝ := max 1 (P.C ^ 2 *
    ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-ep))))
  have hA : 0 ≤ A := zero_le_one.trans (le_max_left _ _)
  let Xc : ℕ → BilateralField d → ℝ := fun N om => 1 + A * (K N om + Z N om)
  let CX : Fin k → ℝ := fun i => 1 + A * (max (CK i) 0 + max CZ 0)
  have hX0 : ∀ N om, 0 ≤ Xc N om := fun N om =>
    add_nonneg zero_le_one (mul_nonneg hA (add_nonneg (hK0 N om) (hZ0 N om)))
  have hXmom := fun i N => aux_prop_growth_holder_assembly_moment
    (chaosSampleLaw M).toMeasure (hps i) (K N) (Z N) hA
    (hKL i N) (hZL i N) (hKB i N) (hZB i N)
  have hrpow : rho ^ (e / 2) ≤ 1 := Real.rpow_le_one hrho.le hrho1 (half_pos he).le
  have hfac (N : ℕ) :
      0 ≤ aux_lem_as_regularity_macro_rho_side rho N ^ (e / 2) ∧
      aux_lem_as_regularity_macro_rho_side rho N ^ (e / 2) ≤ 1 ∧
      aux_lem_as_regularity_macro_rho_side rho N ^ (e / 2) *
        Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N) ≤ 1 := by
    have h := aux_prop_growth_holder_micro_campanato_fac e _ he hrate N
    have hs : aux_prop_growth_holder_macro_campanato_side N = (3 : ℝ) ^ (-(N : ℤ)) := by
      simp only [aux_prop_growth_holder_macro_campanato_side, zpow_neg, zpow_natCast]
    rw [aux_lem_as_regularity_macro_rho_side,
      Real.mul_rpow hrho.le (aux_prop_growth_holder_macro_campanato_side_pos N).le, hs]
    have hp : 0 ≤ rho ^ (e / 2) := Real.rpow_nonneg hrho.le _
    refine ⟨mul_nonneg hp h.1, (mul_le_mul hrpow h.2.1 h.1 zero_le_one).trans_eq (mul_one 1), ?_⟩
    calc _ = rho ^ (e / 2) *
        (((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2) *
          Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N)) := mul_assoc _ _ _
      _ ≤ 1 * 1 := mul_le_mul hrpow h.2.2 (mul_nonneg h.1 (Real.exp_pos _).le) zero_le_one
      _ = 1 := mul_one 1
  let Km : ℕ → BilateralField d → ℝ := fun N om =>
    (1 + CP) * (Mx N om + |K N om|) * aux_lem_as_regularity_macro_rho_side rho N ^ (e / 2)
  let CM : Fin k → ℝ := fun i => (1 + CP) * (CE + max (CK i) 0)
  have hG : 0 ≤ 1 + CP := add_nonneg zero_le_one hCP
  have hM0 : ∀ N om, 0 ≤ Km N om := fun N om =>
    mul_nonneg (mul_nonneg hG (add_nonneg (hDMx N om).2 (abs_nonneg _))) (hfac N).1
  have hMmom := fun i N => aux_prop_growth_holder_micro_campanato_moment
    (chaosSampleLaw M).toMeasure (ps i) q (hps i) (hpq i) (Mx N) (K N)
    (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * N) CE (CK i)
    hG (hfac N).1 (hfac N).2.1 (hfac N).2.2 hCE (hMxLp N).2 (hMxB N) (hKL i N) (hKB i N)
  let Kc : ℕ → BilateralField d → ℝ := fun N om => 1 + Cc * (Xc N om + Km N om)
  let CB : Fin k → ℝ := fun i => 1 + Cc * (max (CX i) 0 + max (CM i) 0)
  have hKc0 : ∀ N om, 0 ≤ Kc N om := fun N om =>
    add_nonneg zero_le_one (mul_nonneg hCc (add_nonneg (hX0 N om) (hM0 N om)))
  have hCmom := fun i N => aux_prop_growth_holder_assembly_moment
    (chaosSampleLaw M).toMeasure (hps i) (Xc N) (Km N) hCc
    (hXmom i N).1 (hMmom i N).1 (hXmom i N).2 (hMmom i N).2
  let C : ℝ := max 1 ((2 + Real.sqrt d) * Cp.C alpha)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hCH : (2 + Real.sqrt d) * Cp.C alpha ≤ C := le_max_right _ _
  have hfinal := fun i N => aux_prop_growth_holder_assembly_moment
    (chaosSampleLaw M).toMeasure (hps i) (K N) (Kc N) hC0
    (hKL i N) (hCmom i N).1 (hKB i N) (hCmom i N).2
  refine ⟨fun N om => 1 + C * (K N om + Kc N om),
    fun i => 1 + C * (max (CK i) 0 + max (CB i) 0), ?_,
    fun i N => (hfinal i N).1, fun i N => (hfinal i N).2, ?_⟩
  · intro N om
    exact add_nonneg zero_le_one (mul_nonneg hC0 (add_nonneg (hK0 N om) (hKc0 N om)))
  · have hsumAE := ae_all_iff.mpr fun N => (hZN N).2.2
    filter_upwards [henergy, hext, hsumAE] with om hen hext hsumm
    intro N F Kf hKf hFm hFb hFz v hsol
    have hEn := hen N F Kf hKf hFm hFb hFz v hsol
    obtain ⟨hMxpos, hbounds, -⟩ := hext N
    have hlo := aux_lem_as_regularity_macro_rho_micro_floor M H om N rho hrho (Mx N om)
      hMxpos (fun y hy => (hbounds y hy).1)
    have hca := hcamp hd E P M H om N rho hrho hrho1 CP hCP hPoinc t e ep
      (K N om) Kf (Mx N om) ht he.le hep hepe hep1 (hK0 N om) hKf hMxpos.le
      (by dsimp only [e]; ring) hlo (hsumm N) v hEn
    obtain ⟨U, hUc, hUH, hUae, hUn⟩ := aux_lem_as_regularity_nc_holder_of_campanato
      Cp alpha ha ha1 (0 : SpatialCoordinates d) hrho hrho1 v (Kc N om) Kf (hKc0 N om) hKf hca
    have hbound (B : ℝ) (hB : 0 ≤ B) (hBK : B ≤ K N om + Kc N om) :
        B ≤ 1 + C * (K N om + Kc N om) := by
      calc B ≤ C * B := le_mul_of_one_le_left hB hC1
        _ ≤ C * (K N om + Kc N om) := mul_le_mul_of_nonneg_left hBK hC0
        _ ≤ 1 + C * (K N om + Kc N om) := by linarith
    refine ⟨⟨U, hUc, hUH, hUae, hUn.trans ?_⟩, ?_⟩
    · apply mul_le_mul_of_nonneg_right _ hKf
      calc (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ C * Kc N om :=
          mul_le_mul_of_nonneg_right hCH (hKc0 N om)
        _ ≤ C * (K N om + Kc N om) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hK0 N om)) hC0
        _ ≤ 1 + C * (K N om + Kc N om) := by linarith
    · intro x rad hx hrad _
      have hE := aux_lem_as_regularity_nc_energy_from_root_radius 0 rho hrho _
        (sobolevGradient (v : SobolevData (centeredCube (0 : SpatialCoordinates d) rho hrho)))
        t (K N om * Kf ^ 2) ht (mul_nonneg (hK0 N om) (sq_nonneg Kf)) hEn x hx rad hrad
      exact hE.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hbound _ (hK0 N om) (le_add_of_nonneg_right (hKc0 N om)))
          (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le _))
/-- A unit mean-zero Sobolev function pushes forward to any positive cube,
with its exact value and gradient ties. -/
theorem aux_lem_as_regularity_nc_meanzero_pushforward {d : ℕ}
    (z z0 : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v1 : meanZeroSobolevGraph (centeredCube z0 1 one_pos)) :
    ∃ v : meanZeroSobolevGraph (centeredCube z r hr),
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (v1 : SobolevData (centeredCube z0 1 one_pos)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z0 r x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (v1 : SobolevData (centeredCube z0 1 one_pos)).2 i x =
          r * (v : SobolevData (centeredCube z r hr)).2 i (cubeDilation z z0 r x)) := by
  obtain ⟨hv1w, hv1z⟩ := (mem_meanZeroSobolevGraph_iff _).mp v1.property
  obtain ⟨v, hv⟩ := aux_lem_as_regularity_affine_transport_weak_pushforward
    d z z0 r hr one_pos ⟨v1, hv1w⟩
  have hs := aux_lem_as_regularity_affine_transport_integral_scaling d z z0 r hr one_pos
    ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
    (Lp.aestronglyMeasurable _).aemeasurable
  have hz : (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (v : SobolevData (centeredCube z r hr)).1 y) = 0 := by
    have h : (r ^ d)⁻¹ * (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (v : SobolevData (centeredCube z r hr)).1 y) = 0 := by
      rw [← hs, ← integral_congr_ae hv, hv1z]
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (pow_ne_zero _ hr.ne'))
  refine ⟨⟨v, (mem_meanZeroSobolevGraph_iff _).mpr ⟨v.property, hz⟩⟩, hv, ?_⟩
  exact lane4_weak_gradient_chain_rule d z z0 r hr one_pos v v1 v.property hv1w hv

/-- Reverse Neumann transport, including the source factor `r⁻²`. -/
theorem aux_lem_as_regularity_nc_neumann_pushforward {d : ℕ}
    (z z0 : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a1 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (ha1 : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      a1.val x = a.val (cubeDilation z z0 r x))
    (G : SpatialCoordinates d → ℝ)
    (hG : AEMeasurable G (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))))
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (v1 : meanZeroSobolevGraph (centeredCube z0 1 one_pos))
    (hv : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (v1 : SobolevData (centeredCube z0 1 one_pos)).1 x =
        (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z0 r x))
    (hsol : SolvesNeumann a1 G v1) :
    SolvesNeumann a (fun y => (r ^ 2)⁻¹ * G (cubeDilation z0 z r⁻¹ y)) v := by
  have hqi := aux_prop_growth_large_root_qmp_inv z z0 hr
  let vw : weakSobolevGraph (centeredCube z r hr) :=
    ⟨v, ((mem_meanZeroSobolevGraph_iff _).mp v.property).1⟩
  let v1w : weakSobolevGraph (centeredCube z0 1 one_pos) :=
    ⟨v1, ((mem_meanZeroSobolevGraph_iff _).mp v1.property).1⟩
  intro psi
  obtain ⟨psi1, hpsi1, -⟩ := aux_lem_as_regularity_affine_transport_weak_pullback
    d z z0 r hr one_pos psi
  have hform := aux_lem_as_regularity_affine_transport_form_scaling d z z0 r hr one_pos
    a a1 vw psi v1w psi1 ha1 hv hpsi1
  let f : SpatialCoordinates d → ℝ := fun y =>
    (r ^ 2)⁻¹ * G (cubeDilation z0 z r⁻¹ y) * (psi : SobolevData (centeredCube z r hr)).1 y
  have hf : AEMeasurable f (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    ((hG.comp_quasiMeasurePreserving hqi).const_mul _).mul
      (Lp.aestronglyMeasurable (psi : SobolevData (centeredCube z r hr)).1).aemeasurable
  have hs := aux_lem_as_regularity_affine_transport_integral_scaling d z z0 r hr one_pos f hf
  have hbase : (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      f (cubeDilation z z0 r x)) = (r ^ 2)⁻¹ *
        ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          G x * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hpsi1] with x hx
    simp only [f]
    rw [aux_prop_growth_large_root_cubeDilation_inv_right z z0 hr x, hx]
    ring
  change sobolevCoefficientForm a (vw : SobolevData (centeredCube z r hr)) psi.val =
    ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y
  rw [hform, hsol psi1]
  have hpow := aux_lem_as_regularity_affine_transport_pow_split d r hr
  have hrd : (r ^ d : ℝ) ≠ 0 := pow_ne_zero _ hr.ne'
  calc r ^ ((d : ℝ) - 2) * ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        G x * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 x
      = r ^ d * ((r ^ 2)⁻¹ * ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        G x * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 x) := by
          rw [hpow]
          field_simp
    _ = r ^ d * ((r ^ d)⁻¹ * ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) := by
      rw [← hbase, hs]
    _ = _ := by field_simp

/-- The complete native estimate on a residual cube implies the estimate for
its actual unit-cube pullback. This closes the interface used by `nc_core`.
The energy factor is `rho^(t-d-2)`; the full Hölder norm costs `rho⁻²`. -/
theorem aux_lem_as_regularity_nc_residual_pullback {d : ℕ}
    (z z0 : SpatialCoordinates d) (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (a : PositiveCoefficient (centeredCube z rho hrho))
    (a1 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (ha1 : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      a1.val x = a.val (cubeDilation z z0 rho x))
    (t alpha K : ℝ) (halpha : 0 ≤ alpha) (hK : 0 ≤ K)
    (hest : aux_lem_as_regularity_nc_estimate z rho hrho a t alpha K) :
    aux_lem_as_regularity_nc_estimate z0 1 one_pos a1 t alpha
      (((rho ^ 2)⁻¹ + rho ^ (t - d - 2)) * K) := by
  intro F Kf hKf hFm hFb hFz v1 hsol
  obtain ⟨v, hv, hgrad⟩ := aux_lem_as_regularity_nc_meanzero_pushforward z z0 rho hrho v1
  let Fr : SpatialCoordinates d → ℝ := fun y => (rho ^ 2)⁻¹ * F (cubeDilation z0 z rho⁻¹ y)
  have hqi := aux_prop_growth_large_root_qmp_inv z z0 hrho
  have hFr : AEMeasurable Fr (volume.restrict (centeredCube z rho hrho : Set (SpatialCoordinates d))) :=
    (hFm.comp_quasiMeasurePreserving hqi).const_mul _
  have hFrb : ∀ᵐ y ∂volume.restrict (centeredCube z rho hrho : Set (SpatialCoordinates d)),
      |Fr y| ≤ (rho ^ 2)⁻¹ * Kf := by
    filter_upwards [hqi.ae hFb] with y hy
    dsimp only [Fr]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr (sq_nonneg _))
  have hFrz : (∫ y in (centeredCube z rho hrho : Set (SpatialCoordinates d)), Fr y) = 0 := by
    have hs := aux_lem_as_regularity_affine_transport_integral_scaling d z z0 rho hrho one_pos Fr hFr
    have hzero : (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        Fr (cubeDilation z z0 rho x)) = 0 := by
      simp only [Fr, aux_prop_growth_large_root_cubeDilation_inv_right z z0 hrho,
        integral_const_mul, hFz, mul_zero]
    rw [hs] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (pow_ne_zero _ hrho.ne'))
  have hsolr := aux_lem_as_regularity_nc_neumann_pushforward z z0 rho hrho a a1 ha1 F hFm v v1 hv hsol
  obtain ⟨⟨U, hUc, hUH, hUae, hUn⟩, hEn⟩ :=
    hest Fr ((rho ^ 2)⁻¹ * Kf) (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) hKf)
      hFr hFrb hFrz v hsolr
  have hHfac : (rho ^ 2)⁻¹ * K ≤ ((rho ^ 2)⁻¹ + rho ^ (t - d - 2)) * K :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.rpow_nonneg hrho.le _)) hK
  have hEfac : rho ^ (t - d - 2) * K ≤ ((rho ^ 2)⁻¹ + rho ^ (t - d - 2)) * K :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (inv_nonneg.mpr (sq_nonneg _))) hK
  constructor
  · have hrhoi : 1 ≤ rho⁻¹ := (one_le_inv₀ hrho).mpr hrho1
    have hscale : (1 : ℝ) = rho⁻¹ * rho := (inv_mul_cancel₀ hrho.ne').symm
    obtain ⟨hVc, hVH, hVn⟩ := aux_prop_growth_large_root_holder_transport_gen z0 z one_pos
      hrho hrhoi hscale halpha U hUc hUH
    simp only [inv_inv] at hVc hVH hVn
    refine ⟨fun x => U (cubeDilation z z0 rho x), hVc, hVH, ?_, ?_⟩
    · have hq := lane4_dilation_quasi_measure_preserving d z z0 rho hrho one_pos
      filter_upwards [hv, hq.ae hUae] with x hx hu
      exact hx.trans hu
    · calc _ ≤ K * ((rho ^ 2)⁻¹ * Kf) := hVn.trans hUn
        _ = ((rho ^ 2)⁻¹ * K) * Kf := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hHfac hKf
  · intro x rad hx hrad hrad1
    have hxR : cubeDilation z z0 rho x ∈ centeredCube z rho hrho := by
      change x ∈ cubeDilation z z0 rho ⁻¹' (centeredCube z rho hrho : Set (SpatialCoordinates d))
      rwa [cubeDilation_preimage_centeredCube z z0 hrho one_pos]
    have hradr : rho * rad ≤ 1 := (mul_le_mul hrho1 hrad1 hrad.le zero_le_one).trans_eq (one_mul 1)
    have hEL := hEn _ (rho * rad) hxR (mul_pos hrho hrad) hradr
    have hscale := aux_lem_as_regularity_affine_transport_local_energy_scaling
      d z z0 rho hrho one_pos a a1 (sobolevGradient (v : SobolevData (centeredCube z rho hrho)))
      (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos))) ha1 hgrad x rad hrad
    have hp : rho ^ ((2 : ℝ) - d) * ((rho ^ (2 : ℕ))⁻¹) ^ 2 * rho ^ t =
        rho ^ (t - d - 2) := by
      have hi : (rho ^ (2 : ℕ))⁻¹ = rho ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hrho.le, Real.rpow_two]
      rw [hi, ← Real.rpow_natCast, ← Real.rpow_mul hrho.le,
        ← Real.rpow_add hrho, ← Real.rpow_add hrho]
      congr 1
      norm_num
      ring
    calc _ = rho ^ ((2 : ℝ) - d) * localGradientEnergy a
          (s := ball (cubeDilation z z0 rho x) (rho * rad) ∩
            (centeredCube z rho hrho : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z rho hrho).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube z rho hrho))) := hscale
      _ ≤ rho ^ ((2 : ℝ) - d) * (K * ((rho ^ 2)⁻¹ * Kf) ^ 2 * (rho * rad) ^ t) :=
        mul_le_mul_of_nonneg_left hEL (Real.rpow_nonneg hrho.le _)
      _ = (rho ^ (t - d - 2) * K) * Kf ^ 2 * rad ^ t := by
        rw [Real.mul_rpow hrho.le hrad.le]
        calc _ = (rho ^ ((2 : ℝ) - d) * ((rho ^ (2 : ℕ))⁻¹) ^ 2 * rho ^ t) * K * Kf ^ 2 * rad ^ t := by ring
          _ = _ := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEfac (sq_nonneg Kf))
        (Real.rpow_nonneg hrad.le _)
/-- Native residual-cube estimates fit the exact coefficient interface of
`nc_core`, without assuming regularity of an unrelated pulled-back field. -/
theorem aux_lem_as_regularity_nc_core_native_residual {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (m : ℤ) (r rho : ℝ) (hr : 0 < r)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hreq : r = (3 : ℝ) ^ (-m) * rho)
    (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ alpha) (N : ℕ) (om : BilateralField d)
    (hcoef : ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (z + (3 : ℝ) ^ (-m) • y) =
        aux_transport_reference M H N m z om *
          cutoffCoefficient M H (aux_transport_S m z om) (((N : ℤ) - m).toNat) y)
    (K : ℝ) (hK : 0 ≤ K)
    (hest : aux_lem_as_regularity_nc_estimate (0 : SpatialCoordinates d) rho hrho
      (cutoffPositiveCoefficient M H (aux_transport_S m z om) (((N : ℤ) - m).toNat) 0 hrho)
      t alpha K) :
    aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
      t alpha (aux_lem_as_regularity_nc_factor d r t alpha *
        (((rho ^ 2)⁻¹ + rho ^ (t - d - 2)) * K) /
        aux_transport_reference M H N m z om) := by
  apply aux_lem_as_regularity_nc_core M H z m r rho hr hrho hreq t alpha ht ha N om hcoef
    (((rho ^ 2)⁻¹ + rho ^ (t - d - 2)) * K)
    (mul_nonneg (add_nonneg (inv_nonneg.mpr (sq_nonneg _)) (Real.rpow_nonneg hrho.le _)) hK)
  intro a1 ha1
  exact aux_lem_as_regularity_nc_residual_pullback 0 (fun _ => (1 / 2 : ℝ)) rho hrho hrho1
    _ a1 ha1 t alpha K ha hK hest

/-- Finite-moment transport from the native residual coefficient to every
translated cube with that residual side. The only cutoffs excluded here have
negative shifted index and are handled by the proved microscopic finite bank. -/
theorem aux_lem_as_regularity_nc_native_residual_finite_bank
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (m : ℤ) (r rho : ℝ) (hr : 0 < r)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hreq : r = (3 : ℝ) ^ (-m) * rho)
    (t alpha : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ alpha)
    (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i)
    (Krho : ℕ → BilateralField d → ℝ) (Crho : Fin k → ℝ)
    (hKrho : ∀ N om, 0 ≤ Krho N om)
    (hKL : ∀ i N, MemLp (Krho N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure)
    (hKB : ∀ i N, eLpNorm (Krho N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Crho i))
    (hAE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
      aux_lem_as_regularity_nc_estimate (0 : SpatialCoordinates d) rho hrho
        (cutoffPositiveCoefficient M H om N 0 hrho) t alpha (Krho N om)) :
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ K N om) ∧
      (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, m ≤ (N : ℤ) →
        aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
          t alpha (K N om) := by
  let A : ℝ := aux_lem_as_regularity_nc_factor d r t alpha *
    ((rho ^ 2)⁻¹ + rho ^ (t - d - 2))
  have hA : 0 ≤ A := by dsimp [A, aux_lem_as_regularity_nc_factor]; positivity
  have hmom := fun i => aux_lem_as_regularity_nc_transport_moment hd M H hIR z m (ps i) A
    (max (Crho i) 0) (lt_of_lt_of_le zero_lt_one (hps i)) hA (le_max_right _ _) Krho (hKL i)
      (fun N => (hKB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  choose Cref hCref hRef using hmom
  let K : ℕ → BilateralField d → ℝ := fun N om =>
    if m ≤ (N : ℤ) then A * Krho (((N : ℤ) - m).toNat) (aux_transport_S m z om) /
      aux_transport_reference M H N m z om else 0
  refine ⟨K, Cref, ?_, ?_, ?_, ?_⟩
  · intro N om
    dsimp only [K]
    split_ifs
    · exact div_nonneg (mul_nonneg hA (hKrho _ _)) (aux_transport_reference_pos M H N m z om).le
    · exact le_rfl
  · intro i N
    by_cases hN : m ≤ (N : ℤ)
    · simpa only [K, if_pos hN] using (hRef i N hN).1
    · simpa only [K, if_neg hN] using (memLp_const (0 : ℝ) :
        MemLp (fun _ : BilateralField d => (0 : ℝ)) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure)
  · intro i N
    by_cases hN : m ≤ (N : ℤ)
    · simpa only [K, if_pos hN] using (hRef i N hN).2
    · simp only [K, if_neg hN, eLpNorm_zero', zero_le]
  · have hshift := (aux_transport_S_measurePreserving M m z).quasiMeasurePreserving.ae hAE
    have hcoef := ae_all_iff.mpr fun N : ℕ => ae_all_iff.mpr fun hN : m ≤ (N : ℤ) =>
      aux_transport_coefficient M m z hIR N hN
    filter_upwards [hshift, hcoef] with om hest hcoef
    intro N hN
    have h := aux_lem_as_regularity_nc_core_native_residual M H z m r rho hr hrho hrho1 hreq
      t alpha ht ha N om (hcoef N hN) _ (hKrho _ _) (hest (((N : ℤ) - m).toNat))
    simpa only [K, if_pos hN, A, mul_assoc] using h

/-- The global bounded-source Neumann estimate on an arbitrary positive cube.
The factors are its physical volume and the square of its side length. -/
theorem aux_lem_as_regularity_nc_global_energy {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (v : meanZeroSobolevGraph (centeredCube z r hr)) (hsol : SolvesNeumann a F v) :
    sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
      (v : SobolevData (centeredCube z r hr)) ≤
      (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * P.C ^ 2 * r ^ 2 *
        (E.lam z r hr a z r 1 1)⁻¹) * Kf ^ 2 := by
  let V : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  let En : ℝ := sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
    (v : SobolevData (centeredCube z r hr))
  let lam : ℝ := E.lam z r hr a z r 1 1
  have hV : 0 < V := centeredCube_volume_pos z hr
  have hsqV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hEn : 0 ≤ En := sobolevCoefficientForm_nonneg a _
  have hlam : 0 < lam := E.lam_pos _ _ _ _ _ _ _ _
  have hweak : (v : SobolevData (centeredCube z r hr)) ∈ weakSobolevGraph (centeredCube z r hr) :=
    (inf_le_left : meanZeroSobolevGraph (centeredCube z r hr) ≤
      weakSobolevGraph (centeredCube z r hr)) v.property
  have hid : En = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      F x * (v : SobolevData (centeredCube z r hr)).1 x := hsol ⟨v, hweak⟩
  have hpair := aux_aux_macro_moment_bank_source_pairing_le F Kf hKf hFm hFb
    (v : SobolevData (centeredCube z r hr)).1
  have hvol : (measureUnivNNReal
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) : ℝ) = V := by
    change ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) univ).toReal = V
    simp only [Measure.restrict_apply_univ]
    rfl
  rw [hvol] at hpair
  norm_num only [ENNReal.toReal_ofNat] at hpair
  rw [← Real.sqrt_eq_rpow] at hpair
  have hP := P.poincare_meanZero_all_radii z r hr a v
  have hnorm : normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (centeredCube z r hr))) =
      Real.sqrt En / Real.sqrt V := by
    unfold normalizedEnergyNorm
    rw [localGradientEnergy_domain_eq_sobolevCoefficientForm]
    exact Real.sqrt_div hEn _
  rw [hnorm] at hP
  have hn : ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
      P.C * r * lam ^ (-(1 / 2) : ℝ) * Real.sqrt En := by
    have h := mul_le_mul_of_nonneg_right hP hsqV.le
    simpa only [V, lam, mul_assoc, div_mul_cancel₀ _ hsqV.ne'] using h
  have he : En ≤ (Real.sqrt V * Kf * (P.C * r * lam ^ (-(1 / 2) : ℝ))) * Real.sqrt En := by
    calc En ≤ Real.sqrt V * Kf * ‖(v : SobolevData (centeredCube z r hr)).1‖ := by
          rw [hid]
          exact hpair
      _ ≤ Real.sqrt V * Kf * (P.C * r * lam ^ (-(1 / 2) : ℝ) * Real.sqrt En) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg hsqV.le hKf)
      _ = _ := by ring
  have hs : (lam ^ (-(1 / 2) : ℝ)) ^ 2 = lam⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    exact Real.rpow_neg_one lam
  calc En ≤ (Real.sqrt V * Kf * (P.C * r * lam ^ (-(1 / 2) : ℝ))) ^ 2 :=
        aux_prop_neumann_growth_absorb _ _ hEn he
    _ = (Real.sqrt V) ^ 2 * P.C ^ 2 * r ^ 2 * (lam ^ (-(1 / 2) : ℝ)) ^ 2 * Kf ^ 2 := by ring
    _ = (V * P.C ^ 2 * r ^ 2 * lam⁻¹) * Kf ^ 2 := by rw [Real.sq_sqrt hV.le, hs]

/-- A native global-energy bank on every fixed cube of side at most one.
Its moments are uniform in the cutoff, and its disorder threshold is chosen
before the model and the cube. This supplies the global term in a local-growth
argument; it does not assert local energy decay. -/
theorem aux_lem_as_regularity_nc_global_energy_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ (K : ℕ → BilateralField d → ℝ) (CK : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CK i)) ∧
          ∀ (om : BilateralField d) (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
            ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
              SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
                (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) ≤
                K N om * Kf ^ 2 := by
  obtain ⟨dl, hdl, hl⟩ := lane4_lambda_inv_moments d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
  have hdli : ∀ i : Fin k, 0 < dl (ps i) := fun i => hdl _ (hps i)
  refine ⟨1 / (1 + ∑ i : Fin k, 1 / dl (ps i)),
    aux_prop_neumann_growth_delta_pos _ hdli, ?_⟩
  intro M Rm H hIR hdelta z r hr hr1
  have hD : ∀ i : Fin k, M.delta ≤ dl (ps i) := fun i =>
    hdelta.trans (aux_prop_neumann_growth_delta_min _ hdli i)
  choose CL hLL hLB using fun i : Fin k => hl M Rm H hIR z r hr hr1 (ps i) (hps i) (hD i)
  let A : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * P.C ^ 2 * r ^ 2
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (centeredCube_volume_pos z hr).le (sq_nonneg _)) (sq_nonneg _)
  let Lam : ℕ → BilateralField d → ℝ := fun N om =>
    (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8 : ℝ) 1)⁻¹
  refine ⟨fun N om => A * Lam N om, fun i => A * CL i, ?_,
    fun i N => (hLL i N).const_mul A, ?_, ?_⟩
  · intro N om
    exact mul_nonneg hA (inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le)
  · intro i N
    calc eLpNorm (fun om => A * Lam N om) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ‖A‖ₑ * eLpNorm (Lam N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
          eLpNorm_const_smul_le (c := A) (f := Lam N) (p := ENNReal.ofReal (ps i))
            (μ := (chaosSampleLaw M).toMeasure)
      _ = ENNReal.ofReal A * eLpNorm (Lam N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure := by rw [Real.enorm_eq_ofReal hA]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (CL i) := mul_le_mul_right (hLB i N) _
      _ = ENNReal.ofReal (A * CL i) := (ENNReal.ofReal_mul hA).symm
  · intro om N F Kf hKf hFm hFb v hsol
    have hinv : (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r 1 1)⁻¹ ≤ Lam N om :=
      inv_anti₀ (E.lam_pos _ _ _ _ _ _ _ _)
        (E.lam_mono z r hr _ z r 1 (1 / 8 : ℝ) 1 (by norm_num))
    exact (aux_lem_as_regularity_nc_global_energy hd E P z r hr _ F Kf hKf hFm hFb v hsol).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hA) (sq_nonneg Kf))


/-- Absorb the finitely many exceptional depths into one random allowance. -/
theorem aux_lem_as_regularity_allowance_of_summable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Cat : ℕ → Type*) [∀ n, Fintype (Cat n)]
    (B : (n : ℕ) → Cat n → Ω → ℝ) (xi : ℝ) (hxi : 0 ≤ xi)
    (hsum : ∑' n : ℕ, P {om | ∃ i : Cat n, xi * n < B n i om} ≠ ⊤) :
    ∀ᵐ om ∂P, ∃ B0 : ℝ, 0 < B0 ∧ ∀ (n : ℕ) (i : Cat n),
      B n i om ≤ xi * n + B0 := by
  classical
  have hbc := ae_eventually_notMem (μ := P) hsum
  filter_upwards [hbc] with om hom
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hom
  let S : ℝ := ∑ n ∈ Finset.range n0, ∑ i : Cat n, max (B n i om) 0
  have hS : 0 ≤ S := Finset.sum_nonneg fun n _ =>
    Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨1 + S, by linarith, ?_⟩
  intro n i
  have hx : 0 ≤ xi * n := mul_nonneg hxi (Nat.cast_nonneg n)
  by_cases hn : n < n0
  · have h1 : max (B n i om) 0 ≤ ∑ j : Cat n, max (B n j om) 0 :=
      Finset.single_le_sum (f := fun j : Cat n => max (B n j om) 0)
        (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    have h2 : (∑ j : Cat n, max (B n j om) 0) ≤ S :=
      Finset.single_le_sum (f := fun m : ℕ => ∑ j : Cat m, max (B m j om) 0)
        (fun m _ => Finset.sum_nonneg fun j _ => le_max_right _ _)
        (Finset.mem_range.mpr hn)
    have h3 := (le_max_left (B n i om) 0).trans (h1.trans h2)
    linarith
  · have h := hn0 n (Nat.le_of_not_gt hn)
    have hB : B n i om ≤ xi * n := by
      by_contra hgt
      exact h ⟨i, lt_of_not_ge hgt⟩
    linarith

/-- The polynomial factor in the number of constructions is absorbed by any
strict exponential gap. -/
theorem aux_lem_as_regularity_allowance_poly_exp (C g : ℝ) (p : ℕ) (hg : 0 < g) :
    Summable (fun n : ℕ => C * ((n : ℝ) + 1) ^ p * Real.exp (-g * n)) := by
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul p hg)
  have ht := hs.mul_left (C * Real.exp g)
  refine ht.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  calc C * Real.exp g * (((n : ℝ) + 1) ^ p * Real.exp (-g * ((n : ℝ) + 1))) =
      C * ((n : ℝ) + 1) ^ p * (Real.exp g * Real.exp (-g * ((n : ℝ) + 1))) := by ring
    _ = C * ((n : ℝ) + 1) ^ p * Real.exp (-g * n) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Paper 4622–4640: exponential prefix tails and the spatial catalogue count
give `B_pi ≤ xi*n + B_omega` simultaneously at every depth. -/
theorem aux_lem_as_regularity_spatial_allowance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Cat : ℕ → Type*) [∀ n, Fintype (Cat n)]
    (B : (n : ℕ) → Cat n → Ω → ℝ)
    (Ccount Ctail beta A xi : ℝ) (p : ℕ)
    (hCcount : 0 ≤ Ccount) (hCtail : 0 ≤ Ctail) (hxi : 0 ≤ xi)
    (hgap : beta < A * xi)
    (hcard : ∀ n, (Fintype.card (Cat n) : ℝ) ≤
      Ccount * ((n : ℝ) + 1) ^ p * Real.exp (beta * n))
    (htail : ∀ (n : ℕ) (i : Cat n) (b : ℝ), 0 ≤ b →
      P {om | b < B n i om} ≤ ENNReal.ofReal (Ctail * Real.exp (-A * b))) :
    ∀ᵐ om ∂P, ∃ B0 : ℝ, 0 < B0 ∧ ∀ (n : ℕ) (i : Cat n),
      B n i om ≤ xi * n + B0 := by
  have hbound (n : ℕ) : P {om | ∃ i : Cat n, xi * n < B n i om} ≤
      ENNReal.ofReal (Ccount * Ctail * ((n : ℝ) + 1) ^ p *
        Real.exp (-(A * xi - beta) * n)) := by
    have hset : {om | ∃ i : Cat n, xi * n < B n i om} =
        ⋃ i : Cat n, {om | xi * n < B n i om} := by ext om; simp
    rw [hset]
    calc P (⋃ i : Cat n, {om | xi * n < B n i om}) ≤
        ∑ i : Cat n, P {om | xi * n < B n i om} := measure_iUnion_fintype_le P _
      _ ≤ ∑ _i : Cat n, ENNReal.ofReal (Ctail * Real.exp (-A * (xi * n))) :=
        Finset.sum_le_sum fun i _ => htail n i (xi * n) (mul_nonneg hxi (Nat.cast_nonneg n))
      _ = ENNReal.ofReal ((Fintype.card (Cat n) : ℝ) *
          (Ctail * Real.exp (-A * (xi * n)))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal ((Ccount * ((n : ℝ) + 1) ^ p * Real.exp (beta * n)) *
          (Ctail * Real.exp (-A * (xi * n)))) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hcard n) (mul_nonneg hCtail (Real.exp_pos _).le))
      _ = _ := by
        congr 1
        calc (Ccount * ((n : ℝ) + 1) ^ p * Real.exp (beta * n)) *
            (Ctail * Real.exp (-A * (xi * n))) =
            Ccount * Ctail * ((n : ℝ) + 1) ^ p *
              (Real.exp (beta * n) * Real.exp (-A * (xi * n))) := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
  apply aux_lem_as_regularity_allowance_of_summable P Cat B xi hxi
  have hs := aux_lem_as_regularity_allowance_poly_exp (Ccount * Ctail)
    (A * xi - beta) p (sub_pos.mpr hgap)
  exact ne_top_of_le_ne_top (Summable.tsum_ofReal_ne_top hs) (ENNReal.tsum_le_tsum hbound)

/-- Paper 4580–4604: choose the truncation fraction before the smaller retained
prefix fraction; both geometric probability exponents have strict slack. -/
theorem aux_lem_as_regularity_prefix_fractions (D c b : ℝ)
    (hD : 0 ≤ D) (hc : 0 < c) (hb : 0 < b) :
    ∃ thetaTail : ℝ, 0 < thetaTail ∧
      ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaTail ∧ theta + thetaTail < 1 ∧
        D * (theta + thetaTail) < c * (1 - theta - thetaTail) ∧
        D * theta < b * thetaTail := by
  let thetaTail : ℝ := c / (8 * (D + c))
  have hDc : 0 < D + c := add_pos_of_nonneg_of_pos hD hc
  have htail : 0 < thetaTail := div_pos hc (mul_pos (by norm_num) hDc)
  have htailEq : 8 * (D + c) * thetaTail = c := by
    dsimp only [thetaTail]
    field_simp
  have htailLe : thetaTail ≤ 1 / 8 := by
    have h1 := mul_nonneg hD htail.le
    nlinarith
  let theta : ℝ := min thetaTail (b * thetaTail / (4 * (D + 1)))
  have htheta : 0 < theta := lt_min htail
    (div_pos (mul_pos hb htail) (by positivity))
  have hle : theta ≤ thetaTail := min_le_left _ _
  have hbound : 4 * (D + 1) * theta ≤ b * thetaTail := by
    have h : theta ≤ b * thetaTail / (4 * (D + 1)) := min_le_right _ _
    simpa only [mul_comm] using
      (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (D + 1))).mp h
  refine ⟨thetaTail, htail, theta, htheta, hle, by linarith, ?_, ?_⟩
  · have hsum : D * (theta + thetaTail) ≤ 2 * D * thetaTail := by nlinarith
    have hDtail := mul_nonneg hD htail.le
    nlinarith
  · have hDtheta := mul_nonneg hD htheta.le
    nlinarith


/-- The reference scalar in exact field covariance has a pathwise inverse
bound independent of the cutoff, on the entire nonnegative shifted range. -/
theorem aux_lem_as_regularity_nc_reference_uniform
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d)
    (N : ℕ) (hmN : m ≤ (N : ℤ)) :
    (aux_transport_reference M H N m w om)⁻¹ ≤
      Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        Real.exp (-(H om w + aux_transport_retained m w om)) := by
  have hratio := (aux_fscc_holNeuH_kappa_ratio_bound M m N hmN).1
  have hratio' : Real.exp (-((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ≤
      aux_transport_kappa M ((N : ℤ) - m).toNat / aux_transport_kappa M N := by
    simpa only [neg_mul] using hratio
  have h := one_div_le_one_div_of_le (Real.exp_pos _) hratio'
  have hinv : (aux_transport_kappa M ((N : ℤ) - m).toNat /
      aux_transport_kappa M N)⁻¹ ≤
      Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    simpa only [one_div, ← Real.exp_neg, neg_neg] using h
  unfold aux_transport_reference
  rw [mul_inv, ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le

/-- Exact scale transport of the imported common unit-cube Neumann bank.
The finite exceptional cutoffs use the proved moment bank; no bound on the
supremum of an arbitrary sequence of moment constants is asserted. -/
theorem aux_lem_as_regularity_nc_triadic_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ), r = (3 : ℝ) ^ j →
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
          t alpha K := by
  classical
  obtain ⟨δU, hδU, hU⟩ := aux_lem_as_regularity_unit_uniform_bank
    d hd E P X W D Cp Step Dbase Interp Sf t alpha ht htd ha ha1
  obtain ⟨δF, hδF, hF⟩ := aux_lem_as_regularity_nc_triadic_all_cutoffs
    d hd E P X W D Cp t alpha 1 (fun _ => 1) ht htd ha ha1 (fun _ => le_rfl)
  refine ⟨min δU δF, lt_min hδU hδF, ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr j hrj
  have hunit := hU M Rm Sreg It H hIR (hδ.trans (min_le_left _ _))
  let UnitEst : BilateralField d → ℝ → Prop := fun om B => ∀ N : ℕ,
    aux_lem_as_regularity_nc_estimate (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) t alpha B
  have hchoose : ∀ om : BilateralField d, ∃ B : ℝ, 0 < B ∧
      ((∃ B : ℝ, 0 < B ∧ UnitEst om B) → UnitEst om B) := by
    intro om
    by_cases h : ∃ B : ℝ, 0 < B ∧ UnitEst om B
    · obtain ⟨B, hB, hest⟩ := h
      exact ⟨B, hB, fun _ => hest⟩
    · exact ⟨1, one_pos, fun h' => (h h').elim⟩
  choose B hB hBS using hchoose
  have hBAE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, UnitEst om (B om) := by
    filter_upwards [hunit] with om hom
    exact hBS om hom
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hrm : r = (3 : ℝ) ^ (-(-j)) := by simpa only [neg_neg] using hrj
  let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
  let A : ℝ := aux_lem_as_regularity_nc_factor d r t alpha
  have hA : 0 ≤ A := by dsimp [A, aux_lem_as_regularity_nc_factor]; positivity
  let Ref : BilateralField d → ℝ := fun om =>
    Real.exp (((-j).natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
      Real.exp (-(H om w + aux_transport_retained (-j) w om))
  have hRef : ∀ om, 0 < Ref om := fun om => mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hhigh : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, -j ≤ (N : ℤ) →
      aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
        t alpha (A * B (aux_transport_S (-j) w om) * Ref om) := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro hN
    have h := aux_lem_as_regularity_nc_triadic_sample M H hIR z (-j) r hr hrm t alpha
      ht0 ha.le (fun _ om => B om) (fun _ om => (hB om).le) hBAE N hN
    filter_upwards [h] with om hom
    refine aux_lem_as_regularity_nc_estimate_mono ?_ hom
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (aux_lem_as_regularity_nc_reference_uniform M H (-j) w om N hN)
      (mul_nonneg hA (hB _).le)
  obtain ⟨KF, CF, hKF, _, _, hFAE⟩ := hF M Rm Sreg It H hIR
    (hδ.trans (min_le_right _ _)) z r hr j hrj
  filter_upwards [hhigh, hFAE] with om hhigh hfinite
  let S : ℝ := ∑ N ∈ Finset.range (-j).toNat, KF N om
  have hS : 0 ≤ S := Finset.sum_nonneg fun N _ => hKF N om
  let Kh : ℝ := A * B (aux_transport_S (-j) w om) * Ref om
  have hKh : 0 ≤ Kh := mul_nonneg (mul_nonneg hA (hB _).le) (hRef _).le
  refine ⟨1 + Kh + S, by positivity, ?_⟩
  intro N
  by_cases hN : -j ≤ (N : ℤ)
  · exact aux_lem_as_regularity_nc_estimate_mono (by dsimp only [Kh]; linarith) (hhigh N hN)
  · have hNm : N < (-j).toNat := by omega
    have hle : KF N om ≤ S :=
      Finset.single_le_sum (f := fun N => KF N om) (fun N _ => hKF N om)
        (Finset.mem_range.mpr hNm)
    exact aux_lem_as_regularity_nc_estimate_mono (by linarith) (hfinite N)



/-- Paper 4672–4674 ("their constants satisfy `K_N ≤ 3^{ξN}` almost surely eventually, for any
fixed `ξ>0`"): Markov at order one and Borel–Cantelli turn a cutoff-uniform first-moment bound
into one random factor `B` with `K_N ≤ B·3^{ξN}` for every `N`. -/
theorem aux_lem_as_regularity_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ → Ω → ℝ) (C : ℝ)
    (hmem : ∀ N, MemLp (K N) 1 P)
    (hnorm : ∀ N, eLpNorm (K N) 1 P ≤ ENNReal.ofReal C)
    (xi : ℝ) (hxi : 0 < xi) :
    ∀ᵐ om ∂P, ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, K N om ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)) := by
  set q : ℝ := (3 : ℝ) ^ (-xi) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set s : ℕ → Set Ω :=
    fun N => {om | ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) ≤ ‖K N om‖ₑ} with hs
  have hpow (N : ℕ) : 0 < (3 : ℝ) ^ (xi * (N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hqN (N : ℕ) : ((3 : ℝ) ^ (xi * (N : ℝ)))⁻¹ = q ^ N := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    ring_nf
  have hmeasN (N : ℕ) : P (s N) ≤ ENNReal.ofReal (max C 0 * q ^ N) := by
    have hM := mul_meas_ge_le_lintegral₀ (μ := P) ((hmem N).aestronglyMeasurable.enorm)
      (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))))
    rw [← eLpNorm_one_eq_lintegral_enorm (hmem N).aestronglyMeasurable] at hM
    have hM2 : ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) * P (s N) ≤
        ENNReal.ofReal (max C 0) :=
      hM.trans ((hnorm N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    have hne0 : ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hpow N
    have hnetop : ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc P (s N)
        = (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))))⁻¹ *
            (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) * P (s N)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
      _ ≤ (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))))⁻¹ * ENNReal.ofReal (max C 0) := by
          gcongr
      _ = ENNReal.ofReal (max C 0 * q ^ N) := by
          rw [← ENNReal.ofReal_inv_of_pos (hpow N),
            ← ENNReal.ofReal_mul (inv_nonneg.2 (hpow N).le), hqN, mul_comm]
  have hsum : ∑' N, P (s N) ≠ ⊤ := by
    have hsumm : Summable (fun N : ℕ => max C 0 * q ^ N) :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeasN)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun N => mul_nonneg (le_max_right _ _) (pow_nonneg hq0 N)) hsumm]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem (μ := P) hsum
  filter_upwards [hae] with om hom
  rcases eventually_atTop.1 hom with ⟨N0, hN0⟩
  have hS0 : 0 ≤ ∑ N ∈ Finset.range N0, |K N om| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨1 + ∑ N ∈ Finset.range N0, |K N om|, by linarith, ?_⟩
  intro N
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (xi * (N : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hxi.le (Nat.cast_nonneg N))
  by_cases hN : N < N0
  · have hle : |K N om| ≤ ∑ N ∈ Finset.range N0, |K N om| :=
      Finset.single_le_sum (f := fun N => |K N om|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hN)
    calc K N om ≤ |K N om| := le_abs_self _
      _ ≤ (1 + ∑ N ∈ Finset.range N0, |K N om|) * 1 := by linarith
      _ ≤ (1 + ∑ N ∈ Finset.range N0, |K N om|) * (3 : ℝ) ^ (xi * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
  · have hnot := hN0 N (not_lt.1 hN)
    simp only [hs, Set.mem_setOf_eq, not_le] at hnot
    rw [Real.enorm_eq_ofReal_abs] at hnot
    have hlt := (ENNReal.ofReal_lt_ofReal_iff (hpow N)).1 hnot
    calc K N om ≤ |K N om| := le_abs_self _
      _ ≤ 1 * (3 : ℝ) ^ (xi * (N : ℝ)) := by linarith
      _ ≤ (1 + ∑ N ∈ Finset.range N0, |K N om|) * (3 : ℝ) ^ (xi * (N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (hpow N).le

/-- Paper 4675–4680: for `ρ ≤ r_N = 3^{-θN}` and `ξ ≤ θe`, the envelope `K ≤ B·3^{ξN}` is
absorbed by the exponent gap: `K ρ^e ≤ B`. -/
theorem aux_lem_as_regularity_rpow_absorb
    (K B xi theta e r : ℝ) (N : ℕ)
    (hB : 0 < B)
    (hKB : K ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)))
    (he : 0 ≤ e) (hxi : xi ≤ theta * e)
    (hr : 0 < r) (hrN : r ≤ (3 : ℝ) ^ (-(theta * (N : ℝ)))) :
    K * r ^ e ≤ B := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3ge1 : (1 : ℝ) ≤ 3 := by norm_num
  have hB3 : (0 : ℝ) ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)) :=
    mul_nonneg hB.le (Real.rpow_pos_of_pos h3pos _).le
  have h2 : r ^ e ≤ (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) := by
    calc r ^ e ≤ ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ^ e :=
          Real.rpow_le_rpow hr.le hrN he
      _ = (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) :=
          (Real.rpow_mul (le_of_lt h3pos) _ e).symm
  have h3 : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * r ^ e ≤
            (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) :=
    mul_le_mul_of_nonneg_left h2 hB3
  have h4 : (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) =
            B * (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) := by
    rw [mul_assoc]
    congr 1
    rw [← Real.rpow_add h3pos]
    congr 1
    ring
  have h5 : (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos h3ge1
    have hle : xi - theta * e ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hle (Nat.cast_nonneg N)
  have h6 : B * (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) ≤ B * 1 :=
    mul_le_mul_of_nonneg_left h5 hB.le
  calc K * r ^ e
      ≤ (B * (3 : ℝ) ^ (xi * (N : ℝ))) * r ^ e :=
        mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg hr.le e)
    _ ≤ (B * (3 : ℝ) ^ (xi * (N : ℝ))) * (3 : ℝ) ^ ((-(theta * (N : ℝ))) * e) := h3
    _ = B * (3 : ℝ) ^ ((xi - theta * e) * (N : ℝ)) := h4
    _ ≤ B * 1 := h6
    _ = B := by ring

/-- A `C^a` bound with its `IsHolderOn` guard gives the pointwise increment bound. -/
theorem aux_lem_as_regularity_holder_pair {d : ℕ}
    (a A : ℝ) (ha : 0 < a) (S : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ)
    (hH : IsHolderOn a S U) (hA : cAlphaNorm a S U ≤ A)
    (x y : SpatialCoordinates d) (hx : x ∈ S) (hy : y ∈ S) :
    |U x - U y| ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ a := by
  by_cases hxy : x = y
  · subst hxy
    simp [Real.zero_rpow ha.ne']
  · have hne_coord : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨j, hj⟩ := hne_coord
    have hsum_pos : 0 < ∑ k : Fin d, (x k - y k) ^ 2 := by
      apply Finset.sum_pos'
      · intro k _
        positivity
      · exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
    set ρ := Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact Real.sqrt_pos.mpr hsum_pos
    have hρa_pos : 0 < ρ ^ a := Real.rpow_pos_of_pos hρpos a
    have hmem : |U x - U y| / ρ ^ a ∈ holderRatioSet a S U := by
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      rw [hρdef]
    have hle1 : |U x - U y| / ρ ^ a ≤ holderSeminorm a S U := le_csSup hH hmem
    have hfirst_nonneg : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} := by
      apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨w, _, rfl⟩
      exact abs_nonneg (U w)
    have hle2 : holderSeminorm a S U ≤ cAlphaNorm a S U := by
      unfold cAlphaNorm holderSeminorm
      linarith
    have hle3 : |U x - U y| / ρ ^ a ≤ A := le_trans hle1 (le_trans hle2 hA)
    rw [div_le_iff₀ hρa_pos] at hle3
    rw [hρdef] at hle3
    exact hle3

/-- Pointwise sup and increment bounds give the `C^α` class and norm bound. -/
theorem aux_lem_as_regularity_cAlphaNorm_of_pairs {d : ℕ}
    (alpha A Sup : ℝ) (hA : 0 ≤ A) (hSup : 0 ≤ Sup)
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ)
    (hsup : ∀ x ∈ S, |U x| ≤ Sup)
    (hpair : ∀ x ∈ S, ∀ y ∈ S,
      |U x - U y| ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    IsHolderOn alpha S U ∧ cAlphaNorm alpha S U ≤ Sup + A := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |U x - U y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ A := by
    intro x hxS y hyS hxy
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    have hj2 : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i - y i))
      (Finset.mem_univ j)
    have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := lt_of_lt_of_le hj2 hle
    have hpos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hsum_pos) alpha
    rw [div_le_iff₀ hpos]
    exact hpair x hxS y hyS
  constructor
  · unfold IsHolderOn
    refine ⟨A, ?_⟩
    intro v hv
    unfold holderRatioSet at hv
    obtain ⟨x, hxS, y, hyS, hxy, rfl⟩ := hv
    exact key x hxS y hyS hxy
  · unfold cAlphaNorm holderSeminorm holderRatioSet
    apply add_le_add
    · apply Real.sSup_le
      · intro v hv
        simp only [Set.mem_setOf_eq] at hv
        obtain ⟨x, hxS, rfl⟩ := hv
        exact hsup x hxS
      · exact hSup
    · apply Real.sSup_le
      · intro v hv
        simp only [Set.mem_setOf_eq] at hv
        obtain ⟨x, hxS, y, hyS, hxy, rfl⟩ := hv
        exact key x hxS y hyS hxy
      · exact hA

/-- The cube (sup) distance is at most the Euclidean distance used in the Hölder quotients. -/
theorem aux_lem_as_regularity_dist_le_euclid {d : ℕ} (x y : SpatialCoordinates d) :
    dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 (fun j => ?_)
  rw [Real.dist_eq]
  calc |x j - y j| = Real.sqrt ((x j - y j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => (x i - y i) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j))

/-- The Euclidean distance is at most `√d` times the cube (sup) distance. -/
theorem aux_lem_as_regularity_euclid_le_dist {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have hj : ∀ j, (x j - y j) ^ 2 ≤ (dist x y) ^ 2 := fun j => by
    have h := dist_le_pi_dist x y j
    rw [Real.dist_eq] at h
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ (dist x y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * (dist x y) ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, (dist x y) ^ 2 :=
          Finset.sum_le_sum (fun j _ => hj j)
      _ = (d : ℝ) * (dist x y) ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * (dist x y) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq dist_nonneg]

/-- Paper 4681–4682 ("point values ... are recovered by averaging at radius `r_N`"): if a
continuous representative varies by at most `c` on `B_ρ(x) ∩ Q`, its value at a point `x` of the
closed cube is within `c` of the average of the `L²` class over `B_ρ(x) ∩ Q`. -/
theorem aux_lem_as_regularity_avg_close {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : DomainL2 (centeredCube z r hr)) (U : SpatialCoordinates d → ℝ) (hUc : Continuous U)
    (hU : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (x : SpatialCoordinates d) (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    (rho : ℝ) (hrho : 0 < rho) (c : ℝ)
    (hc : ∀ w ∈ Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |U w - U x| ≤ c) :
    |setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u -
      U x| ≤ c := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQ
  set S : Set (SpatialCoordinates d) := Metric.ball x rho ∩ Q with hS
  have hQball : Q = Metric.ball z (r / 2) := rfl
  have hSm : MeasurableSet S := measurableSet_ball.inter (by rw [hQball]; exact measurableSet_ball)
  have hSsub : S ⊆ Q := inter_subset_right
  have hSne : S.Nonempty := by
    have hx' : x ∈ closure (Metric.ball z (r / 2)) := by
      rw [closure_ball z (by positivity : r / 2 ≠ 0)]
      exact hx
    obtain ⟨b, hb, hxb⟩ := Metric.mem_closure_iff.1 hx' rho hrho
    refine ⟨b, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      exact hxb
    · rw [hQball]
      exact hb
  have hSopen : IsOpen S := isOpen_ball.inter (by rw [hQball]; exact isOpen_ball)
  have hSpos : 0 < volume S := hSopen.measure_pos volume hSne
  have hSfin : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) measure_ball_lt_top
  have hvol : 0 < volume.real S := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hint : ∫ y in S, (u : SpatialCoordinates d → ℝ) y ∂volume.restrict Q =
      ∫ y in S, U y := by
    rw [Measure.restrict_restrict hSm, inter_eq_left.2 hSsub]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hSsub hU)
  have hbd : ∀ w ∈ S, ‖U w - U x‖ ≤ c := fun w hw => by
    rw [Real.norm_eq_abs]
    exact hc w hw
  have hbd_ae : ∀ᵐ w ∂(volume.restrict S), ‖U w - U x‖ ≤ c :=
    ae_restrict_of_forall_mem hSm hbd
  have hIf : IntegrableOn (fun w => U w - U x) S :=
    Measure.integrableOn_of_bounded hSfin.ne (hUc.sub continuous_const).aestronglyMeasurable
      hbd_ae
  have hIc : IntegrableOn (fun _ : SpatialCoordinates d => U x) S :=
    integrableOn_const hSfin.ne
  have hIU : IntegrableOn U S := by
    have h : IntegrableOn (fun w => (U w - U x) + U x) S := hIf.add hIc
    simpa using h
  have hsub : ∫ w in S, (U w - U x) = (∫ w in S, U w) - volume.real S * U x := by
    rw [integral_sub hIU hIc, setIntegral_const, smul_eq_mul]
  have hnorm := norm_setIntegral_le_of_norm_le_const hSfin hbd
  rw [Real.norm_eq_abs] at hnorm
  have hkey : setAverage S u - U x = (volume.real S)⁻¹ * ∫ w in S, (U w - U x) := by
    unfold setAverage
    rw [hint, hsub]
    field_simp
  rw [hkey, abs_mul, abs_inv, abs_of_pos hvol]
  calc (volume.real S)⁻¹ * |∫ w in S, (U w - U x)|
      ≤ (volume.real S)⁻¹ * (c * volume.real S) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hvol.le)
    _ = c := by field_simp

/-- Paper 4669–4683, Hölder part: small separations use the stronger exponent `α₀` with the
envelope absorbed below `r_N`; large separations use the common-constant averages at radius
`r_N` together with the point-value recovery. -/
theorem aux_lem_as_regularity_holder_combine {d : ℕ} (hd1 : 1 ≤ d)
    (S : Set (SpatialCoordinates d)) (U A : SpatialCoordinates d → ℝ)
    (alpha alpha0 rN c G KA B : ℝ)
    (hal : 0 < alpha) (hal0 : alpha < alpha0) (hal1 : alpha0 ≤ 1)
    (hrN : 0 < rN) (hrN1 : rN ≤ 1) (hc : 0 ≤ c) (hG : 0 ≤ G) (hB : 0 < B) (hKA : 0 ≤ KA)
    (habs : ∀ rho, 0 < rho → rho ≤ rN → G * rho ^ (alpha0 - alpha) ≤ B)
    (hsmall : ∀ x ∈ S, ∀ y ∈ S,
      |U x - U y| ≤ G * c * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha0)
    (hrec : ∀ x ∈ S, |A x - U x| ≤ G * c * (Real.sqrt d * rN) ^ alpha0)
    (hAsup : ∀ x ∈ S, |A x| ≤ KA * c)
    (hApair : ∀ x ∈ S, ∀ y ∈ S, rN ≤ dist x y → |A x - A y| ≤ KA * c * dist x y ^ alpha) :
    (∀ x ∈ S, |U x| ≤ (KA + Real.sqrt d * B) * c) ∧
    (∀ x ∈ S, ∀ y ∈ S, |U x - U y| ≤
      (KA + 3 * Real.sqrt d * B) * c * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  set s : ℝ := Real.sqrt d with hsdef
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    exact Real.one_le_sqrt.2 (by exact_mod_cast hd1)
  have hs0 : 0 ≤ s := by linarith
  have hsa0 : s ^ alpha0 ≤ s := by
    calc s ^ alpha0 ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 hal1
      _ = s := Real.rpow_one s
  have hga : 0 ≤ alpha0 - alpha := by linarith
  have hsag : s ^ (alpha0 - alpha) ≤ s := by
    calc s ^ (alpha0 - alpha) ≤ s ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
      _ = s := Real.rpow_one s
  -- the recovery term is at most `s B c rN^α`
  have hR : G * c * (s * rN) ^ alpha0 ≤ s * B * c * rN ^ alpha := by
    have hsplit : (s * rN) ^ alpha0 = s ^ alpha0 * (rN ^ (alpha0 - alpha) * rN ^ alpha) := by
      rw [Real.mul_rpow hs0 hrN.le, ← Real.rpow_add hrN]
      congr 2
      ring
    have hGr := habs rN hrN le_rfl
    have hra : 0 ≤ rN ^ alpha := Real.rpow_nonneg hrN.le _
    have hsa : 0 ≤ s ^ alpha0 := Real.rpow_nonneg hs0 _
    rw [hsplit]
    calc G * c * (s ^ alpha0 * (rN ^ (alpha0 - alpha) * rN ^ alpha))
        = c * s ^ alpha0 * rN ^ alpha * (G * rN ^ (alpha0 - alpha)) := by ring
      _ ≤ c * s ^ alpha0 * rN ^ alpha * B :=
          mul_le_mul_of_nonneg_left hGr (by positivity)
      _ ≤ c * s * rN ^ alpha * B := by
          apply mul_le_mul_of_nonneg_right _ hB.le
          apply mul_le_mul_of_nonneg_right _ hra
          exact mul_le_mul_of_nonneg_left hsa0 hc
      _ = s * B * c * rN ^ alpha := by ring
  have hrNa1 : rN ^ alpha ≤ 1 := Real.rpow_le_one hrN.le hrN1 hal.le
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h1 := hAsup x hx
    have h2 := (hrec x hx).trans hR
    have h3 : s * B * c * rN ^ alpha ≤ s * B * c := by
      calc s * B * c * rN ^ alpha ≤ s * B * c * 1 :=
            mul_le_mul_of_nonneg_left hrNa1 (by positivity)
        _ = s * B * c := by ring
    calc |U x| = |A x - (A x - U x)| := by ring_nf
      _ ≤ |A x| + |A x - U x| := abs_sub _ _
      _ ≤ KA * c + s * B * c := by linarith
      _ = (KA + s * B) * c := by ring
  · set e : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hedef
    have he0 : 0 ≤ e := Real.sqrt_nonneg _
    have hdist_e : dist x y ≤ e := aux_lem_as_regularity_dist_le_euclid x y
    have he_dist : e ≤ s * dist x y := aux_lem_as_regularity_euclid_le_dist x y
    have hea : 0 ≤ e ^ alpha := Real.rpow_nonneg he0 _
    have hK3 : 0 ≤ (KA + 3 * s * B) * c := by positivity
    by_cases hxy : x = y
    · subst hxy
      simp only [sub_self, abs_zero]
      exact mul_nonneg hK3 hea
    have hdpos : 0 < dist x y := dist_pos.2 hxy
    rcases lt_or_ge (dist x y) rN with hlt | hge
    · -- small separation: stronger exponent, envelope absorbed
      have hepos : 0 < e := lt_of_lt_of_le hdpos hdist_e
      have hsplit : e ^ alpha0 = e ^ (alpha0 - alpha) * e ^ alpha := by
        rw [← Real.rpow_add hepos]
        congr 1
        ring
      have hge' : e ^ (alpha0 - alpha) ≤ s ^ (alpha0 - alpha) * dist x y ^ (alpha0 - alpha) := by
        rw [← Real.mul_rpow hs0 dist_nonneg]
        exact Real.rpow_le_rpow he0 he_dist hga
      have hGd := habs (dist x y) hdpos hlt.le
      have hGe : G * e ^ (alpha0 - alpha) ≤ s * B := by
        calc G * e ^ (alpha0 - alpha) ≤ G * (s ^ (alpha0 - alpha) * dist x y ^ (alpha0 - alpha)) :=
              mul_le_mul_of_nonneg_left hge' hG
          _ = s ^ (alpha0 - alpha) * (G * dist x y ^ (alpha0 - alpha)) := by ring
          _ ≤ s ^ (alpha0 - alpha) * B :=
              mul_le_mul_of_nonneg_left hGd (Real.rpow_nonneg hs0 _)
          _ ≤ s * B := mul_le_mul_of_nonneg_right hsag hB.le
      calc |U x - U y| ≤ G * c * e ^ alpha0 := hsmall x hx y hy
        _ = c * e ^ alpha * (G * e ^ (alpha0 - alpha)) := by rw [hsplit]; ring
        _ ≤ c * e ^ alpha * (s * B) := mul_le_mul_of_nonneg_left hGe (by positivity)
        _ ≤ (KA + 3 * s * B) * c * e ^ alpha := by
            have : c * e ^ alpha * (s * B) = (s * B) * c * e ^ alpha := by ring
            rw [this]
            apply mul_le_mul_of_nonneg_right _ hea
            apply mul_le_mul_of_nonneg_right _ hc
            nlinarith [hKA, hB, hs0]
    · -- large separation: averages at radius `r_N`
      have hA2 := hApair x hx y hy hge
      have hRx := (hrec x hx).trans hR
      have hRy := (hrec y hy).trans hR
      have hrd : rN ^ alpha ≤ dist x y ^ alpha := Real.rpow_le_rpow hrN.le hge hal.le
      have hde : dist x y ^ alpha ≤ e ^ alpha := Real.rpow_le_rpow dist_nonneg hdist_e hal.le
      have hsB : 0 ≤ s * B * c := by positivity
      calc |U x - U y| = |(A x - A y) - (A x - U x) + (A y - U y)| := by ring_nf
        _ ≤ |A x - A y| + |A x - U x| + |A y - U y| := by
            have h1 := abs_add_le ((A x - A y) - (A x - U x)) (A y - U y)
            have h2 := abs_sub (A x - A y) (A x - U x)
            linarith
        _ ≤ KA * c * dist x y ^ alpha + s * B * c * rN ^ alpha + s * B * c * rN ^ alpha := by
            linarith
        _ ≤ KA * c * e ^ alpha + s * B * c * e ^ alpha + s * B * c * e ^ alpha := by
            have h1 : KA * c * dist x y ^ alpha ≤ KA * c * e ^ alpha :=
              mul_le_mul_of_nonneg_left hde (by positivity)
            have h2 : s * B * c * rN ^ alpha ≤ s * B * c * e ^ alpha :=
              mul_le_mul_of_nonneg_left (hrd.trans hde) hsB
            linarith
        _ ≤ (KA + 3 * s * B) * c * e ^ alpha := by
            have : 0 ≤ s * B * c * e ^ alpha := mul_nonneg hsB hea
            nlinarith

/-- Paper 4669–4680, energy part: below `r_N` the stronger exponent `t₀` with the absorbed
envelope; at and above `r_N` the common large-radius constant. -/
theorem aux_lem_as_regularity_energy_split
    (En G B KA c2 rad rN t t0 : ℝ) (hrad : 0 < rad) (hc2 : 0 ≤ c2)
    (habs : ∀ rho, 0 < rho → rho ≤ rN → G * rho ^ (t0 - t) ≤ B)
    (hsmall : En ≤ G * c2 * rad ^ t0)
    (hlarge : rN ≤ rad → En ≤ KA * c2 * rad ^ t) :
    En ≤ max KA B * c2 * rad ^ t := by
  have hrt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad.le _
  by_cases h : rN ≤ rad
  · calc En ≤ KA * c2 * rad ^ t := hlarge h
      _ ≤ max KA B * c2 * rad ^ t := by
          apply mul_le_mul_of_nonneg_right _ hrt
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hc2
  · have hlt : rad < rN := lt_of_not_ge h
    have hG := habs rad hrad hlt.le
    have hsplit : rad ^ t0 = rad ^ (t0 - t) * rad ^ t := by
      rw [← Real.rpow_add hrad]
      congr 1
      ring
    calc En ≤ G * c2 * rad ^ t0 := hsmall
      _ = (G * rad ^ (t0 - t)) * (c2 * rad ^ t) := by rw [hsplit]; ring
      _ ≤ B * (c2 * rad ^ t) := mul_le_mul_of_nonneg_right hG (mul_nonneg hc2 hrt)
      _ ≤ max KA B * (c2 * rad ^ t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hc2 hrt)
      _ = max KA B * c2 * rad ^ t := by ring

/-- One cutoff, one datum (paper 4669–4683): the stronger-exponent finite-cutoff estimates with
their absorbed envelope below `r_N`, and the common large-radius estimates at and above `r_N`,
give the weaker-exponent energy and `C^α` estimates with one explicit constant. Stated for the
common carrier `SobolevData Q`, so it serves the Dirichlet and the Neumann clause. -/
theorem aux_lem_as_regularity_clause
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SobolevData (centeredCube z r hr))
    (alpha alpha0 t t0 rN G B KA c : ℝ)
    (hal : 0 < alpha) (hal0 : alpha < alpha0) (hal1 : alpha0 < 1)
    (hrN : 0 < rN) (hrN1 : rN ≤ 1) (hG : 0 ≤ G) (hB : 0 < B) (hKA : 0 ≤ KA) (hc : 0 ≤ c)
    (habsH : ∀ rho, 0 < rho → rho ≤ rN → G * rho ^ (alpha0 - alpha) ≤ B)
    (habsE : ∀ rho, 0 < rho → rho ≤ rN → G * rho ^ (t0 - t) ≤ B)
    (hE0 : ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr → 0 < rad →
      rad ≤ 1 →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient w) ≤ G * c ^ 2 * rad ^ t0)
    (hH0 : ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      (w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ G * c)
    (hEA : ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr → rN ≤ rad →
      rad ≤ 1 →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient w) ≤ KA * c ^ 2 * rad ^ t)
    (hAsup : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |setAverage (Metric.ball x rN ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) w.1|
        ≤ KA * c)
    (hApair : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)), rN ≤ dist x y →
      |setAverage (Metric.ball x rN ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) w.1 -
        setAverage (Metric.ball y rN ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) w.1|
        ≤ KA * c * dist x y ^ alpha) :
    (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
      localGradientEnergy a
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient w) ≤ 2 * (KA + 3 * Real.sqrt d * B) * c ^ 2 * rad ^ t) ∧
    (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      (w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        2 * (KA + 3 * Real.sqrt d * B) * c) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hs1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (by exact_mod_cast hd1)
  have hmax : max KA B ≤ 2 * (KA + 3 * Real.sqrt d * B) :=
    max_le (by nlinarith) (by nlinarith)
  refine ⟨fun x rad hx h0 h1 => ?_, ?_⟩
  · have hsplit := aux_lem_as_regularity_energy_split _ G B KA (c ^ 2) rad rN t t0 h0
      (sq_nonneg c) habsE (hE0 x rad hx h0 h1) (fun h => hEA x rad hx h h1)
    exact hsplit.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmax (sq_nonneg c)) (Real.rpow_nonneg h0.le _))
  · obtain ⟨U, hUc, hUae, hUH, hUn⟩ := hH0
    have hsmall : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        |U x - U y| ≤ G * c * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha0 :=
      fun x hx y hy => aux_lem_as_regularity_holder_pair alpha0 (G * c) (by linarith) _ U
        hUH hUn x y hx hy
    have hrec : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        |setAverage (Metric.ball x rN ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) w.1
          - U x| ≤ G * c * (Real.sqrt d * rN) ^ alpha0 := by
      intro x hx
      apply aux_lem_as_regularity_avg_close z hr w.1 U hUc hUae x hx rN hrN
      intro p hp
      have hpS : p ∈ (closedCube z r hr : Set (SpatialCoordinates d)) :=
        centeredCube_subset_closedCube z hr hp.2
      have hpx : dist p x < rN := Metric.mem_ball.1 hp.1
      have h2 : Real.sqrt (∑ j : Fin d, (p j - x j) ^ 2) ≤ Real.sqrt d * rN :=
        (aux_lem_as_regularity_euclid_le_dist p x).trans
          (mul_le_mul_of_nonneg_left hpx.le (Real.sqrt_nonneg _))
      exact (hsmall p hpS x hx).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.sqrt_nonneg _) h2 (by linarith)) (mul_nonneg hG hc))
    obtain ⟨hsup, hpair⟩ := aux_lem_as_regularity_holder_combine hd1
      (closedCube z r hr : Set (SpatialCoordinates d)) U
      (fun x => setAverage (Metric.ball x rN ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) w.1)
      alpha alpha0 rN c G KA B hal hal0 hal1.le hrN hrN1 hc hG hB hKA habsH hsmall hrec
      hAsup hApair
    have hA0 : 0 ≤ (KA + 3 * Real.sqrt d * B) * c := by positivity
    have hS0 : 0 ≤ (KA + Real.sqrt d * B) * c := by positivity
    obtain ⟨hH, hN⟩ := aux_lem_as_regularity_cAlphaNorm_of_pairs alpha
      ((KA + 3 * Real.sqrt d * B) * c) ((KA + Real.sqrt d * B) * c) hA0 hS0 _ U hsup hpair
    refine ⟨U, hUc, hUae, hH, hN.trans ?_⟩
    have hsB : 0 ≤ Real.sqrt d * B * c := by positivity
    have hid : (KA + Real.sqrt d * B) * c + (KA + 3 * Real.sqrt d * B) * c =
        2 * (KA + 3 * Real.sqrt d * B) * c - 2 * (Real.sqrt d * B * c) := by ring
    linarith

/-- Per-cutoff Dirichlet supplier on every fixed cube (paper 576–595 for side `≤ 1`, and the
triadic scale shift of `prop_growth_large_root` for side `> 1`): the stronger-exponent energy
and Hölder estimates with a random `K_N` whose listed moments are cutoff-uniform. -/
theorem aux_lem_as_regularity_dirichlet_supply
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < d) (hal : 0 < alpha) (hal1 : alpha < 1)
    (hps : ∀ i, 1 ≤ ps i) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  obtain ⟨δ1, hδ1, h1⟩ := prop_growth d hd E Pc Xc W Cp Sf t alpha k ps ht1 ht2 hal hal1 hps
  obtain ⟨δ2, hδ2, h2⟩ :=
    prop_growth_large_root d hd E Pc Xc W Cp Sf t alpha k ps ht1 ht2 hal hal1 hps
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr
  rcases le_or_gt r 1 with hr1 | hr1
  · exact h1 M Rm Sreg It H hIR (hδ.trans (min_le_left _ _)) z r hr hr1
  · exact h2 M Rm Sreg It H hIR (hδ.trans (min_le_right _ _)) z r hr hr1



/-- The folded energy estimate at an arbitrary positive physical dilation.
The native iteration scales remain integer powers of three. -/
theorem aux_lem_as_regularity_folded_arithmetic
    (d card n m : ℕ) (alpha t : ℝ) (halpha : 2 * (1 - alpha) = (d : ℝ) - t)
    (l Cf Ch cF rf Kf es e3 G : ℝ) (hl : 0 < l) (hCf : 0 ≤ Cf) (hCh : 0 ≤ Ch)
    (hcF : 0 < cF) (hrf : 0 < rf) (hKf : 0 ≤ Kf) (hes : 0 ≤ es) (he3 : 0 ≤ e3)
    (hG0 : 0 ≤ G)
    (hcore : Real.sqrt ((2 ^ card * l ^ d * cF⁻¹ * es) / ((3 : ℝ) ^ n) ^ d) ≤
      Cf * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
        (Real.sqrt ((2 ^ card * l ^ d * cF⁻¹ * e3) / ((3 : ℝ) ^ m) ^ d) +
          Real.sqrt rf⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) * G))
    (hG : G ≤ Ch * Real.sqrt ((d : ℝ) * (3 : ℝ) ^ m) * ((cF * l)⁻¹ * Kf)) :
    es ≤ 2 * Cf ^ 2 * Real.exp (Real.log 3 * (-t * ((m : ℝ) - n))) *
      (e3 + Ch ^ 2 * d * (cF * rf)⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ m / l) ^ (d + 2)) := by
  let X : ℝ := (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n))
  let Y : ℝ := (3 : ℝ) ^ ((m : ℝ) / 2)
  let w : ℝ := Real.exp (Real.log 3 * (-t * ((m : ℝ) - n)))
  have hκ : 0 < 2 ^ card * l ^ d * cF⁻¹ := by positivity
  have h1 := aux_rem_resolved_meshes_arith_sq (2 ^ card * l ^ d * cF⁻¹)
    (((3 : ℝ) ^ n) ^ d) (((3 : ℝ) ^ m) ^ d) X Y G Cf rf es e3
    hκ (by positivity) (by positivity) (by positivity) (by positivity) hG0 hCf hrf hes he3 hcore
  have hX : X ^ 2 * ((3 : ℝ) ^ n) ^ d / ((3 : ℝ) ^ m) ^ d = w :=
    aux_rem_resolved_meshes_arith_X d alpha t halpha n m
  have hXY : X ^ 2 * ((3 : ℝ) ^ n) ^ d = w * ((3 : ℝ) ^ m) ^ d :=
    (div_eq_iff (by positivity)).mp hX
  have hY : Y ^ 2 = (3 : ℝ) ^ m := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hS : X ^ 2 * ((3 : ℝ) ^ n) ^ d * Y ^ 2 * (3 : ℝ) ^ m *
      (l ^ d)⁻¹ * (l ^ 2)⁻¹ = w * ((3 : ℝ) ^ m / l) ^ (d + 2) := by
    rw [hXY, hY, div_pow, pow_add, pow_add]
    field_simp
  have hG2 : G ^ 2 ≤ Ch ^ 2 * ((d : ℝ) * (3 : ℝ) ^ m) * ((cF * l)⁻¹ * Kf) ^ 2 := by
    have h := pow_le_pow_left₀ hG0 hG 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at h
    exact h
  have hP : 0 ≤ ((3 : ℝ) ^ n) ^ d / (2 ^ card * l ^ d * cF⁻¹) *
      X ^ 2 * rf⁻¹ * Y ^ 2 := by positivity
  have hsource : ((3 : ℝ) ^ n) ^ d / (2 ^ card * l ^ d * cF⁻¹) *
      X ^ 2 * rf⁻¹ * Y ^ 2 * G ^ 2 ≤
      w * (Ch ^ 2 * d * (cF * rf)⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ m / l) ^ (d + 2)) := by
    calc
      _ ≤ ((3 : ℝ) ^ n) ^ d / (2 ^ card * l ^ d * cF⁻¹) * X ^ 2 * rf⁻¹ * Y ^ 2 *
          (Ch ^ 2 * ((d : ℝ) * (3 : ℝ) ^ m) * ((cF * l)⁻¹ * Kf) ^ 2) :=
        mul_le_mul_of_nonneg_left hG2 hP
      _ = (2 ^ card : ℝ)⁻¹ * (Ch ^ 2 * d) * ((cF * rf)⁻¹ * Kf ^ 2) *
          (X ^ 2 * ((3 : ℝ) ^ n) ^ d * Y ^ 2 * (3 : ℝ) ^ m * (l ^ d)⁻¹ * (l ^ 2)⁻¹) :=
        aux_rem_resolved_meshes_arith_alg d card _ l X Y rf Ch d _ cF Kf hl hcF hrf
      _ = (2 ^ card : ℝ)⁻¹ *
          (w * (Ch ^ 2 * d * (cF * rf)⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ m / l) ^ (d + 2))) := by
        rw [hS]; ring
      _ ≤ _ := mul_le_of_le_one_left (by dsimp only [w]; positivity)
        (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  rw [hX] at h1
  have h2 := mul_le_mul_of_nonneg_left hsource (by positivity : 0 ≤ 2 * Cf ^ 2)
  calc
    es ≤ 2 * Cf ^ 2 * w * e3 + 2 * Cf ^ 2 *
        (((3 : ℝ) ^ n) ^ d / (2 ^ card * l ^ d * cF⁻¹) * X ^ 2 * rf⁻¹ * Y ^ 2 * G ^ 2) := by
      convert h1 using 1 <;> ring
    _ ≤ 2 * Cf ^ 2 * w * e3 + 2 * Cf ^ 2 *
        (w * (Ch ^ 2 * d * (cF * rf)⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ m / l) ^ (d + 2))) :=
      add_le_add le_rfl h2
    _ = _ := by ring

/-- Native folded iteration after an arbitrary dilation. All probabilistic input
objects belong to the original model. No residual-model response input is required. -/
theorem aux_lem_as_regularity_folded_native_dilation
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t0 : ℝ) (ht0_low : (d : ℝ) - 1 < t0) (ht0_high : t0 < (d : ℝ)) :
    ∃ Cf Ch Kt delta1 : ℝ, 0 < Cf ∧ 0 ≤ Ch ∧
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (hdet : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
        M.delta ≤ delta1 →
        ∀ (om : BilateralField d) (Lv : ℕ) (l : ℝ) (hl : 0 < l) (cF : ℝ), 0 < cF →
        ∀ a : PositiveCoefficient (unitNeumannCube d),
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
          a.val y = cF * (Sreg.cutoffOn Lv om (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl).val (l • y)) →
        ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
        (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
        ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ (I : Finset (Fin d)) (n m : ℕ) (Lstar : ℝ), 10 ≤ Lstar →
        m ≤ Lv → n ≤ m → (3 : ℝ) ^ m < 2 * l →
        (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ m / (6 * l)) ≤ min (y i) (1 - y i)) →
        n + It.prefixLen (l • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m om ≤ m →
        aux_rem_resolved_meshes_energy a u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ n / (2 * l))) ≤
        2 * Cf ^ 2 * Real.exp (Real.log 3 * (-t0 * ((m : ℝ) - n))) *
          (aux_rem_resolved_meshes_energy a u
            (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m / (2 * l))) +
            Ch ^ 2 * d * (cF * It.ref Lv (m - 2) (l • aux_rem_resolved_meshes_center y I) om)⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ m / l) ^ (d + 2)) := by
  obtain ⟨Cf, Kf, hCf, hKf, hfold⟩ := aux_rem_resolved_meshes_folded_uniform_all d hd
  obtain ⟨Ch, hCh, hsrc⟩ := aux_rem_resolved_meshes_fin_source d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hα1 : (t0 + 2 - (d : ℝ)) / 2 < 1 := by linarith
  have hα2 : 1 / 2 ≤ (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have hαeq : 2 * (1 - (t0 + 2 - (d : ℝ)) / 2) = (d : ℝ) - t0 := by ring
  have h1α : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  refine ⟨Cf, Ch, Kf, min (min (1 / 2) (((1 - (t0 + 2 - (d : ℝ)) / 2) / Cf) ^ 2)) Cf⁻¹,
    hCf, hCh, hKf, lt_min (lt_min (by norm_num) (by positivity)) (inv_pos.mpr hCf), ?_⟩
  intro M E Poinc Ext Sreg It hdet hδ om Lv l hl cF hcF a ha f hf Kf0 hKf0 hfb hf0 u hu
    y hy I n m Lstar hLstar hmLv hnm hroot hI hwin
  have hδC : M.delta ≤ Cf⁻¹ := hδ.trans (min_le_right _ _)
  have hαr := aux_rem_resolved_meshes_alpha_range Cf ((t0 + 2 - (d : ℝ)) / 2) hCf hα1 hα2
    M.delta M.shellPrefix.delta_pos (hδ.trans (min_le_left _ _))
  -- the source: a measurable everywhere-bounded representative, same weak equation
  obtain ⟨f2, hf2m, hf2b, hff2⟩ := aux_rem_resolved_meshes_clamp f hf Kf0 hKf0 hfb
  have hf20 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f2 y) = 0 := by
    rw [← hf0]; exact integral_congr_ae hff2.symm
  have hu2 : ∀ ψ : weakSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) ψ =
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          f2 x * (ψ : SobolevData (unitNeumannCube d)).1 x := by
    intro ψ
    rw [hu ψ]
    apply integral_congr_ae
    filter_upwards [hff2] with x hx
    rw [hx]
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hRk : 0 < (3 : ℝ) ^ m / (6 * l) := by positivity
  have hρeq : (3 : ℝ) ^ m / 2 = l * (3 * ((3 : ℝ) ^ m / (6 * l))) := by
    field_simp; ring
  have hRk3 : 3 * ((3 : ℝ) ^ m / (6 * l)) < 1 := by
    have hdiv : (3 : ℝ) ^ m / (2 * l) < 1 := (div_lt_one (by positivity)).mpr hroot
    convert hdiv using 1 <;> field_simp <;> ring
  obtain ⟨fc, ut, hfc, hueq, hE⟩ := aux_rem_resolved_meshes_root_package Sreg Lv om l hl
    cF hcF a ha f2 hf2m Kf0 hKf0 hf2b hf20 u hu2 y hy I Lstar
    ((3 : ℝ) ^ m / (6 * l)) hLstar hRk hRk3 hI ((3 : ℝ) ^ m) hR hρeq
  -- the divergence-form source on the root cube
  have hFrm : Measurable (fun x : SpatialCoordinates d => ((cF * l)⁻¹ *
      f2 (l⁻¹ • coordinateFold (l •
        aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x))) :=
    measurable_const.mul (hf2m.comp ((continuous_const_smul _).comp
      (coordinateFold_continuous _ _ _)).measurable)
  have hMF : 0 ≤ (cF * l)⁻¹ * Kf0 := by positivity
  have hFrb : ∀ x : SpatialCoordinates d, |(cF * l)⁻¹ *
      f2 (l⁻¹ • coordinateFold (l •
        aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x)| ≤
      (cF * l)⁻¹ * Kf0 := by
    intro x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hcF hl))]
    exact mul_le_mul_of_nonneg_left (hf2b _) (by positivity)
  obtain ⟨g, hgrad, hHol, hgae, hid, hGb⟩ := hsrc (l •
    aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR _ hFrm _ hMF hFrb
  have hweq : ∀ φ : killedSobolevGraph (centeredCube (l •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR),
      sobolevCoefficientForm fc (ut : SobolevData (centeredCube (l •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR))
        (φ : SobolevData (centeredCube (l •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR)) =
      -inner ℝ hgrad (subspaceGradient (killedSobolevGraph (centeredCube (l •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR)) φ) :=
    fun φ => (hueq φ).trans (hid φ)
  have hnz : (n : ℤ) ≤ (m : ℤ) - (It.prefixLen (l •
      aux_rem_resolved_meshes_center y I) (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kf) m om : ℤ) := by
    omega
  have hcore := hfold M E Poinc Ext Sreg It hdet hδC ((t0 + 2 - (d : ℝ)) / 2) hαr Lv
    m n (l • aux_rem_resolved_meshes_center y I) hR
    om I (aux_rem_resolved_meshes_faceSet y I) hmLv hnm hnz
    fc hfc g hgrad ut hHol hgae hweq
  -- unfold the normalized norms through the root-cube energy identity
  have hn3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hnρ : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hnm
  have hEs := hE ((3 : ℝ) ^ n) hn3 hnρ
  have hE3 := hE ((3 : ℝ) ^ m) hR le_rfl
  have hvol : ∀ (r : ℝ) (hr : 0 < r), volume.real (centeredCube (l •
      aux_rem_resolved_meshes_center y I) r hr : Set (SpatialCoordinates d)) = r ^ d := by
    intro r hr
    rw [measureReal_def, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
  simp only [normalizedEnergyNorm] at hcore
  rw [hEs, hE3, hvol, hvol] at hcore
  have hEnn : ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      0 ≤ aux_rem_resolved_meshes_energy a u A := fun A hA => by
    rw [aux_rem_resolved_meshes_energy_local a u A hA]; exact localGradientEnergy_nonneg _ _ _
  have hG0 : 0 ≤ halfHolderSeminorm (centeredCube (l •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g :=
    Real.sSup_nonneg (fun v hv => by
      obtain ⟨x, -, y', -, -, rfl⟩ := hv
      positivity)
  exact aux_lem_as_regularity_folded_arithmetic d I.card n m
    ((t0 + 2 - (d : ℝ)) / 2) t0 hαeq l Cf Ch cF _ Kf0 _ _ _ hl hCf.le hCh hcF
    (It.ref_pos _ _ _ _) hKf0 (hEnn _ measurableSet_ball) (hEnn _ measurableSet_ball) hG0
    (by simpa only [mul_assoc] using hcore) hGb


/-- Exact infrared truncation scalar, independent of the working cube. -/
def aux_lem_as_regularity_nc_ir_scalar {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (om : BilateralField d) (N L : ℕ) : ℝ :=
  (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
    Real.exp ((L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
      ∑ n ∈ Finset.range L, om (Int.ofNat (n + 1)) 0)

theorem aux_lem_as_regularity_nc_ir_scalar_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (om : BilateralField d) (N L : ℕ) : 0 < aux_lem_as_regularity_nc_ir_scalar M om N L :=
  mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- The same exact scalar ties truncated coefficients on every working cube
 to the original model's stationary coefficient, with no scale restriction. -/
theorem aux_lem_as_regularity_nc_truncated_native {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (om : BilateralField d) (N L : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (fun w => infraredPartialSum w L) om N z hr).val y =
        aux_lem_as_regularity_nc_ir_scalar M om N L *
          (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N om)
            ((3 : ℝ) ^ (N : ℤ) • z) ((3 : ℝ) ^ (N : ℤ) * r) (by positivity)).val
            ((3 : ℝ) ^ (N : ℤ) • y) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := by positivity
  have hcut := aux_rem_resolved_meshes_physical_cutoff_bridge_ae_smul_pullback h3.ne'
    (centeredCube z r hr).isOpen.measurableSet
    (centeredCube ((3 : ℝ) ^ (N : ℤ) • z) ((3 : ℝ) ^ (N : ℤ) * r) (by positivity)).isOpen.measurableSet
    (aux_rem_resolved_meshes_physical_cutoff_bridge_smul_mem_cube N z r hr
      ((3 : ℝ) ^ (N : ℤ) * r) (by positivity) rfl)
    (Sreg.cutoffOn_eq (N + L) (aux_rem_resolved_meshes_relabel N om)
      ((3 : ℝ) ^ (N : ℤ) • z) ((3 : ℝ) ^ (N : ℤ) * r) (by positivity))
  filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae M
    (fun w => infraredPartialSum w L) om N z hr, hcut] with y hy hcy
  rw [hy, hcy, aux_rem_resolved_meshes_physical_cutoff_bridge_truncation_identity]
  change _ = aux_lem_as_regularity_nc_ir_scalar M om N L * _
  unfold aux_lem_as_regularity_nc_ir_scalar
  congr 3
  apply Finset.sum_congr rfl
  intro j _
  exact (aux_rem_resolved_meshes_relabel_apply N om (j : ℤ) y).symm

/-- Reference convergence at any physical centre and native root level `N-k`.
The coefficient approximations used to establish it need only be taken on the
standard unit cube; the conclusion holds at every deterministic centre. -/
theorem aux_lem_as_regularity_nc_reference_limit {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {Sreg : in_6_16 d M}
    (It : in_iteration d M E Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (hIR : Tendsto (infraredPartialSum om) atTop (nhds (H om)))
    (N k : ℕ) (hk : k + 2 ≤ N) (c : SpatialCoordinates d) :
    ∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      |aux_lem_as_regularity_nc_ir_scalar M om N L *
          It.ref (N + L) (N - k - 2) ((3 : ℝ) ^ (N : ℤ) • c)
            (aux_rem_resolved_meshes_relabel N om) -
          aux_rem_resolved_meshes_bref M H om N k c| < eps := by
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let aFin : ℕ → PositiveCoefficient (unitNeumannCube d) := fun L =>
    cutoffPositiveCoefficient M (fun w => infraredPartialSum w L) om N z0 one_pos
  have hA : ∀ L : ℕ, ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (aFin L).val y = aux_lem_as_regularity_nc_ir_scalar M om N L *
        (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N om)
          ((3 : ℝ) ^ (N : ℤ) • z0) ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val
          ((3 : ℝ) ^ (N : ℤ) • y) := by
    intro L
    filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae
      M (fun w => infraredPartialSum w L) om N z0 one_pos,
      aux_rem_resolved_meshes_cutoffOn_scaled Sreg om N L] with y hy hn
    change (cutoffPositiveCoefficient M (fun w => infraredPartialSum w L) om N z0 one_pos).val y = _
    rw [hy, hn, aux_rem_resolved_meshes_physical_cutoff_bridge_truncation_identity]
    rfl
  have hconv := (aux_rem_resolved_meshes_physical_cutoff_bridge_of_tendsto M Sreg H om hIR
    z0 1 one_pos N ((3 : ℝ) ^ (N : ℤ)) (by positivity) (mul_one _).symm).2
  have h := aux_rem_resolved_meshes_ref_tendsto It H om hIR N aFin
    (aux_lem_as_regularity_nc_ir_scalar M om N)
    (aux_lem_as_regularity_nc_ir_scalar_pos M om N) hA hconv
    (k + 1) (by omega) (by omega) (by omega) c
  have hNk : N - (k + 1) + 1 = N - k := by omega
  simpa only [Nat.add_sub_cancel, hNk] using h

/-- Dilation about the centre of `[0,rho]^d` is ordinary multiplication. -/
theorem aux_lem_as_regularity_nc_dilation_smul {d : ℕ} (rho : ℝ) (y : SpatialCoordinates d) :
    cubeDilation (rho • (fun _ : Fin d => (1 / 2 : ℝ)))
      (fun _ : Fin d => (1 / 2 : ℝ)) rho y = rho • y := by
  ext i
  simp only [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

/-- The actual unit pullback on a residual cube has finite native coefficient
approximations at dilation `rho * 3^N`, with the exact infrared scalar and
uniform coefficient convergence. -/
theorem aux_lem_as_regularity_nc_residual_physical {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (hIR : Tendsto (infraredPartialSum om) atTop (nhds (H om)))
    (rho : ℝ) (hrho : 0 < rho) (N : ℕ)
    (a : PositiveCoefficient (unitNeumannCube d))
    (ha : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a.val y = cutoffCoefficient M H om N (rho • y)) :
    ∃ aFin : ℕ → PositiveCoefficient (unitNeumannCube d),
      (∀ L : ℕ, ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        (aFin L).val y = aux_lem_as_regularity_nc_ir_scalar M om N L *
          (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N om)
            (((3 : ℝ) ^ (N : ℤ) * rho) • (fun _ : Fin d => (1 / 2 : ℝ)))
            ((3 : ℝ) ^ (N : ℤ) * rho) (by positivity)).val
            (((3 : ℝ) ^ (N : ℤ) * rho) • y)) ∧
      (∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
        ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
          |(aFin L).val y - a.val y| < eps) := by
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  choose aFin hFin using fun L => lane4_dilation_coefficient_transport d (rho • z0) z0
    rho hrho one_pos (cutoffPositiveCoefficient M (fun w => infraredPartialSum w L) om N
      (rho • z0) hrho)
  have hq := lane4_dilation_quasi_measure_preserving d (rho • z0) z0 rho hrho one_pos
  refine ⟨aFin, ?_, ?_⟩
  · intro L
    let l : ℝ := (3 : ℝ) ^ (N : ℤ) * rho
    have hl : 0 < l := mul_pos (zpow_pos (by norm_num) _) hrho
    have hqn := lane4_dilation_quasi_measure_preserving d (l • z0) z0 l hl one_pos
    have hcut := hqn.ae (Sreg.cutoffOn_eq (N + L) (aux_rem_resolved_meshes_relabel N om)
      (l • z0) l hl)
    filter_upwards [hFin L, hq.ae
      (aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae
        M (fun w => infraredPartialSum w L) om N (rho • z0) hrho), hcut] with y hy hp hn
    simp only [z0, aux_lem_as_regularity_nc_dilation_smul] at hp hn hy
    change (aFin L).val y = aux_lem_as_regularity_nc_ir_scalar M om N L *
      (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N om) (l • z0) l hl).val (l • y)
    rw [hy, hp, hn, aux_rem_resolved_meshes_physical_cutoff_bridge_truncation_identity]
    unfold aux_lem_as_regularity_nc_ir_scalar
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    simpa only [l, smul_smul] using!
      (aux_rem_resolved_meshes_relabel_apply N om (j : ℤ) (rho • y)).symm
  · intro eps heps
    obtain ⟨L0, hL0⟩ := (aux_rem_resolved_meshes_physical_cutoff_bridge_of_tendsto M Sreg H om
      hIR (rho • z0) rho hrho N ((3 : ℝ) ^ (N : ℤ) * rho) (by positivity) rfl).2 eps heps
    refine ⟨L0, fun L hL => ?_⟩
    filter_upwards [hFin L, hq.ae (hL0 L hL), ha] with y hy hn hya
    erw [hy, hya]
    simpa only [z0, aux_lem_as_regularity_nc_dilation_smul] using hn

/-- Local energy inequalities pass to the limiting positive coefficient.
Both the coefficient and reference scalar are genuine convergent inputs;
the weak solutions for the approximants are supplied by Lax–Milgram. -/
theorem aux_lem_as_regularity_nc_energy_limit {d : ℕ} (hd : 2 ≤ d)
    (a : PositiveCoefficient (unitNeumannCube d))
    (aFin : ℕ → PositiveCoefficient (unitNeumannCube d))
    (hconv : ∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |(aFin L).val y - a.val y| < eps)
    (b : ℝ) (hb : 0 < b) (bFin : ℕ → ℝ)
    (hbconv : ∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → |bFin L - b| < eps)
    (A B : Set (SpatialCoordinates d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (K Z : ℝ) (hK : 0 ≤ K) (hZ : 0 ≤ Z)
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (hu : SolvesNeumann a f u)
    (hfin : ∀ L : ℕ, ∀ v : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann (aFin L) f v →
      aux_rem_resolved_meshes_energy (aFin L) v A ≤
        K * (aux_rem_resolved_meshes_energy (aFin L) v B + (bFin L)⁻¹ * Z)) :
    aux_rem_resolved_meshes_energy a u A ≤
      7 * K * (aux_rem_resolved_meshes_energy a u B + b⁻¹ * Z) := by
  rw [aux_rem_resolved_meshes_energy_local _ _ _ hA, aux_rem_resolved_meshes_energy_local _ _ _ hB]
  refine aux_rem_resolved_meshes_good_final _ _ _ _ _ hK (localGradientEnergy_nonneg _ _ _) hb hZ ?_
  intro eps heps
  let Eu := weightedGradientForm a.val (sobolevGradient (u : SobolevData (unitNeumannCube d)))
    (sobolevGradient (u : SobolevData (unitNeumannCube d)))
  have hEu : 0 ≤ Eu := (localGradientEnergy_nonneg a MeasurableSet.univ
    (sobolevGradient (u : SobolevData (unitNeumannCube d)))).trans
    (localGradientEnergy_le _ MeasurableSet.univ _)
  obtain ⟨m0, hm0, hm0a⟩ := a.property
  let delta := min (1 / 4) (eps / (2 * ((20 / 3 * K + 2) * 2 * (Eu + 1) + 1)))
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  obtain ⟨L1, hL1⟩ := hconv _ (mul_pos hdelta hm0)
  let eta := min (b / 2) (eps * b ^ 2 / (11 * (K * Z + 1)))
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  obtain ⟨L2, hL2⟩ := hbconv eta heta
  obtain ⟨v, hv⟩ := aux_rem_resolved_meshes_neumann_exists hd (aFin (max L1 L2)) f hf Kf hfb hf0
  have hclose : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |(aFin (max L1 L2)).val x - a.val x| ≤ delta * a.val x := by
    filter_upwards [hL1 (max L1 L2) (le_max_left _ _), hm0a] with x hx hm
    exact hx.le.trans (mul_le_mul_of_nonneg_left hm hdelta.le)
  have hF := hfin (max L1 L2) v hv
  rw [aux_rem_resolved_meshes_energy_local _ _ _ hA,
    aux_rem_resolved_meshes_energy_local _ _ _ hB] at hF
  have hW := aux_rem_resolved_meshes_stability a (aFin (max L1 L2)) delta hdelta.le
    (min_le_left _ _) hclose f u v hu hv
  rw [map_sub] at hW
  have hrefL := hL2 (max L1 L2) (le_max_right _ _)
  have hbp := aux_rem_resolved_meshes_pos_of_close hb (min_le_left _ _) hrefL
  have hchain := aux_rem_resolved_meshes_local_chain a (aFin (max L1 L2)) delta hdelta.le
    (min_le_left _ _) hclose (sobolevGradient (u : SobolevData (unitNeumannCube d)))
    (sobolevGradient (v : SobolevData (unitNeumannCube d))) hA hB K ((bFin (max L1 L2))⁻¹ * Z)
    hK (mul_nonneg (inv_pos.mpr hbp).le hZ) hF
  have herr1 := aux_rem_resolved_meshes_err_delta K Eu eps _ delta hK hEu heps hdelta
    ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _) hW
  have herr2 := aux_rem_resolved_meshes_err_inv K Z b (bFin (max L1 L2)) eps eta hK hZ hb heps
    (min_le_left _ _) (min_le_right _ _) hrefL
  linarith
theorem aux_lem_as_regularity_nc_scale_ratio (rho : ℝ) (hrho : 0 < rho)
    (N k : ℕ) (hk : k ≤ N) :
    (3 : ℝ) ^ (N - k) / ((3 : ℝ) ^ (N : ℤ) * rho) = (3 : ℝ) ^ (-(k : ℤ)) / rho := by
  have hp : (3 : ℝ) ^ (N - k) = (3 : ℝ) ^ (N : ℤ) * (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [hp]
  field_simp

theorem aux_lem_as_regularity_nc_scale_small (rho : ℝ) (hrho : 0 < rho) (N n : ℕ) :
    (3 : ℝ) ^ n / (2 * ((3 : ℝ) ^ (N : ℤ) * rho)) =
      ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / rho := by
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  field_simp

theorem aux_lem_as_regularity_nc_iteration_ratio (t : ℝ) (N k n : ℕ) (hk : k ≤ N) :
    Real.exp (Real.log 3 * (-t * (((N - k : ℕ) : ℝ) - n))) =
      (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ^ t := by
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0),
    aux_rem_resolved_meshes_e3z, aux_rem_resolved_meshes_e3z, ← Real.exp_sub,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  push_cast [Nat.cast_sub hk]
  ring

/-- Residual sides in `[1/3,1]` require only bounded geometric losses; the
iteration still uses the original integer root level `N-k`. -/
theorem aux_lem_as_regularity_nc_residual_finite_step
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ)) :
    ∃ Kt C1 delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧
      0 ≤ C1 ∧ 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (P : in_poincare d hd E) (X : in_extension d hd E)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (D : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
        M.delta ≤ delta1 → ∀ (rho : ℝ), 1 / 3 ≤ rho → rho ≤ 1 →
        ∀ (om : BilateralField d) (N L : ℕ) (cF : ℝ), 0 < cF →
        ∀ (a : PositiveCoefficient (unitNeumannCube d)) (hl : 0 < (3 : ℝ) ^ (N : ℤ) * rho),
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
          a.val y = cF * (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N om)
            (((3 : ℝ) ^ (N : ℤ) * rho) • (fun _ : Fin d => (1 / 2 : ℝ)))
            ((3 : ℝ) ^ (N : ℤ) * rho) hl).val (((3 : ℝ) ^ (N : ℤ) * rho) • y)) →
        ∀ (f : SpatialCoordinates d → ℝ),
        AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        ∀ (Kf : ℝ), 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
        (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
        ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ (I : Finset (Fin d)) (n k : ℕ) (Lstar : ℝ), 10 ≤ Lstar → 1 ≤ k → k ≤ N →
        (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ≤ min (y i) (1 - y i)) →
        n + It.prefixLen (((3 : ℝ) ^ (N : ℤ) * rho) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t + 2 - (d : ℝ)) / 2) / Kt) (N - k)
          (aux_rem_resolved_meshes_relabel N om) ≤ N - k →
        aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I)
          ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
          C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ^ t *
            (aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2))) +
              (cF * It.ref (N + L) (N - k - 2)
                (((3 : ℝ) ^ (N : ℤ) * rho) • aux_rem_resolved_meshes_center y I)
                (aux_rem_resolved_meshes_relabel N om))⁻¹ *
                Kf ^ 2 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ ((d : ℝ) + 2)) := by
  obtain ⟨Cf, Ch, Kt, delta1, hCf, hCh, hKt, hdelta1, hnat⟩ :=
    aux_lem_as_regularity_folded_native_dilation d hd t ht htd
  let Q : ℝ := max 1 (Ch ^ 2 * d * 6 ^ (d + 2))
  have hQ1 : 1 ≤ Q := le_max_left _ _
  refine ⟨Kt, 2 * Cf ^ 2 * Q, delta1, hKt, by positivity, hdelta1, ?_⟩
  intro M E P X Sreg It D hdelta rho hrho3 hrho1 om N L cF hcF a hl ha f hf Kf hKf
    hfb hf0 u hu y hy I n k Lstar hLstar hk1 hkN hI hwin
  have hrho : 0 < rho := lt_of_lt_of_le (by norm_num) hrho3
  let l := (3 : ℝ) ^ (N : ℤ) * rho
  let R : ℝ := (3 : ℝ) ^ (-(k : ℤ)) / 2
  let s : ℝ := (3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hs : 0 < s := by dsimp only [s]; positivity
  have hmratio : (3 : ℝ) ^ (N - k) / l = 2 * R / rho := by
    rw [aux_lem_as_regularity_nc_scale_ratio rho hrho N k hkN]
    dsimp only [R]; ring
  have hsmall : (3 : ℝ) ^ n / (2 * l) = s / rho :=
    aux_lem_as_regularity_nc_scale_small rho hrho N n
  have hlarge : (3 : ℝ) ^ (N - k) / (2 * l) = R / rho := by
    calc _ = ((3 : ℝ) ^ (N - k) / l) / 2 := by ring
      _ = _ := by rw [hmratio]; ring
  have hRthird : R ≤ 1 / 6 := by
    have h3 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      (show -(k : ℤ) ≤ -1 by omega)
    norm_num at h3
    dsimp only [R]
    rw [zpow_neg, zpow_natCast]
    linarith
  have hroot : (3 : ℝ) ^ (N - k) < 2 * l := by
    apply (div_lt_iff₀ hl).mp
    rw [hmratio]
    exact (div_lt_iff₀ hrho).mpr (by linarith)
  have hIR : (3 : ℝ) ^ (N - k) / (6 * l) ≤ R := by
    calc _ = ((3 : ℝ) ^ (N - k) / l) / 6 := by ring
      _ = R / (3 * rho) := by rw [hmratio]; ring
      _ ≤ R := div_le_self hR.le (by linarith)
  have hI' : ∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (N - k) / (6 * l)) ≤ min (y i) (1 - y i) :=
    fun i hi => (mul_le_mul_of_nonneg_left hIR (by linarith)).trans (hI i hi)
  have h := hnat M E P X Sreg It D hdelta (aux_rem_resolved_meshes_relabel N om) (N + L)
    l hl cF hcF a ha f hf Kf hKf hfb hf0 u hu y hy I n (N - k) Lstar hLstar (by omega)
    (by omega) hroot hI' hwin
  rw [hsmall, hlarge, aux_lem_as_regularity_nc_iteration_ratio t N k n hkN] at h
  have hmono : ∀ A B : Set (SpatialCoordinates d), A ⊆ B →
      aux_rem_resolved_meshes_energy a u A ≤ aux_rem_resolved_meshes_energy a u B :=
    fun A B hAB => aux_rem_resolved_strata_energy_mono a ⟨u.1, u.2.1⟩ hAB
  have hEl : aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) (R / rho)) ≤
      aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * R)) := by
    apply hmono _ _ (Metric.ball_subset_ball ?_)
    apply (div_le_iff₀ hrho).mpr
    have hLrho : 1 ≤ Lstar * rho := by
      calc 1 ≤ 10 * rho := by linarith
        _ ≤ Lstar * rho := mul_le_mul_of_nonneg_right hLstar hrho.le
    calc R = 1 * R := by ring
      _ ≤ (Lstar * rho) * R := mul_le_mul_of_nonneg_right hLrho hR.le
      _ = _ := by ring
  have hEs : aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
      aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) (s / rho)) :=
    hmono _ _ (Metric.ball_subset_ball ((le_div_iff₀ hrho).mpr (mul_le_of_le_one_right hs.le hrho1)))
  have hpow : ((3 : ℝ) ^ (N - k) / l) ^ (d + 2) ≤
      6 ^ (d + 2) * R ^ ((d : ℝ) + 2) := by
    rw [hmratio]
    have hratio : 2 * R / rho ≤ 6 * R := (div_le_iff₀ hrho).mpr (by nlinarith)
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * R / rho) hratio (d + 2)
    rw [mul_pow] at hp
    have he : R ^ (d + 2) = R ^ ((d : ℝ) + 2) := by norm_cast
    rw [he] at hp
    exact hp
  have hEn0 : 0 ≤ aux_rem_resolved_meshes_energy a u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * R)) :=
    aux_rem_resolved_strata_energy_nonneg a ⟨u.1, u.2.1⟩ _
  have hrf : 0 < cF * It.ref (N + L) (N - k - 2)
      (l • aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N om) :=
    mul_pos hcF (It.ref_pos _ _ _ _)
  refine hEs.trans (h.trans ?_)
  have hsrc := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ Ch ^ 2 * d * (cF * It.ref (N + L) (N - k - 2)
      (l • aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N om))⁻¹ * Kf ^ 2 by positivity)
  have hsrc' : Ch ^ 2 * d * (cF * It.ref (N + L) (N - k - 2)
      (l • aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N om))⁻¹ * Kf ^ 2 *
      ((3 : ℝ) ^ (N - k) / l) ^ (d + 2) ≤
      Q * ((cF * It.ref (N + L) (N - k - 2)
        (l • aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N om))⁻¹ * Kf ^ 2 * R ^ ((d : ℝ) + 2)) := by
    calc _ ≤ (Ch ^ 2 * d * 6 ^ (d + 2)) * ((cF * It.ref (N + L) (N - k - 2)
          (l • aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N om))⁻¹ * Kf ^ 2 * R ^ ((d : ℝ) + 2)) := by
          convert hsrc using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hbig := add_le_add (hEl.trans (le_mul_of_one_le_left hEn0 hQ1)) hsrc'
  have hmult := mul_le_mul_of_nonneg_left hbig
    (show 0 ≤ 2 * Cf ^ 2 * (s / R) ^ t by positivity)
  convert hmult using 1 <;> dsimp only [l, s, R] <;> ring
/-- The actual residual coefficient satisfies a folded one-step inequality,
including both the good-prefix limit passage and the bad-prefix allowance. -/
theorem aux_lem_as_regularity_nc_residual_onestep
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t : ℝ) (hLstar : 10 ≤ Lstar) (hRstar : Rstar < 1 / (100 * Lstar))
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ)) :
    ∃ Kt Cstep c delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧
      1 ≤ Cstep ∧ 0 < c ∧ 0 < delta1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (P : in_poincare d hd E) (X : in_extension d hd E)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (D : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        M.delta ≤ delta1 → ∀ (rho : ℝ), 1 / 3 ≤ rho → rho ≤ 1 →
        ∀ (om : BilateralField d), Tendsto (infraredPartialSum om) atTop (nhds (H om)) →
        ∀ (N : ℕ) (a : PositiveCoefficient (unitNeumannCube d)),
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
          a.val y = cutoffCoefficient M H om N (rho • y)) →
        ∀ (f : SpatialCoordinates d → ℝ),
        AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        ∀ (Kf : ℝ), 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
        (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
        ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
        s ∈ Set.range (fun j : ℤ => (3 : ℝ) ^ j / 2) →
        (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s → k ≤ N →
        8 * s < (3 : ℝ) ^ (-(k : ℤ)) / 2 → (3 : ℝ) ^ (-(k : ℤ)) / 2 ≤ Rstar →
        (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ≤ min (y i) (1 - y i)) →
        aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
          Cstep * Real.exp (c * (It.prefixLen
              (((3 : ℝ) ^ (N : ℤ) * rho) • aux_rem_resolved_meshes_center y I)
              (1 - (1 - (t + 2 - (d : ℝ)) / 2) / Kt) (N - k)
              (aux_rem_resolved_meshes_relabel N om) : ℝ)) *
            (s / ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ^ t *
            (aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2))) +
              (aux_rem_resolved_meshes_bref M H om N k (rho • aux_rem_resolved_meshes_center y I))⁻¹ *
                Kf ^ 2 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ ((d : ℝ) + 2)) := by
  obtain ⟨Kt, C1, delta1, hKt, hC1, hdelta1, hfin⟩ :=
    aux_lem_as_regularity_nc_residual_finite_step d hd t ht htd
  have ht0 : 0 < t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc : 0 < t * Real.log 3 + 1 := by positivity
  refine ⟨Kt, max 1 (7 * C1), t * Real.log 3 + 1, delta1,
    hKt, le_max_left _ _, hc, hdelta1, ?_⟩
  intro M E P X Sreg It D H hdelta rho hrho3 hrho1 om hIR N a ha f hf Kf hKf hfb hf0 u hu
    y hy I s k hs hsN hs0 hk h8 hR hI
  have hrho : 0 < rho := lt_of_lt_of_le (by norm_num) hrho3
  obtain ⟨aFin, hA, hconv⟩ := aux_lem_as_regularity_nc_residual_physical M Sreg H om hIR rho hrho N a ha
  obtain ⟨j, rfl⟩ := hs
  have hjN : -(N : ℤ) ≤ j := by
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp (by linarith)
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    have : (1 : ℝ) / 2 ≤ Rstar := by simpa using hR
    have h100 : 0 < 100 * Lstar := by linarith
    have : 1 / (100 * Lstar) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ h100 (by norm_num)]; linarith
    linarith
  let n : ℕ := (j + (N : ℤ)).toNat
  have hn : (n : ℤ) = j + (N : ℤ) := Int.toNat_of_nonneg (by omega)
  have hjn : j = (n : ℤ) - (N : ℤ) := by omega
  let z := aux_rem_resolved_meshes_center y I
  let pl := It.prefixLen (((3 : ℝ) ^ (N : ℤ) * rho) • z)
    (1 - (1 - (t + 2 - (d : ℝ)) / 2) / Kt) (N - k) (aux_rem_resolved_meshes_relabel N om)
  let R := (3 : ℝ) ^ (-(k : ℤ)) / 2
  let sig := (((3 : ℝ) ^ j / 2) / R) ^ t
  let bv := aux_rem_resolved_meshes_bref M H om N k (rho • z)
  have hbv : 0 < bv := aux_lane4_two_mesh_energy_bound_bpos M H om N k (rho • z)
  have hZ : 0 ≤ Kf ^ 2 * R ^ ((d : ℝ) + 2) := by dsimp only [R]; positivity
  have hsig : 0 ≤ sig := by dsimp only [sig, R]; positivity
  have hEn : 0 ≤ aux_rem_resolved_meshes_energy a u (Metric.ball z (Lstar * R)) :=
    aux_rem_resolved_strata_energy_nonneg a ⟨u.1, u.2.1⟩ _
  have hB : 0 ≤ aux_rem_resolved_meshes_energy a u (Metric.ball z (Lstar * R)) +
      bv⁻¹ * (Kf ^ 2 * R ^ ((d : ℝ) + 2)) := by positivity
  change aux_rem_resolved_meshes_energy a u (Metric.ball z ((3 : ℝ) ^ j / 2)) ≤
    max 1 (7 * C1) * Real.exp ((t * Real.log 3 + 1) * (pl : ℝ)) * sig *
      (aux_rem_resolved_meshes_energy a u (Metric.ball z (Lstar * R)) + bv⁻¹ * Kf ^ 2 * R ^ ((d : ℝ) + 2))
  by_cases hgood : n + pl ≤ N - k
  · have hk2 : k + 2 ≤ N := by
      have hh := It.prefix_lower (((3 : ℝ) ^ (N : ℤ) * rho) • z)
        (1 - (1 - (t + 2 - (d : ℝ)) / 2) / Kt) (N - k) (aux_rem_resolved_meshes_relabel N om)
      rw [It.k_eq] at hh
      change 21 + 5 ≤ pl at hh
      omega
    let bFin : ℕ → ℝ := fun L => aux_lem_as_regularity_nc_ir_scalar M om N L *
      It.ref (N + L) (N - k - 2) (((3 : ℝ) ^ (N : ℤ) * rho) • z)
        (aux_rem_resolved_meshes_relabel N om)
    have hbconv : ∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → |bFin L - bv| < eps := by
      simpa only [bFin, bv, smul_smul] using
        aux_lem_as_regularity_nc_reference_limit It H om hIR N k hk2 (rho • z)
    have hlimit := aux_lem_as_regularity_nc_energy_limit hd a aFin hconv bv hbv bFin hbconv
      (Metric.ball z ((3 : ℝ) ^ j / 2)) (Metric.ball z (Lstar * R)) measurableSet_ball measurableSet_ball
      (C1 * sig) (Kf ^ 2 * R ^ ((d : ℝ) + 2)) (mul_nonneg hC1 hsig) hZ
      f hf Kf hfb hf0 u hu (fun L v hv => by
        have h := hfin M E P X Sreg It D hdelta rho hrho3 hrho1 om N L
          (aux_lem_as_regularity_nc_ir_scalar M om N L) (aux_lem_as_regularity_nc_ir_scalar_pos M om N L)
          (aFin L) (by positivity) (hA L) f hf Kf hKf hfb hf0 v hv y hy I n k Lstar hLstar hk1 hk hI hgood
        rw [← hjn] at h
        simpa only [bFin, z, R, sig, mul_assoc] using h)
    have he : 1 ≤ Real.exp ((t * Real.log 3 + 1) * (pl : ℝ)) :=
      Real.one_le_exp (mul_nonneg hc.le (Nat.cast_nonneg _))
    have hC : 7 * C1 ≤ max 1 (7 * C1) * Real.exp ((t * Real.log 3 + 1) * (pl : ℝ)) :=
      (le_max_right _ _).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) he)
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hsig) hB
    refine hlimit.trans ?_
    convert hmul using 1 <;> ring
  · have hjk : 0 ≤ j + (k : ℤ) + (pl : ℤ) := by omega
    have hfac := aux_rem_resolved_meshes_bad_factor t (t * Real.log 3 + 1) ht0 (by linarith) j k pl hjk
    have hLR : aux_rem_resolved_meshes_energy a u (Metric.ball z ((3 : ℝ) ^ j / 2)) ≤
        aux_rem_resolved_meshes_energy a u (Metric.ball z (Lstar * R)) :=
      aux_rem_resolved_strata_energy_mono a ⟨u.1, u.2.1⟩ (Metric.ball_subset_ball (by
        have hRp : 0 < R := by dsimp only [R]; positivity
        dsimp only [R] at *
        nlinarith))
    have h1 : 1 ≤ max 1 (7 * C1) * Real.exp ((t * Real.log 3 + 1) * (pl : ℝ)) * sig := by
      have h := one_le_mul_of_one_le_of_one_le (le_max_left 1 (7 * C1)) hfac
      simpa only [mul_assoc] using h
    have hsum := hLR.trans (le_add_of_nonneg_right (mul_nonneg (inv_pos.mpr hbv).le hZ))
    refine hsum.trans ?_
    convert le_mul_of_one_le_left hB h1 using 1 <;> ring


/-- Original-model prefix allowance at the residual root centre. -/
def aux_lem_as_regularity_nc_rho_B {d : ℕ} (pl : SpatialCoordinates d → ℕ → ℕ)
    (N kIt : ℕ) (rho : ℝ) (y : SpatialCoordinates d) (I : Finset (Fin d)) (k : ℕ) : ℝ :=
  if k ≤ N then
    (pl (((3 : ℝ) ^ (N : ℤ) * rho) • aux_rem_resolved_meshes_center y I) (N - k) : ℝ) +
      (kIt : ℝ) + 5
  else 0

/-- The residual macro-energy bank, obtained from the original-model prefix
and reference catalogues and the actual residual one-step estimate. -/
theorem aux_lem_as_regularity_nc_residual_mesh
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t eta etas p q : ℝ)
    (hLstar : 10 ≤ Lstar) (hRpos : 0 < Rstar) (hRlt : Rstar < 1 / (100 * Lstar))
    (hRmem : Rstar ∈ Set.range (fun j : ℤ => (3 : ℝ) ^ j / 2))
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (heta : 0 < eta) (hetat : eta < t - ((d : ℝ) - 1))
    (hetas : 0 < etas) (hetast : etas < (d : ℝ) + 2 - t)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hgap : (d : ℝ) < q * eta) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (P : in_poincare d hd E) (X : in_extension d hd E) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (D : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta →
        ∀ rho : ℝ, 1 / 3 ≤ rho → rho ≤ 1 →
        ∃ (U V : ℕ → BilateralField d → ℝ) (CU CV : ℝ),
          (∀ N om, 0 ≤ U N om) ∧ (∀ N om, 0 ≤ V N om) ∧
          (∀ N, MemLp (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, MemLp (V N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CU) ∧
          (∀ N, eLpNorm (V N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CV) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (a : PositiveCoefficient (unitNeumannCube d)),
          (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
            a.val y = cutoffCoefficient M H om N (rho • y)) →
          ∀ (f : SpatialCoordinates d → ℝ),
          AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          ∀ (Kf : ℝ), 0 ≤ Kf →
          (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
          (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
          ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
            aux_rem_resolved_meshes_energy a u (Metric.ball x (r / 2)) ≤
              C * U N om * r ^ (t - eta) *
                (aux_rem_resolved_meshes_energy a u Set.univ + V N om * Kf ^ 2) := by
  obtain ⟨Kt, Cstep, c, delta1, hKt, hCstep, hc, hdelta1, hone⟩ :=
    aux_lem_as_regularity_nc_residual_onestep d hd Lstar Rstar t hLstar hRlt ht htd
  have hq : 1 ≤ q := hp.trans hpq
  obtain ⟨qref, _, _, _, dref, Cmom, Crate, Cosc, CV, hdref, _, _, _, _, _, _, href⟩ :=
    lane4_reference_mesh_statistic d 1 hd le_rfl p q etas hp hq hetas
  obtain ⟨cC, c1, c2, hcC, _, _, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  have hKt1 : 1 ≤ Kt := by
    have h3 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have hn : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  let aT := 1 - (1 - (t + 2 - (d : ℝ)) / 2) / Kt
  have hα1 : 0 < 1 - (t + 2 - (d : ℝ)) / 2 := by linarith
  have haT : aT < 1 := by
    dsimp only [aT]
    have := div_pos hα1 (zero_lt_one.trans_le hKt1)
    linarith
  have haThalf : 1 / 2 ≤ aT := by
    have h := div_le_self hα1.le hKt1
    dsimp only [aT]
    linarith
  have horder : 1 ≤ ((d : ℝ) + 1) * q := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  obtain ⟨hdm, hdfacts⟩ := aux_rem_resolved_meshes_delta_facts cC aT (((d : ℝ) + 1) * q) c
    hcC haT (zero_lt_one.trans_le horder) hc
  let dm := min (1 / 2) (min (1 / cC) (min (((1 - aT) / cC) ^ 2)
    ((1 - aT) ^ 2 / (2 * (((d : ℝ) + 1) * q) * c * cC))))
  let Cm := 2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t * 3 ^ eta * 2 ^ t *
    (Rstar ^ (-t) + (d : ℝ) + 1)
  refine ⟨Cm, min dref (min delta1 dm),
    aux_lane4_two_mesh_energy_bound_Cpos d Lstar Rstar t eta hLstar hRpos,
    lt_min hdref (lt_min hdelta1 hdm), ?_⟩
  intro M E P X Rm Sreg It D H hIR hdelta rho hrho3 hrho1
  have hrho : 0 < rho := lt_of_lt_of_le (by norm_num) hrho3
  have hδref := hdelta.trans (min_le_left _ _)
  have hδ1 := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hδc, haTr, hrate⟩ := hdfacts M.delta M.shellPrefix.delta_pos hδm
  have hCeq : It.C = cC := (hconst E M Sreg It).1
  have hαT : aT ∈ It.alphaRange := by rw [It.alphaRange_eq, hCeq]; exact ⟨haThalf, haTr⟩
  have hδIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hδc
  obtain ⟨_, _, _, _, _, V, hVm, hV0, hVL, hVB, hVae⟩ := href M Rm H hIR hδref
  let pl (N : ℕ) (om : BilateralField d) := fun z m =>
    It.prefixLen z aT m (aux_rem_resolved_meshes_relabel N om)
  let Cat : ℕ → Type := fun n => (Fin d → Fin (3 ^ (n + 1) + 1)) ×
    ((Fin (d + 1) → Fin (n + 1 + 1)) × Equiv.Perm (Fin d))
  let B : (N n : ℕ) → Cat n → Fin (d + 1) → BilateralField d → ℝ := fun N n pi i om =>
    aux_lem_as_regularity_nc_rho_B (pl N om) N It.k rho
      (fun j => ((pi.1 j : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
      (Finset.univ.filter (fun j : Fin d => (pi.2.2.symm j).val < i.val)) (pi.2.1 i).val
  let K := Real.exp (c * 26) * (Real.exp (c * (cC + 1)) * (1 + cC))
  have hK : 1 ≤ K := by
    have h1 : 1 ≤ Real.exp (c * 26) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (cC + 1)) := Real.one_le_exp (by positivity)
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_mul_of_one_le_of_one_le h2 (by linarith))
  have hB0 : ∀ N n pi i om, 0 ≤ B N n pi i om := by
    intro N n pi i om
    dsimp only [B, aux_lem_as_regularity_nc_rho_B]
    split_ifs <;> positivity
  have hBM : ∀ N n pi i,
      MemLp (fun om => Real.exp (c * B N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp (c * B N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal K := by
    intro N n pi i
    simpa only [B, aux_lem_as_regularity_nc_rho_B, pl, Nat.add_zero, Nat.cast_zero, add_zero,
      zero_add, K] using aux_rem_resolved_meshes_allowance_moment It cC hCeq hcC aT hαT hδIt
        c (((d : ℝ) + 1) * q) hc horder hrate 0
        (((3 : ℝ) ^ (N : ℤ) * rho) • aux_rem_resolved_meshes_center
          (fun j => ((pi.1 j : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
          (Finset.univ.filter (fun j : Fin d => (pi.2.2.symm j).val < i.val))) N (pi.2.1 i).val
  obtain ⟨U, hUm, hU0, hUL, hUB, hUae, hRbound⟩ := aux_rem_resolved_meshes_regularity d 1
    (chaosSampleLaw M).toMeasure p q eta hp hpq heta hgap Cstep c K hCstep hc.le hK
    B hB0 (fun N n pi i => (hBM N n pi i).1) (fun N n pi i => (hBM N n pi i).2)
  refine ⟨U, V, (aux_rem_resolved_meshes_Rbound d 1 eta q Cstep K).toReal, CV,
    hU0, hV0, hUL, hVL, ?_, hVB, ?_⟩
  · intro N
    exact (hUB N).trans_eq (ENNReal.ofReal_toReal hRbound).symm
  · filter_upwards [hIR.2, hUae, hVae] with om hom hU hV
    intro N a ha f hf Kf hKf hfb hf0 u hu x hx r hr
    let En := aux_rem_resolved_meshes_energy a u
    have hmono : ∀ A A', A ⊆ A' → En A ≤ En A' :=
      fun A A' h => aux_rem_resolved_strata_energy_mono a ⟨u.1, u.2.1⟩ h
    have hnn : ∀ A, 0 ≤ En A := fun A => aux_rem_resolved_strata_energy_nonneg a ⟨u.1, u.2.1⟩ A
    let b := fun k z => aux_rem_resolved_meshes_bref M H om N k (rho • z)
    have hb : ∀ k z, 0 < b k z := fun k z => aux_lane4_two_mesh_energy_bound_bpos M H om N k (rho • z)
    let B0 := aux_lem_as_regularity_nc_rho_B (pl N om) N It.k rho
    have hB0' : ∀ y I k, 0 ≤ B0 y I k := by
      intro y I k
      dsimp only [B0, aux_lem_as_regularity_nc_rho_B]
      split_ifs <;> positivity
    apply aux_lane4_two_mesh_energy_bound_core d hd Lstar Rstar t eta etas hLstar hRpos hRlt hRmem
      ht htd heta hetat hetast 1 le_rfl Cstep c hCstep hc.le N Kf En hmono hnn b hb B0 hB0' ?_
      (U N om) ?_ (V N om) ?_ x hx r hr
    · intro y hy I s k hs hsN hs0 hk h8 hR hI
      have h := hone M E P X Sreg It D H hδ1 rho hrho3 hrho1 om hom N a ha f hf Kf hKf hfb hf0
        u hu y hy I s k hs hsN hs0 hk h8 hR hI
      refine h.trans ?_
      have hsrc : 0 ≤ En (Metric.ball (aux_rem_resolved_meshes_center y I)
          (Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2))) +
          (b k (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
            ((3 : ℝ) ^ (-(k : ℤ)) / 2) ^ ((d : ℝ) + 2) := by
        have := hb k (aux_rem_resolved_meshes_center y I)
        have := hnn (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * ((3 : ℝ) ^ (-(k : ℤ)) / 2)))
        positivity
      have he : Real.exp (c * (pl N om
          (((3 : ℝ) ^ (N : ℤ) * rho) • aux_rem_resolved_meshes_center y I) (N - k) : ℝ)) ≤
          Real.exp (c * B0 y I k) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc.le
        dsimp only [B0, aux_lem_as_regularity_nc_rho_B]
        rw [if_pos hk]
        have hh : (0 : ℝ) ≤ It.k := Nat.cast_nonneg _
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (zero_le_one.trans hCstep))
        (Real.rpow_nonneg (div_nonneg hs0.le (by positivity)) t)) hsrc
    · intro n g dep sigma
      exact (hU N).1 ⟨n, (g, (dep, sigma)), rfl⟩
    · intro k hk z hz
      apply (hV N).2 k hk (rho • z)
      intro i
      change 0 ≤ rho * z i ∧ rho * z i ≤ 1
      exact ⟨mul_nonneg hrho.le (hz i).1,
        (mul_le_mul hrho1 (hz i).2 (hz i).1 zero_le_one).trans_eq (one_mul 1)⟩
/-- A contraction about the origin maps the closed unit cube into itself. -/
theorem aux_lem_as_regularity_nc_rho_closed {d : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    {y : SpatialCoordinates d}
    (hy : y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d))) :
    rho • y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
  change dist (rho • y) (fun _ : Fin d => (1 / 2 : ℝ)) ≤ 1 / 2
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro i
  have hi := (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hy i
  simp only [Real.dist_eq] at hi
  have hy0 : 0 ≤ y i := by rcases abs_le.mp hi with ⟨h1,h2⟩; linarith
  have hy1 : y i ≤ 1 := by rcases abs_le.mp hi with ⟨h1,h2⟩; linarith
  have h0 := mul_nonneg hrho.le hy0
  have h1 : rho * y i ≤ 1 := (mul_le_mul hrho1 hy1 hy0 zero_le_one).trans_eq (one_mul 1)
  simp only [Pi.smul_apply, smul_eq_mul, Real.dist_eq]
  rw [abs_le]
  constructor <;> linarith

theorem aux_lem_as_regularity_nc_residual_sample (d : ℕ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (a : PositiveCoefficient (unitNeumannCube d))
    (ha : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a.val y = cutoffCoefficient M H om N (rho • y))
    (t t1 t0 Cm Cmic U V DN mN MN : ℝ)
    (htt1 : t ≤ t1) (hCm : 0 ≤ Cm) (hCmic : 0 < Cmic) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hbounds : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)),
      mN ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ MN)
    (hlog : ∀ x y, x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
          Set (SpatialCoordinates d)) →
        y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
          DN * (3 : ℝ) ^ N * dist x y)
    (hmic : ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / (3 : ℝ) ^ (-(N : ℝ)) * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ Kmac : ℝ, 0 ≤ Kmac →
        localGradientEnergy a (aux_rem_resolved_cube_meas x (Cmic * (3 : ℝ) ^ (-(N : ℝ))))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
          Kmac * ((3 : ℝ) ^ (-(N : ℝ))) ^ t1 →
        ∀ r : ℝ, 0 < r → r ≤ (3 : ℝ) ^ (-(N : ℝ)) →
          localGradientEnergy a (aux_rem_resolved_cube_meas x r)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
            Cmic * ((1 + DN) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac +
              mN⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)) * r ^ t)
    (hmac : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann a
          f u →
      ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
        (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
          a.val y *
            ∑ i : Fin d, (((sobolevGradient (u : SobolevData (unitNeumannCube d))) i :
              SpatialCoordinates d → ℝ) y) ^ 2) ≤
          Cm * U * r ^ (t0 - (t0 - t1)) *
            ((∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)) ∩
                (unitNeumannCube d : Set (SpatialCoordinates d)),
              a.val y *
                ∑ i : Fin d, (((sobolevGradient (u : SobolevData (unitNeumannCube d))) i :
                  SpatialCoordinates d → ℝ) y) ^ 2) + V * Kf ^ 2)) :
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann a
        f u →
    ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      localGradientEnergy
          a
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        ((Cm * 2 ^ t1) * (U * (1 + V)) +
          (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
            ((1 + DN) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U * (1 + V))) +
          (Cmic * 2 ^ t) * (‖MN + mN⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))) *
          (sobolevCoefficientForm
            a
            (u : SobolevData (unitNeumannCube d))
            (u : SobolevData (unitNeumannCube d)) + Kf ^ 2) * r ^ t := by
  have heps : 0 < (3 : ℝ) ^ (-(N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  let A : C(SpatialCoordinates d, ℝ) :=
    ⟨fun y => cutoffCoefficient M H om N (rho • y),
      (cutoffCoefficient_continuous M H om N).comp (continuous_const_smul _)⟩
  have haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A := ha
  have hcl : closure (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
    show closure (Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) =
      Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)
    exact closure_ball _ (by norm_num)
  have hAK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      mN ≤ A y ∧ A y ≤ MN := by
    intro y hy
    exact hbounds _ (aux_lem_as_regularity_nc_rho_closed hrho hrho1 (hcl ▸ hy))
  have hinv : DN / (3 : ℝ) ^ (-(N : ℝ)) = DN * (3 : ℝ) ^ N := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_inv_eq_mul]
  have hlog' : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        |Real.log (A y) - Real.log (A z)| ≤ DN / (3 : ℝ) ^ (-(N : ℝ)) * dist y z := by
    rw [hcl, hinv]
    intro y hy z hz
    have h := hlog (rho • y) (rho • z)
      (aux_lem_as_regularity_nc_rho_closed hrho hrho1 hy)
      (aux_lem_as_regularity_nc_rho_closed hrho hrho1 hz)
    have hdil : dist (rho • y) (rho • z) ≤ dist y z := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hrho]
      exact mul_le_of_le_one_left dist_nonneg hrho1
    exact h.trans (mul_le_mul_of_nonneg_left hdil (by positivity))
  have hmM : mN ≤ MN := by
    have hc : (fun _ : Fin d => (1 / 2 : ℝ)) ∈
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) :=
      Metric.mem_closedBall_self (by norm_num)
    exact (hbounds _ hc).1.trans (hbounds _ hc).2
  have hSN : mN⁻¹ ≤ ‖MN + mN⁻¹‖ := by
    have h0 : 0 ≤ MN := hmN.le.trans hmM
    rw [Real.norm_eq_abs]
    exact le_abs.mpr (Or.inl (by linarith))
  refine aux_rem_resolved_first _ t t1 Cm Cmic ((3 : ℝ) ^ (-(N : ℝ))) U V DN mN ‖MN + mN⁻¹‖
    htt1 hCm hCmic heps hU hV hDN hmN hSN (hmic _ A haA DN mN MN hDN hmN hAK hlog') ?_
  intro f hf Kf hKf hfb hmean u hsol x hx r hr
  have hr' : (3 : ℝ) ^ (-(N : ℤ)) ≤ r := by rw [aux_rem_resolved_zpow_eq_rpow]; exact hr
  have h := hmac f hf Kf hKf hfb hmean u hsol x hx r hr'
  rw [sub_sub_cancel, aux_rem_resolved_meshes_energy_eq_local _ _ _ (aux_rem_resolved_cube_meas x r),
    aux_rem_resolved_meshes_energy_eq_local _ _ _ (unitNeumannCube d).isOpen.measurableSet] at h
  exact h
/-- Full residual-pullback energy bank, including microscopic radii. The
finite moment list and threshold precede the residual side. -/
theorem aux_lem_as_regularity_nc_residual_resolved :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < (d : ℝ) → (∀ i, 1 ≤ ps i) →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ rho : ℝ, 1 / 3 ≤ rho → rho ≤ 1 →
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (a : PositiveCoefficient (unitNeumannCube d)),
          (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
            a.val y = cutoffCoefficient M H om N (rho • y)) →
          ∀ (f : SpatialCoordinates d → ℝ),
          AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          ∀ (Kf : ℝ), 0 ≤ Kf →
          (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
          (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
          ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy a
              (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                K N om * (sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
                  (u : SobolevData (unitNeumannCube d)) + Kf ^ 2) * r ^ t := by
  intro d hd _ _ E _P _X _W D t k ps ht_low ht_high hps
  have hdt : 0 < (d : ℝ) - t := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht_nn : 0 ≤ t := by linarith
  -- exponents: t < t1 < t0 < d, eta = t0 - t1, all fixed before disorder
  have hex1 : ∃ t1 : ℝ, t1 = t + ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ := hex1
  have hex0 : ∃ t0 : ℝ, t0 = t + 2 * ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ := hex0
  have htt1 : t < t1 := by rw [ht1]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1]; linarith
  have ht0_low : (d : ℝ) - 1 < t0 := by rw [ht0]; linarith
  have ht0_high : t0 < (d : ℝ) := by rw [ht0]; linarith
  have heta_pos : 0 < t0 - t1 := by rw [ht0, ht1]; linarith
  have heta_lt : t0 - t1 < t0 - ((d : ℝ) - 1) := by rw [ht0, ht1]; linarith
  have hetas_pos : 0 < ((d : ℝ) + 2 - t0) / 2 := by linarith
  have hetas_lt : ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 := by linarith
  -- one moment order covering the finite list
  have hexp : ∃ pmax : ℝ, pmax = 1 + ∑ i : Fin k, |ps i| := ⟨_, rfl⟩
  obtain ⟨pmax, hpmax_def⟩ := hexp
  have hsum_nn : 0 ≤ ∑ i : Fin k, |ps i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hpmax : 1 ≤ pmax := by rw [hpmax_def]; linarith
  have hps_le : ∀ i : Fin k, ps i ≤ pmax := by
    intro i
    have h1 : ps i ≤ |ps i| := le_abs_self _
    have h2 : |ps i| ≤ ∑ j : Fin k, |ps j| :=
      Finset.single_le_sum (f := fun j => |ps j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hpmax_def]; linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hq1 : 1 ≤ 2 * pmax * max 1 t := by nlinarith
  have hpq : pmax ≤ 2 * pmax * max 1 t := by nlinarith
  have hqmesh_p : 1 ≤ 2 * (2 * pmax * max 1 t) := by linarith
  have hqmesh_q : 2 * (2 * pmax * max 1 t) ≤
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) := le_max_left _ _
  have hqmesh_eta : (d : ℝ) <
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) := by
    have h1 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) = (d : ℝ) + 1 := by
      field_simp
    have h2 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) heta_pos.le
    linarith
  -- geometric root radius
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ (-7 : ℤ) / 2 := by positivity
  have hRlt : (3 : ℝ) ^ (-7 : ℤ) / 2 < 1 / (100 * 10) := by norm_num
  have hRmem : (3 : ℝ) ^ (-7 : ℤ) / 2 ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := ⟨-7, rfl⟩
  -- the large-scale common package
  have hM := aux_lem_as_regularity_nc_residual_mesh d hd 10 ((3 : ℝ) ^ (-7 : ℤ) / 2) t0 (t0 - t1)
    (((d : ℝ) + 2 - t0) / 2) (2 * (2 * pmax * max 1 t))
    (max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1))) (by norm_num) hRpos hRlt hRmem
    ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hqmesh_p hqmesh_q hqmesh_eta
  rcases hM with ⟨Cm, delta0m, hCm, hdelta0m, hmesh⟩
  -- the microscopic matched range
  have hp1 : (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by
    have : 0 ≤ 4 * (d : ℝ) / ((d : ℝ) - t) := by positivity
    linarith
  have htp : t < (d : ℝ) - 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) := by
    have hp1pos : 0 < 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by linarith
    have hkey : 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) < ((d : ℝ) - t) / 2 := by
      rw [div_lt_iff₀ hp1pos]
      have h4 : ((d : ℝ) - t) * (4 * (d : ℝ) / ((d : ℝ) - t)) = 4 * (d : ℝ) := by
        field_simp
      nlinarith
    linarith
  have hml := aux_rem_resolved_micro_local d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hml with ⟨Cmic, hCmic, hmicL⟩
  have hms := rem_resolved_microscopic d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hms with ⟨_, _, _, _, _, _, hstat⟩
  -- extremes of the actual cutoff coefficient on the closed unit cube
  have hX := aux_lem_extremes_compat d hd (fun _ => (1 / 2 : ℝ)) 1 one_pos (2 * pmax * max 1 t) hq1
  rcases hX with ⟨Cpe, Cde, cde, hCpe, hCde, hcde, hextM⟩
  -- rate budget
  have hexr : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  obtain ⟨rmax, hrmax_def⟩ := hexr
  have hrmax : 0 < rmax := by
    rw [hrmax_def]
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) hdt)) ?_
    exact Real.log_pos (by norm_num)
  have hqpos : 0 < 2 * pmax * max 1 t := by linarith
  refine ⟨min (min delta0m (cde / (2 * pmax * max 1 t)))
    (min 1 (rmax / (2 * (Cde + Cpe)))), ?_, ?_⟩
  · refine lt_min (lt_min hdelta0m (div_pos hcde hqpos)) (lt_min one_pos ?_)
    exact div_pos hrmax (by positivity)
  intro M _Rm Sreg _It H hIR hδ rho hrho3 hrho1
  have hrho : 0 < rho := lt_of_lt_of_le (by norm_num) hrho3
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδm : M.delta ≤ delta0m := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ cde / (2 * pmax * max 1 t) :=
    hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : M.delta ≤ rmax / (2 * (Cde + Cpe)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate := aux_rem_resolved_rate Cde Cpe rmax M.delta hCde hCpe hrmax hδpos hδ1 hδr
  rw [hrmax_def] at hrate
  -- instantiate the large-scale package and the extremes on the same sample law
  have hmM := hmesh M E _P _X _Rm Sreg _It D H hIR hδm rho hrho3 hrho1
  rcases hmM with ⟨U, V, CU, CV, hU0, hV0, hULp, hVLp, hUb0, hVb0, hae⟩
  let Cp := max 1 (max CU CV)
  have hCp : 0 < Cp := zero_lt_one.trans_le (le_max_left _ _)
  have hUb : ∀ N, eLpNorm (U N) (ENNReal.ofReal (2 * (2 * pmax * max 1 t)))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cp := fun N =>
    (hUb0 N).trans (ENNReal.ofReal_le_ofReal ((le_max_left CU CV).trans (le_max_right _ _)))
  have hVb : ∀ N, eLpNorm (V N) (ENNReal.ofReal (2 * (2 * pmax * max 1 t)))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cp := fun N =>
    (hVb0 N).trans (ENNReal.ofReal_le_ofReal ((le_max_right CU CV).trans (le_max_right _ _)))
  have heM := hextM M H hIR hδe
  rcases heM with ⟨De, mlow, mhigh, hDe0, heae, hDeLp, hmLp, hDeb, hmb⟩
  have hW : ∀ N : ℕ,
      MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t) Cp hq1 hCp.le
      (U N) (V N) (hULp N) (hVLp N) (hUb N) (hVb N)
  have hSb : ∀ N : ℕ,
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖)
        (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * Cpe *
        Real.exp ((Cde * M.delta + Cpe * M.delta ^ 2) * (N : ℝ))) := by
    intro N
    have h2 : (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖) =
        fun om => 2 * ‖mhigh N om + (mlow N om)⁻¹‖ := by
      funext om; ring
    have hm := hmb N
    calc _ = ENNReal.ofReal 2 * eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
            (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure := by
          rw [h2, aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm _ _ 2 (by norm_num),
            eLpNorm_norm _ (hmLp N).aestronglyMeasurable]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal
            (Cpe * Real.exp ((Cde * M.delta + Cpe * M.delta ^ 2) * (N : ℝ))) := by
          gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num), mul_assoc]
  have hstatM := hstat (BilateralField d) (chaosSampleLaw M).toMeasure pmax hpmax De
    (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖) (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖)
    (fun N om => U N om * (1 + V N om)) Cpe (2 * Cpe) (Cp * (1 + Cp))
    (Cde * M.delta + Cpe * M.delta ^ 2) hCpe.le (by positivity) (by positivity) hrate.1 hrate.2
    (fun N om => ⟨hDe0 N om, norm_nonneg _, norm_nonneg _,
      mul_nonneg (hU0 N om) (by linarith [hV0 N om])⟩)
    (fun N => ⟨hDeLp N, (hmLp N).norm, (hmLp N).norm, (hW N).1⟩)
    hDeb hSb (fun N => (hW N).2)
  rcases hstatM with ⟨B, hB0, hBN⟩
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm.le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  have hmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B) := by
    intro i N
    have hBNN := hBN N
    beta_reduce at hBNN
    have hWm := (hW N).1.aestronglyMeasurable
    have hDt := (aux_rem_resolved_microscopic_one_add_power_memLp (chaosSampleLaw M).toMeasure
      pmax t hpmax ht_nn (De N) (hDe0 N) (hDeLp N)).aestronglyMeasurable
    have hT1m : AEStronglyMeasurable (fun om =>
        (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om)))
        (chaosSampleLaw M).toMeasure :=
      (hDt.mul aestronglyMeasurable_const).mul hWm
    have hT2m : AEStronglyMeasurable (fun om =>
        ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (chaosSampleLaw M).toMeasure :=
      (hmLp N).norm.aestronglyMeasurable.mul aestronglyMeasurable_const
    have hWb : eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal pmax)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans (hW N).2
    exact aux_rem_resolved_three_term_moment (chaosSampleLaw M).toMeasure pmax _ _ _
      (Cp * (1 + Cp)) B hpmax hA1 hA2 hA3 (by positivity) hB0 _ _ _ hWm hT1m hT2m hWb
      hBNN.1 hBNN.2.1 (ps i) (hps_le i)
  refine ⟨fun N om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)),
    fun _ => (Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B, ?_,
    fun i N => (hmom i N).1, fun i N => (hmom i N).2, ?_⟩
  · intro N om
    have h1 : 0 ≤ U N om * (1 + V N om) := mul_nonneg (hU0 N om) (by linarith [hV0 N om])
    have h2 : 0 ≤ (1 + De N om) ^ t := (Real.rpow_pos_of_pos (by linarith [hDe0 N om]) _).le
    have h3 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h4 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h5 := norm_nonneg (mhigh N om + (mlow N om)⁻¹)
    exact add_nonneg (add_nonneg (mul_nonneg hA1 h1) (mul_nonneg hA2 (mul_nonneg (mul_nonneg h2 h3) h1)))
      (mul_nonneg hA3 (mul_nonneg h5 h4))
  · filter_upwards [hae, heae] with om hω1 hω2
    intro N a ha
    refine aux_lem_as_regularity_nc_residual_sample d M H om N rho hrho hrho1 a ha t t1 t0 Cm Cmic
      (U N om) (V N om) (De N om) (mlow N om) (mhigh N om) htt1.le hCm.le hCmic
      (hU0 N om) (hV0 N om) (hDe0 N om) (hω2 N).2.1 (hω2 N).2.2 (hω2 N).1
      (hmicL ((3 : ℝ) ^ (-(N : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp))) ?_
    intro f hf Kf hKf hfb hmean u hsol x hx r hr
    have h := hω1 N a ha f hf Kf hKf hfb hmean u hsol x hx r hr
    rw [aux_lane4_two_mesh_energy_bound_ball_eq (by omega : 1 ≤ d) x (r / 2)] at h
    simpa only [aux_rem_resolved_meshes_energy, Set.univ_inter, Set.inter_self] using h


/-- Transport the residual local-energy estimate, retaining the exact global
energy term and the inverse reference on the source term. -/
theorem aux_lem_as_regularity_nc_residual_energy_data {d : ℕ}
    (z z0 : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a1 a2 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (c : ℝ) (hc : 0 < c) (hcoef : a1 = scalePositiveCoefficient c hc a2)
    (ha1 : ∀ᵐ y ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      a1.val y = a.val (cubeDilation z z0 r y))
    (t KR KG Kf : ℝ) (hKR : 0 ≤ KR) (hKf : 0 ≤ Kf)
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (v1 : meanZeroSobolevGraph (centeredCube z0 1 one_pos))
    (F1 : SpatialCoordinates d → ℝ)
    (hFm : AEMeasurable F1 (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ y ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      |F1 y| ≤ r ^ 2 * Kf)
    (hFz : (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F1 y) = 0)
    (hsol : SolvesNeumann a1 F1 v1)
    (hv1 : ∀ᵐ y ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (v1 : SobolevData (centeredCube z0 1 one_pos)).1 y =
        (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z0 r y))
    (henergy : ∀ (x : SpatialCoordinates d) (s : ℝ), 0 < s →
      localGradientEnergy a1
        (s := ball x s ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos))) =
      r ^ ((2 : ℝ) - d) * localGradientEnergy a
        (s := ball (cubeDilation z z0 r x) (r * s) ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube z r hr))))
    (hglobal : sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr)) v ≤ KG * Kf ^ 2)
    (hres : ∀ (f : SpatialCoordinates d → ℝ),
      AEMeasurable f (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ᵐ y ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), |f y| ≤ B) →
      (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), f y) = 0 →
      ∀ u : meanZeroSobolevGraph (centeredCube z0 1 one_pos), SolvesNeumann a2 f u →
      ∀ x ∈ centeredCube z0 1 one_pos, ∀ s : ℝ, 0 < s → s ≤ 1 →
      localGradientEnergy a2
        (s := ball x s ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z0 1 one_pos))) ≤
      KR * (sobolevCoefficientForm a2 (u : SobolevData (centeredCube z0 1 one_pos)) u + B ^ 2) * s ^ t) :
    ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
      localGradientEnergy a
        (s := ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
      (r ^ (-t) * (KR * KG) + r ^ ((d : ℝ) + 2 - t) * KR / c) * Kf ^ 2 * rad ^ t := by
  have hFdiv : ∀ᵐ y ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      |F1 y / c| ≤ r ^ 2 * Kf / c := by
    filter_upwards [hFb] with y hy
    rw [abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right hy hc.le
  have hFdivz : (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F1 y / c) = 0 := by
    rw [integral_div, hFz, zero_div]
  have hsolve2 := aux_fscc_holNeuH_solvesNeumann_unscale c hc a1 a2 hcoef F1 v1 hsol
  let vw : weakSobolevGraph (centeredCube z r hr) :=
    ⟨v, ((mem_meanZeroSobolevGraph_iff _).mp v.property).1⟩
  let v1w : weakSobolevGraph (centeredCube z0 1 one_pos) :=
    ⟨v1, ((mem_meanZeroSobolevGraph_iff _).mp v1.property).1⟩
  have hform := aux_lem_as_regularity_affine_transport_form_scaling d z z0 r hr one_pos
    a a1 vw vw v1w v1w ha1 hv1 hv1
  change sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr)) v =
    r ^ ((d : ℝ) - 2) * sobolevCoefficientForm a1 (v1 : SobolevData (centeredCube z0 1 one_pos)) v1 at hform
  rw [hcoef, sobolevCoefficientForm_scale] at hform
  intro x hx rad hrad hradR
  let x1 := cubeDilation z0 z r⁻¹ x
  have hx1 : x1 ∈ centeredCube z0 1 one_pos :=
    aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube z z0 hr hx
  have hbound := hres (fun y => F1 y / c) (hFm.div_const c) (r ^ 2 * Kf / c)
    (by positivity) hFdiv hFdivz v1 hsolve2 x1 hx1 (rad / r) (div_pos hrad hr)
      ((div_le_one hr).mpr hradR)
  have hE := henergy x1 (rad / r) (div_pos hrad hr)
  rw [hcoef, aux_lem_as_regularity_nc_localGradientEnergy_scale] at hE
  have hTx : cubeDilation z z0 r x1 = x := aux_prop_growth_large_root_cubeDilation_inv_left z z0 hr x
  rw [hTx, mul_div_cancel₀ _ hr.ne'] at hE
  have hinv : r ^ ((d : ℝ) - 2) * r ^ ((2 : ℝ) - d) = 1 := by
    rw [← Real.rpow_add hr]; ring_nf; simp
  have hroot := congrArg (fun y : ℝ => r ^ ((d : ℝ) - 2) * y) hE
  have hsc : r ^ ((d : ℝ) - 2) * (c *
      (KR * (sobolevCoefficientForm a2 (v1 : SobolevData (centeredCube z0 1 one_pos)) v1 +
        (r ^ 2 * Kf / c) ^ 2) * (rad / r) ^ t)) =
      (KR * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr)) v) *
        (rad / r) ^ t + (r ^ ((d : ℝ) + 2 - t) * KR / c) * Kf ^ 2 * rad ^ t := by
    have hsrc := aux_lem_as_regularity_nc_energy_algebra r c KR Kf rad d t hr hc hrad
    rw [hform]
    linear_combination hsrc
  calc _ = r ^ ((d : ℝ) - 2) * (c * localGradientEnergy a2
          (s := ball x1 (rad / r) ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
          (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos)))) := by
        simpa only [← mul_assoc, hinv, one_mul] using hroot.symm
    _ ≤ r ^ ((d : ℝ) - 2) * (c *
        (KR * (sobolevCoefficientForm a2 (v1 : SobolevData (centeredCube z0 1 one_pos)) v1 +
          (r ^ 2 * Kf / c) ^ 2) * (rad / r) ^ t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hc.le) (Real.rpow_nonneg hr.le _)
    _ = _ := hsc
    _ ≤ (KR * (KG * Kf ^ 2)) * (rad / r) ^ t +
        (r ^ ((d : ℝ) + 2 - t) * KR / c) * Kf ^ 2 * rad ^ t :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hglobal hKR)
        (Real.rpow_nonneg (div_pos hrad hr).le _)) le_rfl
    _ = _ := by rw [Real.div_rpow hrad.le hr.le, Real.rpow_neg hr.le]; ring

/-- The native, centred residual cube has an actual finite-moment local energy
bank. Its threshold is independent of the residual side. -/
theorem aux_lem_as_regularity_nc_residual_native_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (rho : ℝ) (hrho : 0 < rho), 1 / 3 ≤ rho → rho ≤ 1 →
        ∃ (K : ℕ → BilateralField d → ℝ) (CK : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CK i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
            aux_lem_as_regularity_rho_energy_estimate rho hrho
              (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho) t (K N om) := by
  have hps2 : ∀ i, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨dr, hdr, hres⟩ := aux_lem_as_regularity_nc_residual_resolved d hd E P X W D t k
    (fun i => 2 * ps i) ht1 ht2 hps2
  obtain ⟨dg, hdg, hglob⟩ := aux_lem_as_regularity_nc_global_energy_bank d hd E P k
    (fun i => 2 * ps i) hps2
  refine ⟨min dr dg, lt_min hdr hdg, ?_⟩
  intro M Rm Sreg It H hIR hdelta rho hrho hrho3 hrho1
  obtain ⟨KR, CR, hKR0, hKRL, hKRB, hRAE⟩ :=
    hres M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) rho hrho3 hrho1
  obtain ⟨KG, CG, hKG0, hKGL, hKGB, hG⟩ :=
    hglob M Rm H hIR (hdelta.trans (min_le_right _ _)) 0 rho hrho hrho1
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let w : SpatialCoordinates d := -(rho • z0)
  let KS : ℕ → BilateralField d → ℝ := fun N om => KR N (aux_transport_S 0 w om)
  have hS := aux_transport_S_measurePreserving M 0 w
  have hKSL : ∀ i N, MemLp (KS N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure :=
    fun i N => (hKRL i N).comp_measurePreserving hS
  have hKSB : ∀ i N, eLpNorm (KS N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (max (CR i) 0) := by
    intro i N
    calc _ = eLpNorm (KR N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure :=
          eLpNorm_comp_measurePreserving (hKRL i N).aestronglyMeasurable hS
      _ ≤ _ := (hKRB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  let K1 : ℕ → BilateralField d → ℝ := fun N om => rho ^ (-t) * (KS N om * KG N om)
  let C1 : Fin k → ℝ := fun i => rho ^ (-t) * (max (CR i) 0 * CG i)
  have h1 := fun i N => aux_lem_as_regularity_nc_product_moment (chaosSampleLaw M).toMeasure
    (ps i) (rho ^ (-t)) (max (CR i) 0) (CG i) (Real.rpow_nonneg hrho.le _) (le_max_right _ _)
    (KS N) (KG N) (hKSL i N) (hKGL i N) (hKSB i N) (hKGB i N)
  have h2 := fun i => aux_lem_as_regularity_nc_transport_moment hd M H hIR w 0 (ps i)
    (rho ^ ((d : ℝ) + 2 - t)) (max (CR i) 0) (lt_of_lt_of_le one_pos (hps i))
    (Real.rpow_nonneg hrho.le _) (le_max_right _ _) KR (hKRL i)
    (fun N => (hKRB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  choose C2 hC2 h2 using h2
  let K2 : ℕ → BilateralField d → ℝ := fun N om =>
    rho ^ ((d : ℝ) + 2 - t) * KS N om / aux_transport_reference M H N 0 w om
  have h2' : ∀ i N, MemLp (K2 N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (K2 N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C2 i) := by
    intro i N
    simpa only [K2, KS, sub_zero, Int.toNat_natCast] using h2 i N (by omega)
  have hsum := fun i N => aux_prop_growth_holder_assembly_moment (chaosSampleLaw M).toMeasure
    (hps i) (K1 N) (K2 N) (show 0 ≤ (1 : ℝ) by norm_num) (h1 i N).1 (h2' i N).1
      (h1 i N).2 (h2' i N).2
  refine ⟨fun N om => 1 + 1 * (K1 N om + K2 N om),
    fun i => 1 + 1 * (max (C1 i) 0 + max (C2 i) 0), ?_,
    fun i N => (hsum i N).1, fun i N => (hsum i N).2, ?_⟩
  · intro N om
    have hr := hKR0 N (aux_transport_S 0 w om)
    have hg := hKG0 N om
    have hc := (aux_transport_reference_pos M H N 0 w om).le
    dsimp [K1, K2, KS]
    positivity
  · have hcoe := ae_all_iff.mpr fun N : ℕ => aux_transport_coefficient M 0 w hIR N (by omega)
    filter_upwards [hS.quasiMeasurePreserving.ae hRAE, hcoe] with om hres hcoef
    intro N F Kf hKf hFm hFb hFz v hsol x hx rad hrad hradR
    obtain ⟨a1, ha1, _, hNeumannPart⟩ := lem_as_regularity_affine_transport d M H om N 0 rho hrho
    obtain ⟨a2, ha2⟩ := lane4_dilation_coefficient_transport d (rho • z0) z0 rho hrho one_pos
      (cutoffPositiveCoefficient M H (aux_transport_S 0 w om) N (rho • z0) hrho)
    have hq1 := lane4_dilation_quasi_measure_preserving d 0 z0 rho hrho one_pos
    have hq2 := lane4_dilation_quasi_measure_preserving d (rho • z0) z0 rho hrho one_pos
    have ha2' : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a2.val y = cutoffCoefficient M H (aux_transport_S 0 w om) N (rho • y) := by
      filter_upwards [ha2, hq2.ae (aux_fscc_holNeuH_cutoffPos_val M H (aux_transport_S 0 w om) N
        (rho • z0) hrho)] with y hy1 hy2
      rw [hy1, hy2, aux_lem_as_regularity_nc_dilation_smul]
    have hident : a1 = scalePositiveCoefficient (aux_transport_reference M H N 0 w om)
        (aux_transport_reference_pos M H N 0 w om) a2 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [ha1, hq1.ae (aux_fscc_holNeuH_cutoffPos_val M H om N 0 hrho), ha2',
        scalePositiveCoefficient_coeFn (aux_transport_reference M H N 0 w om)
          (aux_transport_reference_pos M H N 0 w om) a2] with y hy1 hy2 hy3 hy4
      have hpt : cubeDilation (0 : SpatialCoordinates d) z0 rho y = w + rho • y := by
        funext i; simp only [cubeDilation_apply, Pi.zero_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Pi.neg_apply, w]; ring
      have hp := hcoef N (rho • y)
      simp only [neg_zero, zpow_zero, one_smul, sub_zero, Int.toNat_natCast] at hp
      erw [hy1, hy2, hpt, hp, ← hy3, hy4]
    obtain ⟨F1, v1, _, hF1m, hF1b, hF1z, hsol1, hv1, _, henergy⟩ :=
      hNeumannPart F Kf hKf hFm hFb hFz v hsol
    have h := aux_lem_as_regularity_nc_residual_energy_data 0 z0 rho hrho _ a1 a2
      (aux_transport_reference M H N 0 w om) (aux_transport_reference_pos M H N 0 w om) hident ha1
      t (KS N om) (KG N om) Kf (hKR0 _ _) hKf v v1 F1 hF1m hF1b hF1z hsol1 hv1 henergy
      (hG om N F Kf hKf hFm hFb v hsol) (hres N a2 ha2') x hx rad hrad hradR
    apply h.trans
    have hK : K1 N om + K2 N om ≤ 1 + 1 * (K1 N om + K2 N om) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (sq_nonneg Kf))
      (Real.rpow_nonneg hrad.le _)


/-- Lowering the energy exponent on radii at most one preserves the full
Neumann estimate and its Hölder exponent. -/
theorem aux_lem_as_regularity_nc_exponent_mono {d : ℕ}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {a : PositiveCoefficient (centeredCube z r hr)} {t t' alpha K : ℝ}
    (htt : t ≤ t') (hK : 0 ≤ K)
    (h : aux_lem_as_regularity_nc_estimate z r hr a t' alpha K) :
    aux_lem_as_regularity_nc_estimate z r hr a t alpha K := by
  intro F Kf hKf hFm hFb hFz v hsol
  obtain ⟨hH, hE⟩ := h F Kf hKf hFm hFb hFz v hsol
  refine ⟨hH, ?_⟩
  intro x rad hx hrad hrad1
  exact (hE x rad hx hrad hrad1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hrad hrad1 htt) (mul_nonneg hK (sq_nonneg Kf)))

/-- Full finite-moment Neumann estimates on the actual native residual cube.
The local-energy input is supplied by the proved residual mesh argument. -/
theorem aux_lem_as_regularity_nc_residual_full_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (rho : ℝ) (hrho : 0 < rho), 1 / 3 ≤ rho → rho ≤ 1 →
        ∃ (K : ℕ → BilateralField d → ℝ) (CK : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CK i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
            aux_lem_as_regularity_nc_estimate (0 : SpatialCoordinates d) rho hrho
              (cutoffPositiveCoefficient M H om N (0 : SpatialCoordinates d) hrho) t alpha (K N om) := by
  let tE : ℝ := (max t ((d : ℝ) + 2 * alpha - 2) + d) / 2
  have hm : max t ((d : ℝ) + 2 * alpha - 2) < d := max_lt ht2 (by linarith)
  have htt : t < tE := by have := le_max_left t ((d : ℝ) + 2 * alpha - 2); dsimp [tE]; linarith
  have hEd : tE < (d : ℝ) := by dsimp [tE]; linarith
  have hE1 : (d : ℝ) - 1 < tE := ht1.trans htt
  have hE0 : 0 ≤ tE := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hgap : 0 < 2 + tE - 2 * alpha - d := by
    have := le_max_right t ((d : ℝ) + 2 * alpha - 2); dsimp [tE]; linarith
  obtain ⟨dE, hdE, hEb⟩ := aux_lem_as_regularity_nc_residual_native_bank d hd E P X W D tE k ps hE1 hEd hps
  obtain ⟨dH, hdH, hHb⟩ := aux_lem_as_regularity_rho_bank_of_energy d hd E P Cp tE alpha hE0 ha ha1 hgap k ps hps
  refine ⟨min dE dH, lt_min hdE hdH, ?_⟩
  intro M Rm Sreg It H hIR hdelta rho hrho hrho3 hrho1
  obtain ⟨KE, CE, hKE0, hKEL, hKEB, hKEae⟩ := hEb M Rm Sreg It H hIR
    (hdelta.trans (min_le_left _ _)) rho hrho hrho3 hrho1
  obtain ⟨KH, CH, hKH0, hKHL, hKHB, hKHae⟩ := hHb M Rm H hIR
    (hdelta.trans (min_le_right _ _)) rho hrho hrho1 KE CE hKE0 hKEL hKEB hKEae
  refine ⟨KH, CH, hKH0, hKHL, hKHB, ?_⟩
  filter_upwards [hKHae] with om hom N
  exact aux_lem_as_regularity_nc_exponent_mono htt.le (hKH0 N om) (hom N)

theorem aux_lem_as_regularity_nc_octave_decompose (r : ℝ) (hr : 0 < r) :
    ∃ (m : ℤ) (rho : ℝ), rho ∈ Set.Ioc ((1 : ℝ) / 3) 1 ∧ r = (3 : ℝ) ^ (-m) * rho := by
  set k : ℤ := ⌈Real.logb 3 r⌉ with hkdef
  have hb1 : (1 : ℝ) < 3 := by norm_num
  have hrpow : (3 : ℝ) ^ Real.logb 3 r = r := Real.rpow_logb (by norm_num) (by norm_num) hr
  have hkge : Real.logb 3 r ≤ (k : ℝ) := Int.le_ceil _
  have hkgt : (k : ℝ) - 1 < Real.logb 3 r := by
    have := Int.ceil_lt_add_one (Real.logb 3 r)
    rw [← hkdef] at this
    linarith
  have h1 : r ≤ (3 : ℝ) ^ (k : ℝ) := by
    rw [← hrpow]
    exact (Real.rpow_le_rpow_left_iff hb1).2 hkge
  have h2 : (3 : ℝ) ^ ((k : ℝ) - 1) < r := by
    rw [← hrpow]
    exact (Real.rpow_lt_rpow_left_iff hb1).2 hkgt
  rw [Real.rpow_intCast] at h1
  rw [Real.rpow_sub (by norm_num : (0:ℝ) < 3), Real.rpow_intCast, Real.rpow_one] at h2
  refine ⟨-k, r / (3 : ℝ) ^ k, ⟨?_, ?_⟩, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    linarith
  · rw [neg_neg]
    field_simp


theorem aux_lem_as_regularity_nc_all_cubes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) ,
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
            t alpha (K N om) := by
  have hps2 : ∀ i, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨δH, hδH, hHbank⟩ := aux_lem_as_regularity_nc_residual_full_bank d hd E P X W D Cp
    t alpha k (fun i => 2 * ps i) ht htd ha ha1 hps2
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨δS, hδS, hSbank⟩ := aux_lem_as_regularity_nc_small_bank d hd E P W Cp t alpha
    ht htd ha ha1 k ps hps
  refine ⟨min δH δS, lt_min hδH hδS, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  obtain ⟨j, rho, hrho, hreq⟩ := aux_lem_as_regularity_nc_octave_decompose r hr
  have hrhop : 0 < rho := lt_trans (by norm_num) hrho.1
  obtain ⟨KR, CR, hKR, hKRL, hKRB, hRAE⟩ := hHbank M Rm Sreg It H hIR
    (hdelta.trans (min_le_left _ _)) rho hrhop hrho.1.le hrho.2
  obtain ⟨KH, CH, hKH, hKHm, hKHb, hHAE⟩ := aux_lem_as_regularity_nc_native_residual_finite_bank
    hd M H hIR z j r rho hr hrhop hrho.2 hreq t alpha ht0 ha.le k ps hps KR CR hKR hKRL hKRB hRAE
  by_cases hj : j ≤ 0
  · refine ⟨KH, CH, hKH, hKHm, hKHb, ?_⟩
    filter_upwards [hHAE] with om hom N
    exact hom N (by omega)
  · have hj0 : 0 < j := lt_of_not_ge hj
    let m : ℕ := j.toNat
    have hmj : (m : ℤ) = j := Int.toNat_of_nonneg (by omega)
    have hrm : (3 : ℝ) ^ m * r = rho := by
      rw [hreq, ← zpow_natCast, hmj, ← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp only [add_neg_cancel, zpow_zero, one_mul]
    have hr1 : r ≤ 1 := by
      have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      nlinarith [hrho.2]
    obtain ⟨KS, CS, hKS, hKSm, hKSb, hSAE⟩ := hSbank M Rm H hIR
      (hdelta.trans (min_le_right _ _)) z r hr hr1 m (hrm.le.trans hrho.2)
    refine ⟨fun N om => KH N om + KS N om, fun i => max (CH i) 0 + max (CS i) 0,
      fun N om => add_nonneg (hKH N om) (hKS N om),
      fun i N => (hKHm i N).add (hKSm i N), ?_, ?_⟩
    · intro i N
      have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hps i)
      calc eLpNorm (fun om => KH N om + KS N om) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure
          ≤ eLpNorm (KH N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
            eLpNorm (KS N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
              eLpNorm_add_le hp
        _ ≤ ENNReal.ofReal (max (CH i) 0) + ENNReal.ofReal (max (CS i) 0) :=
          add_le_add ((hKHb i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hKSb i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        _ = ENNReal.ofReal (max (CH i) 0 + max (CS i) 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
    · filter_upwards [hHAE, hSAE] with om hhigh hsmall N
      by_cases hN : j ≤ (N : ℤ)
      · exact aux_lem_as_regularity_nc_estimate_mono
          (le_add_of_nonneg_right (hKS N om)) (hhigh N hN)
      · have hNm : N < m := by omega
        exact aux_lem_as_regularity_nc_estimate_mono
          (le_add_of_nonneg_left (hKH N om)) (hsmall N hNm)


def aux_lem_as_regularity_dc_estimate {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ)
    (a : PositiveCoefficient (centeredCube z r hr)) (K : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf →
    AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf) →
  ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
    ContDiff ℝ 2 phi →
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
  ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
    ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
    SolvesDirichlet a F b u →
    (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
      0 < rad → rad ≤ 1 →
      localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter
            (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
    (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        K * (Kf + Cphi))

theorem aux_lem_as_regularity_dc_estimate_mono {d : ℕ}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {a : PositiveCoefficient (centeredCube z r hr)} {t alpha K L : ℝ}
    (hKL : K ≤ L) (h : aux_lem_as_regularity_dc_estimate z r hr t alpha a K) :
    aux_lem_as_regularity_dc_estimate z r hr t alpha a L := by
  intro F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  obtain ⟨hEn, U, hUc, hUae, hUH, hUn⟩ := h F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hC : 0 ≤ Cphi := (aux_prop_growth_large_root_c2Norm_nonneg' _ _).trans hCphi
  refine ⟨?_, U, hUc, hUae, hUH, hUn.trans (mul_le_mul_of_nonneg_right hKL (add_nonneg hKf hC))⟩
  intro x rad hx hrad hrad1
  exact (hEn x rad hx hrad hrad1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKL (sq_nonneg _)) (Real.rpow_nonneg hrad.le _))

def aux_lem_as_regularity_dc_factor (d : ℕ) (r E t alpha : ℝ) : ℝ :=
  (1 + r ^ (-alpha)) * ((1 + r + r ^ 2) * E) +
    r ^ ((d : ℝ) - 2 - t) * E * ((1 + r + r ^ 2) * E) ^ 2

theorem aux_lem_as_regularity_dc_factor_nonneg (d : ℕ) (r E t alpha : ℝ)
    (hr : 0 < r) (hE : 0 ≤ E) : 0 ≤ aux_lem_as_regularity_dc_factor d r E t alpha := by
  unfold aux_lem_as_regularity_dc_factor
  positivity

/-- Full Dirichlet estimates transport through any positive dilation, including
contractions. Both the source and the smooth boundary datum retain their scaling. -/
theorem aux_lem_as_regularity_dc_transfer {d : ℕ}
    (z z0 : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t alpha K c E : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ alpha) (hK : 0 ≤ K)
    (hc : 0 < c) (hE1 : 1 ≤ E) (hcE : c ≤ E) (hciE : c⁻¹ ≤ E)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a1 a2 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (ha1 : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      a1.val x = a.val (cubeDilation z z0 r x))
    (hcoef : a1 = scalePositiveCoefficient c hc a2)
    (hest : aux_lem_as_regularity_dc_estimate z0 1 one_pos t alpha a2 K) :
    aux_lem_as_regularity_dc_estimate z r hr t alpha a
      (aux_lem_as_regularity_dc_factor d r E t alpha * K) := by
  intro F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hC : 0 ≤ Cphi := (aux_prop_growth_large_root_c2Norm_nonneg' _ _).trans hCphi
  have hX : 0 ≤ Kf + Cphi := add_nonneg hKf hC
  have hE : 0 ≤ E := zero_le_one.trans hE1
  let q : ℝ := (1 + r + r ^ 2) * E
  have hq : 0 ≤ q := by dsimp [q]; positivity
  obtain ⟨F1, phi1, b1, u1, _, hF1m, hF1b, _, hphi1, hCphi1, htrace1, hsol1,
    _, hu1, _, henergy⟩ := aux_prop_growth_large_root_dirichlet_transport z z0 r hr a a1
      ha1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hscale : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      a1.val x = c * a2.val x := by
    rw [hcoef]
    exact scalePositiveCoefficient_coeFn c hc a2
  have hsol2 := aux_prop_growth_large_root_solvesDirichlet_scale a1 a2 c hc hscale
    F1 b1 u1 hsol1
  have hF2b : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      |c⁻¹ * F1 x| ≤ c⁻¹ * (r ^ 2 * Kf) := by
    filter_upwards [hF1b] with x hx
    rw [abs_mul, abs_of_pos (inv_pos.mpr hc)]
    exact mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
  have hCphi1' : c2Norm (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) phi1 ≤
      (1 + r + r ^ 2) * Cphi := hCphi1.choose_spec.1.trans hCphi1.choose_spec.2
  obtain ⟨hEn, U1, hU1c, hU1ae, hU1H, hU1n⟩ := hest (fun x => c⁻¹ * F1 x)
    (c⁻¹ * (r ^ 2 * Kf)) (by positivity) (hF1m.const_mul _) hF2b phi1
    ((1 + r + r ^ 2) * Cphi) hphi1 hCphi1' b1 u1 htrace1 hsol2
  let src : ℝ := c⁻¹ * (r ^ 2 * Kf) + (1 + r + r ^ 2) * Cphi
  have hsrc : 0 ≤ src := by dsimp [src]; positivity
  have hsrcq : src ≤ q * (Kf + Cphi) :=
    aux_prop_growth_large_root_sum_real hr.le hKf hC hciE hE1
  have hHle : (1 + r ^ (-alpha)) * q ≤ aux_lem_as_regularity_dc_factor d r E t alpha :=
    le_add_of_nonneg_right (by positivity)
  have hEle : r ^ ((d : ℝ) - 2 - t) * E * q ^ 2 ≤
      aux_lem_as_regularity_dc_factor d r E t alpha :=
    le_add_of_nonneg_left (by positivity)
  constructor
  · intro x rad hx hrad _
    let x1 := cubeDilation z0 z r⁻¹ x
    have hx1 : x1 ∈ centeredCube z0 1 one_pos :=
      aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube z z0 hr hx
    have hEnq : ∀ y ∈ centeredCube z0 1 one_pos, ∀ s : ℝ, 0 < s → s ≤ 1 →
        localGradientEnergy a2
          (s := Metric.ball y s ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
          (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) ≤
          K * (q * (Kf + Cphi)) ^ 2 * s ^ t := by
      intro y hy s hs hs1
      exact (hEn y s hy hs hs1).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsrc hsrcq 2) hK)
        (Real.rpow_nonneg hs.le _))
    have hEall := aux_lem_as_regularity_nc_energy_all_radii z0 a2
      (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) t
      (K * (q * (Kf + Cphi)) ^ 2) ht (by positivity) hEnq x1 hx1
      (rad / r) (div_pos hrad hr)
    have hEn0 := localGradientEnergy_nonneg a2
      (s := Metric.ball x1 (rad / r) ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
      (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos)))
    have hEn1 := henergy x1 (rad / r) (div_pos hrad hr)
    rw [aux_prop_growth_large_root_localGradientEnergy_scale a1 a2 c hscale] at hEn1
    rw [aux_prop_growth_large_root_cubeDilation_inv_left z z0 hr x,
      mul_div_cancel₀ rad hr.ne'] at hEn1
    have hinv : r ^ ((d : ℝ) - 2) * r ^ ((2 : ℝ) - d) = 1 := by
      rw [← Real.rpow_add hr]
      rw [show (d : ℝ) - 2 + (2 - d) = 0 by ring, Real.rpow_zero]
    have hroot := congrArg (fun a : ℝ => r ^ ((d : ℝ) - 2) * a) hEn1
    calc _ = r ^ ((d : ℝ) - 2) * (c * localGradientEnergy a2
          (s := Metric.ball x1 (rad / r) ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
          (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos)))) := by
            simpa only [← mul_assoc, hinv, one_mul] using hroot.symm
      _ ≤ r ^ ((d : ℝ) - 2) * (E * (K * (q * (Kf + Cphi)) ^ 2 * (rad / r) ^ t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcE hEall hEn0 hE) (Real.rpow_nonneg hr.le _)
      _ = (r ^ ((d : ℝ) - 2 - t) * E * q ^ 2 * K) * (Kf + Cphi) ^ 2 * rad ^ t := by
        rw [Real.div_rpow hrad.le hr.le, Real.rpow_sub hr ((d : ℝ) - 2) t]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEle hK) (sq_nonneg _))
        (Real.rpow_nonneg hrad.le _)
  · have hUn : cAlphaNorm alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U1 ≤
        K * (q * (Kf + Cphi)) := hU1n.trans (mul_le_mul_of_nonneg_left hsrcq hK)
    obtain ⟨hUc, hUH, hUn'⟩ := aux_lem_as_regularity_nc_cAlpha_transport z z0 hr ha
      (show 0 ≤ K * (q * (Kf + Cphi)) by positivity) U1 hU1c hU1H hUn
    refine ⟨fun y => U1 (cubeDilation z0 z r⁻¹ y), hUc,
      aux_lem_as_regularity_nc_representative z z0 hr u u1 U1 hu1 hU1ae, hUH, ?_⟩
    calc _ ≤ (1 + r ^ (-alpha)) * (K * (q * (Kf + Cphi))) := hUn'
      _ = ((1 + r ^ (-alpha)) * q * K) * (Kf + Cphi) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHle hK) hX

theorem aux_lem_as_regularity_dc_reference_upper
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d)
    (N : ℕ) (hmN : m ≤ (N : ℤ)) :
    aux_transport_reference M H N m w om ≤
      Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        Real.exp (H om w + aux_transport_retained m w om) := by
  unfold aux_transport_reference
  exact mul_le_mul_of_nonneg_right (aux_fscc_holNeuH_kappa_ratio_bound M m N hmN).2
    (Real.exp_pos _).le

/-- The unit theorem's envelope premise follows from its first moment.
Higher listed moments decrease to this one on the probability space. -/
theorem aux_lem_as_regularity_dc_cutoff_envelope
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (p C : ℝ) (hp : 1 ≤ p) (_hC : 0 ≤ C) (Kcut : ℕ → BilateralField d → ℝ)
    (hmem : ∀ N, MemLp (Kcut N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hnorm : ∀ N, eLpNorm (Kcut N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal C) (xi : ℝ) (hxi : 0 < xi) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
      ∀ N, |Kcut N om| ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)) := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hm1 := fun N => (hmem N).mono_exponent hpE
  have hn1 : ∀ N, eLpNorm (fun om => ‖Kcut N om‖) 1 (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal C := by
    intro N
    rw [eLpNorm_norm _ (hmem N).aestronglyMeasurable]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hpE).trans (hnorm N)
  simpa only [Real.norm_eq_abs] using aux_lem_as_regularity_envelope
    (chaosSampleLaw M).toMeasure (fun N om => ‖Kcut N om‖) C
      (fun N => (hm1 N).norm) hn1 xi hxi

/-- Common Dirichlet energy and full Hölder estimates on every translated
triadic cube, including contractions and the finite exceptional cutoffs. -/
theorem aux_lem_as_regularity_dc_triadic_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ), r = (3 : ℝ) ^ j →
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        aux_lem_as_regularity_dc_estimate z r hr t alpha
          (cutoffPositiveCoefficient M H om N z hr) K := by
  classical
  obtain ⟨δU, hδU, hU⟩ := lem_as_regularity_unit d hd E P X W D Cp Sf Step Dbase Interp
    alpha ((alpha + 1) / 2) t ((t + d) / 2) ha (by linarith) (by linarith)
      ht (by linarith) (by linarith)
  obtain ⟨δF, hδF, hF⟩ := aux_lem_as_regularity_dirichlet_supply d hd E P X W Cp Sf
    t alpha 1 (fun _ => 1) ht htd ha ha1 (fun _ => le_rfl)
  refine ⟨min 1 (min δU δF), lt_min one_pos (lt_min hδU hδF), ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr j hrj
  have hδ1 : M.delta ≤ 1 := hδ.trans (min_le_left _ _)
  have hδU' : M.delta ≤ δU := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδF' : M.delta ≤ δF := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hunit := hU M Rm Sreg It H hIR (le_min hδ1 hδU')
    (aux_lem_as_regularity_dc_cutoff_envelope M)
  let UnitEst : BilateralField d → ℝ → Prop := fun om B => ∀ N : ℕ,
    aux_lem_as_regularity_dc_estimate (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos t alpha
      (cutoffPositiveCoefficient M H om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) B
  have hchoose : ∀ om : BilateralField d, ∃ B : ℝ, 0 < B ∧
      ((∃ B : ℝ, 0 < B ∧ UnitEst om B) → UnitEst om B) := by
    intro om
    by_cases h : ∃ B : ℝ, 0 < B ∧ UnitEst om B
    · obtain ⟨B, hB, hest⟩ := h
      exact ⟨B, hB, fun _ => hest⟩
    · exact ⟨1, one_pos, fun h' => (h h').elim⟩
  choose B hB hBS using hchoose
  have hBAE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, UnitEst om (B om) := by
    filter_upwards [hunit] with om hom
    obtain ⟨K, hK, hKN⟩ := hom
    exact hBS om ⟨K, hK, fun N => (hKN N).1⟩
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
  let Rp : BilateralField d → ℝ := fun om =>
    Real.exp (((-j).natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
      Real.exp (H om w + aux_transport_retained (-j) w om)
  let Rm' : BilateralField d → ℝ := fun om =>
    Real.exp (((-j).natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
      Real.exp (-(H om w + aux_transport_retained (-j) w om))
  let Re : BilateralField d → ℝ := fun om => 1 + Rp om + Rm' om
  have hRp : ∀ om, 0 ≤ Rp om := fun om => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hRm : ∀ om, 0 ≤ Rm' om := fun om => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hRe : ∀ om, 1 ≤ Re om := fun om => by dsimp only [Re]; linarith [hRp om, hRm om]
  let Kh : BilateralField d → ℝ := fun om =>
    aux_lem_as_regularity_dc_factor d r (Re om) t alpha * B (aux_transport_S (-j) w om)
  have hKh : ∀ om, 0 ≤ Kh om := fun om =>
    mul_nonneg (aux_lem_as_regularity_dc_factor_nonneg d r _ t alpha hr
      (zero_le_one.trans (hRe om))) (hB _).le
  have hTeq (x : SpatialCoordinates d) :
      cubeDilation z z0 r x = w + (3 : ℝ) ^ (-(-j)) • x := by
    funext i
    simp only [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_neg]
    rw [← hrj]
    dsimp [w, z0]
    ring
  have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
  have hhigh : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, -j ≤ (N : ℤ) →
      aux_lem_as_regularity_dc_estimate z r hr t alpha
        (cutoffPositiveCoefficient M H om N z hr) (Kh om) := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro hN
    filter_upwards [aux_fscc_holNeuH_coeff_ident M H hIR (-j) w N hN z0,
      (aux_transport_S_measurePreserving M (-j) w).quasiMeasurePreserving.ae hBAE]
      with om hcoef hunit
    obtain ⟨a1, ha1⟩ := lane4_dilation_coefficient_transport d z z0 r hr one_pos
      (cutoffPositiveCoefficient M H om N z hr)
    have ha1' : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        a1.val x = cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-(-j)) • x) := by
      filter_upwards [ha1, hq.ae (aux_fscc_holNeuH_cutoffPos_val M H om N z hr)] with x hx1 hx2
      rw [hx1, hx2, hTeq]
    have hcE : aux_transport_reference M H N (-j) w om ≤ Re om :=
      (aux_lem_as_regularity_dc_reference_upper M H (-j) w om N hN).trans
        (by dsimp only [Re]; linarith [hRm om])
    have hciE : (aux_transport_reference M H N (-j) w om)⁻¹ ≤ Re om :=
      (aux_lem_as_regularity_nc_reference_uniform M H (-j) w om N hN).trans
        (by dsimp only [Re]; linarith [hRp om])
    exact aux_lem_as_regularity_dc_transfer z z0 r hr t alpha _ _ (Re om) ht0 ha.le
      (hB _).le (aux_transport_reference_pos M H N (-j) w om) (hRe om) hcE hciE
      _ a1 _ ha1 (hcoef a1 ha1') (hunit (((N : ℤ) - (-j)).toNat))
  obtain ⟨KF, CF, _, _, hKF, hFAE⟩ := hF M Rm Sreg It H hIR hδF' z r hr
  filter_upwards [hhigh, hKF, hFAE] with om hhigh hfiniteK hfinite
  let S : ℝ := ∑ N ∈ Finset.range (-j).toNat, KF N om
  have hKF0 : ∀ N, 0 ≤ KF N om := fun N => zero_le_one.trans (hfiniteK N)
  have hS : 0 ≤ S := Finset.sum_nonneg fun N _ => hKF0 N
  refine ⟨1 + Kh om + S, by have := hKh om; positivity, ?_⟩
  intro N
  by_cases hN : -j ≤ (N : ℤ)
  · exact aux_lem_as_regularity_dc_estimate_mono (by linarith) (hhigh N hN)
  · have hNm : N < (-j).toNat := by omega
    have hle : KF N om ≤ S := Finset.single_le_sum (f := fun N => KF N om)
      (fun N _ => hKF0 N) (Finset.mem_range.mpr hNm)
    exact aux_lem_as_regularity_dc_estimate_mono (by linarith [hKh om]) (hfinite N)

/-- A full Hölder estimate gives the exact ball-average bounds required by
the large-radius assembly, also at boundary points of an arbitrary cube. -/
theorem aux_lem_as_regularity_averages_of_holder {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (alpha A : ℝ) (ha : 0 < alpha) (hA : 0 ≤ A)
    (u : DomainL2 (centeredCube z r hr)) (U : SpatialCoordinates d → ℝ)
    (hUc : Continuous U)
    (hUae : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hUH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    (hUn : cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ A)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u| ≤
        (1 + 3 * (Real.sqrt d) ^ alpha) * A) ∧
    (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)), rho ≤ dist x y →
      |setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u -
        setAverage (Metric.ball y rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u| ≤
        (1 + 3 * (Real.sqrt d) ^ alpha) * A * dist x y ^ alpha) := by
  let Cd : ℝ := (Real.sqrt d) ^ alpha
  have hCd : 0 ≤ Cd := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hpair : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |U x - U y| ≤ A * Cd * dist x y ^ alpha := by
    intro x hx y hy
    calc _ ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
        aux_lem_as_regularity_holder_pair alpha A ha _ U hUH hUn x y hx hy
      _ ≤ A * (Real.sqrt d * dist x y) ^ alpha := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.sqrt_nonneg _) (aux_lem_as_regularity_euclid_le_dist x y) ha.le) hA
      _ = A * Cd * dist x y ^ alpha := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg, ← mul_assoc]
  have hclose : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      |setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u -
        U x| ≤ A * Cd * rho ^ alpha := by
    intro x hx
    apply aux_lem_as_regularity_avg_close z hr u U hUc hUae x hx rho hrho
    intro w hw
    exact (hpair w (centeredCube_subset_closedCube z hr hw.2) x hx).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg
        (Metric.mem_ball.mp hw.1).le ha.le) (mul_nonneg hA hCd))
  have hsup : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |U x| ≤ A := by
    intro x hx
    have hbdd := aux_lem_as_regularity_affine_transport_sup_bdd _ (closedCube z r hr).isCompact
      (fun x => |U x|) (continuous_abs.comp hUc)
    have hle := le_csSup hbdd (show |U x| ∈
      {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |U x|} from ⟨x, hx, rfl⟩)
    have hsemi := aux_lem_finite_source_comparison_cells_holderSeminorm_nonneg alpha
      (closedCube z r hr : Set (SpatialCoordinates d)) U
    unfold cAlphaNorm at hUn
    linarith
  have hp1 : rho ^ alpha ≤ 1 := Real.rpow_le_one hrho.le hrho1 ha.le
  constructor
  · intro x hx
    have he := (hclose x hx).trans (mul_le_mul_of_nonneg_left hp1 (mul_nonneg hA hCd))
    have htri := abs_add_le
      (setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u - U x)
      (U x)
    rw [sub_add_cancel] at htri
    have hpos : 0 ≤ A * Cd := mul_nonneg hA hCd
    change _ ≤ (1 + 3 * Cd) * A
    nlinarith [hsup x hx]
  · intro x hx y hy hxy
    have hp : rho ^ alpha ≤ dist x y ^ alpha := Real.rpow_le_rpow hrho.le hxy ha.le
    have hcx := (hclose x hx).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hA hCd))
    have hcy := (hclose y hy).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hA hCd))
    have hxy' := hpair x hx y hy
    have htri := abs_add_three
      (setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u - U x)
      (U x - U y)
      (U y - setAverage (Metric.ball y rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u)
    have hid : (setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u - U x) +
        (U x - U y) +
        (U y - setAverage (Metric.ball y rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u) =
        setAverage (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u -
          setAverage (Metric.ball y rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u := by ring
    rw [hid, abs_sub_comm (U y)] at htri
    have hpos : 0 ≤ A * dist x y ^ alpha := mul_nonneg hA (Real.rpow_nonneg dist_nonneg _)
    change _ ≤ (1 + 3 * Cd) * A * dist x y ^ alpha
    nlinarith

theorem aux_lem_as_regularity_large_radius_dirichlet_triadic
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha t : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
  ∃ theta : ℝ, 0 < theta ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
                ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
                SolvesDirichlet (cutoffPositiveCoefficient M H omega N z hr) F b u →
                (∀ (x : SpatialCoordinates d) (rad : ℝ),
                  x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad → rad ≤ 1 →
                  localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                    (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                    K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
                (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (u : SobolevData (centeredCube z r hr)).1| ≤ K * (Kf + Cphi)) ∧
                (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ dist x y →
                  |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                      (u : SobolevData (centeredCube z r hr)).1 -
                    setAverage (Metric.ball y ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                      (u : SobolevData (centeredCube z r hr)).1| ≤
                    K * (Kf + Cphi) * dist x y ^ alpha) := by
  obtain ⟨δ, hδ, hbank⟩ := aux_lem_as_regularity_dc_triadic_uniform
    d hd E Pc Xc W D Cp Sf Step Dbase Interp t alpha ht1 ht2 hal hal1
  refine ⟨1, one_pos, δ, hδ, ?_⟩
  intro M Rm Sreg It H hIR hdel z r hr htri
  obtain ⟨j, hrj⟩ := htri
  filter_upwards [hbank M Rm Sreg It H hIR (hdel.trans (min_le_right _ _)) z r hr j hrj]
    with om hom
  obtain ⟨K0, hK0, hest⟩ := hom
  let A : ℝ := 1 + 3 * (Real.sqrt d) ^ alpha
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hK : K0 ≤ A * K0 := le_mul_of_one_le_left hK0.le hA
  refine ⟨A * K0, mul_pos (zero_lt_one.trans_le hA) hK0, ?_⟩
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hC : 0 ≤ Cphi := (aux_prop_growth_large_root_c2Norm_nonneg' _ _).trans hCphi
  obtain ⟨hEn, U, hUc, hUae, hUH, hUn⟩ :=
    hest N F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hav := aux_lem_as_regularity_averages_of_holder z r hr alpha (K0 * (Kf + Cphi))
    hal (mul_nonneg hK0.le (add_nonneg hKf hC)) (u : SobolevData (centeredCube z r hr)).1
    U hUc hUae hUH hUn ((3 : ℝ) ^ (-(1 * (N : ℝ))))
    (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num) (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith))
  refine ⟨?_, ?_, ?_⟩
  · intro x rad hx hrad hrad1
    have hrad0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-(1 * (N : ℝ)))).trans_le hrad
    exact (hEn x rad hx hrad0 hrad1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) (Real.rpow_nonneg hrad0.le _))
  · intro x hx
    simpa only [A, mul_assoc] using hav.1 x hx
  · intro x hx y hy hxy
    simpa only [A, mul_assoc] using hav.2 x hx y hy hxy

theorem aux_lem_as_regularity_large_radius_neumann_triadic
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha t : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
  ∃ theta : ℝ, 0 < theta ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
              SolvesNeumann (cutoffPositiveCoefficient M H omega N z hr) F v →
              (∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad → rad ≤ 1 →
                localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
                  K * Kf ^ 2 * rad ^ t) ∧
              (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (v : SobolevData (centeredCube z r hr)).1| ≤ K * Kf) ∧
              (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ dist x y →
                |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (v : SobolevData (centeredCube z r hr)).1 -
                  setAverage (Metric.ball y ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (v : SobolevData (centeredCube z r hr)).1| ≤
                  K * Kf * dist x y ^ alpha) := by
  obtain ⟨δ, hδ, hbank⟩ := aux_lem_as_regularity_nc_triadic_uniform
    d hd E Pc Xc W D Cp Sf Step Dbase Interp t alpha ht1 ht2 hal hal1
  refine ⟨1, one_pos, δ, hδ, ?_⟩
  intro M Rm Sreg It H hIR hdel z r hr htri
  obtain ⟨j, hrj⟩ := htri
  filter_upwards [hbank M Rm Sreg It H hIR (hdel.trans (min_le_right _ _)) z r hr j hrj]
    with om hom
  obtain ⟨K0, hK0, hest⟩ := hom
  let A : ℝ := 1 + 3 * (Real.sqrt d) ^ alpha
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hK : K0 ≤ A * K0 := le_mul_of_one_le_left hK0.le hA
  refine ⟨A * K0, mul_pos (zero_lt_one.trans_le hA) hK0, ?_⟩
  intro N F Kf hKf hFm hFb hFz v hsol
  obtain ⟨⟨U, hUc, hUH, hUae, hUn⟩, hEn⟩ := hest N F Kf hKf hFm hFb hFz v hsol
  have hav := aux_lem_as_regularity_averages_of_holder z r hr alpha (K0 * Kf)
    hal (mul_nonneg hK0.le hKf) (v : SobolevData (centeredCube z r hr)).1 U hUc hUae hUH hUn
    ((3 : ℝ) ^ (-(1 * (N : ℝ)))) (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith))
  refine ⟨?_, ?_, ?_⟩
  · intro x rad hx hrad hrad1
    have hrad0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-(1 * (N : ℝ)))).trans_le hrad
    exact (hEn x rad hx hrad0 hrad1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) (Real.rpow_nonneg hrad0.le _))
  · intro x hx
    simpa only [A, mul_assoc] using hav.1 x hx
  · intro x hx y hy hxy
    simpa only [A, mul_assoc] using hav.2 x hx y hy hxy



theorem aux_lem_as_regularity_neumann_cube
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < d) (hal : 0 < alpha) (hal1 : alpha < 1)
    (hps : ∀ i, 1 ≤ ps i) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
              K N om * Kf ^ 2 * rad ^ t) := by
  obtain ⟨delta0, hdelta0, hAll⟩ := aux_lem_as_regularity_nc_all_cubes
    d hd E Pc Xc W D Cp t alpha k ps ht1 ht2 hal hal1 hps
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  obtain ⟨K, Cbound, _, hmem, hnorm, hAE⟩ :=
    hAll M Rm Sreg It H hIR hdelta z r hr
  exact ⟨K, Cbound, hmem, hnorm, hAE⟩


section
-- Checked source component: NativePrefix.lean
open MeasureTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem aux_lem_as_regularity_potential_ext {d : ℕ}
    (f g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (h : ∀ x, f x = g x) : f = g := by
  have hv : f.val.1 = g.val.1 := ContinuousMap.ext h
  apply Subtype.ext
  apply Prod.ext hv
  apply ContinuousMap.ext
  intro x
  have hf := f.property.1 x
  rw [hv] at hf
  exact hf.unique (g.property.1 x)

/-- The original iteration carrier reads the actual native sample, including
its derivative data; the defining fibre has a unique sample. -/
theorem aux_lem_as_regularity_iteration_score_actual
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {S : in_6_16 d M}
    (It : in_iteration d M E S) (om : BilateralField d)
    (xi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hxi : ∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x)
    (j : ℕ) (z : SpatialCoordinates d) (s : ℝ) :
    It.score j z s om = SubdiffusiveProcess.CoarseGrainingVocab.accumulatedError M none j z s xi := by
  rw [It.score_eq]
  have hset : {v : ℝ | ∃ xi' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      (∀ (i : ℕ) (x : SpatialCoordinates d), xi' i x = om (i : ℤ) x) ∧
      v = SubdiffusiveProcess.CoarseGrainingVocab.accumulatedError M none j z s xi'} =
      {SubdiffusiveProcess.CoarseGrainingVocab.accumulatedError M none j z s xi} := by
    ext v
    constructor
    · rintro ⟨xi', hxi', rfl⟩
      have heq : xi' = xi := by
        funext i
        exact aux_lem_as_regularity_potential_ext (xi' i) (xi i) fun x =>
          (hxi' i x).trans (hxi i x).symm
      simp only [heq, Set.mem_singleton_iff]
    · intro hv
      exact ⟨xi, hxi, Set.mem_singleton_iff.mp hv⟩
  rw [hset, csSup_singleton]

theorem aux_lem_as_regularity_iteration_good_actual
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {S : in_6_16 d M}
    (It : in_iteration d M E S) (om : BilateralField d)
    (xi : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hxi : ∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x)
    (j : ℕ) (z : SpatialCoordinates d) (eps s : ℝ) :
    It.good j z eps s om ↔ xi ∈ SubdiffusiveProcess.CoarseGrainingVocab.goodEvent M none j z eps s := by
  rw [It.good_eq]
  constructor
  · rintro ⟨xi', hxi', hg⟩
    have heq : xi' = xi := by
      funext i
      exact aux_lem_as_regularity_potential_ext (xi' i) (xi i) fun x =>
        (hxi' i x).trans (hxi i x).symm
    rwa [heq] at hg
  · intro hg
    exact ⟨xi, hxi, hg⟩

/-- The three literal inputs consumed by the score-driven folded iteration. -/
def aux_lem_as_regularity_native_prefix_good
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {S : in_6_16 d M}
    (It : in_iteration d M E S) (alpha : ℝ) (L m n : ℕ)
    (z : SpatialCoordinates d) (om : BilateralField d) : Prop :=
  (∑ j ∈ Finset.Icc n m, It.score j z It.s0 om) ≤
    It.C1⁻¹ * (1 - alpha) * ((m : ℝ) - n) ∧
  (((Finset.Icc n m).filter (fun j =>
    ¬ It.good j z (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) It.s0 om)).card : ℝ) <
      1 + It.C1⁻¹ * (1 - alpha) * ((m : ℝ) - n) ∧
  ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
    It.C⁻¹ * Real.exp (-(It.C * (It.C1⁻¹ * (1 - alpha)) * ((m : ℝ) - n))) ≤
        It.ref L j z om / It.ref L (m - 2) z om ∧
      It.ref L j z om / It.ref L (m - 2) z om ≤
        It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - alpha)) * ((m : ℝ) - n))

/-- Finite prefixes fail only if the published stopping witness is too large.
The conclusion involves actual scores and references rather than that witness. -/
theorem aux_lem_as_regularity_native_prefix_tail
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {S : in_6_16 d M}
    (It : in_iteration d M E S) (alpha : ℝ)
    (ha : alpha ∈ It.alphaRange) (hdelta : M.delta ≤ It.C⁻¹)
    (L m n : ℕ) (hmL : m ≤ L) (hnm : n ≤ m) (z : SpatialCoordinates d) :
    (chaosSampleLaw M).toMeasure
      {om | ¬ aux_lem_as_regularity_native_prefix_good It alpha L m n z om} ≤
      ENNReal.ofReal (It.C * Real.exp (-((1 - alpha) ^ 2 *
        max (((m - n : ℕ) : ℝ) - It.C) 0 /
          (It.C * M.delta ^ 2 * |Real.log M.delta|)))) := by
  have hsub : {om | ¬ aux_lem_as_regularity_native_prefix_good It alpha L m n z om} ⊆
      {om | m - n < It.prefixLen z alpha m om} := by
    intro om hbad
    by_contra hlarge
    have hpre : (n : ℤ) ≤ (m : ℤ) - It.prefixLen z alpha m om := by
      simp only [Set.mem_setOf_eq] at hlarge
      omega
    obtain ⟨hs, hc⟩ := It.good_scale_sums z alpha ha hdelta _ _ rfl rfl n m om hpre
    exact hbad ⟨hs, hc, fun j hnj hjm =>
      It.ref_ratio L z alpha ha hdelta _ rfl n m j om hpre hmL hnj hjm⟩
  exact (measure_mono hsub).trans (It.prefix_tail z alpha ha hdelta m (m - n))

/-- The prefix tail in the uniform exponential form used for the limiting
allowances. The rate is fixed first and obtained by reducing disorder. -/
theorem aux_lem_as_regularity_native_prefix_exp_tail
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {S : in_6_16 d M}
    (It : in_iteration d M E S) (alpha A : ℝ)
    (ha : alpha ∈ It.alphaRange) (hdelta : M.delta ≤ It.C⁻¹)
    (hA : 0 ≤ A) (hden : 0 < It.C * M.delta ^ 2 * |Real.log M.delta|)
    (hrate : A * (It.C * M.delta ^ 2 * |Real.log M.delta|) ≤ (1 - alpha) ^ 2)
    (L m n : ℕ) (hmL : m ≤ L) (hnm : n ≤ m) (z : SpatialCoordinates d) :
    (chaosSampleLaw M).toMeasure
      {om | ¬ aux_lem_as_regularity_native_prefix_good It alpha L m n z om} ≤
      ENNReal.ofReal (It.C * Real.exp (A * It.C) * Real.exp (-A * ((m : ℝ) - n))) := by
  apply (aux_lem_as_regularity_native_prefix_tail It alpha ha hdelta L m n hmL hnm z).trans
  apply ENNReal.ofReal_le_ofReal
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ It.C_pos.le
  apply Real.exp_le_exp.mpr
  have hmax : 0 ≤ max (((m - n : ℕ) : ℝ) - It.C) 0 := le_max_right _ _
  have hr := mul_le_mul_of_nonneg_right hrate hmax
  have h1 : A * max (((m - n : ℕ) : ℝ) - It.C) 0 ≤
      (1 - alpha) ^ 2 * max (((m - n : ℕ) : ℝ) - It.C) 0 /
        (It.C * M.delta ^ 2 * |Real.log M.delta|) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hr]
  have h2 := mul_le_mul_of_nonneg_left
    (le_max_left (((m - n : ℕ) : ℝ) - It.C) 0) hA
  rw [Nat.cast_sub hnm] at h1 h2 ⊢
  linarith


end


section
-- Checked source component: IterationNative.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

def aux_lem_as_regularity_it_good (M : GMCModel d) (j : ℕ)
    (z : SpatialCoordinates d) (eps s : ℝ) (om : BilateralField d) : Prop :=
  ∃ xi : PotentialSample d, (∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x) ∧
    xi ∈ goodEvent M none j z eps s

def aux_lem_as_regularity_it_score (M : GMCModel d) (j : ℕ)
    (z : SpatialCoordinates d) (s : ℝ) (om : BilateralField d) : ℝ :=
  sSup {v : ℝ | ∃ xi : PotentialSample d,
    (∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x) ∧
    v = accumulatedError M none j z s xi}

theorem aux_lem_as_regularity_it_score_actual (M : GMCModel d) (j : ℕ)
    (z : SpatialCoordinates d) (s : ℝ) (om : BilateralField d) (xi : PotentialSample d)
    (hxi : ∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x) :
    aux_lem_as_regularity_it_score M j z s om = accumulatedError M none j z s xi := by
  have hs : {v : ℝ | ∃ xi' : PotentialSample d,
      (∀ (i : ℕ) (x : SpatialCoordinates d), xi' i x = om (i : ℤ) x) ∧
      v = accumulatedError M none j z s xi'} = {accumulatedError M none j z s xi} := by
    ext v
    constructor
    · rintro ⟨xi', hxi', rfl⟩
      have heq : xi' = xi := by
        funext i
        exact aux_lem_as_regularity_potential_ext (xi' i) (xi i) fun x =>
          (hxi' i x).trans (hxi i x).symm
      simp only [heq, Set.mem_singleton_iff]
    · intro hv
      exact ⟨xi, hxi, Set.mem_singleton_iff.mp hv⟩
  unfold aux_lem_as_regularity_it_score
  rw [hs, csSup_singleton]

theorem aux_lem_as_regularity_it_good_actual (M : GMCModel d) (j : ℕ)
    (z : SpatialCoordinates d) (eps s : ℝ) (om : BilateralField d) (xi : PotentialSample d)
    (hxi : ∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x) :
    aux_lem_as_regularity_it_good M j z eps s om ↔ xi ∈ goodEvent M none j z eps s := by
  constructor
  · rintro ⟨xi', hxi', hg⟩
    have heq : xi' = xi := by
      funext i
      exact aux_lem_as_regularity_potential_ext (xi' i) (xi i) fun x =>
        (hxi' i x).trans (hxi i x).symm
    rwa [heq] at hg
  · exact fun hg => ⟨xi, hxi, hg⟩

theorem aux_lem_as_regularity_it_score_nonneg (M : GMCModel d) (j : ℕ)
    (z : SpatialCoordinates d) (s : ℝ) (om : BilateralField d) :
    0 ≤ aux_lem_as_regularity_it_score M j z s om := by
  by_cases hex : ∃ xi : PotentialSample d,
      ∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x
  · obtain ⟨xi, hxi⟩ := hex
    rw [aux_lem_as_regularity_it_score_actual M j z s om xi hxi]
    exact Section6Holder.accumulatedError_nonneg M none s j z xi
  · have hs : {v : ℝ | ∃ xi : PotentialSample d,
        (∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x) ∧
        v = accumulatedError M none j z s xi} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨xi, hxi, _⟩
      exact hex ⟨xi, hxi⟩
    simp [aux_lem_as_regularity_it_score, hs]

def aux_lem_as_regularity_it_prefix (M : GMCModel d) (c1 c2 : ℝ)
    (z : SpatialCoordinates d) (alpha : ℝ) (m : ℕ) (om : BilateralField d) : ℕ :=
  if om ∈ aux_prop_growth_macro_energy_good d then
    Section6Stopping.measurableHolderStoppingScale M alpha
      (Section6Stopping.holderStoppingLambda c1 alpha)
      (Section6Stopping.holderStoppingEpsilon c2 alpha) 21 m
      (translatePotentialSample z (aux_prop_growth_macro_energy_lift om))
  else m + 26

theorem aux_lem_as_regularity_it_prefix_measurable (M : GMCModel d) (c1 c2 : ℝ)
    (z : SpatialCoordinates d) (alpha : ℝ) (m : ℕ) :
    Measurable (aux_lem_as_regularity_it_prefix M c1 c2 z alpha m) := by
  unfold aux_lem_as_regularity_it_prefix
  exact Measurable.ite aux_prop_growth_macro_energy_measurableSet_good
    ((Section6Stopping.measurable_measurableHolderStoppingScale M alpha _ _ 21 m).comp
      ((Section6Covariance.measurable_translatePotentialSample z).comp
        aux_prop_growth_macro_energy_measurable_lift)) measurable_const

theorem aux_lem_as_regularity_it_prefix_lower (M : GMCModel d) (c1 c2 : ℝ)
    (z : SpatialCoordinates d) (alpha : ℝ) (m : ℕ) (om : BilateralField d) :
    26 ≤ aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om := by
  unfold aux_lem_as_regularity_it_prefix
  split_ifs
  · exact Section6HolderInterior.step_add_five_le_measurableHolderStoppingScale M alpha _ _ 21 m _
  · omega

theorem aux_lem_as_regularity_it_prefix_active (M : GMCModel d) (c1 c2 : ℝ)
    (z : SpatialCoordinates d) (alpha : ℝ) (n m : ℕ) (om : BilateralField d)
    (h : (n : ℤ) ≤ (m : ℤ) - aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om) :
    om ∈ aux_prop_growth_macro_energy_good d ∧ n + 26 ≤ m ∧
      (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda c1 alpha)
        (Section6Stopping.holderStoppingEpsilon c2 alpha) 21 m
        (translatePotentialSample z (aux_prop_growth_macro_energy_lift om)) : ℤ) ≤
          (m : ℤ) - n := by
  have h26 := aux_lem_as_regularity_it_prefix_lower M c1 c2 z alpha m om
  have hg : om ∈ aux_prop_growth_macro_energy_good d := by
    by_contra hg
    simp only [aux_lem_as_regularity_it_prefix, if_neg hg, Nat.cast_add, Nat.cast_ofNat] at h
    omega
  refine ⟨hg, by omega, ?_⟩
  simp only [aux_lem_as_regularity_it_prefix, if_pos hg] at h
  omega

theorem aux_lem_as_regularity_it_controls (M : GMCModel d) (c1 c2 : ℝ)
    (z : SpatialCoordinates d) (alpha : ℝ) (n m : ℕ) (om : BilateralField d)
    (h : (n : ℤ) ≤ (m : ℤ) - aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om) :
    (∑ j ∈ Finset.Icc n m, aux_lem_as_regularity_it_score M j z (1 / 32) om) ≤
      c1⁻¹ * (1 - alpha) * ((m : ℝ) - n) ∧
    (((Finset.Icc n m).filter (fun j =>
      ¬ aux_lem_as_regularity_it_good M j z (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
        (1 / 32) om)).card : ℝ) < 1 + c1⁻¹ * (1 - alpha) * ((m : ℝ) - n) := by
  obtain ⟨hg, _, hstop⟩ := aux_lem_as_regularity_it_prefix_active M c1 c2 z alpha n m om h
  let xi := aux_prop_growth_macro_energy_lift om
  have hx : ∀ (i : ℕ) (x : SpatialCoordinates d), xi i x = om (i : ℤ) x :=
    aux_prop_growth_macro_energy_lift_apply_of_good hg
  have hc := Section6Stopping.measurableHolder_stopped_controls_at_parameters
    M c1 c2 alpha 21 m n (translatePotentialSample z xi) hstop 0
      (fun i => ⟨0, by simp⟩) (Section6ExcessDecay.zero_mem_cube d (m : ℤ))
  simp only [Section6Stopping.holderStoppingLambda, Section6Stopping.holderStoppingEpsilon,
    Section6Stopping.holderStoppingS] at hc
  have he : ∀ j, aux_lem_as_regularity_it_score M j z (1 / 32) om =
      accumulatedError M none j 0 (1 / 32) (translatePotentialSample z xi) := by
    intro j
    rw [aux_lem_as_regularity_it_score_actual M j z (1 / 32) om xi hx,
      Section6Holder.accumulatedError_translatePotentialSample]
  have hgood : ∀ j, aux_lem_as_regularity_it_good M j z
      (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (1 / 32) om ↔
      translatePotentialSample z xi ∈ goodEvent M none j 0
        (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (1 / 32) := by
    intro j
    exact (aux_lem_as_regularity_it_good_actual M j z _ _ om xi hx).trans
      (Section6Covariance.mem_goodEvent_iff_translate_zero M none j _ _ z xi)
  refine ⟨by simpa only [he] using hc.1, ?_⟩
  have hcard : (((Finset.Icc n m).filter (fun j =>
      ¬ aux_lem_as_regularity_it_good M j z (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
        (1 / 32) om)).card : ℝ) =
      ∑ j ∈ Finset.Icc n m, (1 - if translatePotentialSample z xi ∈
        goodEvent M none j 0 (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (1 / 32) then 1 else 0) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : aux_lem_as_regularity_it_good M j z
        (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (1 / 32) om
    · simp only [hj, not_true_eq_false, if_false, (hgood j).mp hj, if_true, sub_self]
    · simp only [hj, not_false_eq_true, if_true, (not_congr (hgood j)).mp hj,
        if_false, sub_zero]
  rw [hcard]
  simpa only [Real.sqrt_eq_rpow] using hc.2


end


section
-- Checked source component: IterationParameters.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators

theorem aux_lem_as_regularity_it_c12 {c1 c2 : ℝ} (h1 : 2 ≤ c1) (h12 : c1 ≤ c2) :
    c1 * c2 ^ (-8 : ℝ) ≤ 1 := by
  have h2 : 1 ≤ c2 := by linarith
  have h2pos : 0 < c2 := by linarith
  rw [Real.rpow_neg h2pos.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos h2pos _), one_mul]
  exact h12.trans (le_self_pow₀ h2 (by norm_num : (8 : ℕ) ≠ 0))

theorem aux_lem_as_regularity_it_parameters {delta alpha C c1 c2 : ℝ}
    (hd : 0 < delta) (hdC : delta ≤ C⁻¹) (hC46 : 46 ≤ C)
    (h1 : 2 ≤ c1) (h12 : c1 ≤ c2) (hc1C : c1 ≤ C)
    (ha : alpha ∈ Set.Icc (1 / 2 : ℝ) (1 - C * delta * Real.sqrt |Real.log delta|)) :
    0 ≤ c1⁻¹ * (1 - alpha) ∧ c1⁻¹ * (1 - alpha) < 1 ∧
    0 ≤ c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) ∧
    delta ^ 2 ≤ c1⁻¹ * (1 - alpha) ∧
    (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) ^ 8 ≤ c1⁻¹ * (1 - alpha) := by
  have hC : 0 < C := by linarith
  have hc1 : 0 < c1 := by linarith
  have hc2 : 0 < c2 := by linarith
  have hd46 : delta ≤ 1 / 46 := by
    exact hdC.trans ((inv_anti₀ (by norm_num) hC46).trans_eq (by norm_num))
  have hd1 : delta ≤ 1 := by linarith
  have hs := aux_prop_folded_iteration_sqrt_log_ge_one hd hd46
  have hCd : C * delta ≤ 1 - alpha := by
    have hp := le_mul_of_one_le_right (mul_nonneg hC.le hd.le) hs
    linarith [ha.2]
  have hx : 0 ≤ 1 - alpha := (mul_nonneg hC.le hd.le).trans hCd
  have hx1 : 1 - alpha ≤ 1 := by linarith [ha.1]
  have hxi : c1⁻¹ * (1 - alpha) ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hc1]
    nlinarith [ha.1]
  refine ⟨mul_nonneg (inv_nonneg.mpr hc1.le) hx, lt_of_le_of_lt hxi (by norm_num),
    by positivity, ?_, ?_⟩
  · rw [le_inv_mul_iff₀ hc1]
    calc c1 * delta ^ 2 ≤ C * delta := by
          have hsq : delta ^ 2 ≤ delta := by nlinarith
          exact (mul_le_mul_of_nonneg_left hsq hc1.le).trans
            (mul_le_mul_of_nonneg_right hc1C hd.le)
      _ ≤ _ := hCd
  · rw [← Real.sqrt_eq_rpow]
    exact aux_prop_folded_iteration_eps8_le hc1 hc2
      (aux_lem_as_regularity_it_c12 h1 h12) hx hx1

theorem aux_lem_as_regularity_it_ratio_rate (d : ℕ) (hd : 2 ≤ d) (C : ℝ)
    (h46 : 46 ≤ C) (hdim : ((d : ℝ) + 1) ^ 2 ≤ C) :
    Section6HolderInterior.ratioRate d ≤ C := by
  have hp : ((3 : ℝ) ^ (-(Section6Stopping.holderStoppingS / 8)))⁻¹ ≤ 3 := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), neg_neg]
    calc (3 : ℝ) ^ (Section6Stopping.holderStoppingS / 8) ≤ (3 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          norm_num [Section6Stopping.holderStoppingS]
      _ = 3 := Real.rpow_one _
  unfold Section6HolderInterior.ratioRate
  by_cases heq : d = 2
  · subst d
    norm_num at hdim ⊢
    linarith
  · have hd3 : 3 ≤ d := by omega
    have hd3r : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    nlinarith


end


section
-- Checked source component: IterationTail.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem aux_lem_as_regularity_it_prefix_tail
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (c1 c2 Ct C : ℝ) (hCt : 0 < Ct) (hCtC : Ct ≤ C) (hC1 : 1 ≤ C)
    (htail : Section6HolderInterior.UncutGammaOneTailAt d Ct c1 c2 21)
    (z : SpatialCoordinates d) (alpha : ℝ)
    (ha : alpha ∈ Set.Icc (1 / 2 : ℝ) (1 - C * M.delta * Real.sqrt |Real.log M.delta|))
    (hd : M.delta ≤ C⁻¹) (m k : ℕ) :
    (chaosSampleLaw M).toMeasure {om | k < aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om} ≤
      ENNReal.ofReal (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
        (C * M.delta ^ 2 * |Real.log M.delta|)))) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst k
    have hmax : max (((0 : ℕ) : ℝ) - C) 0 = 0 := by
      apply max_eq_right
      norm_num
      linarith
    rw [hmax, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
    exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal hC1)
  have hd' : M.delta ≤ Ct⁻¹ := hd.trans (inv_anti₀ hCt hCtC)
  have ha' : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - Ct * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) := by
    refine ⟨ha.1, ha.2.trans ?_⟩
    rw [← Real.sqrt_eq_rpow]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCtC M.shellPrefix.delta_pos.le)
      (Real.sqrt_nonneg |Real.log M.delta|)
    linarith
  let X := Section6Stopping.measurableHolderStoppingScale M alpha
    (Section6Stopping.holderStoppingLambda c1 alpha)
    (Section6Stopping.holderStoppingEpsilon c2 alpha) 21 m
  let T := fun om : BilateralField d =>
    translatePotentialSample z (aux_prop_growth_macro_energy_lift om)
  have hmp : MeasurePreserving T (chaosSampleLaw M).toMeasure M.P.toMeasure :=
    (Section6Covariance.measurePreserving_translatePotentialSample M z).comp
      (aux_prop_growth_macro_energy_measurePreserving_lift M)
  have hXm : MeasurableSet {xi : PotentialSample d | k < X xi} :=
    measurableSet_lt measurable_const
      (Section6Stopping.measurable_measurableHolderStoppingScale M alpha _ _ 21 m)
  have heq : {om | k < aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om}
      =ᵐ[(chaosSampleLaw M).toMeasure] T ⁻¹' {xi | k < X xi} := by
    filter_upwards [aux_prop_growth_macro_energy_ae_good M] with om hom
    apply propext
    change (k < aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om) ↔ k < X (T om)
    simp only [Set.mem_setOf_eq, Set.mem_preimage, aux_lem_as_regularity_it_prefix,
      if_pos hom, T, X]
  calc (chaosSampleLaw M).toMeasure {om | k < aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om}
      = (chaosSampleLaw M).toMeasure (T ⁻¹' {xi | k < X xi}) := measure_congr heq
    _ = M.P.toMeasure {xi | k < X xi} := hmp.measure_preimage hXm.nullMeasurableSet
    _ ≤ ENNReal.ofReal (Section6HolderInterior.gammaOneRHS M Ct alpha k) :=
      htail M hd' alpha ha' m k hk
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (aux_prop_growth_macro_energy_tail_const_mono hCt hCtC
        (sq_nonneg _) (sq_nonneg _) (abs_nonneg _))


end


section
-- Checked source component: IterationError.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lem_as_regularity_it_error_eq (M : GMCModel d) (E : in_J d)
    (L j : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ (j + 2))
    (om : BilateralField d) (hom : om ∈ aux_prop_growth_macro_energy_good d) :
    E.err z ((3 : ℝ) ^ (j + 2)) hR
        ((aux_prop_growth_macro_energy_nativeSreg M).cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hR)
        z ((3 : ℝ) ^ (j + 2))
        ((aux_prop_growth_macro_energy_nativeSreg M).refAvg L (j + 2) z om) (1 / 32) 2 =
      section6HomogenizationError M (1 / 32) L (j + 2)
        (aux_prop_growth_macro_energy_lift om) z := by
  let xi := translatePotentialSample z (aux_prop_growth_macro_energy_lift om)
  have hc := aux_prop_growth_macro_energy_aCutoff_ae M L hom (j + 2) z hR
  have he := aux_in_deterministic_core_err_scaled E z ((3 : ℝ) ^ (j + 2)) hR
    ((j + 2 : ℕ) : ℤ)
    ((aux_prop_growth_macro_energy_nativeSreg M).cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hR)
    (aCutoff M L xi) 0
  have hz : (fun y : SpatialCoordinates d => aCutoff M L xi (y + 0)) = aCutoff M L xi := by
    funext y
    rw [add_zero]
  rw [hz] at he
  have hc' : ∀ᵐ y ∂volume.restrict
      (Homogenization.openCubeSet (Homogenization.originCube d ((j + 2 : ℕ) : ℤ))),
      aCutoff M L xi y =
        ((aux_prop_growth_macro_energy_nativeSreg M).cutoffOn L om z
          ((3 : ℝ) ^ (j + 2)) hR).val
          (fun i => z i + (3 : ℝ) ^ (j + 2) * ((3 : ℝ) ^ ((j + 2 : ℕ) : ℤ))⁻¹ * y i) := by
    filter_upwards [hc] with y hy
    simpa only [zpow_natCast, mul_inv_cancel₀ (ne_of_gt hR), one_mul,
      aux_prop_growth_macro_energy_nativeSreg, Pi.add_apply, add_comm, xi] using! hy
  have href : (aux_prop_growth_macro_energy_nativeSreg M).refAvg L (j + 2) z om =
      tailCoefficientCubeAverage M L (j + 2) xi := by
    rw [Section6HolderInterior.tailCoefficientCubeAverage_eq_tailAverage_cube,
      aux_prop_growth_macro_energy_tailAverage_eq M L (j + 2) hom z]
    rfl
  exact (he (by simpa only [add_zero] using hc') (aCutoffTriadicData M L xi)
    ((aux_prop_growth_macro_energy_nativeSreg M).refAvg L (j + 2) z om)
    ((aux_prop_growth_macro_energy_nativeSreg M).refAvg_pos L (j + 2) z om)
    (1 / 32) (by norm_num)).1.trans (by
      rw [href]
      rfl)

theorem aux_lem_as_regularity_it_good_error (M : GMCModel d) (E : in_J d)
    (Ce C : ℝ) (hCeC : Ce ≤ C)
    (hCe : ∀ (M : GMCModel d) (s : ℝ), s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) →
      ∀ L m : ℕ, m ≤ L → ∀ (xi : PotentialSample d) (z : SpatialCoordinates d)
        (eps : ℝ), eps ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1 →
      xi ∈ goodEvent M (some L) m z eps s →
        section6HomogenizationError M s L m xi z ≤
          Ce * min eps (s⁻¹ * M.delta ^ 2 + eps ^ 8 + accumulatedError M (some L) m z s xi))
    (L j : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ (j + 2))
    (eps : ℝ) (om : BilateralField d)
    (hd : 64 * M.delta ^ 2 ≤ (1 / 32 : ℝ)) (_hs : (1 / 32 : ℝ) ≤ 1 / 2)
    (hep : (1 / 32 : ℝ)⁻¹ * M.delta ^ 2 ≤ eps) (hep1 : eps ≤ 1)
    (hg : aux_lem_as_regularity_it_good M (j + 2) z eps (1 / 32) om)
    (hjL : j + 2 ≤ L) :
    E.err z ((3 : ℝ) ^ (j + 2)) hR
        ((aux_prop_growth_macro_energy_nativeSreg M).cutoffOn L om z ((3 : ℝ) ^ (j + 2)) hR)
        z ((3 : ℝ) ^ (j + 2))
        ((aux_prop_growth_macro_energy_nativeSreg M).refAvg L (j + 2) z om) (1 / 32) 2 ≤
      C * min eps ((1 / 32 : ℝ)⁻¹ * M.delta ^ 2 + eps ^ 8 +
        aux_lem_as_regularity_it_score M (j + 2) z (1 / 32) om) := by
  obtain ⟨xi, hxi, hgood⟩ := hg
  have hom : om ∈ aux_prop_growth_macro_energy_good d := by
    intro i
    exact ⟨xi i, ContinuousMap.ext (hxi i)⟩
  have heq : xi = aux_prop_growth_macro_energy_lift om := by
    funext i
    exact aux_lem_as_regularity_potential_ext (xi i) _ fun x =>
      (hxi i x).trans (aux_prop_growth_macro_energy_lift_apply_of_good hom i x).symm
  rw [aux_lem_as_regularity_it_error_eq M E L j z hR om hom, ← heq,
    aux_lem_as_regularity_it_score_actual M (j + 2) z (1 / 32) om xi hxi]
  have hg' := (Section6Cutoff.mem_goodEvent_some_iff_none_of_scale_le_cutoff
    M hjL z eps (1 / 32) xi).mpr hgood
  have hb := hCe M (1 / 32) ⟨hd, by norm_num⟩ L (j + 2) hjL xi z eps ⟨hep, hep1⟩ hg'
  rw [Section6Cutoff.accumulatedError_some_eq_none_of_scale_le_cutoff M hjL] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hCeC (le_min
    ((by positivity : 0 ≤ (1 / 32 : ℝ)⁻¹ * M.delta ^ 2).trans hep)
    (by have := Section6Holder.accumulatedError_nonneg M none (1 / 32) (j + 2) z xi
        positivity)))


end


section
-- Checked source component: IterationRatio.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem aux_lem_as_regularity_it_ref_ratio
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (C c1 c2 : ℝ) (hC46 : 46 ≤ C)
    (h1 : 2 ≤ c1) (h12 : c1 ≤ c2) (hc1C : c1 ≤ C)
    (hrate : Section6HolderInterior.ratioRate d ≤ C)
    (L : ℕ) (z : SpatialCoordinates d) (alpha : ℝ)
    (ha : alpha ∈ Set.Icc (1 / 2 : ℝ) (1 - C * M.delta * Real.sqrt |Real.log M.delta|))
    (hd : M.delta ≤ C⁻¹) (n m j : ℕ) (om : BilateralField d)
    (hpre : (n : ℤ) ≤ (m : ℤ) - aux_lem_as_regularity_it_prefix M c1 c2 z alpha m om)
    (hmL : m ≤ L) (hnj : n ≤ j) (hjm : j + 5 ≤ m) :
    C⁻¹ * Real.exp (-(C * (c1⁻¹ * (1 - alpha)) * ((m : ℝ) - n))) ≤
      aux_prop_growth_macro_energy_refAvg M L (j + 2) z om /
        aux_prop_growth_macro_energy_refAvg M L ((m - 2) + 2) z om ∧
    aux_prop_growth_macro_energy_refAvg M L (j + 2) z om /
        aux_prop_growth_macro_energy_refAvg M L ((m - 2) + 2) z om ≤
      C * Real.exp (C * (c1⁻¹ * (1 - alpha)) * ((m : ℝ) - n)) := by
  obtain ⟨hg, hnm, hstop⟩ := aux_lem_as_regularity_it_prefix_active M c1 c2 z alpha n m om hpre
  obtain ⟨hlam, hlam1, heps, hdel, _⟩ := aux_lem_as_regularity_it_parameters
    M.shellPrefix.delta_pos hd hC46 h1 h12 hc1C ha
  let xi := translatePotentialSample z (aux_prop_growth_macro_energy_lift om)
  have h0 : (0 : SpatialCoordinates d) ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.zero_mem_cube d (m : ℤ)
  have h0grid : OnTriadicGrid n (0 : SpatialCoordinates d) := fun i => ⟨0, by simp⟩
  have hforward := Section6HolderInterior.stoppedRatio_row_forward M c1 c2 alpha 21 m n j L xi
    (by omega) hmL hjm hlam hlam1 (by simpa only [Section6Stopping.holderStoppingEpsilon,
      Real.sqrt_eq_rpow] using heps) hdel 0 h0 hstop h0grid j (Finset.mem_Icc.mpr ⟨hnj, le_rfl⟩)
  have hback := Section6HolderInterior.stoppedRatio_row M c1 c2 alpha 21 m n j L xi
    (by omega) hmL hjm hlam hlam1 (by simpa only [Section6Stopping.holderStoppingEpsilon,
      Real.sqrt_eq_rpow] using heps) hdel 0 h0 hstop h0grid j (Finset.mem_Icc.mpr ⟨hnj, le_rfl⟩)
  have hcube : translatedCube d ((j + 2 : ℕ) : ℤ) (0 : SpatialCoordinates d) =
      cube d ((j + 2 : ℕ) : ℤ) := by
    ext x
    simp [translatedCube]
  rw [hcube, Section6HolderInterior.tailCoefficientCubeAverage_eq_tailAverage_cube,
    aux_prop_growth_macro_energy_tailAverage_eq M L (j + 2) hg z,
    aux_prop_growth_macro_energy_tailAverage_eq M L m hg z] at hforward hback
  rw [Nat.sub_add_cancel (by omega : 2 ≤ m)]
  have hgap : 0 ≤ (m : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast (show n ≤ m by omega))
  have hexp : Real.exp (Section6HolderInterior.ratioRate d * (c1⁻¹ * (1 - alpha)) *
      ((m : ℝ) - n)) ≤ Real.exp (C * (c1⁻¹ * (1 - alpha)) * ((m : ℝ) - n)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrate hlam) hgap
  have htop := hforward.trans hexp
  have hbot := hback.trans hexp
  have hA := aux_prop_growth_macro_energy_refAvg_pos M L (j + 2) z om
  have hB := aux_prop_growth_macro_energy_refAvg_pos M L m z om
  have hC : 1 ≤ C := by linarith
  have hi := inv_anti₀ (div_pos hB hA) hbot
  rw [inv_div, ← Real.exp_neg] at hi
  refine ⟨le_trans ?_ hi, htop.trans ?_⟩
  · exact mul_le_of_le_one_left (Real.exp_pos _).le (inv_le_one_of_one_le₀ hC)
  · exact le_mul_of_one_le_left (Real.exp_pos _).le hC


end


section
-- Checked source component: IterationSums.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem aux_lem_as_regularity_it_bad_count (good : ℕ → Prop) (n m k : ℕ) :
    ((Finset.Icc n m).filter (fun j => j + 2 ≤ m ∧ (j < n + k ∨ ¬ good (j + 2)))).card ≤
      k + ((Finset.Icc n m).filter (fun j => ¬ good j)).card := by
  let lo := (Finset.Icc n m).filter (fun j => j < n + k)
  let fail := (Finset.Icc n m).filter (fun j => j + 2 ≤ m ∧ ¬ good (j + 2))
  have hsub : (Finset.Icc n m).filter (fun j => j + 2 ≤ m ∧ (j < n + k ∨ ¬ good (j + 2))) ⊆
      lo ∪ fail := by
    intro j hj
    obtain ⟨hj, hj2, hjlow | hjbad⟩ := Finset.mem_filter.mp hj
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, hjlow⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, hj2, hjbad⟩)
  have hlo : lo.card ≤ k := by
    have hs : lo ⊆ Finset.Ico n (n + k) := by
      intro j hj
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1,
        (Finset.mem_filter.mp hj).2⟩
    simpa using Finset.card_le_card hs
  have hfail : fail.card ≤ ((Finset.Icc n m).filter (fun j => ¬ good j)).card := by
    have hs : fail.image (· + 2) ⊆ (Finset.Icc n m).filter (fun j => ¬ good j) := by
      rintro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hj, hj2, hjbad⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by have := (Finset.mem_Icc.mp hj).1; omega, hj2⟩, hjbad⟩
    have hcard := Finset.card_le_card hs
    rwa [Finset.card_image_of_injective _ (add_left_injective 2)] at hcard
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (add_le_add hlo hfail))

theorem aux_lem_as_regularity_it_sum_bounds (n m : ℕ) (hnm : n + 2 ≤ m)
    (K b eps lam : ℝ) (hK : 0 ≤ K) (hb : 0 ≤ b) (hb2 : b ≤ 2 * lam)
    (good : ℕ → Prop) (score : ℕ → ℝ) (hs0 : ∀ j, 0 ≤ score j)
    (hscore : (∑ j ∈ Finset.Icc n m, score j) ≤ lam * ((m : ℝ) - n)) :
    (∑ j ∈ (Finset.Icc n m).filter (fun j => j + 2 ≤ m),
      K * min eps (b + score (j + 2)) * (if good (j + 2) then 1 else 0)) ≤
      K * (b * ((m : ℝ) - n) +
        ∑ j ∈ (Finset.Icc n m).filter (fun j => j + 2 ≤ m), score (j + 2)) ∧
    K * (b * ((m : ℝ) - n) +
        ∑ j ∈ (Finset.Icc n m).filter (fun j => j + 2 ≤ m), score (j + 2)) ≤
      3 * K * lam * ((m : ℝ) - n) := by
  let I := (Finset.Icc n m).filter (fun j => j + 2 ≤ m)
  have hI : I = Finset.Icc n (m - 2) := by
    ext j
    simp only [I, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hcard : (I.card : ℝ) ≤ (m : ℝ) - n := by
    rw [hI, Nat.card_Icc]
    have hh : m - 2 + 1 - n ≤ m - n := by omega
    have hh' : ((m - 2 + 1 - n : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : n ≤ m)] using hh'
  have hsub : I.image (· + 2) ⊆ Finset.Icc n m := by
    rintro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hj, hj2⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hj).1; omega, hj2⟩
  have hs : (∑ j ∈ I, score (j + 2)) ≤ lam * ((m : ℝ) - n) := by
    rw [← Finset.sum_image (f := score) (g := (· + 2)) (fun a _ b _ h => by
      dsimp only at h
      omega)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hs0 j)).trans hscore
  have hg : 0 ≤ (m : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast (show n ≤ m by omega))
  constructor
  · calc (∑ j ∈ I, K * min eps (b + score (j + 2)) * (if good (j + 2) then 1 else 0))
        ≤ ∑ j ∈ I, K * (b + score (j + 2)) := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs
          · simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_right eps _) hK
          · simpa only [mul_zero] using mul_nonneg hK (add_nonneg hb (hs0 _))
      _ = K * (b * (I.card : ℝ) + ∑ j ∈ I, score (j + 2)) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hcard hb) le_rfl) hK
  · have hbase := mul_le_mul_of_nonneg_right hb2 hg
    have hinner : b * ((m : ℝ) - n) + ∑ j ∈ I, score (j + 2) ≤
        3 * lam * ((m : ℝ) - n) := by linarith
    have hh := mul_le_mul_of_nonneg_left hinner hK
    nlinarith only [hh]


end


section
-- Checked source component: IterationConstants.lean
open MeasureTheory Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab

def aux_lem_as_regularity_it_rows (d : ℕ) [NeZero d] :=
  Section6HolderInterior.exists_interiorRowsAboveCutoff d
    (Section6ExcessDecayInterior.interiorHolderExcessDecayInput_of_interiorHarmonic
      d (fun [NeZero d] => SubdiffusiveProcess.Frozen.Section6.harmonic_approximation_good_scales_interior d))

def aux_lem_as_regularity_it_c1 (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (aux_lem_as_regularity_it_rows d)
def aux_lem_as_regularity_it_c2 (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (Classical.choose_spec (aux_lem_as_regularity_it_rows d))
def aux_lem_as_regularity_it_cmin (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (aux_lem_as_regularity_it_rows d)))

theorem aux_lem_as_regularity_it_c1_two (d : ℕ) [NeZero d] :
    2 ≤ aux_lem_as_regularity_it_c1 d :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (aux_lem_as_regularity_it_rows d)))).1
theorem aux_lem_as_regularity_it_c1_le_c2 (d : ℕ) [NeZero d] :
    aux_lem_as_regularity_it_c1 d ≤ aux_lem_as_regularity_it_c2 d :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (aux_lem_as_regularity_it_rows d)))).2.1
theorem aux_lem_as_regularity_it_c1_one (d : ℕ) [NeZero d] :
    1 ≤ aux_lem_as_regularity_it_c1 d :=
  le_trans (by norm_num) (aux_lem_as_regularity_it_c1_two d)
theorem aux_lem_as_regularity_it_c2_one (d : ℕ) [NeZero d] :
    1 ≤ aux_lem_as_regularity_it_c2 d :=
  (aux_lem_as_regularity_it_c1_one d).trans (aux_lem_as_regularity_it_c1_le_c2 d)

def aux_lem_as_regularity_it_c0 (d : ℕ) [NeZero d] : ℝ :=
  max (max 46 (aux_lem_as_regularity_it_c1 d))
    (max (1024 * aux_lem_as_regularity_it_c2 d ^ 2) (aux_lem_as_regularity_it_cmin d))
def aux_lem_as_regularity_it_ct (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (Section6HolderInterior.exists_uncutGammaOneTail d 21
    (aux_lem_as_regularity_it_c1_one d) (aux_lem_as_regularity_it_c2_one d))
def aux_lem_as_regularity_it_ce (d : ℕ) : ℝ :=
  Classical.choose
    (Section6Cutoff.exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d)
def aux_lem_as_regularity_it_c (d : ℕ) [NeZero d] : ℝ :=
  max (aux_prop_growth_macro_energy_C d)
    (max (aux_lem_as_regularity_it_c0 d)
      (max (aux_lem_as_regularity_it_ct d) (aux_lem_as_regularity_it_ce d)))

theorem aux_lem_as_regularity_it_ct_spec (d : ℕ) [NeZero d] :
    0 < aux_lem_as_regularity_it_ct d ∧
      Section6HolderInterior.UncutGammaOneTailAt d (aux_lem_as_regularity_it_ct d)
        (aux_lem_as_regularity_it_c1 d) (aux_lem_as_regularity_it_c2 d) 21 :=
  Classical.choose_spec (Section6HolderInterior.exists_uncutGammaOneTail d 21
    (aux_lem_as_regularity_it_c1_one d) (aux_lem_as_regularity_it_c2_one d))

theorem aux_lem_as_regularity_it_c0_46 (d : ℕ) [NeZero d] :
    46 ≤ aux_lem_as_regularity_it_c0 d := (le_max_left _ _).trans (le_max_left _ _)
theorem aux_lem_as_regularity_it_c0_le (d : ℕ) [NeZero d] :
    aux_lem_as_regularity_it_c0 d ≤ aux_lem_as_regularity_it_c d :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem aux_lem_as_regularity_it_c_46 (d : ℕ) [NeZero d] :
    46 ≤ aux_lem_as_regularity_it_c d :=
  (aux_lem_as_regularity_it_c0_46 d).trans (aux_lem_as_regularity_it_c0_le d)
theorem aux_lem_as_regularity_it_c1_le (d : ℕ) [NeZero d] :
    aux_lem_as_regularity_it_c1 d ≤ aux_lem_as_regularity_it_c d :=
  ((le_max_right _ _).trans (le_max_left _ _)).trans (aux_lem_as_regularity_it_c0_le d)
theorem aux_lem_as_regularity_it_ct_le (d : ℕ) [NeZero d] :
    aux_lem_as_regularity_it_ct d ≤ aux_lem_as_regularity_it_c d :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
theorem aux_lem_as_regularity_it_ce_le (d : ℕ) [NeZero d] :
    aux_lem_as_regularity_it_ce d ≤ aux_lem_as_regularity_it_c d :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem aux_lem_as_regularity_it_c_dim (d : ℕ) [NeZero d] :
    ((d : ℝ) + 1) ^ 2 ≤ aux_lem_as_regularity_it_c d := by
  apply le_trans ?_ (le_max_left _ _)
  unfold aux_prop_growth_macro_energy_C
  exact le_mul_of_one_le_right (sq_nonneg _) (le_max_left _ _)


end


section
-- Checked source component: IterationFactory.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- The published native stopping-scale estimates, as the exact original-field
iteration carrier. This is a constructed witness, including its pinned constants. -/
def aux_lem_as_regularity_native_iteration
    (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d) (E : in_J d) :
    in_iteration d M E (aux_prop_growth_macro_energy_nativeSreg M) := by
  haveI inst : NeZero d := ⟨by omega⟩
  let c1 := aux_lem_as_regularity_it_c1 d
  let c2 := aux_lem_as_regularity_it_c2 d
  let c0 := aux_lem_as_regularity_it_c0 d
  let Ct := aux_lem_as_regularity_it_ct d
  let Ce := aux_lem_as_regularity_it_ce d
  let C := aux_lem_as_regularity_it_c d
  let S := aux_prop_growth_macro_energy_nativeSreg M
  have hc1 := aux_lem_as_regularity_it_c1_two d
  have hc12 := aux_lem_as_regularity_it_c1_le_c2 d
  have hc046 := aux_lem_as_regularity_it_c0_46 d
  have hC46 := aux_lem_as_regularity_it_c_46 d
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 46) hC46
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC46
  have hc1C := aux_lem_as_regularity_it_c1_le d
  have hCtC := aux_lem_as_regularity_it_ct_le d
  have hCeC := aux_lem_as_regularity_it_ce_le d
  have hCt := aux_lem_as_regularity_it_ct_spec d
  have hCe := Classical.choose_spec
    (Section6Cutoff.exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d)
  have hrate := aux_lem_as_regularity_it_ratio_rate d hd C hC46
    (aux_lem_as_regularity_it_c_dim d)
  refine {
    good := aux_lem_as_regularity_it_good M
    good_eq := fun _ _ _ _ _ => Iff.rfl
    score := aux_lem_as_regularity_it_score M
    score_eq := fun _ _ _ _ => rfl
    score_nonneg := aux_lem_as_regularity_it_score_nonneg M
    ref := fun L j z om => S.refAvg L (j + 2) z om
    ref_pos := fun L j z om => S.refAvg_pos L (j + 2) z om
    ref_eq := fun _ _ _ _ => rfl
    C0 := c0
    C0_pos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 46) hc046
    C0_eq := fun _ => rfl
    C := C
    C_pos := hCpos
    C_eq := fun _ => rfl
    C_ge_one := hC1
    C1 := c1
    C1_pos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hc1
    C1_eq := fun _ => rfl
    C2 := c2
    C2_pos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hc1.trans hc12)
    C2_eq := fun _ => rfl
    C1_C2_le_one := aux_lem_as_regularity_it_c12 hc1 hc12
    k := 21
    k_eq := rfl
    s0 := 1 / 32
    s0_eq := rfl
    theta := (3 : ℝ) ^ (-(1 / 4) : ℝ)
    theta_eq := rfl
    alphaRange := Set.Icc (1 / 2 : ℝ) (1 - C * M.delta * Real.sqrt |Real.log M.delta|)
    alphaRange_eq := rfl
    good_error := ?_
    prefixLen := aux_lem_as_regularity_it_prefix M c1 c2
    prefix_measurable := aux_lem_as_regularity_it_prefix_measurable M c1 c2
    prefix_lower := aux_lem_as_regularity_it_prefix_lower M c1 c2
    prefix_tail := aux_lem_as_regularity_it_prefix_tail M c1 c2 Ct C hCt.1 hCtC hC1 hCt.2
    good_scale_sums := ?_
    badSet := fun z alpha n m om => (Finset.Icc n m).filter (fun j => j + 2 ≤ m ∧
      (j < n + 21 ∨ ¬ aux_lem_as_regularity_it_good M (j + 2) z
        (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (1 / 32) om))
    badSet_eq := fun _ _ _ _ _ => rfl
    bad_count := ?_
    stepError := fun j z eps om => C * (1 / 32 : ℝ) ^ (-(3 / 2 : ℝ)) *
      min eps (M.delta ^ 2 + eps ^ 8 + aux_lem_as_regularity_it_score M (j + 2) z (1 / 32) om) *
      (if aux_lem_as_regularity_it_good M (j + 2) z eps (1 / 32) om then 1 else 0)
    stepError_eq := fun _ _ _ _ => rfl
    Csum := 3 * C * (1 / 32 : ℝ) ^ (-(3 / 2 : ℝ))
    Csum_pos := by positivity
    Csum_eq := rfl
    error_sum := ?_
    ref_ratio := ?_ }
  · exact aux_lem_as_regularity_it_good_error M E Ce C hCeC
      (fun M s hs L m hm xi z eps hep hg => (hCe.2 M s hs L m hm xi z eps hep hg).1)
  · intro z alpha _ _ lam eps hlam heps n m om hpre
    subst lam
    subst eps
    exact aux_lem_as_regularity_it_controls M c1 c2 z alpha n m om hpre
  · intro z alpha _ _ lam hlam n m om hpre
    subst lam
    have hc := (aux_lem_as_regularity_it_controls M c1 c2 z alpha n m om hpre).2
    have hb := aux_lem_as_regularity_it_bad_count
      (fun j => aux_lem_as_regularity_it_good M j z (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
        (1 / 32) om) n m 21
    have hb' : (((Finset.Icc n m).filter (fun j => j + 2 ≤ m ∧
        (j < n + 21 ∨ ¬ aux_lem_as_regularity_it_good M (j + 2) z
          (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (1 / 32) om))).card : ℝ) ≤
      21 + (((Finset.Icc n m).filter (fun j =>
        ¬ aux_lem_as_regularity_it_good M j z (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
          (1 / 32) om)).card : ℝ) := by exact_mod_cast hb
    exact le_of_lt (lt_of_le_of_lt hb' (by linarith))
  · intro z alpha ha hdelta lam eps hlam heps n m om hpre
    subst lam
    subst eps
    obtain ⟨_, _, _, hdel, heps8⟩ := aux_lem_as_regularity_it_parameters
      M.shellPrefix.delta_pos hdelta hC46 hc1 hc12 hc1C ha
    have hnm := (aux_lem_as_regularity_it_prefix_active M c1 c2 z alpha n m om hpre).2.1
    have hs := (aux_lem_as_regularity_it_controls M c1 c2 z alpha n m om hpre).1
    have hbound := aux_lem_as_regularity_it_sum_bounds n m (by omega)
      (C * (1 / 32 : ℝ) ^ (-(3 / 2 : ℝ)))
      (M.delta ^ 2 + (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) ^ 8)
      (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) (c1⁻¹ * (1 - alpha))
      (by positivity) (by positivity) (by linarith)
      (fun j => aux_lem_as_regularity_it_good M j z (c2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
        (1 / 32) om)
      (fun j => aux_lem_as_regularity_it_score M j z (1 / 32) om)
      (fun j => aux_lem_as_regularity_it_score_nonneg M j z (1 / 32) om) hs
    simpa only [mul_assoc] using hbound
  · intro L z alpha ha hdelta lam hlam n m j om hpre hmL hnj hjm
    subst lam
    exact aux_lem_as_regularity_it_ref_ratio M C c1 c2 hC46 hc1 hc12 hc1C hrate
      L z alpha ha hdelta n m j om hpre hmL hnj hjm


end


section
-- Checked source component: NativeResponses.lean
open MeasureTheory Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators

/-- The exact response maximum and the published bounds construct an actual
response carrier for every model, including the boundedly dilated model. -/
theorem aux_lem_as_regularity_nonempty_responses
    (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d) : Nonempty (in_responses d M) := by
  haveI : NeZero d := ⟨by omega⟩
  choose defect hdefect hmax using fun m y om => aux_rbpf_defect_exists M m y om
  obtain ⟨C, hC, hbank⟩ := paper_responses_bank d hd
  have horder : ∀ n m : ℕ, n < m → ahom M m ≤ ahom M n ∧
      ahom M n ≤ Real.exp (2 * tauSq M.P * ((m : ℝ) - n)) * ahom M m := by
    intro n m hnm
    have hb := Section6Cutoff.cutoff_ahom_ratio_ordering M m hnm.le
    rw [min_eq_left hnm.le, min_self] at hb
    constructor
    · have hh := (le_div_iff₀ (ahom_pos M m)).mp hb.1
      simpa only [one_mul] using hh
    · have hh := (div_le_iff₀ (ahom_pos M m)).mp hb.2
      simpa only [Nat.cast_sub hnm.le] using hh
  obtain ⟨Rm, _, _, _⟩ := hbank M horder (ahom_le_one M)
    (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M) defect hdefect hmax
  exact ⟨Rm⟩


end


section
-- Checked source component: ScaleCovariance.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Exact covariance to one genuine GMC model for an arbitrary positive cube.
The two scalar normalizations and their inverses have a common cutoff-independent bound. -/
theorem aux_lem_as_regularity_scale_covariance
    (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIR : InfraredCharacterization M H)
    (hdelta : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ (M' : GMCModel d) (H' : BilateralField d → C(SpatialCoordinates d, ℝ))
      (T : BilateralField d → BilateralField d) (c : ℕ → BilateralField d → ℝ)
      (V : BilateralField d → ℝ) (L : ℕ) (I : ℕ → ℕ),
      ∃ hc : ∀ N om, 0 < c N om,
      M'.delta = ResidualModel.residualDisorderFactor d * M.delta ∧
      InfraredCharacterization M' H' ∧
      MeasurePreserving T (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure ∧
      (∀ om, 1 ≤ V om) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, L ≤ N →
        c N om ≤ V om ∧ (c N om)⁻¹ ≤ V om ∧
        ∀ a1 : PositiveCoefficient (unitNeumannCube d),
          (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
            a1.val x = (cutoffPositiveCoefficient M H om N z hr).val
              (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) →
          a1 = scalePositiveCoefficient (c N om) (hc N om)
            (cutoffPositiveCoefficient M' H' (T om) (I N)
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) := by
  obtain ⟨j, rho, hrho, hreq⟩ := aux_lem_as_regularity_nc_octave_decompose r hr
  have hs1 : 1 ≤ rho * (3 : ℝ) ^ (1 : ℕ) := by norm_num; linarith [hrho.1]
  have hs3 : rho * (3 : ℝ) ^ (1 : ℕ) ≤ 3 := by norm_num; linarith [hrho.2]
  let M' := ResidualModel.residualModel M hs1 hs3 hdelta
  obtain ⟨H', hIR'⟩ := exists_infraredCharacterization hd M'
  let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
  let S := aux_transport_S j w
  let T := fun om : BilateralField d => MacroAllCube.residualShift rho 1 (S om)
  let I := fun N : ℕ => ((N : ℤ) - j).toNat - 1
  let c := fun N om => aux_transport_reference M H N j w om *
    aux_prop_growth_macro_energy_shiftC M M' 1 (I N) (S om)
  let Rp := fun om => Real.exp ((j.natAbs : ℝ) * tauSq M.P) *
    Real.exp (H om w + aux_transport_retained j w om)
  let Rn := fun om => Real.exp ((j.natAbs : ℝ) * tauSq M.P) *
    Real.exp (-(H om w + aux_transport_retained j w om))
  let V := fun om => (1 + Rp om + Rn om) * aux_prop_growth_macro_energy_env M 1 (S om)
  have hRp : ∀ om, 0 ≤ Rp om := fun _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hRn : ∀ om, 0 ≤ Rn om := fun _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hRef : ∀ om, 1 ≤ 1 + Rp om + Rn om := fun om => by linarith [hRp om, hRn om]
  have hV : ∀ om, 1 ≤ V om := fun om =>
    one_le_mul_of_one_le_of_one_le (hRef om) (aux_prop_growth_macro_energy_one_le_env M 1 (S om))
  have hc : ∀ N om, 0 < c N om := fun N om =>
    mul_pos (aux_transport_reference_pos M H N j w om)
      (aux_prop_growth_macro_energy_shiftC_pos M M' 1 (I N) (S om))
  have hS : MeasurePreserving S (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_transport_S_measurePreserving M j w
  have hR : MeasurePreserving (MacroAllCube.residualShift (d := d) rho 1)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure :=
    ResidualModel.measurePreserving_residualModel M rho 1 hs1 hs3 hdelta
  have htau : tauSq M'.P = tauSq M.P := ResidualModel.residualModel_tauSq M hs1 hs3 hdelta
  refine ⟨M', H', T, c, V, (j + 1).toNat, I, hc,
    ResidualModel.residualModel_delta M hs1 hs3 hdelta, hIR', hR.comp hS, hV, ?_⟩
  have hfirst : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, j ≤ (N : ℤ) →
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-j) • x) =
          aux_transport_reference M H N j w om *
            cutoffCoefficient M H (S om) ((N : ℤ) - j).toNat x := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro hN
    exact aux_transport_coefficient M j w hIR N hN
  have hsecond := hS.quasiMeasurePreserving.ae
    (aux_prop_growth_macro_energy_coeff_identity M M' htau H H' hIR hIR' rho 1 hR)
  filter_upwards [hfirst, hsecond] with om hfirst hsecond N hN
  have hjN : j ≤ (N : ℤ) := by omega
  have hI : I N + 1 = ((N : ℤ) - j).toNat := by dsimp [I]; omega
  have hp := aux_lem_as_regularity_dc_reference_upper M H j w om N hjN
  have hn := aux_lem_as_regularity_nc_reference_uniform M H j w om N hjN
  have hshift := aux_prop_growth_macro_energy_shiftC_bounds M hs1 hs3 hdelta 1 (I N) (S om)
  have hp' : aux_transport_reference M H N j w om ≤ 1 + Rp om + Rn om :=
    hp.trans (by linarith [hRn om])
  have hn' : (aux_transport_reference M H N j w om)⁻¹ ≤ 1 + Rp om + Rn om :=
    hn.trans (by linarith [hRp om])
  refine ⟨mul_le_mul hp' hshift.1
    (aux_prop_growth_macro_energy_shiftC_pos M M' 1 (I N) (S om)).le
    (zero_le_one.trans (hRef om)), ?_, ?_⟩
  · dsimp only [c, V]
    rw [mul_inv]
    exact mul_le_mul hn' hshift.2 (inv_pos.mpr
      (aux_prop_growth_macro_energy_shiftC_pos M M' 1 (I N) (S om))).le
        (zero_le_one.trans (hRef om))
  · intro a1 ha1
    have hq := lane4_dilation_quasi_measure_preserving d z
      (fun _ : Fin d => (1 / 2 : ℝ)) r hr one_pos
    have hpoint : ∀ x : SpatialCoordinates d,
        cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x =
          w + (3 : ℝ) ^ (-j) • (rho • x) := by
      intro x
      funext i
      simp only [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp only [w]
      rw [hreq]
      ring
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [ha1, hq.ae (aux_fscc_holNeuH_cutoffPos_val M H om N z hr),
      aux_fscc_holNeuH_cutoffPos_val M' H' (T om) (I N)
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos,
      scalePositiveCoefficient_coeFn (c N om) (hc N om)
        (cutoffPositiveCoefficient M' H' (T om) (I N)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)] with x hx1 hx2 hx3 hx4
    erw [hx1, hx2, hpoint x, hfirst N hjN (rho • x), ← hI, hsecond.2 (I N) x, hx4, hx3]
    exact (mul_assoc _ _ _).symm


end


section
-- Checked source component: UniformNeumann.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Common energy and full Hölder estimates on every positive cube side.
The residual model inputs and both changes of sample law are constructed. -/
theorem aux_lem_as_regularity_nc_all_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M H om N z hr)
          t alpha K := by
  obtain ⟨deltaU, hdU, hU⟩ := aux_lem_as_regularity_unit_uniform_bank
    d hd E P X W D Cp Step Dbase Interp Sf t alpha ht htd ha ha1
  obtain ⟨deltaF, hdF, hF⟩ := aux_lem_as_regularity_nc_all_cubes
    d hd E P X W D Cp t alpha 1 (fun _ => 1) ht htd ha ha1 (fun _ => le_rfl)
  have hRes := ResidualModel.residualDisorderFactor_pos d
  refine ⟨min deltaF (min (deltaU / ResidualModel.residualDisorderFactor d)
    (2 * ResidualModel.residualDisorderFactor d)⁻¹),
    lt_min hdF (lt_min (div_pos hdU hRes) (by positivity)), ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  have hdF' := hdelta.trans (min_le_left _ _)
  have hdU' := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdRes := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨M', H', T, c, V, L, I, hc, hdel', hIR', hT, hV, hcoef⟩ :=
    aux_lem_as_regularity_scale_covariance d hd M H hIR hdRes z r hr
  have hdU'' : M'.delta ≤ deltaU := by
    rw [hdel']
    have hh := (le_div_iff₀ hRes).mp hdU'
    linarith
  let Rm' := Classical.choice (aux_lem_as_regularity_nonempty_responses d hd M')
  have hunit := hU M' Rm' (aux_prop_growth_macro_energy_nativeSreg M')
    (aux_lem_as_regularity_native_iteration d hd M' E) H' hIR' hdU''
  obtain ⟨KF, CF, hKF, _, _, hFAE⟩ := hF M Rm Sreg It H hIR hdF' z r hr
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let A := aux_lem_as_regularity_nc_factor d r t alpha
  have hA : 0 ≤ A := by dsimp [A, aux_lem_as_regularity_nc_factor]; positivity
  filter_upwards [hcoef, hT.quasiMeasurePreserving.ae hunit, hFAE] with om hcoef hunit hfinite
  obtain ⟨B, hB, hbank⟩ := hunit
  let S := ∑ N ∈ Finset.range L, KF N om
  have hS : 0 ≤ S := Finset.sum_nonneg (fun N _ => hKF N om)
  have hV0 : 0 ≤ V om := zero_le_one.trans (hV om)
  have hAB : 0 ≤ A * B := mul_nonneg hA hB.le
  have hABV : 0 ≤ A * B * V om := mul_nonneg hAB hV0
  refine ⟨1 + A * B * V om + S, by positivity, ?_⟩
  intro N
  by_cases hN : L ≤ N
  · obtain ⟨_, hci, hco⟩ := hcoef N hN
    have hest : aux_lem_as_regularity_nc_estimate z r hr
        (cutoffPositiveCoefficient M H om N z hr) t alpha (A * B / c N om) := by
      obtain ⟨a1, ha1, _, hNeumann⟩ := lem_as_regularity_affine_transport d M H om N z r hr
      have hco' := hco a1 ha1
      intro F Kf hKf hFm hFb hFz v hsol
      obtain ⟨F1, v1, _, hF1m, hF1b, hF1z, hsol1, hv1, _, henergy⟩ :=
        hNeumann F Kf hKf hFm hFb hFz v hsol
      exact aux_lem_as_regularity_nc_transfer_data z (fun _ : Fin d => (1 / 2 : ℝ))
        r hr t alpha B (c N om) ht0 ha.le hB.le (hc N om)
        _ a1 _ hco' (hbank (I N)) v v1 F1 Kf hKf hF1m hF1b hF1z hsol1 hv1 henergy
    apply aux_lem_as_regularity_nc_estimate_mono _ hest
    have hh : A * B / c N om ≤ A * B * V om := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hci hAB
    linarith
  · have hNL : N < L := lt_of_not_ge hN
    have hle : KF N om ≤ S := Finset.single_le_sum (f := fun N => KF N om)
      (fun N _ => hKF N om) (Finset.mem_range.mpr hNL)
    exact aux_lem_as_regularity_nc_estimate_mono (by linarith) (hfinite N)


end


section
-- Checked source component: UniformDirichlet.lean
open MeasureTheory Filter Set Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- All-cutoff Dirichlet estimates on every positive cube side, from exact
covariance and actual input witnesses for the residual model. -/
theorem aux_lem_as_regularity_dc_all_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        aux_lem_as_regularity_dc_estimate z r hr t alpha
          (cutoffPositiveCoefficient M H om N z hr) K := by
  obtain ⟨deltaU, hdU, hU⟩ := lem_as_regularity_unit d hd E P X W D Cp Sf Step Dbase Interp
    alpha ((alpha + 1) / 2) t ((t + d) / 2) ha (by linarith) (by linarith)
      ht (by linarith) (by linarith)
  obtain ⟨deltaF, hdF, hF⟩ := aux_lem_as_regularity_dirichlet_supply
    d hd E P X W Cp Sf t alpha 1 (fun _ => 1) ht htd ha ha1 (fun _ => le_rfl)
  have hRes := ResidualModel.residualDisorderFactor_pos d
  refine ⟨min deltaF (min (deltaU / ResidualModel.residualDisorderFactor d)
    (2 * ResidualModel.residualDisorderFactor d)⁻¹),
    lt_min hdF (lt_min (div_pos hdU hRes) (by positivity)), ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  have hdF' := hdelta.trans (min_le_left _ _)
  have hdU' := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdRes := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨M', H', T, c, V, L, I, hc, hdel', hIR', hT, hV, hcoef⟩ :=
    aux_lem_as_regularity_scale_covariance d hd M H hIR hdRes z r hr
  have hdU'' : M'.delta ≤ min 1 deltaU := by
    refine le_min (by linarith [M'.shellPrefix.delta_le_half]) ?_
    rw [hdel']
    have hh := (le_div_iff₀ hRes).mp hdU'
    linarith
  let Rm' := Classical.choice (aux_lem_as_regularity_nonempty_responses d hd M')
  have hunit := hU M' Rm' (aux_prop_growth_macro_energy_nativeSreg M')
    (aux_lem_as_regularity_native_iteration d hd M' E) H' hIR' hdU''
    (aux_lem_as_regularity_dc_cutoff_envelope M')
  obtain ⟨KF, CF, _, _, hKF, hFAE⟩ := hF M Rm Sreg It H hIR hdF' z r hr
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  filter_upwards [hcoef, hT.quasiMeasurePreserving.ae hunit, hKF, hFAE]
    with om hcoef hunit hfiniteK hfinite
  obtain ⟨B, hB, hbank⟩ := hunit
  let A := aux_lem_as_regularity_dc_factor d r (V om) t alpha
  have hA : 0 ≤ A := aux_lem_as_regularity_dc_factor_nonneg d r (V om) t alpha hr
    (zero_le_one.trans (hV om))
  let S := ∑ N ∈ Finset.range L, KF N om
  have hKF0 : ∀ N, 0 ≤ KF N om := fun N => zero_le_one.trans (hfiniteK N)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun N _ => hKF0 N)
  have hAB : 0 ≤ A * B := mul_nonneg hA hB.le
  refine ⟨1 + A * B + S, by positivity, ?_⟩
  intro N
  by_cases hN : L ≤ N
  · obtain ⟨hcV, hciV, hco⟩ := hcoef N hN
    obtain ⟨a1, ha1⟩ := lane4_dilation_coefficient_transport d z
      (fun _ : Fin d => (1 / 2 : ℝ)) r hr one_pos (cutoffPositiveCoefficient M H om N z hr)
    have hest := aux_lem_as_regularity_dc_transfer z (fun _ : Fin d => (1 / 2 : ℝ))
      r hr t alpha B (c N om) (V om) ht0 ha.le hB.le (hc N om) (hV om) hcV hciV
      _ a1 _ ha1 (hco a1 ha1) (hbank (I N)).1
    exact aux_lem_as_regularity_dc_estimate_mono (by linarith) hest
  · have hNL : N < L := lt_of_not_ge hN
    have hle : KF N om ≤ S := Finset.single_le_sum (f := fun N => KF N om)
      (fun N _ => hKF0 N) (Finset.mem_range.mpr hNL)
    exact aux_lem_as_regularity_dc_estimate_mono (by linarith) (hfinite N)


end
/-- **Common large-radius Dirichlet estimates.** Paper 4570–4667:
prefix transfer to the limiting response bank (`prop_as_response_bank`, `lem_band`,
`lem_prefix_limit`), the allowance union bound over the two-mesh constructions of
`rem_resolved` (`B_π ≤ ξ₀ n + B_ω`), `thm_fold` for reflected strata, the reference-mesh
depth loss via the shallow-cell argument of `lem_as_coarse` and `lem_extremes`, and the
deterministic iteration (`in_6_16`, `in_iteration`) "yield a single random constant for the
required oscillation and energy bounds at all radii `r ≥ r_N := 3^{-θN}`" (4666–4667).
The oscillation bound is recorded in the form used at 4681–4682: averages over
`B_{r_N}(x) ∩ Q` are bounded and `α`-Hölder at separations `≥ r_N`. `θ` is chosen after the
exponents and before the disorder threshold, as in 4601–4604. -/
theorem aux_lem_as_regularity_large_radius_dirichlet
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha t : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
  ∃ theta : ℝ, 0 < theta ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
                ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
                SolvesDirichlet (cutoffPositiveCoefficient M H omega N z hr) F b u →
                (∀ (x : SpatialCoordinates d) (rad : ℝ),
                  x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad → rad ≤ 1 →
                  localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                    (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                    K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
                (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (u : SobolevData (centeredCube z r hr)).1| ≤ K * (Kf + Cphi)) ∧
                (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ dist x y →
                  |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                      (u : SobolevData (centeredCube z r hr)).1 -
                    setAverage (Metric.ball y ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                      (u : SobolevData (centeredCube z r hr)).1| ≤
                    K * (Kf + Cphi) * dist x y ^ alpha) := by
  obtain ⟨δ, hδ, hbank⟩ := aux_lem_as_regularity_dc_all_uniform
    d hd E Pc Xc W D Cp Sf Step Dbase Interp t alpha ht1 ht2 hal hal1
  refine ⟨1, one_pos, δ, hδ, ?_⟩
  intro M Rm Sreg It H hIR hdel z r hr
  filter_upwards [hbank M Rm Sreg It H hIR (hdel.trans (min_le_right _ _)) z r hr]
    with om hom
  obtain ⟨K0, hK0, hest⟩ := hom
  let A : ℝ := 1 + 3 * (Real.sqrt d) ^ alpha
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hK : K0 ≤ A * K0 := le_mul_of_one_le_left hK0.le hA
  refine ⟨A * K0, mul_pos (zero_lt_one.trans_le hA) hK0, ?_⟩
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hC : 0 ≤ Cphi := (aux_prop_growth_large_root_c2Norm_nonneg' _ _).trans hCphi
  obtain ⟨hEn, U, hUc, hUae, hUH, hUn⟩ :=
    hest N F Kf hKf hFm hFb phi Cphi hphi hCphi b u htrace hsol
  have hav := aux_lem_as_regularity_averages_of_holder z r hr alpha (K0 * (Kf + Cphi))
    hal (mul_nonneg hK0.le (add_nonneg hKf hC)) (u : SobolevData (centeredCube z r hr)).1
    U hUc hUae hUH hUn ((3 : ℝ) ^ (-(1 * (N : ℝ))))
    (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num) (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith))
  refine ⟨?_, ?_, ?_⟩
  · intro x rad hx hrad hrad1
    have hrad0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-(1 * (N : ℝ)))).trans_le hrad
    exact (hEn x rad hx hrad0 hrad1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) (Real.rpow_nonneg hrad0.le _))
  · intro x hx
    simpa only [A, mul_assoc] using hav.1 x hx
  · intro x hx y hy hxy
    simpa only [A, mul_assoc] using hav.2 x hx y hy hxy

/-- **Common large-radius Neumann estimates.** The Neumann counterpart of
`aux_lem_as_regularity_large_radius_dirichlet` (paper 4570–4667, the estimates of
`cor_neumann_source` at radii `r ≥ r_N := 3^{-θN}`; reflected boundary strata through the
original-grid convolution of `thm_fold`, 4642–4645). -/
theorem aux_lem_as_regularity_large_radius_neumann
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha t : ℝ) (hal : 0 < alpha) (hal1 : alpha < 1)
    (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
  ∃ theta : ℝ, 0 < theta ∧ ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
              SolvesNeumann (cutoffPositiveCoefficient M H omega N z hr) F v →
              (∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad → rad ≤ 1 →
                localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
                  K * Kf ^ 2 * rad ^ t) ∧
              (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (v : SobolevData (centeredCube z r hr)).1| ≤ K * Kf) ∧
              (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ dist x y →
                |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (v : SobolevData (centeredCube z r hr)).1 -
                  setAverage (Metric.ball y ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (v : SobolevData (centeredCube z r hr)).1| ≤
                  K * Kf * dist x y ^ alpha) := by
  obtain ⟨δ, hδ, hbank⟩ := aux_lem_as_regularity_nc_all_uniform
    d hd E Pc Xc W D Cp Sf Step Dbase Interp t alpha ht1 ht2 hal hal1
  refine ⟨1, one_pos, δ, hδ, ?_⟩
  intro M Rm Sreg It H hIR hdel z r hr
  filter_upwards [hbank M Rm Sreg It H hIR (hdel.trans (min_le_right _ _)) z r hr]
    with om hom
  obtain ⟨K0, hK0, hest⟩ := hom
  let A : ℝ := 1 + 3 * (Real.sqrt d) ^ alpha
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  have hK : K0 ≤ A * K0 := le_mul_of_one_le_left hK0.le hA
  refine ⟨A * K0, mul_pos (zero_lt_one.trans_le hA) hK0, ?_⟩
  intro N F Kf hKf hFm hFb hFz v hsol
  obtain ⟨⟨U, hUc, hUH, hUae, hUn⟩, hEn⟩ := hest N F Kf hKf hFm hFb hFz v hsol
  have hav := aux_lem_as_regularity_averages_of_holder z r hr alpha (K0 * Kf)
    hal (mul_nonneg hK0.le hKf) (v : SobolevData (centeredCube z r hr)).1 U hUc hUae hUH hUn
    ((3 : ℝ) ^ (-(1 * (N : ℝ)))) (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith))
  refine ⟨?_, ?_, ?_⟩
  · intro x rad hx hrad hrad1
    have hrad0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-(1 * (N : ℝ)))).trans_le hrad
    exact (hEn x rad hx hrad0 hrad1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (sq_nonneg _)) (Real.rpow_nonneg hrad0.le _))
  · intro x hx
    simpa only [A, mul_assoc] using hav.1 x hx
  · intro x hx y hy hxy
    simpa only [A, mul_assoc] using hav.2 x hx y hy hxy

/-- The scale `r_N = 3^{-θN}` lies in `(0,1]`. -/
theorem aux_lem_as_regularity_rN_bounds (theta : ℝ) (htheta : 0 < theta) (N : ℕ) :
    0 < (3 : ℝ) ^ (-(theta * (N : ℝ))) ∧ (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ 1 :=
  ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.2 (mul_nonneg htheta.le (Nat.cast_nonneg N)))⟩

/-- Assembles the Dirichlet conjunct of `lem_as_regularity`'s per-`(N,omega)` clause from the
small-radius supplier `hG1` (stronger exponents `alpha0,t0`) and the large-radius supplier
`hKD'` (radius `≥ r_N`), combined via `aux_lem_as_regularity_clause`. Split out from the
principal (with `om`, `N` already fixed) purely to keep each declaration's own heartbeat
budget small (paper 4669–4683). -/
theorem aux_lem_as_regularity_dirichlet_branch
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha) (hal0 : alpha < alpha0) (hal1 : alpha0 < 1) (ht0 : t < t0)
    (theta xi KG BG KD Ktot : ℝ)
    (htheta : 0 < theta) (hBG : 0 < BG) (hKD : 0 < KD)
    (hgeKG : 0 ≤ KG)
    (hBGN : KG ≤ BG * (3 : ℝ) ^ (xi * (N : ℝ)))
    (hxi1 : xi ≤ theta * (alpha0 - alpha)) (hxi2 : xi ≤ theta * (t0 - t))
    (hKtot : 2 * (KD + 3 * Real.sqrt d * BG) ≤ Ktot)
    (hG1 : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
              0 < rad → rad ≤ 1 →
              localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                KG * (Kf + Cphi) ^ 2 * rad ^ t0) ∧
            (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
              IsHolderOn alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
              cAlphaNorm alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
                KG * (Kf + Cphi)))
    (hKD' : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (∀ (x : SpatialCoordinates d) (rad : ℝ),
              x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad → rad ≤ 1 →
              localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                KD * (Kf + Cphi) ^ 2 * rad ^ t) ∧
            (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (u : SobolevData (centeredCube z r hr)).1| ≤ KD * (Kf + Cphi)) ∧
            (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ dist x y →
              |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1 -
                setAverage (Metric.ball y ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1| ≤
                KD * (Kf + Cphi) * dist x y ^ alpha)) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
          ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
            ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
            SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
            (∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
                localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                  Ktot * (Kf + Cphi) ^ 2 * rad ^ t) ∧
            (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
              IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
              cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
                Ktot * (Kf + Cphi)) := by
  intro F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have hc : 0 ≤ Kf + Cphi :=
    add_nonneg hKf ((aux_prop_growth_c2Norm_nonneg _ phi).trans hCphi)
  have hsup := hG1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have hlarge := hKD' F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have hrN := aux_lem_as_regularity_rN_bounds theta htheta N
  have hcl := aux_lem_as_regularity_clause hd z hr (cutoffPositiveCoefficient M H om N z hr)
    (u : SobolevData (centeredCube z r hr)) alpha alpha0 t t0
    ((3 : ℝ) ^ (-(theta * (N : ℝ)))) KG BG KD (Kf + Cphi) hal hal0 hal1 hrN.1 hrN.2
    hgeKG hBG hKD.le hc
    (fun rho h0 h1 => aux_lem_as_regularity_rpow_absorb KG BG _ theta (alpha0 - alpha)
      rho N hBG hBGN (by linarith) hxi1 h0 h1)
    (fun rho h0 h1 => aux_lem_as_regularity_rpow_absorb KG BG _ theta (t0 - t)
      rho N hBG hBGN (by linarith) hxi2 h0 h1)
    hsup.1 hsup.2 hlarge.1 hlarge.2.1 hlarge.2.2
  refine ⟨fun x rad hx h0 h1 => (hcl.1 x rad hx h0 h1).trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKtot (sq_nonneg _)) (Real.rpow_nonneg h0.le _)
  · obtain ⟨U, hUc, hUae, hUH, hUn⟩ := hcl.2
    exact ⟨U, hUc, hUae, hUH, hUn.trans (mul_le_mul_of_nonneg_right hKtot hc)⟩

/-- Assembles the Neumann conjunct of `lem_as_regularity`'s per-`(N,omega)` clause, the
Neumann analogue of `aux_lem_as_regularity_dirichlet_branch`. Split out for the same
heartbeat-budget reason. -/
theorem aux_lem_as_regularity_neumann_branch
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha) (hal0 : alpha < alpha0) (hal1 : alpha0 < 1) (ht0 : t < t0)
    (theta xi KBval KBmax BB KN Ktot : ℝ)
    (htheta : 0 < theta) (hBB : 0 < BB) (hKN : 0 < KN)
    (hKBmax0 : 0 ≤ KBmax) (hKBle : KBval ≤ KBmax)
    (hKBmaxN : KBmax ≤ BB * (3 : ℝ) ^ (xi * (N : ℝ)))
    (hxi1 : xi ≤ theta * (alpha0 - alpha)) (hxi2 : xi ≤ theta * (t0 - t))
    (hKtot : 2 * (KN + 3 * Real.sqrt d * BB) ≤ Ktot)
    (hB1 : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              KBval * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
              KBval * Kf ^ 2 * rad ^ t0))
    (hKN' : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
          (∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
              KN * Kf ^ 2 * rad ^ t) ∧
          (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (v : SobolevData (centeredCube z r hr)).1| ≤ KN * Kf) ∧
          (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            (3 : ℝ) ^ (-(theta * (N : ℝ))) ≤ dist x y →
            |setAverage (Metric.ball x ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
                (v : SobolevData (centeredCube z r hr)).1 -
              setAverage (Metric.ball y ((3 : ℝ) ^ (-(theta * (N : ℝ)))) ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
                (v : SobolevData (centeredCube z r hr)).1| ≤
              KN * Kf * dist x y ^ alpha)) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              Ktot * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
              Ktot * Kf ^ 2 * rad ^ t) := by
  intro F Kf hKf hFm hFb hF0 v hsol
  have hsup := hB1 F Kf hKf hFm hFb hF0 v hsol
  have hlarge := hKN' F Kf hKf hFm hFb hF0 v hsol
  have hrN := aux_lem_as_regularity_rN_bounds theta htheta N
  obtain ⟨U0, hU0c, hU0H, hU0ae, hU0n⟩ := hsup.1
  have hcl := aux_lem_as_regularity_clause hd z hr (cutoffPositiveCoefficient M H om N z hr)
    (v : SobolevData (centeredCube z r hr)) alpha alpha0 t t0
    ((3 : ℝ) ^ (-(theta * (N : ℝ)))) KBmax BB KN Kf hal hal0 hal1 hrN.1 hrN.2
    hKBmax0 hBB hKN.le hKf
    (fun rho h0 h1 => aux_lem_as_regularity_rpow_absorb KBmax BB _ theta (alpha0 - alpha)
      rho N hBB hKBmaxN (by linarith) hxi1 h0 h1)
    (fun rho h0 h1 => aux_lem_as_regularity_rpow_absorb KBmax BB _ theta (t0 - t)
      rho N hBB hKBmaxN (by linarith) hxi2 h0 h1)
    (fun x rad hx h0 h1 => (hsup.2 x rad hx h0 h1).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKBle (sq_nonneg Kf))
        (Real.rpow_nonneg h0.le _)))
    ⟨U0, hU0c, hU0ae, hU0H, hU0n.trans (mul_le_mul_of_nonneg_right hKBle hKf)⟩
    hlarge.1 hlarge.2.1 hlarge.2.2
  obtain ⟨U, hUc, hUae, hUH, hUn⟩ := hcl.2
  refine ⟨⟨U, hUc, hUH, hUae, hUn.trans (mul_le_mul_of_nonneg_right hKtot hKf)⟩,
    fun x rad hx h0 h1 => (hcl.1 x rad hx h0 h1).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKtot (sq_nonneg _)) (Real.rpow_nonneg h0.le _)

/-- The `omega`-quantified per-cutoff bundle of `lem_as_regularity`'s conclusion for one fixed
cube, taking the four already-`M`-and-`(z,r,hr)`-instantiated suppliers as opaque hypotheses:
`hGz`/`hBz` (small-radius Dirichlet/Neumann, exponents `alpha0,t0`) and `hADz`/`hANz`
(large-radius Dirichlet/Neumann, radius `≥ r_N := 3^{-θN}`). Combines them via the
subexponential envelope and the two branch lemmas above. This separate declaration keeps
the assembly within Lean's default elaboration budget. -/
theorem aux_lem_as_regularity_omega_bundle
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha) (hal0 : alpha < alpha0) (hal1 : alpha0 < 1) (ht0 : t < t0)
    (θD θN : ℝ) (hθD : 0 < θD) (hθN : 0 < θN)
    (hGz : ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin 1 → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal ((fun _ : Fin 1 => (1 : ℝ)) i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal ((fun _ : Fin 1 => (1 : ℝ)) i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
            ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
              SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
              (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
                0 < rad → rad ≤ 1 →
                localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                    (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                  K N om * (Kf + Cphi) ^ 2 * rad ^ t0) ∧
              (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
                IsHolderOn alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
                cAlphaNorm alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
                  K N om * (Kf + Cphi)))
    (hBz : ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin 1 → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal ((fun _ : Fin 1 => (1 : ℝ)) i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal ((fun _ : Fin 1 => (1 : ℝ)) i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
          ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
            (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              IsHolderOn alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
              ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
              cAlphaNorm alpha0 (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
                K N om * Kf) ∧
            (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
              0 < rad → rad ≤ 1 →
              localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
                K N om * Kf ^ 2 * rad ^ t0))
    (hADz : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
                ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
                SolvesDirichlet (cutoffPositiveCoefficient M H omega N z hr) F b u →
                (∀ (x : SpatialCoordinates d) (rad : ℝ),
                  x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(θD * (N : ℝ))) ≤ rad → rad ≤ 1 →
                  localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                    (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                    K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
                (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  |setAverage (Metric.ball x ((3 : ℝ) ^ (-(θD * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (u : SobolevData (centeredCube z r hr)).1| ≤ K * (Kf + Cphi)) ∧
                (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                  (3 : ℝ) ^ (-(θD * (N : ℝ))) ≤ dist x y →
                  |setAverage (Metric.ball x ((3 : ℝ) ^ (-(θD * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                      (u : SobolevData (centeredCube z r hr)).1 -
                    setAverage (Metric.ball y ((3 : ℝ) ^ (-(θD * (N : ℝ)))) ∩
                      (centeredCube z r hr : Set (SpatialCoordinates d)))
                      (u : SobolevData (centeredCube z r hr)).1| ≤
                    K * (Kf + Cphi) * dist x y ^ alpha))
    (hANz : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            0 ≤ Kf →
            AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
              SolvesNeumann (cutoffPositiveCoefficient M H omega N z hr) F v →
              (∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ centeredCube z r hr → (3 : ℝ) ^ (-(θN * (N : ℝ))) ≤ rad → rad ≤ 1 →
                localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
                  K * Kf ^ 2 * rad ^ t) ∧
              (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                |setAverage (Metric.ball x ((3 : ℝ) ^ (-(θN * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (v : SobolevData (centeredCube z r hr)).1| ≤ K * Kf) ∧
              (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
                (3 : ℝ) ^ (-(θN * (N : ℝ))) ≤ dist x y →
                |setAverage (Metric.ball x ((3 : ℝ) ^ (-(θN * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (v : SobolevData (centeredCube z r hr)).1 -
                  setAverage (Metric.ball y ((3 : ℝ) ^ (-(θN * (N : ℝ)))) ∩
                    (centeredCube z r hr : Set (SpatialCoordinates d)))
                    (v : SobolevData (centeredCube z r hr)).1| ≤
                  K * Kf * dist x y ^ alpha)) :
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
    ∀ N : ℕ,
      ((∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
            ContDiff ℝ 2 phi →
            c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
            ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
              ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
              SolvesDirichlet (cutoffPositiveCoefficient M H omega N z hr) F b u →
              (∀ (x : SpatialCoordinates d) (rad : ℝ),
                x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
                localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                  (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                  (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
                  K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
              (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
                IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
                cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
                  K * (Kf + Cphi))) ∧
      (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
          ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            SolvesNeumann (cutoffPositiveCoefficient M H omega N z hr) F v →
            (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
              ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
              cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
                K * Kf) ∧
            (∀ (x : SpatialCoordinates d) (rad : ℝ),
              x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
              localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
                K * Kf ^ 2 * rad ^ t))) := by
  have hgap : 0 < min (alpha0 - alpha) (t0 - t) := lt_min (by linarith) (by linarith)
  obtain ⟨KG, CG, hmemG, hnormG, hgeG, hestG⟩ := hGz
  obtain ⟨KB, CB, hmemB, hnormB, hestB⟩ := hBz
  have hEG := aux_lem_as_regularity_envelope (chaosSampleLaw M).toMeasure KG (CG 0)
    (fun N => by simpa using hmemG 0 N) (fun N => by simpa using hnormG 0 N)
    (θD * min (alpha0 - alpha) (t0 - t)) (mul_pos hθD hgap)
  have hEB := aux_lem_as_regularity_envelope (chaosSampleLaw M).toMeasure KB (CB 0)
    (fun N => by simpa using hmemB 0 N) (fun N => by simpa using hnormB 0 N)
    (θN * min (alpha0 - alpha) (t0 - t)) (mul_pos hθN hgap)
  have hξD1 : θD * min (alpha0 - alpha) (t0 - t) ≤ θD * (alpha0 - alpha) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hθD.le
  have hξD2 : θD * min (alpha0 - alpha) (t0 - t) ≤ θD * (t0 - t) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hθD.le
  have hξN1 : θN * min (alpha0 - alpha) (t0 - t) ≤ θN * (alpha0 - alpha) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hθN.le
  have hξN2 : θN * min (alpha0 - alpha) (t0 - t) ≤ θN * (t0 - t) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hθN.le
  filter_upwards [hestG, hgeG, hestB, hADz, hANz, hEG, hEB] with om hG1 hge1 hB1 hAD2 hAN2
    hEG1 hEB1
  obtain ⟨KD, hKD, hKD'⟩ := hAD2
  obtain ⟨KN, hKN, hKN'⟩ := hAN2
  obtain ⟨BG, hBG, hBG'⟩ := hEG1
  obtain ⟨BB, hBB, hBB'⟩ := hEB1
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hKD0 : 0 ≤ 2 * (KD + 3 * Real.sqrt d * BG) := by positivity
  have hKN0 : 0 ≤ 2 * (KN + 3 * Real.sqrt d * BB) := by positivity
  refine ⟨2 * (KD + 3 * Real.sqrt d * BG) + 2 * (KN + 3 * Real.sqrt d * BB), by positivity, ?_⟩
  intro N
  refine ⟨?_, ?_⟩
  · exact aux_lem_as_regularity_dirichlet_branch hd z hr M H om N alpha alpha0 t t0
      hal hal0 hal1 ht0 θD (θD * min (alpha0 - alpha) (t0 - t)) (KG N om) BG KD
      (2 * (KD + 3 * Real.sqrt d * BG) + 2 * (KN + 3 * Real.sqrt d * BB))
      hθD hBG hKD (le_trans zero_le_one (hge1 N)) (hBG' N) hξD1 hξD2 (by linarith)
      (hG1 N) (hKD' N)
  · exact aux_lem_as_regularity_neumann_branch hd z hr M H om N alpha alpha0 t t0
      hal hal0 hal1 ht0 θN (θN * min (alpha0 - alpha) (t0 - t)) (KB N om) (max (KB N om) 0) BB KN
      (2 * (KD + 3 * Real.sqrt d * BG) + 2 * (KN + 3 * Real.sqrt d * BB))
      hθN hBB hKN (le_max_right _ _) (le_max_left _ _)
      (max_le (hBB' N) (by positivity)) hξN1 hξN2 (by linarith)
      (hB1 N) (hKN' N)

/-- Docstring ticks: actual energies, weak solution classes, representatives, all data, same randomK beforeN; weak exponent margins fixedbefore moment/disorder; old stronger estimates are prop_growth/cor_neumann_source proof suppliers, not hgrowth/hneu assumptions; summable response bank transfers finite prefixes via lem_band/lem_prefix_limit and response polarization; rem_resolved meshes/strata and thm_fold original-grid convolution; lem_as_coarse supplies common coarse bounds; allowances and reference-mesh depth loss plus deterministic iteration are obligations here (no hbig); Markov/BorelCantelli from old moments and exponent conversion produce small-scale control here (no hsub); finite exceptionalN absorbed; actual arbitrary fixedQ transport is part of source4564 and source proof, not an arbitrary unpinned Qc. Standing published M inputs in_6_16/in_iteration and small-perturbation/fractional inputs are explicit, never a new pathwise premise. Phase1 statement only; no proof is claimed. -/
theorem lem_as_regularity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (Pc : in_poincare d hd E)
    (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (alpha alpha0 t t0 : ℝ)
    (hal : 0 < alpha)
    (hal0 : alpha < alpha0)
    (hal1 : alpha0 < 1)
    (ht1 : (d : ℝ) - 1 < t)
    (ht0 : t < t0)
    (ht2 : t0 < (d : ℝ)) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M)
      (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        let Q := centeredCube z r hr;
        let closedQ := closedCube z r hr;
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ N : ℕ,
            let a := cutoffPositiveCoefficient M H omega N z hr;
            ((∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
                0 ≤ Kf →
                AEMeasurable F
                  (volume.restrict (Q : Set (SpatialCoordinates d))) →
                (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
                  |F x| ≤ Kf) →
                ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
                  ContDiff ℝ 2 phi →
                  c2Norm (closedQ : Set (SpatialCoordinates d)) phi ≤ Cphi →
                  ∀ (b u : weakSobolevGraph Q),
                    ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                      volume.restrict (Q : Set (SpatialCoordinates d))] phi →
                    SolvesDirichlet a F b u →
                    (∀ (x : SpatialCoordinates d) (rad : ℝ),
                      x ∈ Q → 0 < rad → rad ≤ 1 →
                      localGradientEnergy a
                        (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                        (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                        (sobolevGradient (u : SobolevData Q)) ≤
                        K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
                  (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                    ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                      volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
                    IsHolderOn alpha (closedQ : Set (SpatialCoordinates d)) U ∧
                    cAlphaNorm alpha (closedQ : Set (SpatialCoordinates d)) U ≤
                      K * (Kf + Cphi))) ∧
            (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
                0 ≤ Kf →
                AEMeasurable F
                  (volume.restrict (Q : Set (SpatialCoordinates d))) →
                (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
                  |F x| ≤ Kf) →
                (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
                ∀ v : meanZeroSobolevGraph Q,
                  SolvesNeumann a F v →
                  (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                    IsHolderOn alpha (closedQ : Set (SpatialCoordinates d)) U ∧
                    ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                      volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
                    cAlphaNorm alpha (closedQ : Set (SpatialCoordinates d)) U ≤
                      K * Kf) ∧
                  (∀ (x : SpatialCoordinates d) (rad : ℝ),
                    x ∈ Q → 0 < rad → rad ≤ 1 →
                    localGradientEnergy a
                      (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                      (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                      (sobolevGradient (v : SobolevData Q)) ≤
                      K * Kf ^ 2 * rad ^ t))) := by
  have hal1' : alpha < 1 := hal0.trans hal1
  have ht2' : t < (d : ℝ) := ht0.trans ht2
  have ht1' : (d : ℝ) - 1 < t0 := ht1.trans ht0
  have hal0' : 0 < alpha0 := hal.trans hal0
  obtain ⟨θD, hθD, δAD, hδAD, hAD⟩ :=
    aux_lem_as_regularity_large_radius_dirichlet d hd E Pc Xc W D Cp Sf Step Dbase Interp alpha t hal hal1'
      ht1 ht2'
  obtain ⟨θN, hθN, δAN, hδAN, hAN⟩ :=
    aux_lem_as_regularity_large_radius_neumann d hd E Pc Xc W D Cp Sf Step Dbase Interp alpha t hal hal1'
      ht1 ht2'
  obtain ⟨δG, hδG, hG⟩ :=
    aux_lem_as_regularity_dirichlet_supply d hd E Pc Xc W Cp Sf t0 alpha0 1 (fun _ => 1)
      ht1' ht2 hal0' hal1 (fun _ => le_rfl)
  obtain ⟨δB, hδB, hB⟩ :=
    aux_lem_as_regularity_neumann_cube d hd E Pc Xc W D Cp t0 alpha0 1 (fun _ => 1)
      ht1' ht2 hal0' hal1 (fun _ => le_rfl)
  refine ⟨min (min δAD δAN) (min δG δB), lt_min (lt_min hδAD hδAN) (lt_min hδG hδB), ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr
  have hδ1 : M.delta ≤ 1 := hδ.trans (min_le_left _ _)
  have hδ0 : M.delta ≤ min (min δAD δAN) (min δG δB) := hδ.trans (min_le_right _ _)
  have hδAD' : M.delta ≤ min 1 δAD :=
    le_min hδ1 (hδ0.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδAN' : M.delta ≤ min 1 δAN :=
    le_min hδ1 (hδ0.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδG' : M.delta ≤ δG := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδB' : M.delta ≤ δB := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact aux_lem_as_regularity_omega_bundle hd z hr M H alpha alpha0 t t0 hal hal0 hal1 ht0
    θD θN hθD hθN
    (hG M Rm Sreg It H hIR hδG' z r hr) (hB M Rm Sreg It H hIR hδB' z r hr)
    (hAD M Rm Sreg It H hIR hδAD' z r hr) (hAN M Rm Sreg It H hIR hδAN' z r hr)

end Paper



