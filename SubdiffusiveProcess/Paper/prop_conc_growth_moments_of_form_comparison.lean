module

public import SubdiffusiveProcess.Paper.prop_conc_level_zoom
public import SubdiffusiveProcess.Paper.prop_conc_affine_minimizer_dilation
public import SubdiffusiveProcess.Paper.prop_conc_level_local_minimizers
public import SubdiffusiveProcess.Paper.prop_conc_unit_inverse_trace_moment
public import SubdiffusiveProcess.Paper.prop_conc_cutoff_affine_coercivity
public import SubdiffusiveProcess.Paper.prop_conc_coordinate_measure_order
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic
public import SubdiffusiveProcess.Lane2.LocalAffineLimitData
public import SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer
public import SubdiffusiveProcess.Analysis.FiniteMeasureGrowth
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

/-- A finite family of level-cell growth bounds controls its sum at arbitrary centers. -/
theorem aux_prop_conc_growth_moments_finite_sum_growth
    {d : ℕ} {ι : Type*} [Fintype ι] (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (mu : ι → Measure (SpatialCoordinates d))
    (K t : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hg : ∀ i, ∀ x ∈ centeredCube z r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      mu i (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (K * rho ^ t)) :
    ∀ x : SpatialCoordinates d, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ((∑ i, mu i) (Metric.ball x rho ∩
        (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal ≤
        (2 ^ t * (Fintype.card ι : ℝ) * K) * rho ^ t := by
  have hsum : ∀ x ∈ centeredCube z r hr,
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      (∑ i, mu i) (Metric.ball x rho ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (((Fintype.card ι : ℝ) * K) * rho ^ t) := by
    intro x hx rho hrho hrho1
    rw [Measure.finset_sum_apply]
    calc
      _ ≤ ∑ i : ι, ENNReal.ofReal (K * rho ^ t) :=
          Finset.sum_le_sum (fun i _ => hg i x hx rho hrho hrho1)
      _ = ENNReal.ofReal (((Fintype.card ι : ℝ) * K) * rho ^ t) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hK (Real.rpow_nonneg hrho.le _))]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  have hall := measure_ball_inter_growth_of_centers_mem (∑ i, mu i)
    (centeredCube z r hr : Set (SpatialCoordinates d)) z
    (Metric.mem_ball_self (by linarith : 0 < r / 2))
    (fun u hu => by
      have hu' : u ∈ Metric.ball z (r / 2) := hu
      exact Metric.ball_subset_ball (by linarith : r / 2 ≤ 1) hu')
    ((Fintype.card ι : ℝ) * K) t (mul_nonneg (Nat.cast_nonneg _) hK) ht hsum
  intro x rho hrho hrho1
  have hbound := hall x rho hrho hrho1
  rw [← mul_assoc] at hbound
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) hK)
      (Real.rpow_nonneg hrho.le _)) hbound


/-- Level-cell version of `prop_conc_local_minimizers_normalized_growth`: local coordinate minimizers
and form order give the explicit normalized growth majorant on the cell of side `r` about `z`. -/
theorem aux_prop_conc_growth_moments_normalized_growth
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (h3r : 0 < 3 * r)
    (E F : _root_.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (m C0 : ℝ) (hm : 0 < m) (hminv : m⁻¹ ≤ C0)
    (hform : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v)
    (LE LF : Fin d → ℝ) (KE KF t D : ℝ) (hKE : 0 ≤ KE) (hKF : 0 ≤ KF)
    (ht : 0 ≤ t) (hD : 0 < D)
    (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer z r hr h3r
      E GammaE (Pi.single i 1) (LE i) KE t)
    (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer z r hr h3r
      F GammaF (Pi.single i 1) (LF i) KF t) :
    ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ 1 →
      ((ENNReal.ofReal D⁻¹ •
        ((∑ i, GammaE.measure (uE i).u) + ∑ i, GammaE.measure (uF i).u))
        (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal ≤
      (((2 ^ t * d * KE) + C0 * (2 ^ t * d * KF)) * D⁻¹) * rho ^ t := by
  let muE : Measure (SpatialCoordinates d) := ∑ i, GammaE.measure (uE i).u
  let muEF : Measure (SpatialCoordinates d) := ∑ i, GammaE.measure (uF i).u
  let muF : Measure (SpatialCoordinates d) := ∑ i, GammaF.measure (uF i).u
  have hgE := aux_prop_conc_growth_moments_finite_sum_growth z r hr hr1
    (fun i => GammaE.measure (uE i).u) KE t hKE ht (fun i => (uE i).growth)
  have hgF := aux_prop_conc_growth_moments_finite_sum_growth z r hr hr1
    (fun i => GammaF.measure (uF i).u) KF t hKF ht (fun i => (uF i).growth)
  have horder := prop_conc_coordinate_measure_order
    (centeredCube z (3 * r) h3r)
    E F hFcore hdom GammaE GammaF m hm hform (fun i => (uF i).u) (fun i => (uF i).mem)
  have hfiniteE (A : Set (SpatialCoordinates d)) : muE A ≠ ⊤ := by
    rw [show muE = ∑ i, GammaE.measure (uE i).u from rfl, Measure.finset_sum_apply]
    exact ENNReal.sum_ne_top.mpr (fun i _ => GammaE.measure_ne_top (uE i).mem A)
  have hfiniteEF (A : Set (SpatialCoordinates d)) : muEF A ≠ ⊤ := by
    rw [show muEF = ∑ i, GammaE.measure (uF i).u from rfl, Measure.finset_sum_apply]
    exact ENNReal.sum_ne_top.mpr (fun i _ => GammaE.measure_ne_top (hdom.symm ▸ (uF i).mem) A)
  intro x rho hrho hrho1
  let B := Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))
  have he : (muE B).toReal ≤ (2 ^ t * d * KE) * rho ^ t := by
    simpa only [Fintype.card_fin] using hgE x rho hrho hrho1
  have hf : (muF B).toReal ≤ (2 ^ t * d * KF) * rho ^ t := by
    simpa only [Fintype.card_fin] using hgF x rho hrho hrho1
  have hef : (muEF B).toReal ≤ C0 * ((2 ^ t * d * KF) * rho ^ t) :=
    (horder B).trans ((mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr hm.le)).trans
      (mul_le_mul_of_nonneg_right hminv
        (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) hKF)
          (Real.rpow_nonneg hrho.le _))))
  change ((ENNReal.ofReal D⁻¹ • (muE + muEF)) B).toReal ≤ _
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hD.le), Measure.add_apply,
    ENNReal.toReal_add (hfiniteE B) (hfiniteEF B)]
  exact (mul_le_mul_of_nonneg_left (add_le_add he hef) (inv_nonneg.mpr hD.le)).trans_eq (by ring)



/-- Fatou: the pointwise `liminf` of an `Lq`-bounded sequence of nonnegative functions is `Lq`-bounded. -/
theorem aux_prop_conc_growth_moments_liminf_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (g : ℕ → Ω → ℝ) (hg : ∀ n, Measurable (g n))
    (q C : ℝ) (hq : 0 < q)
    (hb : ∀ n, eLpNorm (g n) (ENNReal.ofReal q) P ≤ ENNReal.ofReal C) :
    Measurable (fun ω => (liminf (fun n => ENNReal.ofReal (g n ω)) atTop).toReal) ∧
    eLpNorm (fun ω => (liminf (fun n => ENNReal.ofReal (g n ω)) atTop).toReal)
      (ENNReal.ofReal q) P ≤ ENNReal.ofReal C := by
  have hmeasA : ∀ n, Measurable (fun ω => ENNReal.ofReal (g n ω)) :=
    fun n => (hg n).ennreal_ofReal
  have hmeasW : Measurable (fun ω => liminf (fun n => ENNReal.ofReal (g n ω)) atTop) :=
    Measurable.liminf hmeasA
  refine ⟨hmeasW.ennreal_toReal, ?_⟩
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hpT : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hqt : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq.le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT hmeasW.ennreal_toReal.aestronglyMeasurable, hqt]
  have hbn : ∀ n, ∫⁻ ω, (ENNReal.ofReal (g n ω)) ^ q ∂P ≤ ENNReal.ofReal C ^ q := by
    intro n
    have h := hb n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT (hg n).aestronglyMeasurable, hqt] at h
    have h2 : ∫⁻ ω, ‖g n ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C ^ q := by
      have h3 := ENNReal.rpow_le_rpow h hq.le
      rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one] at h3
    refine le_trans (lintegral_mono fun ω => ?_) h2
    refine ENNReal.rpow_le_rpow ?_ hq.le
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hfatou : ∫⁻ ω, (liminf (fun n => ENNReal.ofReal (g n ω)) atTop) ^ q ∂P ≤
      ENNReal.ofReal C ^ q := by
    calc ∫⁻ ω, (liminf (fun n => ENNReal.ofReal (g n ω)) atTop) ^ q ∂P
        = ∫⁻ ω, liminf (fun n => (ENNReal.ofReal (g n ω)) ^ q) atTop ∂P := by
          refine lintegral_congr fun ω => ?_
          have h := Monotone.map_liminf_of_continuousAt
            (f := fun x : ℝ≥0∞ => x ^ q) (F := atTop)
            (ENNReal.monotone_rpow_of_nonneg hq.le)
            (fun n => ENNReal.ofReal (g n ω))
            (ENNReal.continuous_rpow_const.continuousAt)
          simpa only [Function.comp_def] using h
      _ ≤ liminf (fun n => ∫⁻ ω, (ENNReal.ofReal (g n ω)) ^ q ∂P) atTop :=
          lintegral_liminf_le (fun n => (hmeasA n).pow_const q)
      _ ≤ ENNReal.ofReal C ^ q :=
          liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbn).frequently
  have hmono : ∫⁻ ω, ‖(liminf (fun n => ENNReal.ofReal (g n ω)) atTop).toReal‖ₑ ^ q ∂P ≤
      ∫⁻ ω, (liminf (fun n => ENNReal.ofReal (g n ω)) atTop) ^ q ∂P := by
    refine lintegral_mono fun ω => ?_
    refine ENNReal.rpow_le_rpow ?_ hq.le
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  calc (∫⁻ ω, ‖(liminf (fun n => ENNReal.ofReal (g n ω)) atTop).toReal‖ₑ ^ q ∂P) ^ (1 / q)
      ≤ (ENNReal.ofReal C ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (hmono.trans hfatou) (by positivity)
    _ = ENNReal.ofReal C := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- Hölder at the doubled order for a product. -/
theorem aux_prop_conc_growth_moments_eLpNorm_mul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ) (p : ℝ≥0∞)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) (Cf Cg : ℝ≥0∞)
    (hfm : eLpNorm f (2 * p) P ≤ Cf) (hgm : eLpNorm g (2 * p) P ≤ Cg) :
    eLpNorm (fun ω => f ω * g ω) p P ≤ Cf * Cg := by
  letI : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
    rw [ENNReal.mul_inv (by norm_num) (by norm_num), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]⟩
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2 * p) (q := 2 * p) (r := p) hf hg
  simpa only [smul_eq_mul, Pi.mul_apply, mul_comm] using! hh.trans (mul_le_mul' hfm hgm)

/-- A cutoff sequence has a subsequence along which the normalizer ratio converges. -/
theorem aux_prop_conc_growth_moments_ratio_subseq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) :
    ∃ (σ : ℕ → ℕ) (rho : ℝ), StrictMono σ ∧ 0 < rho ∧
      Tendsto (fun n => aux_prop_conc_level_zoom_kap M (N (σ n) - k) /
        aux_prop_conc_level_zoom_kap M (N (σ n))) atTop (𝓝 rho) := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp (hN.eventually_ge_atTop k)
  let x : ℕ → ℝ := fun n => aux_prop_conc_level_zoom_kap M (N (n0 + n) - k) /
    aux_prop_conc_level_zoom_kap M (N (n0 + n))
  have hx : ∀ n, x n ∈ Set.Icc (Real.exp (-((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))
      (Real.exp ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := fun n =>
    aux_prop_conc_level_zoom_kap_ratio_bounds M k (N (n0 + n)) (hn0 _ (Nat.le_add_right _ _))
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  refine ⟨fun n => n0 + φ n, a, ?_, ?_, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_left (hφ hij) n0
  · exact lt_of_lt_of_le (Real.exp_pos _) ha.1
  · exact hlim


/-- Two-sided form order transfers to the diagonal affine responses of the local minimizers. -/
theorem aux_prop_conc_growth_moments_response_order
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E F : _root_.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (m Mo : ℝ) (hm : 0 < m) (hMo : 0 < Mo)
    (hlow : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v)
    (hup : ∀ v ∈ E.domain, F.form v v ≤ Mo * E.form v v)
    (LE LF : Fin d → ℝ) (KE KF t : ℝ)
    (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer z r hr h3r
      E GammaE (Pi.single i 1) (LE i) KE t)
    (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer z r hr h3r
      F GammaF (Pi.single i 1) (LF i) KF t) (i : Fin d) :
    m * LE i ≤ LF i ∧ LF i ≤ Mo * LE i := by
  have hA : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have huE_F : (uE i).u ∈ F.toClosedForm.domain := hdom ▸ (uE i).mem
  have huF_E : (uF i).u ∈ E.toClosedForm.domain := hdom.symm ▸ (uF i).mem
  -- upper: L_F ≤ Mo L_E
  have hupF : LF i ≤ Mo * LE i := by
    have hmin := (uF i).minimal (uE i).u huE_F (uE i).representative (uE i).continuous
      (uE i).coeFn (uE i).boundary
    have hord := aux_prop_conc_coordinate_measure_order_single
      (centeredCube z (3 * r) h3r) F E hEcore hdom.symm GammaF GammaE Mo⁻¹ (inv_pos.mpr hMo)
      (fun v hv => by
        have h := hup v (hdom.symm ▸ hv)
        calc Mo⁻¹ * F.form v v ≤ Mo⁻¹ * (Mo * E.form v v) :=
              mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hMo.le)
          _ = E.form v v := by field_simp)
      (uE i).u (hdom ▸ (uE i).mem)
    have hmeas := hord (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [Measure.smul_apply, smul_eq_mul, inv_inv] at hmeas
    have hfin : (GammaE.measure (uE i).u (centeredCube z r hr : Set (SpatialCoordinates d))) ≠ ⊤ :=
      GammaE.measure_ne_top (uE i).mem _
    have hreal : (GammaF.measure (uE i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        Mo * (GammaE.measure (uE i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmeas
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMo.le] using h
    calc LF i = (GammaF.measure (uF i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
          (uF i).response_eq.symm
      _ ≤ (GammaF.measure (uE i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := hmin
      _ ≤ Mo * (GammaE.measure (uE i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := hreal
      _ = Mo * LE i := by rw [(uE i).response_eq]
  -- lower: m L_E ≤ L_F
  have hlowF : m * LE i ≤ LF i := by
    have hmin := (uE i).minimal (uF i).u huF_E (uF i).representative (uF i).continuous
      (uF i).coeFn (uF i).boundary
    have hord := aux_prop_conc_coordinate_measure_order_single
      (centeredCube z (3 * r) h3r) E F hFcore hdom GammaE GammaF m hm hlow (uF i).u (uF i).mem
    have hmeas := hord (centeredCube z r hr : Set (SpatialCoordinates d))
    rw [Measure.smul_apply, smul_eq_mul] at hmeas
    have hfin : (GammaF.measure (uF i).u (centeredCube z r hr : Set (SpatialCoordinates d))) ≠ ⊤ :=
      GammaF.measure_ne_top (uF i).mem _
    have hreal : (GammaE.measure (uF i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        m⁻¹ * (GammaF.measure (uF i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hmeas
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hm.le)] using h
    have h2 : LE i ≤ m⁻¹ * LF i := by
      calc LE i = (GammaE.measure (uE i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
            (uE i).response_eq.symm
        _ ≤ (GammaE.measure (uF i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := hmin
        _ ≤ m⁻¹ * (GammaF.measure (uF i).u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := hreal
        _ = m⁻¹ * LF i := by rw [(uF i).response_eq]
    calc m * LE i ≤ m * (m⁻¹ * LF i) := mul_le_mul_of_nonneg_left h2 hm.le
      _ = LF i := by field_simp
  exact ⟨hlowF, hupF⟩



/-- Level response versus unit response of the shifted field. -/
theorem aux_prop_conc_growth_moments_response_tie {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hrk : r = (3 : ℝ) ^ (-(k : ℤ)))
    (hcoef : ∀ N : ℕ, k ≤ N → ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (aux_prop_conc_level_zoom_T k zcell y) =
        (aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N *
          Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) *
        cutoffCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (N - k) y)
    (Nn : ℕ) (hkN : k ≤ Nn)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
      ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
    (hP0 : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
    (i : Fin d) :
    affineDirichletResponse (centeredCube_isBounded zcell hr) hP
        (cutoffPositiveCoefficient M H om Nn zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal =
      (aux_prop_conc_level_zoom_kap M (Nn - k) / aux_prop_conc_level_zoom_kap M Nn *
          Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) *
        affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
          (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (Nn - k)
            (0 : SpatialCoordinates d) one_pos) (Pi.single i 1) := by
  have hkap : 0 < aux_prop_conc_level_zoom_kap M (Nn - k) / aux_prop_conc_level_zoom_kap M Nn :=
    div_pos (aux_prop_conc_level_zoom_kap_pos M _) (aux_prop_conc_level_zoom_kap_pos M _)
  have hlam : 0 < aux_prop_conc_level_zoom_kap M (Nn - k) / aux_prop_conc_level_zoom_kap M Nn *
      Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) := mul_pos hkap (Real.exp_pos _)
  have hab := aux_prop_conc_level_growth_coefficient_tie M H om zcell k r hr hrk Nn hkN hcoef
  have h1 := (prop_conc_affine_minimizer_dilation zcell r hr one_pos
    (cutoffPositiveCoefficient M H om Nn zcell hr)
    (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (Nn - k)
      (0 : SpatialCoordinates d) one_pos) _ hlam hab hP hP0 (Pi.single i 1)).1
  have hvol : (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal = r ^ d :=
    centeredCube_volume_real zcell hr
  rw [h1, hvol]
  have hrd : 0 < r ^ d := pow_pos hr d
  field_simp

/-- The scalar bookkeeping between absolute growth constants and the normalized growth constant. -/
theorem aux_prop_conc_growth_moments_algebra (d P2 rt rp rE rF eG KEb KFb rd T C0 : ℝ)
    (hrt : 0 < rt) (hrd : 0 < rd) (hT : 0 < T) :
    (P2 * d * (2 * rE * eG * (rd * KEb / rt)) + C0 * (P2 * d * (2 * rF * eG * (rd * KFb / rt)))) *
        (rd * T)⁻¹ * rp =
      (P2 * 2 * d) * (KEb * (rE * eG / T) + C0 * (KFb * (rF * eG / T))) * (rp / rt) := by
  field_simp

/-- Deterministic final bound: the level-cell minimizers with absolute growth constants and the
two-sided form order give the normalized growth of `ν` with the reference-trace ratios. -/
theorem aux_prop_conc_growth_moments_final
    {d : ℕ} (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (h3r : 0 < 3 * r)
    (E F : _root_.DirichletForm (volume.restrict
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (m Mo C0 t : ℝ) (hmpos : 0 < m) (hMopos : 0 < Mo) (hminv : m⁻¹ ≤ C0) (hMoC0 : Mo ≤ C0)
    (hC00 : 0 ≤ C0) (ht0 : 0 ≤ t)
    (hlow : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v)
    (hup : ∀ v ∈ E.domain, F.form v v ≤ Mo * E.form v v)
    (AEm AFm : Matrix (Fin d) (Fin d) ℝ) (KE KF rE rF eG KEb KFb : ℝ)
    (hrE : 0 < rE) (hrF : 0 < rF) (heG : 0 < eG) (hKEb : 0 ≤ KEb) (hKFb : 0 ≤ KFb)
    (hKE : KE = 2 * rE * eG * (r ^ d * KEb / r ^ t))
    (hKF : KF = 2 * rF * eG * (r ^ d * KFb / r ^ t))
    (hTE : 0 < Matrix.trace AEm)
    (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r E GammaE (Pi.single i 1)
      ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AEm i i) KE t)
    (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r F GammaF (Pi.single i 1)
      ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AFm i i) KF t) :
    0 < Matrix.trace AFm ∧
    ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ r →
      ((ENNReal.ofReal ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
          Matrix.trace AEm)⁻¹ •
        ((∑ i, GammaE.measure (uE i).u) + ∑ i, GammaE.measure (uF i).u))
        (Metric.ball x rho ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d)))).toReal ≤
      (2 ^ (t + 1) * d) * (KEb * (rE * eG / Matrix.trace AEm) +
        C0 * C0 * (KFb * (rF * eG / Matrix.trace AFm))) * (rho / r) ^ t := by
  have hvol : (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal = r ^ d :=
    centeredCube_volume_real zcell hr
  have hrd : 0 < r ^ d := pow_pos hr d
  have hrt : 0 < r ^ t := Real.rpow_pos_of_pos hr t
  have hord := fun i : Fin d => aux_prop_conc_growth_moments_response_order zcell r hr h3r
    E F GammaE GammaF hEcore hFcore hdom m Mo hmpos hMopos hlow hup
    (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AEm i i)
    (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AFm i i)
    KE KF t uE uF i
  have hTF_up : Matrix.trace AFm ≤ Mo * Matrix.trace AEm := by
    have h : r ^ d * Matrix.trace AFm ≤ r ^ d * (Mo * Matrix.trace AEm) := by
      calc r ^ d * Matrix.trace AFm = ∑ i, r ^ d * AFm i i := by
            simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
        _ ≤ ∑ i, Mo * (r ^ d * AEm i i) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := (hord i).2
            rw [hvol] at this
            exact this
        _ = r ^ d * (Mo * Matrix.trace AEm) := by
            simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    exact le_of_mul_le_mul_left h hrd
  have hTF_low : m * Matrix.trace AEm ≤ Matrix.trace AFm := by
    have h : r ^ d * (m * Matrix.trace AEm) ≤ r ^ d * Matrix.trace AFm := by
      calc r ^ d * (m * Matrix.trace AEm) = ∑ i, m * (r ^ d * AEm i i) := by
            simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ ∑ i, r ^ d * AFm i i := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := (hord i).1
            rw [hvol] at this
            exact this
        _ = r ^ d * Matrix.trace AFm := by
            simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    exact le_of_mul_le_mul_left h hrd
  have hTF : 0 < Matrix.trace AFm := lt_of_lt_of_le (mul_pos hmpos hTE) hTF_low
  refine ⟨hTF, ?_⟩
  intro x rho hrho hrhor
  have hKE0' : 0 ≤ KE := by rw [hKE]; positivity
  have hKF0' : 0 ≤ KF := by rw [hKF]; positivity
  have hgrowth := aux_prop_conc_growth_moments_normalized_growth zcell r hr hr1 h3r E F
    GammaE GammaF hFcore hdom m C0 hmpos hminv hlow
    (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AEm i i)
    (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AFm i i)
    KE KF t ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
      Matrix.trace AEm) hKE0' hKF0' ht0 (by rw [hvol]; exact mul_pos hrd hTE) uE uF x rho hrho
    (hrhor.trans hr1)
  refine hgrowth.trans ?_
  have hdiv : (rho / r) ^ t = rho ^ t / r ^ t := Real.div_rpow hrho.le hr.le t
  have halg := aux_prop_conc_growth_moments_algebra d (2 ^ t) (r ^ t) (rho ^ t) rE rF eG KEb KFb
    (r ^ d) (Matrix.trace AEm) C0 hrt hrd hTE
  have h2t : (2 : ℝ) ^ (t + 1) = 2 ^ t * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hu : rF * eG / Matrix.trace AEm ≤ Mo * (rF * eG / Matrix.trace AFm) := by
    rw [div_le_iff₀ hTE]
    have h1 : rF * eG * Matrix.trace AFm ≤ rF * eG * (Mo * Matrix.trace AEm) :=
      mul_le_mul_of_nonneg_left hTF_up (mul_pos hrF heG).le
    calc rF * eG = rF * eG * Matrix.trace AFm / Matrix.trace AFm := by field_simp
      _ ≤ rF * eG * (Mo * Matrix.trace AEm) / Matrix.trace AFm :=
          div_le_div_of_nonneg_right h1 hTF.le
      _ = Mo * (rF * eG / Matrix.trace AFm) * Matrix.trace AEm := by field_simp
  have hinner : KEb * (rE * eG / Matrix.trace AEm) +
      C0 * (KFb * (rF * eG / Matrix.trace AEm)) ≤
      KEb * (rE * eG / Matrix.trace AEm) +
        C0 * C0 * (KFb * (rF * eG / Matrix.trace AFm)) := by
    have hw : 0 ≤ rF * eG / Matrix.trace AFm := by positivity
    have hkw : 0 ≤ KFb * (rF * eG / Matrix.trace AFm) := mul_nonneg hKFb hw
    have h1 : C0 * (KFb * (rF * eG / Matrix.trace AEm)) ≤
        C0 * (KFb * (Mo * (rF * eG / Matrix.trace AFm))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hKFb) hC00
    have h2 : C0 * (KFb * (Mo * (rF * eG / Matrix.trace AFm))) ≤
        C0 * C0 * (KFb * (rF * eG / Matrix.trace AFm)) := by
      calc C0 * (KFb * (Mo * (rF * eG / Matrix.trace AFm)))
          = C0 * (Mo * (KFb * (rF * eG / Matrix.trace AFm))) := by ring
        _ ≤ C0 * (C0 * (KFb * (rF * eG / Matrix.trace AFm))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMoC0 hkw) hC00
        _ = C0 * C0 * (KFb * (rF * eG / Matrix.trace AFm)) := by ring
    linarith
  have hnn : 0 ≤ 2 ^ t * 2 * (d : ℝ) := by positivity
  have hnn2 : 0 ≤ rho ^ t / r ^ t := by positivity
  rw [hvol, hKE, hKF, halg, hdiv, h2t]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hnn) hnn2

/-- Unit responses of the shifted field converge to the level limits rescaled by the normalizers. -/
theorem aux_prop_conc_growth_moments_unit_limit {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hrk : r = (3 : ℝ) ^ (-(k : ℤ)))
    (hcoef : ∀ N : ℕ, k ≤ N → ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (aux_prop_conc_level_zoom_T k zcell y) =
        (aux_prop_conc_level_zoom_kap M (N - k) / aux_prop_conc_level_zoom_kap M N *
          Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) *
        cutoffCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (N - k) y)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (rho : ℝ) (hrho : 0 < rho)
    (hlim : Tendsto (fun n => aux_prop_conc_level_zoom_kap M (N n - k) /
      aux_prop_conc_level_zoom_kap M (N n)) atTop (𝓝 rho))
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
      ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
    (hP0 : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
    (a : Fin d → ℝ)
    (hlev : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal)
      atTop (𝓝 (a i))) (i : Fin d) :
    Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
      (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om) (N n - k)
        (0 : SpatialCoordinates d) one_pos) (Pi.single i 1)) atTop
      (𝓝 (a i / (rho * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)))) := by
  have hlam : Tendsto (fun n => aux_prop_conc_level_zoom_kap M (N n - k) /
      aux_prop_conc_level_zoom_kap M (N n) *
        Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) atTop
      (𝓝 (rho * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell))) :=
    hlim.mul_const _
  have hdiv := (hlev i).div hlam (mul_pos hrho (Real.exp_pos _)).ne'
  refine hdiv.congr' ?_
  filter_upwards [hN.eventually_ge_atTop k] with n hn
  have htie := aux_prop_conc_growth_moments_response_tie M H om zcell k r hr hrk hcoef
    (N n) hn hP hP0 i
  have hpos : 0 < aux_prop_conc_level_zoom_kap M (N n - k) /
      aux_prop_conc_level_zoom_kap M (N n) *
        Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) :=
    mul_pos (div_pos (aux_prop_conc_level_zoom_kap_pos M _) (aux_prop_conc_level_zoom_kap_pos M _))
      (Real.exp_pos _)
  have hk1 := (aux_prop_conc_level_zoom_kap_pos M (N n - k)).ne'
  have hk2 := (aux_prop_conc_level_zoom_kap_pos M (N n)).ne'
  simp only [Pi.div_apply]
  rw [htie]
  field_simp

/-- The pointwise `liminf` of reciprocal traces of convergent responses is the reciprocal limit. -/
theorem aux_prop_conc_growth_moments_liminf_inv {d : ℕ} (u : ℕ → Fin d → ℝ) (a : Fin d → ℝ)
    (c : ℝ) (hc : 0 < c) (ha : 0 < ∑ i, a i)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (a i / c))) :
    (liminf (fun n => ENNReal.ofReal ((∑ i, u n i)⁻¹)) atTop).toReal = c / ∑ i, a i := by
  have hsum : Tendsto (fun n => ∑ i, u n i) atTop (𝓝 (∑ i, a i / c)) :=
    tendsto_finset_sum _ fun i _ => hu i
  have hlim : ∑ i, a i / c = (∑ i, a i) / c := by rw [Finset.sum_div]
  rw [hlim] at hsum
  have hpos : 0 < (∑ i, a i) / c := div_pos ha hc
  have hinv := hsum.inv₀ hpos.ne'
  have h2 := ENNReal.tendsto_ofReal hinv
  rw [h2.liminf_eq, ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le), inv_div]

/-- Combination of the two normalized moment bounds into the moment bound of `K`. -/
theorem aux_prop_conc_growth_moments_K_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f1 f2 : Ω → ℝ) (a0 c : ℝ) (ha0 : 0 ≤ a0)
    (hc : 0 ≤ c) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (h1 : AEStronglyMeasurable f1 P) (h2 : AEStronglyMeasurable f2 P) (C1 C2 : ℝ≥0∞)
    (hn1 : eLpNorm f1 p P ≤ C1) (hn2 : eLpNorm f2 p P ≤ C2) :
    eLpNorm (fun ω => a0 * (f1 ω + c * f2 ω)) p P ≤
      ENNReal.ofReal a0 * (C1 + ENNReal.ofReal c * C2) := by
  change eLpNorm (a0 • (f1 + c • f2)) p P ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ha0]
  refine mul_le_mul_right ?_ _
  refine (eLpNorm_add_le hp).trans (add_le_add hn1 ?_)
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  exact mul_le_mul_right hn2 _




theorem prop_conc_growth_moments_of_form_comparison
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t p C0 : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p) (hC0 : 1 ≤ C0) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r),
        r = (3 : ℝ) ^ (-(k : ℝ)) →
      ∀ (S : ResponseSpace (centeredCube zcell (3 * r) h3r)),
        S.space = killedSobolevGraph (centeredCube zcell (3 * r) h3r) →
      ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
          ‖v.val.1‖ ≤ C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
        (NE NF : ℕ → ℕ), Tendsto NE atTop atTop → Tendsto NF atTop atTop →
      ∀ AE AF : BilateralField d → Matrix (Fin d) (Fin d) ℝ,
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i : Fin d,
          Tendsto (fun n => affineDirichletResponse
            (centeredCube_isBounded zcell hr) hP
            (cutoffPositiveCoefficient M H om (NE n) zcell hr) (Pi.single i 1) /
              (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal)
            atTop (𝓝 (AE om i i))) →
      ∃ K KE KF : BilateralField d → ℝ,
        AEStronglyMeasurable K (chaosSampleLaw M).toMeasure ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, 0 ≤ K om) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, 0 < Matrix.trace (AE om)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (DE : LocalAffineLimitData S
          (fun n => cutoffPositiveCoefficient M H om (NE n) zcell h3r)
          (centeredCube_isBounded zcell hr) hP
          (fun n => cutoffPositiveCoefficient M H om (NE n) zcell hr)
          (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
            AE om i i))
          (DF : LocalAffineLimitData S
          (fun n => cutoffPositiveCoefficient M H om (NF n) zcell h3r)
          (centeredCube_isBounded zcell hr) hP
          (fun n => cutoffPositiveCoefficient M H om (NF n) zcell hr)
          (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
            AF om i i)),
        DE.E.domain = DF.E.domain →
        ∀ m : ℝ, C0⁻¹ ≤ m →
        ∀ Mo : ℝ, m ≤ Mo → Mo ≤ C0 →
        (∀ v ∈ DE.E.domain, m * DE.E.form v v ≤ DF.E.form v v) →
        (∀ v ∈ DE.E.domain, DF.E.form v v ≤ Mo * DE.E.form v v) →
        ∃ (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r DE.E DE.Gamma
            (Pi.single i 1)
            ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
              AE om i i) (KE om) t)
          (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r DF.E DF.Gamma
            (Pi.single i 1)
            ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
              AF om i i) (KF om) t),
        ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ r →
          ((ENNReal.ofReal ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
              Matrix.trace (AE om))⁻¹ •
            ((∑ i, DE.Gamma.measure (uE i).u) + ∑ i, DE.Gamma.measure (uF i).u))
            (Metric.ball x rho ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d)))).toReal ≤
          K om * (rho / r) ^ t := by
  haveI : NeZero d := ⟨by omega⟩
  have hdim : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith only [ht, hdim]
  have hC00 : 0 ≤ C0 := zero_le_one.trans hC0
  obtain ⟨δ1, B1, hδ1, hB1, hL⟩ := prop_conc_level_local_minimizers d hd I Pin X W Cp Sob Interp
    t (2 * p) ht htd (by linarith only [hp])
  obtain ⟨δ2, CI, hδ2, hCI, hInv⟩ :=
    prop_conc_unit_inverse_trace_moment d hd I (2 * p) (by linarith only [hp])
  refine ⟨min δ1 δ2, (2 ^ (t + 1) * d) * (B1 * (CI / d)) * (1 + C0 * C0), lt_min hδ1 hδ2,
    by positivity, ?_⟩
  intro M Rm Sreg It H hIR hdelta zcell k r hr h3r hrk S hS hP NE NF hNE hNF AE AF hAE
  have hrk' : r = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hrk, show (-(k : ℝ)) = (((-(k : ℤ) : ℤ)) : ℝ) by push_cast; ring, Real.rpow_intCast]
  have hr1 : r ≤ 1 := by
    rw [hrk']
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hδ1' : M.delta ≤ δ1 := hdelta.trans (min_le_left _ _)
  have hδ2' : M.delta ≤ δ2 := hdelta.trans (min_le_right _ _)
  obtain ⟨hmp, -, hcoefAE⟩ := prop_conc_level_zoom d M H hIR k zcell
  obtain ⟨σE, ρE, hσE, hρE, hlimE⟩ := aux_prop_conc_growth_moments_ratio_subseq M k NE hNE
  obtain ⟨σF, ρF, hσF, hρF, hlimF⟩ := aux_prop_conc_growth_moments_ratio_subseq M k NF hNF
  obtain ⟨KEb, hKEm, hKE0, hKEn, hKEa⟩ := hL M Rm Sreg It H hIR hδ1' zcell k r hr h3r hrk S hS
    (NE ∘ σE) (hNE.comp hσE.tendsto_atTop) ρE hρE hlimE
  obtain ⟨KFb, hKFm, hKF0, hKFn, hKFa⟩ := hL M Rm Sreg It H hIR hδ1' zcell k r hr h3r hrk S hS
    (NF ∘ σF) (hNF.comp hσF.tendsto_atTop) ρF hρF hlimF
  obtain ⟨hP0⟩ : Nonempty (∃ C : ℝ≥0, ∀ v : killedSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖) :=
    ⟨centeredCube_killedPoincare (0 : SpatialCoordinates d) one_pos⟩
  -- the rescaled E-limit matrix and its inverse trace moment
  let AEt : BilateralField d → Matrix (Fin d) (Fin d) ℝ := fun om =>
    (ρE * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell))⁻¹ • AE om
  have hAEt : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i : Fin d,
      Tendsto (fun n => affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
        (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om)
          ((NE ∘ σE) n - k) (0 : SpatialCoordinates d) one_pos) (Pi.single i 1))
        atTop (𝓝 (AEt om i i)) := by
    filter_upwards [hAE, hcoefAE] with om hom hcoef i
    have h := aux_prop_conc_growth_moments_unit_limit M H om zcell k r hr hrk' hcoef (NE ∘ σE)
      (hNE.comp hσE.tendsto_atTop) ρE hρE hlimE hP hP0 (fun i => AE om i i)
      (fun i => (hom i).comp hσE.tendsto_atTop) i
    have hlim : AEt om i i = AE om i i / (ρE * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell)) := by
      simp [AEt, div_eq_inv_mul]
    rw [hlim]
    exact h
  obtain ⟨hEpos, hEmeas, hEnorm⟩ := hInv M hδ2' Rm H hIR (BilateralField d)
    (chaosSampleLaw M).toMeasure (aux_prop_conc_level_zoom_Theta k zcell) hmp hP0
    (fun n => NE (σE n) - k) AEt hAEt
  -- F: finite-cutoff unit reciprocal traces and their pointwise liminf
  let RF : ℕ → BilateralField d → ℝ := fun n om => ∑ i : Fin d, affineDirichletResponse
    (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
    (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om)
      (NF (σF n) - k) (0 : SpatialCoordinates d) one_pos) (Pi.single i 1)
  have hRFmeas : ∀ n, Measurable (RF n) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      (aux_prop_conc_resp_measurable M H hIR.1 (NF (σF n) - k) (0 : SpatialCoordinates d)
        one_pos hP0 (Pi.single i 1)).comp hmp.measurable
  have hRFnorm : ∀ n, eLpNorm (fun om => (RF n om)⁻¹) (ENNReal.ofReal (2 * p))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (CI / d) := by
    intro n
    have h := (hInv M hδ2' Rm H hIR (BilateralField d) (chaosSampleLaw M).toMeasure
      (aux_prop_conc_level_zoom_Theta k zcell) hmp hP0 (fun _ => NF (σF n) - k)
      (fun om => Matrix.diagonal (fun i => affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
        (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om)
          (NF (σF n) - k) (0 : SpatialCoordinates d) one_pos) (Pi.single i 1)))
      (Filter.Eventually.of_forall fun om i => by
        simp only [Matrix.diagonal_apply_eq]
        exact tendsto_const_nhds)).2.2
    simpa only [Matrix.trace_diagonal, RF] using h
  obtain ⟨hWm, hWn⟩ := aux_prop_conc_growth_moments_liminf_norm (chaosSampleLaw M).toMeasure
    (fun n om => (RF n om)⁻¹) (fun n => (hRFmeas n).inv) (2 * p) (CI / d)
    (by linarith only [hp]) hRFnorm
  let WF : BilateralField d → ℝ := fun om =>
    (liminf (fun n => ENNReal.ofReal ((RF n om)⁻¹)) atTop).toReal
  let VE : BilateralField d → ℝ := fun om => (Matrix.trace (AEt om))⁻¹
  let a0 : ℝ := 2 ^ (t + 1) * d
  have ha0 : 0 ≤ a0 := by positivity
  let K : BilateralField d → ℝ := fun om => a0 * (KEb om * VE om + (C0 * C0) * (KFb om * WF om))
  have hdouble : ENNReal.ofReal (2 * p) = 2 * ENNReal.ofReal p := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hKEV : AEStronglyMeasurable (fun om => KEb om * VE om) (chaosSampleLaw M).toMeasure :=
    hKEm.aestronglyMeasurable.mul hEmeas
  have hKFW : AEStronglyMeasurable (fun om => KFb om * WF om) (chaosSampleLaw M).toMeasure :=
    hKFm.aestronglyMeasurable.mul hWm.aestronglyMeasurable
  have hn1 := aux_prop_conc_growth_moments_eLpNorm_mul (chaosSampleLaw M).toMeasure KEb VE
    (ENNReal.ofReal p) hKEm.aestronglyMeasurable hEmeas (ENNReal.ofReal B1)
    (ENNReal.ofReal (CI / d)) (by rw [← hdouble]; exact hKEn) (by rw [← hdouble]; exact hEnorm)
  have hn2 := aux_prop_conc_growth_moments_eLpNorm_mul (chaosSampleLaw M).toMeasure KFb WF
    (ENNReal.ofReal p) hKFm.aestronglyMeasurable hWm.aestronglyMeasurable (ENNReal.ofReal B1)
    (ENNReal.ofReal (CI / d)) (by rw [← hdouble]; exact hKFn) (by rw [← hdouble]; exact hWn)
  have hKmoment := aux_prop_conc_growth_moments_K_moment (chaosSampleLaw M).toMeasure
    (fun om => KEb om * VE om) (fun om => KFb om * WF om) a0 (C0 * C0) ha0
    (mul_nonneg hC00 hC00) (ENNReal.ofReal p) hpE hKEV hKFW _ _ hn1 hn2
  have hBeq : ENNReal.ofReal a0 * (ENNReal.ofReal B1 * ENNReal.ofReal (CI / d) +
      ENNReal.ofReal (C0 * C0) * (ENNReal.ofReal B1 * ENNReal.ofReal (CI / d))) =
      ENNReal.ofReal ((2 ^ (t + 1) * d) * (B1 * (CI / d)) * (1 + C0 * C0)) := by
    have hcd : 0 ≤ CI / d := by positivity
    have hBc : 0 ≤ B1 * (CI / d) := mul_nonneg hB1 hcd
    rw [← ENNReal.ofReal_mul hB1, ← ENNReal.ofReal_mul (mul_nonneg hC00 hC00),
      ← ENNReal.ofReal_add hBc (mul_nonneg (mul_nonneg hC00 hC00) hBc),
      ← ENNReal.ofReal_mul ha0]
    congr 1
    ring
  let KEf : BilateralField d → ℝ := fun om => 2 * ρE *
    Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) * (r ^ d * KEb om / r ^ t)
  let KFf : BilateralField d → ℝ := fun om => 2 * ρF *
    Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) * (r ^ d * KFb om / r ^ t)
  refine ⟨K, KEf, KFf, (hKEV.add (hKFW.const_mul (C0 * C0))).const_mul a0, ?_,
    hKmoment.trans hBeq.le, ?_, ?_⟩
  · filter_upwards [hEpos] with om hom
    have hV : 0 ≤ VE om := inv_nonneg.mpr hom.le
    have hW : 0 ≤ WF om := ENNReal.toReal_nonneg
    exact mul_nonneg ha0 (add_nonneg (mul_nonneg (hKE0 om) hV)
      (mul_nonneg (mul_nonneg hC00 hC00) (mul_nonneg (hKF0 om) hW)))
  · filter_upwards [hEpos] with om hpos
    have h1 : Matrix.trace (AEt om) = (ρE * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell))⁻¹ *
        Matrix.trace (AE om) := by
      simp [AEt, Matrix.trace_smul]
    rw [h1] at hpos
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (mul_pos hρE (Real.exp_pos _)))).mp hpos
  filter_upwards [hKEa, hKFa, hAE, hEpos, hcoefAE] with om hEa hFa hom hpos hcoef
  intro DE DF hdom m hm Mo hmMo hMoC0 hlow hup
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr (zero_lt_one.trans_le hC0)) hm
  have hMopos : 0 < Mo := hmpos.trans_le hmMo
  have hminv : m⁻¹ ≤ C0 := (inv_le_comm₀ hmpos (zero_lt_one.trans_le hC0)).mpr hm
  let uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r DE.E DE.Gamma
      (Pi.single i 1) ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
        AE om i i) (KEf om) t := fun i =>
    Classical.choice (hEa (fun n => DE.GN (σE n)) DE.G DE.E DE.Gamma
      (fun n f => DE.inverse_eq (σE n) f) (DE.inverse_tendsto.comp hσE.tendsto_atTop)
      DE.energy_eq DE.core hP
      (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AE om i i)
      (fun i => (DE.affine_tendsto i).comp hσE.tendsto_atTop) i)
  let uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r DF.E DF.Gamma
      (Pi.single i 1) ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
        AF om i i) (KFf om) t := fun i =>
    Classical.choice (hFa (fun n => DF.GN (σF n)) DF.G DF.E DF.Gamma
      (fun n f => DF.inverse_eq (σF n) f) (DF.inverse_tendsto.comp hσF.tendsto_atTop)
      DF.energy_eq DF.core hP
      (fun i => (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AF om i i)
      (fun i => (DF.affine_tendsto i).comp hσF.tendsto_atTop) i)
  refine ⟨uE, uF, ?_⟩
  have hTE : 0 < Matrix.trace (AE om) := by
    have h1 : Matrix.trace (AEt om) = (ρE * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell))⁻¹ *
        Matrix.trace (AE om) := by
      simp [AEt, Matrix.trace_smul]
    rw [h1] at hpos
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (mul_pos hρE (Real.exp_pos _)))).mp hpos
  obtain ⟨hTF, hfinal⟩ := aux_prop_conc_growth_moments_final zcell r hr hr1 h3r DE.E DF.E DE.Gamma
    DF.Gamma DE.core DF.core hdom m Mo C0 t hmpos hMopos hminv hMoC0 hC00 ht0 hlow hup (AE om)
    (AF om) (KEf om) (KFf om) ρE ρF (Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell))
    (KEb om) (KFb om) hρE hρF (Real.exp_pos _) (hKE0 om) (hKF0 om) rfl rfl hTE uE uF
  -- identify the two normalized factors
  have hVE : VE om = ρE * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) /
      Matrix.trace (AE om) := by
    have hpos' := mul_pos hρE (Real.exp_pos (aux_prop_conc_level_zoom_Gc H k om zcell))
    simp only [VE, AEt, Matrix.trace_smul, smul_eq_mul]
    field_simp
  have hvol : (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal = r ^ d :=
    centeredCube_volume_real zcell hr
  have hlevF : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H om (NF (σF n)) zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal)
      atTop (𝓝 (AF om i i)) := by
    intro i
    have hvpos : 0 < (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal := by
      rw [hvol]; exact pow_pos hr d
    have h := ((DF.affine_tendsto i).comp hσF.tendsto_atTop).div_const
      (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal
    have e : (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * AF om i i /
        (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal = AF om i i := by
      field_simp
    rw [e] at h
    exact h
  have hWF : WF om = ρF * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell) /
      Matrix.trace (AF om) := by
    have hTr : Matrix.trace (AF om) = ∑ i, AF om i i := by simp [Matrix.trace]
    have h := aux_prop_conc_growth_moments_liminf_inv
      (fun n i => affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP0
        (cutoffPositiveCoefficient M H (aux_prop_conc_level_zoom_Theta k zcell om)
          (NF (σF n) - k) (0 : SpatialCoordinates d) one_pos) (Pi.single i 1))
      (fun i => AF om i i)
      (ρF * Real.exp (aux_prop_conc_level_zoom_Gc H k om zcell))
      (mul_pos hρF (Real.exp_pos _)) (by rw [← hTr]; exact hTF)
      (fun i => aux_prop_conc_growth_moments_unit_limit M H om zcell k r hr hrk' hcoef
        (NF ∘ σF) (hNF.comp hσF.tendsto_atTop) ρF hρF hlimF hP hP0 (fun i => AF om i i) hlevF i)
    rw [← hTr] at h
    exact h
  intro x rho hrho hrhor
  refine (hfinal x rho hrho hrhor).trans (le_of_eq ?_)
  simp only [K, a0, hVE, hWF]

end
end Paper
