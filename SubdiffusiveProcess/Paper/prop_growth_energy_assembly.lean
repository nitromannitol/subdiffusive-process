module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic
public import SubdiffusiveProcess.Paper.prop_growth_common_moment_bank
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Lane3.LocalEnergyAux
public import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.prop_as_response_bank_shift_invariance
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.Main.InfraredAdmissible

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-! ### Geometry and source helpers -/

/-- The coordinate cube of side `r` about `x` is the sup-metric ball of radius `r / 2`. -/
theorem aux_prop_growth_energy_assembly_cube_eq_ball {d : ℕ} (x : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) :
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} = Metric.ball x (r / 2) := by
  rw [ball_pi x (half_pos hr)]
  ext y
  simp [Real.dist_eq]

/-- Local energy only depends on the set, not on its measurability proof. -/
theorem aux_prop_growth_energy_assembly_lge_congr {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s s' : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (hs' : MeasurableSet s') (h : s = s') (g : HilbertGradient Ω) :
    localGradientEnergy a hs g = localGradientEnergy a hs' g := by
  subst h
  rfl

/-- The microscopic `gamma` of a continuous representative is the actual local energy on the
sup-metric ball of radius `r / 2`. -/
theorem aux_prop_growth_energy_assembly_gamma_eq {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (v : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, (v.2 i y) ^ 2) =
      localGradientEnergy a
        (s := Metric.ball x (r / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient v) := by
  rw [aux_prop_growth_energy_assembly_cube_eq_ball x hr]
  have h := aux_rem_resolved_meshes_energy_eq_local a (sobolevGradient v)
    (Metric.ball x (r / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
  rw [← h, Set.inter_assoc, Set.inter_self]
  apply integral_congr_ae
  have h2 := ae_restrict_of_ae_restrict_of_subset
    (Set.inter_subset_right (s := Metric.ball x (r / 2))
      (t := (unitNeumannCube d : Set (SpatialCoordinates d)))) haA
  filter_upwards [h2] with y hy
  rw [hy]
  rfl

/-- The Dirichlet equation only sees the source through `∫_Ω F ψ`. -/
theorem aux_prop_growth_energy_assembly_dirichlet_congr {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (f g : SpatialCoordinates d → ℝ)
    (hfg : g =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] f)
    (b u : weakSobolevGraph Ω) (hsol : SolvesDirichlet a f b u) :
    SolvesDirichlet a g b u := by
  refine ⟨hsol.1, fun ψ => ?_⟩
  rw [hsol.2 ψ]
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- An a.e.-bounded a.e.-measurable source has a measurable modification bounded everywhere. -/
theorem aux_prop_growth_energy_assembly_clamp {d : ℕ} (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (hf : AEMeasurable f (volume.restrict S))
    (Kf : ℝ) (hKf : 0 ≤ Kf) (hb : ∀ᵐ y ∂volume.restrict S, |f y| ≤ Kf) :
    ∃ g : SpatialCoordinates d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ Kf) ∧
      g =ᵐ[volume.restrict S] f := by
  refine ⟨fun y => max (-Kf) (min Kf (hf.mk f y)), ?_, ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min hf.measurable_mk)
  · intro y
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [hf.ae_eq_mk, hb] with y h1 h2
    rw [← h1]
    have h3 := abs_le.mp h2
    rw [min_eq_right h3.2, max_eq_right h3.1]

/-- The `C²` norm is nonnegative. -/
theorem aux_prop_growth_energy_assembly_c2Norm_nonneg {d : ℕ} (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> apply Real.sSup_nonneg <;>
    rintro v ⟨x, -, rfl⟩ <;> positivity

/-- The closure of the unit Neumann cube is the closed unit cube about its centre. -/
theorem aux_prop_growth_energy_assembly_closure_unit (d : ℕ) :
    closure (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
  change closure (Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) =
    Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)
  exact closure_ball _ (by norm_num)

/-! ### Translation of the field (root-independent extremes) -/

/-- The deterministic translation of the whole bilateral field by `w`: exactly the map of
`prop_as_response_bank_shift_invariance`. -/
def aux_prop_growth_energy_assembly_shift (d : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) : BilateralField d :=
  fun j => (om j).comp
    (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
      C(SpatialCoordinates d, SpatialCoordinates d))

theorem aux_prop_growth_energy_assembly_shift_apply (d : ℕ) (w : SpatialCoordinates d)
    (om : BilateralField d) (j : ℤ) (x : SpatialCoordinates d) :
    aux_prop_growth_energy_assembly_shift d w om j x = om j (w + x) := by
  have hx : cubeDilation w 0 1 x = w + x := by
    funext i
    simp [cubeDilation]
  simp [aux_prop_growth_energy_assembly_shift, hx]

theorem aux_prop_growth_energy_assembly_shift_map {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d) :
    Measure.map (aux_prop_growth_energy_assembly_shift d w) (chaosSampleLaw M).toMeasure =
      (chaosSampleLaw M).toMeasure :=
  prop_as_response_bank_shift_invariance d M w

theorem aux_prop_growth_energy_assembly_shift_aemeas {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d) :
    AEMeasurable (aux_prop_growth_energy_assembly_shift d w) (chaosSampleLaw M).toMeasure := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (⟨cubeDilation w 0 1, continuous_cubeDilation w 0 1⟩ :
        C(SpatialCoordinates d, SpatialCoordinates d)) := by
    fun_prop
  exact (measurable_pi_iff.mpr (fun j => hc.comp (measurable_pi_apply j))).aemeasurable

theorem aux_prop_growth_energy_assembly_shift_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d)
    {P : BilateralField d → Prop}
    (hP : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, P om) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, P (aux_prop_growth_energy_assembly_shift d w om) := by
  refine ae_of_ae_map (aux_prop_growth_energy_assembly_shift_aemeas M w) ?_
  rw [aux_prop_growth_energy_assembly_shift_map M w]
  exact hP

theorem aux_prop_growth_energy_assembly_shift_memLp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d)
    {g : BilateralField d → ℝ} {p : ℝ≥0∞} (hg : MemLp g p (chaosSampleLaw M).toMeasure) :
    MemLp (fun om => g (aux_prop_growth_energy_assembly_shift d w om)) p
      (chaosSampleLaw M).toMeasure := by
  rw [← aux_prop_growth_energy_assembly_shift_map M w] at hg
  exact hg.comp_of_map (aux_prop_growth_energy_assembly_shift_aemeas M w)

theorem aux_prop_growth_energy_assembly_shift_eLpNorm {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (w : SpatialCoordinates d)
    {g : BilateralField d → ℝ} (p : ℝ≥0∞)
    (hg : AEStronglyMeasurable g (chaosSampleLaw M).toMeasure) :
    eLpNorm (fun om => g (aux_prop_growth_energy_assembly_shift d w om)) p
      (chaosSampleLaw M).toMeasure = eLpNorm g p (chaosSampleLaw M).toMeasure := by
  have hg' : AEStronglyMeasurable g
      (Measure.map (aux_prop_growth_energy_assembly_shift d w) (chaosSampleLaw M).toMeasure) := by
    rw [aux_prop_growth_energy_assembly_shift_map M w]
    exact hg
  have h := eLpNorm_map_measure (p := p) hg' (aux_prop_growth_energy_assembly_shift_aemeas M w)
  rw [aux_prop_growth_energy_assembly_shift_map M w] at h
  exact h.symm

/-- Translation of the infrared partial sums: they are anchored at the origin. -/
theorem aux_prop_growth_energy_assembly_infraredPartialSum_shift (d : ℕ)
    (w : SpatialCoordinates d) (om : BilateralField d) (L : ℕ) (x : SpatialCoordinates d) :
    infraredPartialSum (aux_prop_growth_energy_assembly_shift d w om) L x =
      infraredPartialSum om L (w + x) - infraredPartialSum om L w := by
  unfold infraredPartialSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, aux_prop_growth_energy_assembly_shift_apply, add_zero]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- The infrared field transforms by translation and recentring, almost surely. -/
theorem aux_prop_growth_energy_assembly_ir_shift {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredAdmissible M H) (w : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      H (aux_prop_growth_energy_assembly_shift d w om) x = H om (w + x) - H om w := by
  rcases hH with hH | ⟨L0, rfl⟩
  swap
  · exact Filter.Eventually.of_forall (fun om x =>
      aux_prop_growth_energy_assembly_infraredPartialSum_shift d w om L0 x)
  have h1 := hH.2
  have h2 := aux_prop_growth_energy_assembly_shift_ae M w h1
  filter_upwards [h1, h2] with om h1 h2
  intro x
  have hA : Filter.Tendsto (fun L => infraredPartialSum (aux_prop_growth_energy_assembly_shift d w om)
      L x) Filter.atTop (nhds (H (aux_prop_growth_energy_assembly_shift d w om) x)) :=
    ((continuous_eval_const x).tendsto _).comp h2
  have hB : Filter.Tendsto (fun L => infraredPartialSum om L (w + x)) Filter.atTop (nhds (H om (w + x))) :=
    ((continuous_eval_const (w + x)).tendsto _).comp h1
  have hC : Filter.Tendsto (fun L => infraredPartialSum om L w) Filter.atTop (nhds (H om w)) :=
    ((continuous_eval_const w).tendsto _).comp h1
  have hD : Filter.Tendsto (fun L => infraredPartialSum (aux_prop_growth_energy_assembly_shift d w om)
      L x) Filter.atTop (nhds (H om (w + x) - H om w)) := by
    simp only [aux_prop_growth_energy_assembly_infraredPartialSum_shift]
    exact hB.sub hC
  exact tendsto_nhds_unique hA hD

/-- The cutoff coefficient of the translated field is the translated coefficient times the
constant infrared recentring factor. -/
theorem aux_prop_growth_energy_assembly_cutoff_shift {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (om : BilateralField d)
    (hHw : ∀ x : SpatialCoordinates d,
      H (aux_prop_growth_energy_assembly_shift d w om) x = H om (w + x) - H om w)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H (aux_prop_growth_energy_assembly_shift d w om) N x =
      cutoffCoefficient M H om N (w + x) * Real.exp (-H om w) := by
  unfold cutoffCoefficient cutoffPotential
  rw [hHw x]
  simp only [aux_prop_growth_energy_assembly_shift_apply]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Exponential moments of the infrared field at one point. -/
theorem aux_prop_growth_energy_assembly_exp_H_memLp {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredAdmissible M H) (z : SpatialCoordinates d) (q : ℝ) (hq : 0 < q) :
    MemLp (fun om => Real.exp |H om z|) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := by
  let K : Compacts (SpatialCoordinates d) := ⟨{z}, isCompact_singleton⟩
  obtain ⟨CC, hCC0, hCCb⟩ := exists_uniform_compactExponentialMoment_of_admissible hd
  have hint := (hCCb M H hH K q hq.le).1
  have hmeasH : Measurable fun om => H om z := (continuous_eval_const z).measurable.comp hH.measurable
  have hmeas : AEStronglyMeasurable (fun om => Real.exp |H om z|) (chaosSampleLaw M).toMeasure :=
    (Real.measurable_exp.comp hmeasH.abs).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas (by simp [hq]) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hq.le]
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun om => ?_)
  · exact ((Real.measurable_exp.comp hmeasH.abs).norm.pow_const q).aestronglyMeasurable
  · have hzK : z ∈ (K : Set (SpatialCoordinates d)) := rfl
    have hle : |H om z| ≤ ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ := by
      have := ContinuousMap.norm_coe_le_norm ((H om).restrict (K : Set (SpatialCoordinates d)))
        ⟨z, hzK⟩
      rw [Real.norm_eq_abs] at this
      exact this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _), ← Real.exp_mul]
    exact Real.exp_le_exp.mpr (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hle hq.le)

/-- The a.s. envelope of the cutoff coefficient on an arbitrary root `closedCube z r` with
`r ≤ 1`, read from the reference-cube envelope of the translated field. -/
theorem aux_prop_growth_energy_assembly_root_envelope_ae {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (om : BilateralField d) (N : ℕ) (Dv mlow mhigh : ℝ)
    (hHz : ∀ x : SpatialCoordinates d,
      H (aux_prop_growth_energy_assembly_shift d z om) x = H om (z + x) - H om z)
    (hlip : ∀ x y, x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)) →
        y ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H (aux_prop_growth_energy_assembly_shift d z om) N x) -
            Real.log (cutoffCoefficient M H (aux_prop_growth_energy_assembly_shift d z om) N y)| ≤
          Dv * (3 : ℝ) ^ N * dist x y)
    (hlo : 0 < mlow)
    (hbd : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      mlow ≤ cutoffCoefficient M H (aux_prop_growth_energy_assembly_shift d z om) N x ∧
        cutoffCoefficient M H (aux_prop_growth_energy_assembly_shift d z om) N x ≤ mhigh) :
    0 < Real.exp |H om z| * |mhigh + mlow⁻¹| ∧
    (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      (Real.exp |H om z| * |mhigh + mlow⁻¹|)⁻¹ ≤ cutoffCoefficient M H om N x ∧
        cutoffCoefficient M H om N x ≤ Real.exp |H om z| * |mhigh + mlow⁻¹|) ∧
    (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
        Dv * (3 : ℝ) ^ N * dist x y) := by
  set s := aux_prop_growth_energy_assembly_shift d z om with hs
  have h0 : (0 : SpatialCoordinates d) ∈
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    change dist (0 : SpatialCoordinates d) 0 ≤ 1 / 2
    rw [dist_self]
    norm_num
  have hhigh : 0 < mhigh := hlo.trans_le ((hbd 0 h0).1.trans (hbd 0 h0).2)
  have hY : 0 < mhigh + mlow⁻¹ := add_pos hhigh (inv_pos.mpr hlo)
  have habsY : |mhigh + mlow⁻¹| = mhigh + mlow⁻¹ := abs_of_pos hY
  have hmem : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      x - z ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    intro x hx
    change dist (x - z) 0 ≤ 1 / 2
    change dist x z ≤ r / 2 at hx
    rw [dist_zero_right, ← dist_eq_norm]
    linarith
  have hA : ∀ x, cutoffCoefficient M H om N x =
      cutoffCoefficient M H s N (x - z) * Real.exp (H om z) := by
    intro x
    have h := aux_prop_growth_energy_assembly_cutoff_shift M H z om hHz N (x - z)
    rw [show z + (x - z) = x by abel] at h
    rw [hs, h, mul_assoc, ← Real.exp_add]
    simp
  rw [habsY]
  refine ⟨mul_pos (Real.exp_pos _) hY, ?_, ?_⟩
  · intro x hx
    have hb := hbd (x - z) (hmem x hx)
    rw [hA x]
    constructor
    · rw [mul_inv]
      have e1 : (Real.exp |H om z|)⁻¹ ≤ Real.exp (H om z) := by
        rw [← Real.exp_neg]
        exact Real.exp_le_exp.mpr (neg_abs_le _)
      have e2 : (mhigh + mlow⁻¹)⁻¹ ≤ cutoffCoefficient M H s N (x - z) := by
        calc (mhigh + mlow⁻¹)⁻¹ ≤ (mlow⁻¹)⁻¹ :=
              inv_anti₀ (inv_pos.mpr hlo) (le_add_of_nonneg_left hhigh.le)
          _ = mlow := inv_inv _
          _ ≤ _ := hb.1
      calc (Real.exp |H om z|)⁻¹ * (mhigh + mlow⁻¹)⁻¹
          ≤ Real.exp (H om z) * cutoffCoefficient M H s N (x - z) :=
            mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le
        _ = _ := mul_comm _ _
    · have e1 : Real.exp (H om z) ≤ Real.exp |H om z| := Real.exp_le_exp.mpr (le_abs_self _)
      have e2 : cutoffCoefficient M H s N (x - z) ≤ mhigh + mlow⁻¹ :=
        hb.2.trans (le_add_of_nonneg_right (inv_pos.mpr hlo).le)
      calc cutoffCoefficient M H s N (x - z) * Real.exp (H om z)
          ≤ (mhigh + mlow⁻¹) * Real.exp |H om z| := mul_le_mul e2 e1 (Real.exp_pos _).le hY.le
        _ = _ := mul_comm _ _
  · intro x y hx hy
    have hAx := cutoffCoefficient_pos M H s N (x - z)
    have hAy := cutoffCoefficient_pos M H s N (y - z)
    rw [hA x, hA y, Real.log_mul hAx.ne' (Real.exp_pos _).ne',
      Real.log_mul hAy.ne' (Real.exp_pos _).ne']
    have h := hlip (x - z) (y - z) (hmem x hx) (hmem y hy)
    rw [dist_sub_right] at h
    calc _ = |Real.log (cutoffCoefficient M H s N (x - z)) -
          Real.log (cutoffCoefficient M H s N (y - z))| := by congr 1; ring
      _ ≤ _ := h

/-- **Root-independent coefficient envelope with moments.**  `lem_extremes` is applied once, on
the reference unit cube at the origin and at order `2q`; the constants `Cp, Cd, cd` are fixed
before the model and the root.  For an arbitrary root `closedCube z r` with `r ≤ 1` the
envelope is transported by translation invariance of the field law, and the infrared
recentring factor `e^{|H(z)|}` is absorbed by Hölder's inequality and the exponential moments
of the infrared field. -/
theorem aux_prop_growth_energy_assembly_root_extremes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cp Cd cd : ℝ, 0 < Cp ∧ 0 < Cd ∧ 0 < cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ cd / (2 * q) →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ (D Mx : ℕ → BilateralField d → ℝ) (CE : ℝ), 0 ≤ CE ∧
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M H om N x ∧
                cutoffCoefficient M H om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x) -
                  Real.log (cutoffCoefficient M H om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
          (∀ N, eLpNorm (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N))) := by
  obtain ⟨Cd, cd, hCd, hcd, hallext⟩ := aux_lem_extremes_upper d hd
  obtain ⟨Cp, hCp, hext⟩ := hallext (0 : SpatialCoordinates d) 1 one_pos (2 * q) (by linarith)
  refine ⟨Cp, Cd, cd, hCp, hCd, hcd, ?_⟩
  intro M H hH hδ z r hr hr1
  obtain ⟨D0, mlow0, mhigh0, hD0, hae0, hD0mem, hYmem, hD0mom, hYmom⟩ := hext M H hH hδ
  have h2q : 0 < 2 * q := by linarith
  have hq0 : 0 < q := by linarith
  have hle : ENNReal.ofReal q ≤ ENNReal.ofReal (2 * q) := ENNReal.ofReal_le_ofReal (by linarith)
  have hEmem := aux_prop_growth_energy_assembly_exp_H_memLp hd M H hH z (2 * q) h2q
  set CE0 := (eLpNorm (fun om => Real.exp |H om z|) (ENNReal.ofReal (2 * q))
    (chaosSampleLaw M).toMeasure).toReal with hCE0def
  have hCE0 : eLpNorm (fun om => Real.exp |H om z|) (ENNReal.ofReal (2 * q))
      (chaosSampleLaw M).toMeasure = ENNReal.ofReal CE0 :=
    (ENNReal.ofReal_toReal hEmem.eLpNorm_lt_top.ne).symm
  have hYs : ∀ N, MemLp (fun om => |mhigh0 N (aux_prop_growth_energy_assembly_shift d z om) +
      (mlow0 N (aux_prop_growth_energy_assembly_shift d z om))⁻¹|) (ENNReal.ofReal (2 * q))
      (chaosSampleLaw M).toMeasure := by
    intro N
    simpa only [Real.norm_eq_abs] using
      (aux_prop_growth_energy_assembly_shift_memLp M z (hYmem N)).norm
  have hprod : ∀ N, eLpNorm (fun om => Real.exp |H om z| *
      |mhigh0 N (aux_prop_growth_energy_assembly_shift d z om) +
        (mlow0 N (aux_prop_growth_energy_assembly_shift d z om))⁻¹|) (ENNReal.ofReal q)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE0 * Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) := by
    intro N
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure q
      (2 * q) hq0 le_rfl _ _ hEmem (hYs N)
    have hYn : eLpNorm (fun om => |mhigh0 N (aux_prop_growth_energy_assembly_shift d z om) +
        (mlow0 N (aux_prop_growth_energy_assembly_shift d z om))⁻¹|) (ENNReal.ofReal (2 * q))
        (chaosSampleLaw M).toMeasure =
        eLpNorm (fun om => mhigh0 N om + (mlow0 N om)⁻¹) (ENNReal.ofReal (2 * q))
          (chaosSampleLaw M).toMeasure := by
      have hn : (fun om => |mhigh0 N (aux_prop_growth_energy_assembly_shift d z om) +
          (mlow0 N (aux_prop_growth_energy_assembly_shift d z om))⁻¹|) =
          fun om => ‖mhigh0 N (aux_prop_growth_energy_assembly_shift d z om) +
            (mlow0 N (aux_prop_growth_energy_assembly_shift d z om))⁻¹‖ := by
        funext om
        rw [Real.norm_eq_abs]
      rw [hn, eLpNorm_norm _ (aux_prop_growth_energy_assembly_shift_memLp M z (hYmem N)).aestronglyMeasurable]
      exact aux_prop_growth_energy_assembly_shift_eLpNorm M z
        (g := fun om => mhigh0 N om + (mlow0 N om)⁻¹) _ (hYmem N).aestronglyMeasurable
    calc _ ≤ _ := hb
      _ = ENNReal.ofReal CE0 * eLpNorm (fun om => mhigh0 N om + (mlow0 N om)⁻¹)
            (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure := by rw [hCE0, hYn]
      _ ≤ ENNReal.ofReal CE0 *
            ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) :=
          by gcongr; exact hYmom N
      _ = _ := by
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_assoc]
  refine ⟨fun N om => D0 N (aux_prop_growth_energy_assembly_shift d z om),
    fun N om => Real.exp |H om z| *
      |mhigh0 N (aux_prop_growth_energy_assembly_shift d z om) +
        (mlow0 N (aux_prop_growth_energy_assembly_shift d z om))⁻¹|,
    CE0 * Cp, mul_nonneg ENNReal.toReal_nonneg hCp.le, ?_, ?_, ?_, ?_, ?_⟩
  · intro N om
    exact ⟨hD0 N _, mul_nonneg (Real.exp_pos _).le (abs_nonneg _)⟩
  · filter_upwards [aux_prop_growth_energy_assembly_shift_ae M z hae0,
      aux_prop_growth_energy_assembly_ir_shift M H hH z] with om h1 h2
    intro N
    obtain ⟨hlip, hlo, hbd⟩ := h1 N
    exact aux_prop_growth_energy_assembly_root_envelope_ae M H z r hr hr1 om N _ _ _ h2 hlip
      hlo hbd
  · intro N
    have hDs : MemLp (fun om => D0 N (aux_prop_growth_energy_assembly_shift d z om))
        (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure :=
      aux_prop_growth_energy_assembly_shift_memLp M z (hD0mem N)
    refine ⟨hDs.mono_exponent hle, ?_⟩
    exact lt_of_le_of_lt (hprod N) ENNReal.ofReal_lt_top
  · intro N
    rw [aux_prop_growth_energy_assembly_shift_eLpNorm M z (g := D0 N) _ (hD0mem N).aestronglyMeasurable]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle).trans (hD0mom N)
  · exact hprod

/-- The matched-range microscopic Dirichlet estimate of `rem_resolved_microscopic`, read on the
actual local energy of the unit-cube positive coefficient (balls of the sup metric). -/
def aux_prop_growth_energy_assembly_MicroLocal (d : ℕ) (t t1 C : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
  ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
  a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
  ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
  (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
  (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
    ∀ y' ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      |Real.log (A y) - Real.log (A y')| ≤ DN / eps * dist y y') →
  ∀ f : SpatialCoordinates d → ℝ, Measurable f →
  ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
  ∀ h : SpatialCoordinates d → ℝ, ContDiff ℝ 2 h →
  ∀ hdata u : weakSobolevGraph (unitNeumannCube d),
  ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h →
  SolvesDirichlet a f hdata u →
  ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
  ∀ Kmac : ℝ, 0 ≤ Kmac →
    localGradientEnergy a
        (s := Metric.ball x (C * eps / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ Kmac * eps ^ t1 →
    ∀ r' : ℝ, 0 < r' → r' ≤ eps →
      localGradientEnergy a
          (s := Metric.ball x (r' / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
          mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
          MN * (c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h) ^ 2 *
            eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) * r' ^ t

/-- The statistical (moment-absorption) clause of `rem_resolved_microscopic`, verbatim. -/
def aux_prop_growth_energy_assembly_MomentClause (d : ℕ) (t t1 : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ p : ℝ, 1 ≤ p →
      let q := 2 * p * max 1 t
      ∀ D M mInv Kmac : ℕ → Ω → ℝ,
      ∀ CD CE CK aRate : ℝ, 0 ≤ CD → 0 ≤ CE → 0 ≤ CK → 0 ≤ aRate →
      aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 →
      (∀ N o, 0 ≤ D N o ∧ 0 ≤ M N o ∧ 0 ≤ mInv N o ∧ 0 ≤ Kmac N o) →
      (∀ N, MemLp (D N) (ENNReal.ofReal q) P ∧ MemLp (M N) (ENNReal.ofReal q) P ∧
        MemLp (mInv N) (ENNReal.ofReal q) P ∧ MemLp (Kmac N) (ENNReal.ofReal q) P) →
      (∀ N, eLpNorm (D N) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) →
      (∀ N, eLpNorm (fun o => M N o + mInv N o) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ)))) →
      (∀ N, eLpNorm (Kmac N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal CK) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        eLpNorm (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun o => mInv N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun o => M N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N o) ^ t)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B

/-- `rem_resolved_microscopic` supplies one constant `C` for the local Dirichlet estimate and
the moment clause. -/
theorem aux_prop_growth_energy_assembly_micro_local (d : ℕ) (hd : 2 ≤ d)
    (W : SmallPerturbationInput d)
    (p1 t t1 : ℝ) (hp1 : 2 ≤ p1) (ht : (d : ℝ) - 1 < t)
    (htt1 : t < t1) (ht1d : t1 < (d : ℝ))
    (htp : t < (d : ℝ) - 2 * (d : ℝ) / p1) :
    ∃ C : ℝ, 0 < C ∧ aux_prop_growth_energy_assembly_MicroLocal d t t1 C ∧
      aux_prop_growth_energy_assembly_MomentClause d t t1 := by
  have h := rem_resolved_microscopic d hd W p1 t t1 hp1 ht htt1 ht1d htp
  rcases h with ⟨C, c, hC, _hc, _hc16, hdet, hstat⟩
  refine ⟨C, hC, ?_, hstat⟩
  intro eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb h hh hdata u hhd hsol
    x hx Kmac hKmac hK r' hr' hre
  have h2 := hdet eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb
  rcases h2 with ⟨_, _, hdir, _⟩
  have h3 := hdir h hh hdata u hhd hsol
  rcases h3 with ⟨_, _, _, hKcl⟩
  have hCe : 0 < C * eps := mul_pos hC heps
  have hK' : (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < C * eps / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤
      Kmac * eps ^ t1 := by
    rw [aux_prop_growth_energy_assembly_gamma_eq a A haA _ x hCe]
    exact hK
  have h4 := hKcl Kmac hKmac x hx hK' r' hr' hre
  beta_reduce at h4
  rw [aux_prop_growth_energy_assembly_gamma_eq a A haA _ x hr'] at h4
  exact h4

/-! ### Pure real steps -/

/-- Monotonicity, saturation above radius one and the macro bound on `[w,1]` give the macro
bound at every radius, with `max ρ w`. -/
theorem aux_prop_growth_energy_assembly_lmac (L : ℝ → ℝ) (w KE t1 : ℝ) (hw1 : w ≤ 1)
    (hKE : 0 ≤ KE) (ht1 : 0 ≤ t1)
    (hmono : ∀ r1 r2 : ℝ, 0 < r1 → r1 ≤ r2 → L r1 ≤ L r2)
    (hsat : ∀ ρ : ℝ, 1 ≤ ρ → L ρ ≤ L 1)
    (hmac : ∀ ρ : ℝ, w ≤ ρ → ρ ≤ 1 → L ρ ≤ KE * ρ ^ t1) :
    ∀ ρ : ℝ, 0 < ρ → L ρ ≤ KE * (max ρ w) ^ t1 := by
  intro ρ hρ
  rcases le_or_gt ρ 1 with h1 | h1
  · have hm1 : max ρ w ≤ 1 := max_le h1 hw1
    calc L ρ ≤ L (max ρ w) := hmono _ _ hρ (le_max_left _ _)
      _ ≤ KE * (max ρ w) ^ t1 := hmac _ (le_max_right _ _) hm1
  · have hmx : max ρ w = ρ := max_eq_left (hw1.trans h1.le)
    rw [hmx]
    calc L ρ ≤ L 1 := hsat ρ h1.le
      _ ≤ KE * (1 : ℝ) ^ t1 := hmac 1 hw1 le_rfl
      _ ≤ KE * ρ ^ t1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow zero_le_one h1.le ht1) hKE

/-- The macro range: radii at least half the wavelength or half the side. -/
theorem aux_prop_growth_energy_assembly_case_macro (w r rad t t1 KE : ℝ)
    (hw1 : w ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hrad : 0 < rad) (hrad1 : rad ≤ 1)
    (ht : 0 ≤ t) (htt1 : t ≤ t1) (hKE : 0 ≤ KE)
    (hcase : w ≤ 2 * rad ∨ r ≤ 2 * rad) :
    KE * (max rad w) ^ t1 ≤ (2 / r) ^ t * KE * rad ^ t := by
  have hm0 : 0 < max rad w := lt_of_lt_of_le hrad (le_max_left _ _)
  have hm1 : max rad w ≤ 1 := max_le hrad1 hw1
  have h2r : 1 ≤ 2 / r := by rw [le_div_iff₀ hr]; linarith
  have hmle : max rad w ≤ 2 / r * rad := by
    refine max_le (le_mul_of_one_le_left hrad.le h2r) ?_
    rcases hcase with h | h
    · calc w ≤ 2 * rad := h
        _ ≤ 2 / r * rad := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr]
          nlinarith
    · calc w ≤ 1 := hw1
        _ ≤ 2 / r * rad := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr]
          linarith
  have h1 : (max rad w) ^ t1 ≤ (max rad w) ^ t :=
    Real.rpow_le_rpow_of_exponent_ge hm0 hm1 htt1
  have h2 : (max rad w) ^ t ≤ (2 / r * rad) ^ t := Real.rpow_le_rpow hm0.le hmle ht
  have h3 : (2 / r * rad) ^ t = (2 / r) ^ t * rad ^ t :=
    Real.mul_rpow (by positivity) hrad.le
  calc KE * (max rad w) ^ t1 ≤ KE * (2 / r * rad) ^ t :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hKE
    _ = (2 / r) ^ t * KE * rad ^ t := by rw [h3]; ring

/-- The wavelength-scale parent energy in unit coordinates. -/
theorem aux_prop_growth_energy_assembly_kmac_bound (w r C t1 KE : ℝ) (hw : 0 < w)
    (hw1 : w ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 < C) (ht1 : 0 ≤ t1) (hKE : 0 ≤ KE) :
    KE * (max (r * (C * min 1 (w / r) / 2)) w) ^ t1 ≤
      (max (C / 2) 1) ^ t1 * KE * (min 1 (w / r)) ^ t1 := by
  have heps0 : 0 < min 1 (w / r) := lt_min one_pos (div_pos hw hr)
  have hreps : r * min 1 (w / r) ≤ w := by
    calc r * min 1 (w / r) ≤ r * (w / r) := mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le
      _ = w := by field_simp
  have hweps : w ≤ min 1 (w / r) := le_min hw1 (by rw [le_div_iff₀ hr]; nlinarith)
  have hC' : 1 ≤ max (C / 2) 1 := le_max_right _ _
  have hmle : max (r * (C * min 1 (w / r) / 2)) w ≤ max (C / 2) 1 * w := by
    refine max_le ?_ (le_mul_of_one_le_left hw.le hC')
    calc r * (C * min 1 (w / r) / 2) = C / 2 * (r * min 1 (w / r)) := by ring
      _ ≤ C / 2 * w := mul_le_mul_of_nonneg_left hreps (by positivity)
      _ ≤ max (C / 2) 1 * w := mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le
  have hm0 : 0 ≤ max (r * (C * min 1 (w / r) / 2)) w := le_trans hw.le (le_max_right _ _)
  calc KE * (max (r * (C * min 1 (w / r) / 2)) w) ^ t1
      ≤ KE * (max (C / 2) 1 * w) ^ t1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0 hmle ht1) hKE
    _ = KE * ((max (C / 2) 1) ^ t1 * w ^ t1) := by
        rw [Real.mul_rpow (by positivity) hw.le]
    _ ≤ KE * ((max (C / 2) 1) ^ t1 * (min 1 (w / r)) ^ t1) := by
        gcongr
    _ = (max (C / 2) 1) ^ t1 * KE * (min 1 (w / r)) ^ t1 := by ring

/-- `eps ^ s ≤ w ^ s / r ^ s` whenever `0 < eps ≤ w / r`, `s ≥ 0`. -/
theorem aux_prop_growth_energy_assembly_eps_pow (eps w r s : ℝ) (heps : 0 < eps)
    (hw : 0 < w) (hr : 0 < r) (hepsw : eps ≤ w / r) (hs : 0 ≤ s) :
    eps ^ s ≤ w ^ s * (r ^ s)⁻¹ := by
  calc eps ^ s ≤ (w / r) ^ s := Real.rpow_le_rpow heps.le hepsw hs
    _ = w ^ s * (r ^ s)⁻¹ := by rw [Real.div_rpow hw.le hr.le, div_eq_mul_inv]

/-- Abstract collection of three matched contributions. -/
theorem aux_prop_growth_energy_assembly_collect
    (rd C P R G1 T1 T2 T3 a1 a2 a3 Z1 Z2 Z3 E : ℝ)
    (hrd : 0 ≤ rd) (hC : 0 ≤ C) (hP : 0 ≤ P) (hR : 0 ≤ R) (hE : 0 ≤ E)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3)
    (hT1 : T1 ≤ a1 * Z1 * E) (hT2 : T2 ≤ a2 * Z2 * E) (hT3 : T3 ≤ a3 * Z3 * E)
    (hG1 : G1 ≤ C * (T1 + T2 + T3) * (P * R)) :
    rd * G1 ≤ (rd * C * P * (a1 + a2 + a3)) * (Z1 + Z2 + Z3) * E * R := by
  have hx1 : 0 ≤ a1 * (Z2 + Z3) * E := by positivity
  have hx2 : 0 ≤ a2 * (Z1 + Z3) * E := by positivity
  have hx3 : 0 ≤ a3 * (Z1 + Z2) * E := by positivity
  have hexp : (a1 + a2 + a3) * (Z1 + Z2 + Z3) * E =
      a1 * Z1 * E + a2 * Z2 * E + a3 * Z3 * E +
        (a1 * (Z2 + Z3) * E + a2 * (Z1 + Z3) * E + a3 * (Z1 + Z2) * E) := by ring
  have hsum : T1 + T2 + T3 ≤ (a1 + a2 + a3) * (Z1 + Z2 + Z3) * E := by linarith
  have hPR : 0 ≤ P * R := mul_nonneg hP hR
  calc rd * G1 ≤ rd * (C * (T1 + T2 + T3) * (P * R)) := mul_le_mul_of_nonneg_left hG1 hrd
    _ ≤ rd * (C * ((a1 + a2 + a3) * (Z1 + Z2 + Z3) * E) * (P * R)) := by
        apply mul_le_mul_of_nonneg_left _ hrd
        apply mul_le_mul_of_nonneg_right _ hPR
        exact mul_le_mul_of_nonneg_left hsum hC
    _ = (rd * C * P * (a1 + a2 + a3)) * (Z1 + Z2 + Z3) * E * R := by ring

/-- The deterministic microscopic constant (it depends on the root side `r` only through
explicit powers). -/
def aux_prop_growth_energy_assembly_Cr (d : ℕ) (r t t1 C : ℝ) : ℝ :=
  r ^ ((d : ℝ) - 2) * C * (2 / r) ^ t *
    ((r ^ (t1 - t))⁻¹ * r ^ ((2 : ℝ) - (d : ℝ)) * (max (C / 2) 1) ^ t1 +
      (r ^ ((d : ℝ) + 2 - t))⁻¹ + 9 * (r ^ ((d : ℝ) - t))⁻¹)

theorem aux_prop_growth_energy_assembly_Cr_nonneg (d : ℕ) (r t t1 C : ℝ) (hr : 0 < r)
    (hC : 0 ≤ C) : 0 ≤ aux_prop_growth_energy_assembly_Cr d r t t1 C := by
  unfold aux_prop_growth_energy_assembly_Cr
  have h1 : 0 ≤ (r ^ (t1 - t))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hr.le _)
  have h2 : 0 ≤ (r ^ ((d : ℝ) + 2 - t))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hr.le _)
  have h3 : 0 ≤ (r ^ ((d : ℝ) - t))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hr.le _)
  have h4 : 0 ≤ r ^ ((2 : ℝ) - (d : ℝ)) := Real.rpow_nonneg hr.le _
  have h5 : 0 ≤ (max (C / 2) 1) ^ t1 :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have h6 : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  have h7 : 0 ≤ (2 / r) ^ t := Real.rpow_nonneg (by positivity) _
  positivity

/-- The microscopic range: collect the three matched contributions into the three
moment-clause random variables. -/
theorem aux_prop_growth_energy_assembly_micro_arith
    (dd r w eps rad t t1 C Cq Dv Kmac Mx Kf Kf1 Cphi Kh G1 : ℝ)
    (hr : 0 < r) (hw : 0 < w) (heps : 0 < eps) (hepsw : eps ≤ w / r)
    (hrad : 0 < rad) (htt1 : t < t1) (htd : t < dd)
    (hC : 0 ≤ C) (hCq : 0 ≤ Cq) (hDv : 0 ≤ Dv) (hKmac : 0 ≤ Kmac) (hMx : 0 ≤ Mx)
    (hKf : 0 ≤ Kf) (hKf10 : 0 ≤ Kf1) (hKf1 : Kf1 ≤ Kf)
    (hCphi : 0 ≤ Cphi) (hKh0 : 0 ≤ Kh) (hKh : Kh ≤ 3 * Cphi)
    (hG1 : G1 ≤ C * ((1 + Dv) ^ t * eps ^ (t1 - t) *
          (r ^ ((2 : ℝ) - dd) * Cq * (Kmac * (Kf + Cphi) ^ 2)) +
        Mx * Kf1 ^ 2 * eps ^ (dd + 2 - t) +
        Mx * Kh ^ 2 * eps ^ (dd - t) * (1 + Dv) ^ t) * (2 * rad / r) ^ t) :
    r ^ (dd - 2) * G1 ≤
      (r ^ (dd - 2) * C * (2 / r) ^ t *
        ((r ^ (t1 - t))⁻¹ * r ^ ((2 : ℝ) - dd) * Cq + (r ^ (dd + 2 - t))⁻¹ +
          9 * (r ^ (dd - t))⁻¹)) *
      ((1 + Dv) ^ t * w ^ (t1 - t) * Kmac + Mx * w ^ (dd + 2 - t) +
        Mx * w ^ (dd - t) * (1 + Dv) ^ t) * (Kf + Cphi) ^ 2 * rad ^ t := by
  have hE0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hKfE : Kf1 ^ 2 ≤ (Kf + Cphi) ^ 2 := by
    have : Kf1 ≤ Kf + Cphi := by linarith
    exact pow_le_pow_left₀ hKf10 this 2
  have hKhE : Kh ^ 2 ≤ 9 * (Kf + Cphi) ^ 2 := by
    have : Kh ^ 2 ≤ (3 * Cphi) ^ 2 := pow_le_pow_left₀ hKh0 hKh 2
    nlinarith
  have e1 := aux_prop_growth_energy_assembly_eps_pow eps w r (t1 - t) heps hw hr hepsw
    (by linarith)
  have e2 := aux_prop_growth_energy_assembly_eps_pow eps w r (dd + 2 - t) heps hw hr hepsw
    (by linarith)
  have e3 := aux_prop_growth_energy_assembly_eps_pow eps w r (dd - t) heps hw hr hepsw
    (by linarith)
  have hDt : 0 ≤ (1 + Dv) ^ t := Real.rpow_nonneg (by linarith) _
  have hr2d : 0 ≤ r ^ ((2 : ℝ) - dd) := Real.rpow_nonneg hr.le _
  have hR1 : 0 ≤ (r ^ (t1 - t))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hr.le _)
  have hR2 : 0 ≤ (r ^ (dd + 2 - t))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hr.le _)
  have hR3 : 0 ≤ (r ^ (dd - t))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hr.le _)
  have hW1 : 0 ≤ w ^ (t1 - t) := Real.rpow_nonneg hw.le _
  have hW2 : 0 ≤ w ^ (dd + 2 - t) := Real.rpow_nonneg hw.le _
  have hW3 : 0 ≤ w ^ (dd - t) := Real.rpow_nonneg hw.le _
  have he1 : 0 ≤ eps ^ (t1 - t) := Real.rpow_nonneg heps.le _
  have he2 : 0 ≤ eps ^ (dd + 2 - t) := Real.rpow_nonneg heps.le _
  have he3 : 0 ≤ eps ^ (dd - t) := Real.rpow_nonneg heps.le _
  have hT1 : (1 + Dv) ^ t * eps ^ (t1 - t) *
      (r ^ ((2 : ℝ) - dd) * Cq * (Kmac * (Kf + Cphi) ^ 2)) ≤
      ((r ^ (t1 - t))⁻¹ * r ^ ((2 : ℝ) - dd) * Cq) *
        ((1 + Dv) ^ t * w ^ (t1 - t) * Kmac) * (Kf + Cphi) ^ 2 := by
    have hK : 0 ≤ r ^ ((2 : ℝ) - dd) * Cq * (Kmac * (Kf + Cphi) ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hDt) hK
    calc _ ≤ (1 + Dv) ^ t * (w ^ (t1 - t) * (r ^ (t1 - t))⁻¹) *
          (r ^ ((2 : ℝ) - dd) * Cq * (Kmac * (Kf + Cphi) ^ 2)) := this
      _ = _ := by ring
  have hT2 : Mx * Kf1 ^ 2 * eps ^ (dd + 2 - t) ≤
      (r ^ (dd + 2 - t))⁻¹ * (Mx * w ^ (dd + 2 - t)) * (Kf + Cphi) ^ 2 := by
    have h1 : Mx * Kf1 ^ 2 ≤ Mx * (Kf + Cphi) ^ 2 := mul_le_mul_of_nonneg_left hKfE hMx
    have h2 := mul_le_mul h1 e2 he2 (by positivity)
    calc _ ≤ Mx * (Kf + Cphi) ^ 2 * (w ^ (dd + 2 - t) * (r ^ (dd + 2 - t))⁻¹) := h2
      _ = _ := by ring
  have hT3 : Mx * Kh ^ 2 * eps ^ (dd - t) * (1 + Dv) ^ t ≤
      (9 * (r ^ (dd - t))⁻¹) * (Mx * w ^ (dd - t) * (1 + Dv) ^ t) * (Kf + Cphi) ^ 2 := by
    have h1 : Mx * Kh ^ 2 ≤ Mx * (9 * (Kf + Cphi) ^ 2) := mul_le_mul_of_nonneg_left hKhE hMx
    have h2 := mul_le_mul h1 e3 he3 (by positivity)
    have h3 := mul_le_mul_of_nonneg_right h2 hDt
    calc _ ≤ Mx * (9 * (Kf + Cphi) ^ 2) * (w ^ (dd - t) * (r ^ (dd - t))⁻¹) *
          (1 + Dv) ^ t := h3
      _ = _ := by ring
  have hrad2 : (2 * rad / r) ^ t = (2 / r) ^ t * rad ^ t := by
    rw [show 2 * rad / r = 2 / r * rad by ring]
    exact Real.mul_rpow (by positivity) hrad.le
  rw [hrad2] at hG1
  exact aux_prop_growth_energy_assembly_collect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Real.rpow_nonneg hr.le _) hC (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg hrad.le _) hE0 (by positivity) hR2 (by positivity)
    (by positivity) (by positivity) (by positivity) hT1 hT2 hT3 hG1

/-- The cutoff wavelength as a real power. -/
theorem aux_prop_growth_energy_assembly_zpow_eq_rpow (N : ℕ) :
    (3 : ℝ) ^ (-(N : ℤ)) = (3 : ℝ) ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, zpow_neg, zpow_natCast]

/-- The dilation scales sup-metric distances by `r`. -/
theorem aux_prop_growth_energy_assembly_dilation_dist {d : ℕ} (z z0 : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (y y' : SpatialCoordinates d) :
    dist (cubeDilation z z0 r y) (cubeDilation z z0 r y') = r * dist y y' := by
  have h : cubeDilation z z0 r y - cubeDilation z z0 r y' = r • (y - y') := by
    funext i
    simp only [cubeDilation, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, abs_of_pos hr, ← dist_eq_norm]

/-- The dilation carries the closed unit cube about `z0` into the closed root. -/
theorem aux_prop_growth_energy_assembly_dilation_closed {d : ℕ} (z z0 : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (y : SpatialCoordinates d)
    (hy : y ∈ (closedCube z0 1 one_pos : Set (SpatialCoordinates d))) :
    cubeDilation z z0 r y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
  have hz : cubeDilation z z0 r z0 = z := by
    funext i
    simp [cubeDilation]
  change dist (cubeDilation z z0 r y) z ≤ r / 2
  change dist y z0 ≤ 1 / 2 at hy
  calc dist (cubeDilation z z0 r y) z = dist (cubeDilation z z0 r y) (cubeDilation z z0 r z0) := by
        rw [hz]
    _ = r * dist y z0 := aux_prop_growth_energy_assembly_dilation_dist z z0 hr y z0
    _ ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left hy hr.le
    _ = r / 2 := by ring

/-- The inverse dilation. -/
theorem aux_prop_growth_energy_assembly_dilation_inv {d : ℕ} (z z0 : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (x : SpatialCoordinates d) :
    cubeDilation z z0 r (cubeDilation z0 z r⁻¹ x) = x := by
  funext i
  simp only [cubeDilation]
  field_simp
  ring

/-- The pulled-back coefficient on the unit cube: its continuous representative, envelope and
logarithmic Lipschitz bound at the unit-cube wavelength `eps`. -/
theorem aux_prop_growth_energy_assembly_unit_coeff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Dv Mxv eps : ℝ) (hD0 : 0 ≤ Dv) (h3N : (3 : ℝ) ^ N * r ≤ eps⁻¹)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
        Dv * (3 : ℝ) ^ N * dist x y) :
    ∃ A1 : C(SpatialCoordinates d, ℝ),
      (∀ a1 : PositiveCoefficient (unitNeumannCube d),
        (∀ᵐ y ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
          (a1.val : SpatialCoordinates d → ℝ) y =
            ((cutoffPositiveCoefficient M H om N z hr).val : SpatialCoordinates d → ℝ)
              (cubeDilation z (fun _ => (1 / 2 : ℝ)) r y)) →
        a1.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A1) ∧
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        Mxv⁻¹ ≤ A1 y ∧ A1 y ≤ Mxv) ∧
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ y' ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A1 y) - Real.log (A1 y')| ≤ Dv / eps * dist y y') := by
  have hcl := aux_prop_growth_energy_assembly_closure_unit d
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  refine ⟨⟨fun y => cutoffCoefficient M H om N (cubeDilation z z0 r y),
    (cutoffCoefficient_continuous M H om N).comp (continuous_cubeDilation z z0 r)⟩, ?_, ?_, ?_⟩
  · intro a1 ha1
    have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
    have hcoef := aux_prop_growth_macro_energy_coeff_ae M H om N z hr
    filter_upwards [ha1, hq.ae hcoef] with y h1 h2
    rw [h1]
    exact h2
  · intro y hy
    rw [hcl] at hy
    exact henv _ (aux_prop_growth_energy_assembly_dilation_closed z z0 hr y hy)
  · intro y hy y' hy'
    rw [hcl] at hy hy'
    have h1 := hlip _ _ (aux_prop_growth_energy_assembly_dilation_closed z z0 hr y hy)
      (aux_prop_growth_energy_assembly_dilation_closed z z0 hr y' hy')
    rw [aux_prop_growth_energy_assembly_dilation_dist z z0 hr] at h1
    show |Real.log (cutoffCoefficient M H om N (cubeDilation z z0 r y)) -
        Real.log (cutoffCoefficient M H om N (cubeDilation z z0 r y'))| ≤ _
    have hdist : 0 ≤ dist y y' := dist_nonneg
    calc _ ≤ Dv * (3 : ℝ) ^ N * (r * dist y y') := h1
      _ = Dv * ((3 : ℝ) ^ N * r) * dist y y' := by ring
      _ ≤ Dv * eps⁻¹ * dist y y' := by gcongr
      _ = Dv / eps * dist y y' := by ring

/-- The microscopic range `2 rad < min(3^{-N}, r)`: transport to the unit cube, apply the
matched microscopic Dirichlet estimate with the parent energy from the macro bound, and scale
back. -/
theorem aux_prop_growth_energy_assembly_micro_branch {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t t1 C : ℝ) (ht0 : 0 ≤ t) (htt1 : t < t1) (ht1d : t1 < (d : ℝ)) (hC : 0 < C)
    (hmic : aux_prop_growth_energy_assembly_MicroLocal d t t1 C)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1)
    (Kmacv Dv Mxv : ℝ) (hK0 : 0 ≤ Kmacv) (hD0 : 0 ≤ Dv) (hMx : 0 < Mxv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
        Dv * (3 : ℝ) ^ N * dist x y)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u)
    (x : SpatialCoordinates d) (rad : ℝ) (hx : x ∈ centeredCube z r hr) (hrad0 : 0 < rad)
    (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1) (hw3 : (3 : ℝ) ^ N * w = 1)
    (hcw : 2 * rad < w) (hcr : 2 * rad < r)
    (hLall : ∀ ρ : ℝ, 0 < ρ →
      localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x ρ ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        Kmacv * (Kf + Cphi) ^ 2 * (max ρ w) ^ t1) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
      aux_prop_growth_energy_assembly_Cr d r t t1 C *
        ((1 + Dv) ^ t * w ^ (t1 - t) * Kmacv + Mxv * w ^ ((d : ℝ) + 2 - t) +
          Mxv * w ^ ((d : ℝ) - t) * (1 + Dv) ^ t) * (Kf + Cphi) ^ 2 * rad ^ t := by
  have hCphi0 : 0 ≤ Cphi :=
    (aux_prop_growth_energy_assembly_c2Norm_nonneg _ _).trans hCphi
  have hE0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have ht1 : 0 ≤ t1 := le_trans ht0 htt1.le
  have hKE : 0 ≤ Kmacv * (Kf + Cphi) ^ 2 := mul_nonneg hK0 hE0
  have hcl := aux_prop_growth_energy_assembly_closure_unit d
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  obtain ⟨eps, hepsdef⟩ : ∃ e : ℝ, e = min 1 (w / r) := ⟨_, rfl⟩
  have heps0 : 0 < eps := by rw [hepsdef]; exact lt_min one_pos (div_pos hw0 hr)
  have heps1 : eps ≤ 1 := by rw [hepsdef]; exact min_le_left _ _
  have hepsw : eps ≤ w / r := by rw [hepsdef]; exact min_le_right _ _
  have hre : r * eps ≤ w := by
    calc r * eps ≤ r * (w / r) := mul_le_mul_of_nonneg_left hepsw hr.le
      _ = w := by field_simp
  have h3N : (3 : ℝ) ^ N * r ≤ eps⁻¹ := by
    have h4 : (3 : ℝ) ^ N * r * eps ≤ 1 := by
      calc (3 : ℝ) ^ N * r * eps = (3 : ℝ) ^ N * (r * eps) := by ring
        _ ≤ (3 : ℝ) ^ N * w := mul_le_mul_of_nonneg_left hre (by positivity)
        _ = 1 := hw3
    calc (3 : ℝ) ^ N * r = (3 : ℝ) ^ N * r * eps / eps := by field_simp
      _ ≤ 1 / eps := div_le_div_of_nonneg_right h4 heps0.le
      _ = eps⁻¹ := one_div eps
  obtain ⟨A1, hA1ae, hAK, hlog1⟩ := aux_prop_growth_energy_assembly_unit_coeff M H om N z r hr
    Dv Mxv eps hD0 h3N henv hlip
  have htr := lem_as_regularity_affine_transport d M H om N z r hr
  obtain ⟨a1, ha1, hdir, -⟩ := htr
  obtain ⟨F1, phi1, b1, u1, -, hF1m, hF1b, -, hphi1, ⟨Cphi1, hc2, hCphi1le⟩, hb1,
    hsol1, -, -, -, hen⟩ := hdir F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have haA1 := hA1ae a1 ha1
  obtain ⟨f, hfm, hfb, hfeq⟩ := aux_prop_growth_energy_assembly_clamp
    (unitNeumannCube d : Set (SpatialCoordinates d)) F1 hF1m (r ^ 2 * Kf) (by positivity) hF1b
  have hsol' := aux_prop_growth_energy_assembly_dirichlet_congr a1 F1 f hfeq b1 u1 hsol1
  obtain ⟨x1, hx1def⟩ : ∃ y : SpatialCoordinates d, y = cubeDilation z0 z r⁻¹ x := ⟨_, rfl⟩
  have hTx1 : cubeDilation z z0 r x1 = x := by
    rw [hx1def]
    exact aux_prop_growth_energy_assembly_dilation_inv z z0 hr x
  have hx1 : x1 ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    have hpre := cubeDilation_preimage_centeredCube z z0 hr one_pos
    change x1 ∈ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))
    rw [← hpre, Set.mem_preimage, hTx1]
    exact hx
  have hCq0 : 0 ≤ (max (C / 2) 1) ^ t1 :=
    Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have hr2d : 0 ≤ r ^ ((2 : ℝ) - (d : ℝ)) := Real.rpow_nonneg hr.le _
  have hKm0 : 0 ≤ r ^ ((2 : ℝ) - (d : ℝ)) * (max (C / 2) 1) ^ t1 *
      (Kmacv * (Kf + Cphi) ^ 2) := by positivity
  have hK' : localGradientEnergy a1
      (s := Metric.ball x1 (C * eps / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (sobolevGradient (u1 : SobolevData (unitNeumannCube d))) ≤
        r ^ ((2 : ℝ) - (d : ℝ)) * (max (C / 2) 1) ^ t1 * (Kmacv * (Kf + Cphi) ^ 2) *
          eps ^ t1 := by
    rw [hen x1 (C * eps / 2) (by positivity), hTx1]
    have h1 := hLall (r * (C * eps / 2)) (by positivity)
    have h2 := aux_prop_growth_energy_assembly_kmac_bound w r C t1
      (Kmacv * (Kf + Cphi) ^ 2) hw0 hw1 hr hr1 hC ht1 hKE
    rw [← hepsdef] at h2
    calc r ^ ((2 : ℝ) - (d : ℝ)) * localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x (r * (C * eps / 2)) ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr)))
        ≤ r ^ ((2 : ℝ) - (d : ℝ)) * ((max (C / 2) 1) ^ t1 * (Kmacv * (Kf + Cphi) ^ 2) *
            eps ^ t1) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hr2d
      _ = _ := by ring
  have hr' : 0 < 2 * rad / r := by positivity
  have hr'e : 2 * rad / r ≤ eps := by
    rw [hepsdef]
    refine le_min ?_ ?_
    · rw [div_le_one hr]
      exact hcr.le
    · exact div_le_div_of_nonneg_right hcw.le hr.le
  have hMxi : 0 < Mxv⁻¹ := inv_pos.mpr hMx
  have hr2K : 0 ≤ r ^ 2 * Kf := by positivity
  have hfb' : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ r ^ 2 * Kf :=
    fun y _ => hfb y
  have hmicro := hmic eps heps0 heps1 a1 A1 haA1 Dv Mxv⁻¹ Mxv hD0 hMxi hAK hlog1
    f hfm (r ^ 2 * Kf) hr2K hfb' phi1 hphi1 b1 u1 hb1 hsol' x1 hx1 _ hKm0 hK'
    (2 * rad / r) hr' hr'e
  rw [inv_inv] at hmicro
  have hball : localGradientEnergy a1
      (s := Metric.ball x1 (2 * rad / r / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (sobolevGradient (u1 : SobolevData (unitNeumannCube d))) =
      localGradientEnergy a1
      (s := Metric.ball x1 (rad / r) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (sobolevGradient (u1 : SobolevData (unitNeumannCube d))) :=
    aux_prop_growth_energy_assembly_lge_congr a1 _ _
      (by rw [show 2 * rad / r / 2 = rad / r by ring]) _
  rw [hball] at hmicro
  have hphys := hen x1 (rad / r) (div_pos hrad0 hr)
  rw [hTx1, show r * (rad / r) = rad by field_simp] at hphys
  have hrr : r ^ ((d : ℝ) - 2) * r ^ ((2 : ℝ) - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]
    norm_num
  have hKh0 := aux_prop_growth_energy_assembly_c2Norm_nonneg
    (closure (unitNeumannCube d : Set (SpatialCoordinates d))) phi1
  have hKh : c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) phi1 ≤
      3 * Cphi := by
    rw [hcl]
    have hr2 : r ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hr1 hr.le hr1
    have h3 : 1 + r + r ^ 2 ≤ 3 := by linarith only [hr1, hr2]
    calc _ ≤ Cphi1 := hc2
      _ ≤ (1 + r + r ^ 2) * Cphi := hCphi1le
      _ ≤ 3 * Cphi := mul_le_mul_of_nonneg_right h3 hCphi0
  have hr2Kf : r ^ 2 * Kf ≤ Kf := by
    have hr2 : r ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hr1 hr.le hr1
    calc r ^ 2 * Kf ≤ 1 * Kf := mul_le_mul_of_nonneg_right hr2 hKf
      _ = Kf := one_mul _
  have hfin := aux_prop_growth_energy_assembly_micro_arith (d : ℝ) r w eps rad t t1 C
    ((max (C / 2) 1) ^ t1) Dv Kmacv Mxv Kf (r ^ 2 * Kf) Cphi
    (c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) phi1) _
    hr hw0 heps0 hepsw hrad0 htt1 (htt1.trans ht1d) hC.le hCq0 hD0 hK0 hMx.le hKf
    hr2K hr2Kf hCphi0 hKh0 hKh hmicro
  rw [hphys, ← mul_assoc, hrr, one_mul] at hfin
  exact hfin

/-- **Per-sample physical estimate.**  At one sample and one cutoff, the macro bound
(`rad ≥ 3^{-N}`), the coefficient envelope and the matched microscopic Dirichlet estimate on
the unit cube give the energy bound at every radius `0 < rad ≤ 1`, with an explicit constant
linear in the macro constant and in the three moment-clause quantities. -/
theorem aux_prop_growth_energy_assembly_physical {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t t1 C : ℝ) (ht0 : 0 ≤ t) (htt1 : t < t1) (ht1d : t1 < (d : ℝ)) (hC : 0 < C)
    (hmic : aux_prop_growth_energy_assembly_MicroLocal d t t1 C)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1)
    (Kmacv Dv Mxv : ℝ) (hK0 : 0 ≤ Kmacv) (hD0 : 0 ≤ Dv) (hMx : 0 < Mxv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
        Dv * (3 : ℝ) ^ N * dist x y)
    (hmacro : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ), ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 → (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            Kmacv * (Kf + Cphi) ^ 2 * rad ^ t1) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
        |F x| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ), ContDiff ℝ 2 phi →
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
      ∀ (x : SpatialCoordinates d) (rad : ℝ),
        x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
        localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
            (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
            (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
          ((2 / r) ^ t * Kmacv + aux_prop_growth_energy_assembly_Cr d r t t1 C *
            ((1 + Dv) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmacv +
              Mxv * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) +
              Mxv * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + Dv) ^ t)) *
            (Kf + Cphi) ^ 2 * rad ^ t := by
  intro F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  have hCphi0 : 0 ≤ Cphi :=
    (aux_prop_growth_energy_assembly_c2Norm_nonneg _ _).trans hCphi
  have hE0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have ht1 : 0 ≤ t1 := by linarith
  set w : ℝ := (3 : ℝ) ^ (-(N : ℝ)) with hwdef
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  have hwz : (3 : ℝ) ^ (-(N : ℤ)) = w := aux_prop_growth_energy_assembly_zpow_eq_rpow N
  have hw3 : (3 : ℝ) ^ N * w = 1 := by
    rw [hwdef, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    exact mul_inv_cancel₀ (by positivity)
  -- the local energy as a function of the radius
  set a := cutoffPositiveCoefficient M H om N z hr with ha
  set g := sobolevGradient (u : SobolevData (centeredCube z r hr)) with hg
  let L : ℝ → ℝ := fun ρ => localGradientEnergy a
    (s := Metric.ball x ρ ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet) g
  have hLmono : ∀ r1 r2 : ℝ, 0 < r1 → r1 ≤ r2 → L r1 ≤ L r2 := by
    intro r1 r2 _ h12
    exact SubdiffusiveProcess.Lane3.localGradientEnergy_mono a _ _
      (Set.inter_subset_inter_left _ (Metric.ball_subset_ball h12)) g
  have hLsat : ∀ ρ : ℝ, 1 ≤ ρ → L ρ ≤ L 1 := by
    intro ρ _
    refine SubdiffusiveProcess.Lane3.localGradientEnergy_mono a _ _ ?_ g
    intro y hy
    refine ⟨?_, hy.2⟩
    have hyz : dist y z < r / 2 := hy.2
    have hxz : dist x z < r / 2 := hx
    change dist y x < 1
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [dist_comm z x]; linarith
      _ ≤ 1 := by linarith
  have hLmac : ∀ ρ : ℝ, w ≤ ρ → ρ ≤ 1 → L ρ ≤ Kmacv * (Kf + Cphi) ^ 2 * ρ ^ t1 := by
    intro ρ hwρ hρ1
    exact hmacro F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x ρ hx
      (lt_of_lt_of_le hw0 hwρ) hρ1 (by rw [hwz]; exact hwρ)
  have hKE : 0 ≤ Kmacv * (Kf + Cphi) ^ 2 := mul_nonneg hK0 hE0
  have hLall := aux_prop_growth_energy_assembly_lmac L w (Kmacv * (Kf + Cphi) ^ 2) t1 hw1 hKE
    ht1 hLmono hLsat hLmac
  -- the two nonnegative pieces of the constant
  set Zs := (1 + Dv) ^ t * w ^ (t1 - t) * Kmacv + Mxv * w ^ ((d : ℝ) + 2 - t) +
    Mxv * w ^ ((d : ℝ) - t) * (1 + Dv) ^ t with hZs
  have hZs0 : 0 ≤ Zs := by
    have h1 : 0 ≤ (1 + Dv) ^ t := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ w ^ (t1 - t) := Real.rpow_nonneg hw0.le _
    have h3 : 0 ≤ w ^ ((d : ℝ) + 2 - t) := Real.rpow_nonneg hw0.le _
    have h4 : 0 ≤ w ^ ((d : ℝ) - t) := Real.rpow_nonneg hw0.le _
    have := hMx.le
    positivity
  have hCr0 := aux_prop_growth_energy_assembly_Cr_nonneg d r t t1 C hr hC.le
  have hradt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad0.le _
  have h2r : 0 ≤ (2 / r) ^ t := Real.rpow_nonneg (by positivity) _
  have hA0 : 0 ≤ (2 / r) ^ t * Kmacv * (Kf + Cphi) ^ 2 * rad ^ t := by positivity
  have hB0 : 0 ≤ aux_prop_growth_energy_assembly_Cr d r t t1 C * Zs * (Kf + Cphi) ^ 2 *
      rad ^ t := by positivity
  have hsplit : ((2 / r) ^ t * Kmacv + aux_prop_growth_energy_assembly_Cr d r t t1 C * Zs) *
      (Kf + Cphi) ^ 2 * rad ^ t =
      (2 / r) ^ t * Kmacv * (Kf + Cphi) ^ 2 * rad ^ t +
        aux_prop_growth_energy_assembly_Cr d r t t1 C * Zs * (Kf + Cphi) ^ 2 * rad ^ t := by
    ring
  change L rad ≤ _
  rw [hsplit]
  by_cases hcase : w ≤ 2 * rad ∨ r ≤ 2 * rad
  · -- macro range
    have h1 := hLall rad hrad0
    have h2 := aux_prop_growth_energy_assembly_case_macro w r rad t t1
      (Kmacv * (Kf + Cphi) ^ 2) hw1 hr hr1 hrad0 hrad1 ht0 htt1.le hKE hcase
    have h3 : (2 / r) ^ t * (Kmacv * (Kf + Cphi) ^ 2) * rad ^ t =
        (2 / r) ^ t * Kmacv * (Kf + Cphi) ^ 2 * rad ^ t := by ring
    linarith
  · -- microscopic range, through the unit cube
    push_neg at hcase
    obtain ⟨hcw, hcr⟩ := hcase
    exact le_add_of_nonneg_of_le hA0
      (aux_prop_growth_energy_assembly_micro_branch t t1 C ht0 htt1 ht1d hC hmic M H om N z r hr hr1
        Kmacv Dv Mxv hK0 hD0 hMx henv hlip F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
        x rad hx hrad0 w hw0 hw1 hw3 hcw hcr hLall)

/-- Choice of the microscopic integrability order. -/
theorem aux_prop_growth_energy_assembly_p1_choice (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (htd : t < (d : ℝ)) :
    ∃ p1 : ℝ, 2 ≤ p1 ∧ t < (d : ℝ) - 2 * (d : ℝ) / p1 := by
  have hdt : 0 < (d : ℝ) - t := by linarith
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨max 2 (2 * (d : ℝ) / ((d : ℝ) - t) + 1), le_max_left _ _, ?_⟩
  have hp : 2 * (d : ℝ) / ((d : ℝ) - t) < max 2 (2 * (d : ℝ) / ((d : ℝ) - t) + 1) :=
    lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hp0 : 0 < max 2 (2 * (d : ℝ) / ((d : ℝ) - t) + 1) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h1 : 2 * (d : ℝ) < ((d : ℝ) - t) * max 2 (2 * (d : ℝ) / ((d : ℝ) - t) + 1) := by
    rw [div_lt_iff₀ hdt] at hp
    linarith
  have h2 : 2 * (d : ℝ) / max 2 (2 * (d : ℝ) / ((d : ℝ) - t) + 1) < (d : ℝ) - t := by
    rw [div_lt_iff₀ hp0]
    exact h1
  linarith

/-- Small disorder keeps the extremes rate below the matched gain, uniformly below `delta0`. -/
theorem aux_prop_growth_energy_assembly_threshold (Cd Cp rmax dM cdq : ℝ) (hCd : 0 < Cd)
    (hCp : 0 < Cp) (hrmax : 0 < rmax) (hdM : 0 < dM) (hcdq : 0 < cdq) :
    ∃ delta0 aRate : ℝ, 0 < delta0 ∧ delta0 ≤ dM ∧ delta0 ≤ cdq ∧ 0 ≤ aRate ∧
      aRate < rmax ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ delta0 → Cd * δ + Cp * δ ^ 2 ≤ aRate := by
  have hs : 0 < rmax / (2 * (Cd + Cp)) := div_pos hrmax (by positivity)
  refine ⟨min dM (min cdq (min 1 (rmax / (2 * (Cd + Cp))))),
    Cd * min dM (min cdq (min 1 (rmax / (2 * (Cd + Cp))))) +
      Cp * (min dM (min cdq (min 1 (rmax / (2 * (Cd + Cp)))))) ^ 2,
    lt_min hdM (lt_min hcdq (lt_min one_pos hs)), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_, ?_, ?_⟩
  · have h0 : 0 < min dM (min cdq (min 1 (rmax / (2 * (Cd + Cp))))) :=
      lt_min hdM (lt_min hcdq (lt_min one_pos hs))
    positivity
  · set δ := min dM (min cdq (min 1 (rmax / (2 * (Cd + Cp))))) with hδ
    have h0 : 0 < δ := lt_min hdM (lt_min hcdq (lt_min one_pos hs))
    have h1 : δ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : δ ≤ rmax / (2 * (Cd + Cp)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have h3 : δ ^ 2 ≤ δ := by nlinarith
    have h4 : (Cd + Cp) * δ ≤ rmax / 2 := by
      have hpos : 0 < 2 * (Cd + Cp) := by positivity
      rw [le_div_iff₀ hpos] at h2
      nlinarith
    nlinarith
  · intro δ' h0 h1
    have h2 : δ' ^ 2 ≤ (min dM (min cdq (min 1 (rmax / (2 * (Cd + Cp)))))) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have h3 := mul_le_mul_of_nonneg_left h1 hCd.le
    have h4 := mul_le_mul_of_nonneg_left h2 hCp.le
    linarith

/-- Probability bookkeeping: one common majorant, at least one, dominating the macro constant
and the three microscopic moment-clause quantities, with all listed moments. -/
theorem aux_prop_growth_energy_assembly_final {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i)
    (t t1 dd c1 c2 CK : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hCK : 0 ≤ CK)
    (Kmac D Mx : ℕ → Ω → ℝ)
    (hKm : ∀ N, AEStronglyMeasurable (Kmac N) P) (hDm : ∀ N, AEStronglyMeasurable (D N) P)
    (hMm : ∀ N, AEStronglyMeasurable (Mx N) P)
    (hKmom : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal CK)
    (hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        eLpNorm (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
          (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t))
          (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t)
          (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal B) :
    ∃ (K : ℕ → Ω → ℝ) (Cbound : Fin k → ℝ),
      (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) P) ∧
      (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (Cbound i)) ∧
      (∀ N o, 1 ≤ K N o) ∧
      (∀ N o, c1 * Kmac N o +
        c2 * ((1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o +
          Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t) +
          Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t) ≤ K N o) := by
  choose B hB0 hBb using hB
  let f0 : ℕ → Ω → ℝ := fun _ _ => 1
  let f1 : ℕ → Ω → ℝ := fun N o => c1 * Kmac N o
  let f2 : ℕ → Ω → ℝ := fun N o =>
    c2 * ((1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
  let f3 : ℕ → Ω → ℝ := fun N o => c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t))
  let f4 : ℕ → Ω → ℝ := fun N o =>
    c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t)
  let X : Fin 5 → ℕ → Ω → ℝ := ![f0, f1, f2, f3, f4]
  let Bm : Fin 5 → Fin k → ℝ := ![fun _ => 1, fun _ => c1 * CK, fun i => c2 * B i,
    fun i => c2 * B i, fun i => c2 * B i]
  have hscal : ∀ (s : ℝ) (hs : 0 ≤ s) (g : Ω → ℝ) (i : Fin k) (Bg : ℝ),
      eLpNorm g (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal Bg →
      eLpNorm (fun o => s * g o) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (s * Bg) := by
    intro s hs g i Bg hg
    rw [aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm P (ps i) s hs g,
      ENNReal.ofReal_mul hs]
    gcongr
  have hmemOf : ∀ (g : Ω → ℝ) (i : Fin k) (Bg : ℝ), AEStronglyMeasurable g P →
      eLpNorm g (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal Bg →
      MemLp g (ENNReal.ofReal (ps i)) P :=
    fun g i Bg hg hb => lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  have hwm : ∀ (N : ℕ) (s : ℝ), AEStronglyMeasurable
      (fun _ : Ω => ((3 : ℝ) ^ (-(N : ℝ))) ^ s) P := fun _ _ => aestronglyMeasurable_const
  have hm2 : ∀ N, AEStronglyMeasurable
      (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o) P := by
    intro N
    exact ((((hDm N).aemeasurable.const_add 1).pow_const t).mul_const _).mul
      (hKm N).aemeasurable |>.aestronglyMeasurable
  have hm3 : ∀ N, AEStronglyMeasurable
      (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t)) P := by
    intro N
    exact ((hMm N).aemeasurable.mul_const _).aestronglyMeasurable
  have hm4 : ∀ N, AEStronglyMeasurable
      (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t) P := by
    intro N
    exact (((hMm N).aemeasurable.mul_const _).mul
      (((hDm N).aemeasurable.const_add 1).pow_const t)).aestronglyMeasurable
  have hn0 : ∀ i N, eLpNorm (f0 N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal 1 := by
    intro i N
    have hp0 : ENNReal.ofReal (ps i) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith [hps i]
    change eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal 1
    rw [eLpNorm_const _ hp0 (NeZero.ne P)]
    simp
  have hn1 : ∀ i N, eLpNorm (f1 N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (c1 * CK) :=
    fun i N => hscal c1 hc1 (Kmac N) i CK (hKmom i N)
  have hn2 : ∀ i N, eLpNorm (f2 N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (c2 * B i) :=
    fun i N => hscal c2 hc2 _ i (B i) (hBb i N).1
  have hn3 : ∀ i N, eLpNorm (f3 N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (c2 * B i) :=
    fun i N => hscal c2 hc2 _ i (B i) (hBb i N).2.1
  have hn4 : ∀ i N, eLpNorm (f4 N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (c2 * B i) :=
    fun i N => hscal c2 hc2 _ i (B i) (hBb i N).2.2
  have hXnorm : ∀ j i N, eLpNorm (X j N) (ENNReal.ofReal (ps i)) P ≤
      ENNReal.ofReal (Bm j i) := by
    intro j i N
    fin_cases j
    · exact hn0 i N
    · exact hn1 i N
    · exact hn2 i N
    · exact hn3 i N
    · exact hn4 i N
  have hXmem : ∀ j i N, MemLp (X j N) (ENNReal.ofReal (ps i)) P := by
    intro j i N
    fin_cases j
    · exact hmemOf _ i _ aestronglyMeasurable_const (hn0 i N)
    · exact hmemOf _ i _ ((hKm N).const_mul c1) (hn1 i N)
    · exact hmemOf _ i _ ((hm2 N).const_mul c2) (hn2 i N)
    · exact hmemOf _ i _ ((hm3 N).const_mul c2) (hn3 i N)
    · exact hmemOf _ i _ ((hm4 N).const_mul c2) (hn4 i N)
  have hBm : ∀ j i, 0 ≤ Bm j i := by
    intro j i
    fin_cases j
    · exact zero_le_one
    · exact mul_nonneg hc1 hCK
    · exact mul_nonneg hc2 (hB0 i)
    · exact mul_nonneg hc2 (hB0 i)
    · exact mul_nonneg hc2 (hB0 i)
  obtain ⟨Kb, Cb, _hKb0, hKbX, hKbmem, hKbnorm⟩ :=
    prop_growth_common_moment_bank Ω P 5 k ps hps X Bm hBm hXmem hXnorm
  refine ⟨fun N o => 4 * Kb N o, fun i => 4 * Cb i, ?_, ?_, ?_, ?_⟩
  · intro i N
    exact (hKbmem i N).const_mul 4
  · intro i N
    rw [aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm P (ps i) 4 (by norm_num) (Kb N),
      ENNReal.ofReal_mul (by norm_num)]
    gcongr
    exact hKbnorm i N
  · intro N o
    have h := hKbX 0 N o
    change |(1 : ℝ)| ≤ Kb N o at h
    rw [abs_one] at h
    linarith
  · intro N o
    have h1 := hKbX 1 N o
    have h2 := hKbX 2 N o
    have h3 := hKbX 3 N o
    have h4 := hKbX 4 N o
    change |c1 * Kmac N o| ≤ Kb N o at h1
    change |c2 * ((1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)| ≤
      Kb N o at h2
    change |c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t))| ≤ Kb N o at h3
    change |c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t)| ≤
      Kb N o at h4
    have e1 := le_abs_self (c1 * Kmac N o)
    have e2 := le_abs_self (c2 * ((1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) *
      Kmac N o))
    have e3 := le_abs_self (c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t)))
    have e4 := le_abs_self (c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) *
      (1 + D N o) ^ t))
    have hsplit : c1 * Kmac N o +
        c2 * ((1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o +
          Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t) +
          Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t) =
        c1 * Kmac N o +
          c2 * ((1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o) +
          c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd + 2 - t)) +
          c2 * (Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ (dd - t) * (1 + D N o) ^ t) := by ring
    rw [hsplit]
    linarith

/-- A doubled random variable, moved down to a lower moment order. -/
theorem aux_prop_growth_energy_assembly_double {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (q Q c : ℝ) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hf : AEStronglyMeasurable f P) (hc : 0 ≤ c)
    (hb : eLpNorm f (ENNReal.ofReal Q) P ≤ ENNReal.ofReal c) :
    eLpNorm (fun o => f o + f o) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (2 * c) := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have h1 : eLpNorm f (ENNReal.ofReal q) P ≤ ENNReal.ofReal c :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqQ)).trans hb
  calc eLpNorm (fun o => f o + f o) (ENNReal.ofReal q) P
      ≤ eLpNorm f (ENNReal.ofReal q) P + eLpNorm f (ENNReal.ofReal q) P :=
        eLpNorm_add_le hq1
    _ ≤ ENNReal.ofReal c + ENNReal.ofReal c := add_le_add h1 h1
    _ = ENNReal.ofReal (2 * c) := by rw [← ENNReal.ofReal_add hc hc]; ring_nf



theorem prop_growth_energy_assembly :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d) (_S : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 →
    (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t := by

  intro d hd _ _ E P X W Cp S t alpha k ps ht htd halp halt hps
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨p1, hp1, hp1t⟩ := aux_prop_growth_energy_assembly_p1_choice d hd t htd
  obtain ⟨t1, ht1def⟩ : ∃ s : ℝ, s = (t + d) / 2 := ⟨_, rfl⟩
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < d := by rw [ht1def]; linarith
  obtain ⟨C, hC, hmic, hmom⟩ :=
    aux_prop_growth_energy_assembly_micro_local d hd W p1 t t1 hp1 ht htt1 ht1d hp1t
  obtain ⟨Q0, hQ0def⟩ : ∃ q : ℝ, q = 2 * (1 + ∑ i, ps i) * max 1 t := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg (fun i _ => le_trans zero_le_one (hps i))
  have hmax1 : 1 ≤ max 1 t := le_max_left _ _
  have hQ0 : 1 ≤ Q0 := by
    rw [hQ0def]
    have h1 : 1 ≤ 2 * (1 + ∑ i, ps i) := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * (1 + ∑ i, ps i) * max 1 t := mul_le_mul h1 hmax1 zero_le_one (by linarith)
  have hqi : ∀ i, 2 * ps i * max 1 t ≤ Q0 := by
    intro i
    rw [hQ0def]
    have h1 : ps i ≤ 1 + ∑ j, ps j := by
      have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j))
        (Finset.mem_univ i)
      linarith
    have h2 : 2 * ps i ≤ 2 * (1 + ∑ j, ps j) := by linarith
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd Q0 hQ0
  obtain ⟨dM, hdM, hmacro⟩ := prop_growth_macro_energy d hd E P X S t1 1 (fun _ => Q0)
    (by linarith) ht1d (fun _ => hQ0)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrmax : 0 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := by
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))) hlog3
  obtain ⟨delta0, aRate, hδ0, hδM, hδc, haR0, haR, hmono⟩ :=
    aux_prop_growth_energy_assembly_threshold Cd Cpe _ dM (cd / (2 * Q0)) hCd hCpe hrmax hdM
      (by positivity)
  refine ⟨delta0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hr1
  obtain ⟨Kmac, CbM, hKmac0, hKmem, hKnorm, hKae⟩ :=
    hmacro M Rm Sreg It H hH (hδ.trans hδM) z r hr hr1
  obtain ⟨D, Mx, CE, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ :=
    hroot M H hH (hδ.trans hδc) z r hr hr1
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ aRate :=
    hmono _ M.shellPrefix.delta_pos.le hδ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      eLpNorm (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N o) ^ t)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    intro i
    have hle : ENNReal.ofReal (2 * ps i * max 1 t) ≤ ENNReal.ofReal Q0 :=
      ENNReal.ofReal_le_ofReal (hqi i)
    have hqi1 : 1 ≤ 2 * ps i * max 1 t := by
      have := hps i
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * ps i * max 1 t := mul_le_mul (by linarith) hmax1 zero_le_one (by linarith)
    have hMxN : ∀ N : ℕ, eLpNorm (fun o => Mx N o + Mx N o)
        (ENNReal.ofReal (2 * ps i * max 1 t)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * CE * Real.exp (aRate * (N : ℝ))) := by
      intro N
      have h1 := aux_prop_growth_energy_assembly_double (chaosSampleLaw M).toMeasure (Mx N)
        (2 * ps i * max 1 t) Q0 (CE * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N))
        hqi1 (hqi i) (hmem N).2.aestronglyMeasurable (by positivity) (hMxmom N)
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have he : Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N) ≤
          Real.exp (aRate * (N : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate hN)
      have := mul_le_mul_of_nonneg_left he hCE
      linarith
    exact hmom (BilateralField d) (chaosSampleLaw M).toMeasure (ps i) (hps i) D Mx Mx Kmac
      Cpe (2 * CE) (max (CbM 0) 0) aRate hCpe.le (by positivity) (le_max_right _ _) haR0 haR
      (fun N o => ⟨(hDMx0 N o).1, (hDMx0 N o).2, (hDMx0 N o).2, hKmac0 N o⟩)
      (fun N => ⟨(hmem N).1.mono_exponent hle, (hmem N).2.mono_exponent hle,
        (hmem N).2.mono_exponent hle, (hKmem 0 N).mono_exponent hle⟩)
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans (hDmom N))
      hMxN
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans
        ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  have hKps : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (max (CbM 0) 0) := by
    intro i N
    have hle : ENNReal.ofReal (ps i) ≤ ENNReal.ofReal Q0 := by
      refine ENNReal.ofReal_le_ofReal ?_
      have := hqi i
      have h2 : ps i ≤ 2 * ps i * max 1 t := by
        have hp := hps i
        calc ps i = ps i * 1 * 1 := by ring
          _ ≤ ps i * 2 * max 1 t := by
            apply mul_le_mul _ hmax1 zero_le_one (by linarith)
            exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
          _ = 2 * ps i * max 1 t := by ring
      linarith
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle).trans
      ((hKnorm 0 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have h2r : 0 ≤ (2 / r) ^ t := Real.rpow_nonneg (by positivity) _
  obtain ⟨K, Cbound, hKmem', hKnorm', hK1, hKdom⟩ :=
    aux_prop_growth_energy_assembly_final (chaosSampleLaw M).toMeasure k ps hps t t1 (d : ℝ)
      ((2 / r) ^ t) (aux_prop_growth_energy_assembly_Cr d r t t1 C) (max (CbM 0) 0) h2r
      (aux_prop_growth_energy_assembly_Cr_nonneg d r t t1 C hr hC.le) (le_max_right _ _)
      Kmac D Mx (fun N => (hKmem 0 N).aestronglyMeasurable) (fun N => (hmem N).1.aestronglyMeasurable) (fun N => (hmem N).2.aestronglyMeasurable)
      hKps hB
  refine ⟨K, Cbound, hKmem', hKnorm', Filter.Eventually.of_forall (fun om N => hK1 N om), ?_⟩
  filter_upwards [hKae, hae] with om hmac hen
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  obtain ⟨hMxpos, henvN, hlipN⟩ := hen N
  have hphys := aux_prop_growth_energy_assembly_physical t t1 C ht0 htt1 ht1d hC hmic M H om N
    z r hr hr1 (Kmac N om) (D N om) (Mx N om) (hKmac0 N om) (hDMx0 N om).1 hMxpos henvN hlipN
    (hmac N) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  refine hphys.trans ?_
  have hE : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hradt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad0.le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hKdom N om) hE) hradt

end Paper
