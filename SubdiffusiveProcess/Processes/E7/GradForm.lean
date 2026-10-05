module

public import SubdiffusiveProcess.DirichletForm.Regular
public import SubdiffusiveProcess.DirichletForm.Resolvent
public import Mathlib

@[expose] public section

/-!
# The closure of the smooth weighted gradient form

For continuous positive `c, ρ` on `ℝ^d` let `E₀(φ, ψ) = ∫ c ∇φ·∇ψ dx` on smooth compactly supported
functions, viewed in `L²(ρ dx)`. This file builds the closure `E` as a `ClosedForm` on
`L²(ρ dx)`: the graph `{([φ], ∇φ)}` is closed up in `L²(ρ) × L²(c)^d`, closability is proved by
integration by parts, and the form of an element of the domain is the norm of its gradient.
-/
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- Euclidean-space carrier `ℝ^d` (sup metric, product Lebesgue measure). -/
abbrev St (d : ℕ) := Fin d → ℝ

/-- Lebesgue measure with density `w`. -/
def wm (w : St d → ℝ) : Measure (St d) := volume.withDensity fun x => ENNReal.ofReal (w x)

/-- Smooth compactly supported functions. -/
def testFns (d : ℕ) : Submodule ℝ (St d → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun _a _ hφ => ⟨contDiff_const.smul hφ.1, hφ.2.smul_left⟩

/-- The `i`-th classical partial derivative. -/
def dpartial (i : Fin d) (φ : St d → ℝ) : St d → ℝ := fun x => fderiv ℝ φ x (Pi.single i 1)

theorem isLocallyFiniteMeasure_wm {w : St d → ℝ} (hw : Continuous w) :
    IsLocallyFiniteMeasure (wm w) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hw.continuousOn
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  rw [wm, MeasureTheory.withDensity_apply _ measurableSet_ball]
  calc ∫⁻ y in Metric.ball x 1, ENNReal.ofReal (w y) ∂volume
      ≤ ∫⁻ y in Metric.ball x 1, ENNReal.ofReal C ∂volume := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_ball
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        have h1 : ‖w y‖ ≤ C := hC y (Metric.ball_subset_closedBall hy)
        calc w y ≤ |w y| := le_abs_self _
          _ = ‖w y‖ := (Real.norm_eq_abs _).symm
          _ ≤ C := h1
    _ = ENNReal.ofReal C * volume (Metric.ball x 1) := MeasureTheory.setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- Sets are `wm w`-null exactly when they are Lebesgue-null, for a positive continuous weight. -/
theorem wm_null_iff {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x) (s : Set (St d)) :
    wm w s = 0 ↔ volume s = 0 := by
  constructor
  · intro h
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal (w x)) volume :=
      (ENNReal.measurable_ofReal.comp hw.measurable).aemeasurable
    have hz := (MeasureTheory.withDensity_apply_eq_zero' hmeas (s := s)).mp h
    have hset : {x | ENNReal.ofReal (w x) ≠ 0} ∩ s = s := by
      ext x
      simp only [Set.mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro hx; exact hx.2
      · intro hx; exact ⟨ne_of_gt (ENNReal.ofReal_pos.mpr (hpos x)), hx⟩
    rwa [hset] at hz
  · intro h
    exact (MeasureTheory.withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (w x))) h

theorem ae_volume_of_ae_wm {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {p : St d → Prop} (h : ∀ᵐ x ∂(wm w), p x) : ∀ᵐ x ∂(volume : Measure (St d)), p x := by
  rw [MeasureTheory.ae_iff] at h ⊢
  rw [wm_null_iff hw hpos] at h
  exact h

theorem ae_wm_of_ae_volume {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    {p : St d → Prop} (h : ∀ᵐ x ∂(volume : Measure (St d)), p x) : ∀ᵐ x ∂(wm w), p x := by
  rw [MeasureTheory.ae_iff] at h ⊢
  exact (wm_null_iff hw hpos {x | ¬ p x}).mpr h

theorem memLp_wm_of_test {w : St d → ℝ} (hw : Continuous w) {φ : St d → ℝ}
    (hφ : φ ∈ testFns d) : MemLp φ 2 (wm w) := by
  have : IsLocallyFiniteMeasure (wm w) := isLocallyFiniteMeasure_wm hw
  have : IsFiniteMeasureOnCompacts (wm w) := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  exact hφ.1.continuous.memLp_of_hasCompactSupport hφ.2

theorem memLp_wm_dpartial {w : St d → ℝ} (hw : Continuous w) {φ : St d → ℝ}
    (hφ : φ ∈ testFns d) (i : Fin d) : MemLp (dpartial i φ) 2 (wm w) := by
  refine memLp_wm_of_test hw ⟨?_, ?_⟩
  · unfold dpartial
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : St d × St d => (fderiv ℝ φ p.1) p.2) :=
      ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) (f := φ) hφ.1 (by simp)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : St d => (x, (Pi.single i (1 : ℝ) : St d))) := by
      fun_prop
    exact h1.comp h2
  · unfold dpartial
    exact hφ.2.fderiv_apply ℝ (Pi.single i 1)

theorem dpartial_mem_test_cont {φ : St d → ℝ} (hφ : φ ∈ testFns d) (i : Fin d) :
    Continuous (dpartial i φ) := by
  unfold dpartial
  have h : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by norm_num)
  exact h.clm_apply continuous_const

/-- The ambient space of the graph. -/
abbrev GSpace (c ρ : St d → ℝ) := Lp ℝ 2 (wm ρ) × (Fin d → Lp ℝ 2 (wm c))

/-- The graph point of a smooth compactly supported function. -/
def testToG {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) (φ : testFns d) :
    GSpace c ρ :=
  ((memLp_wm_of_test hρ φ.2).toLp φ,
    fun i => (memLp_wm_dpartial hc φ.2 i).toLp (dpartial i φ))

theorem testToG_add {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) (φ ψ : testFns d) :
    testToG hc hρ (φ + ψ) = testToG hc hρ φ + testToG hc hρ ψ := by
  unfold testToG
  apply Prod.ext
  · simp only [Prod.fst_add]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_wm_of_test hρ (φ + ψ).2),
      Lp.coeFn_add ((memLp_wm_of_test hρ φ.2).toLp (φ : St d → ℝ))
        ((memLp_wm_of_test hρ ψ.2).toLp (ψ : St d → ℝ)),
      MemLp.coeFn_toLp (memLp_wm_of_test hρ φ.2),
      MemLp.coeFn_toLp (memLp_wm_of_test hρ ψ.2)] with x h1 h2 h3 h4
    rw [h1]
    simp only [h2, Pi.add_apply]
    rw [h3, h4]
    simp only [Submodule.coe_add, Pi.add_apply]
  · simp only [Prod.snd_add]
    funext i
    simp only [Pi.add_apply]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_wm_dpartial hc (φ + ψ).2 i),
      Lp.coeFn_add ((memLp_wm_dpartial hc φ.2 i).toLp (dpartial i φ))
        ((memLp_wm_dpartial hc ψ.2 i).toLp (dpartial i ψ)),
      MemLp.coeFn_toLp (memLp_wm_dpartial hc φ.2 i),
      MemLp.coeFn_toLp (memLp_wm_dpartial hc ψ.2 i)] with x h1 h2 h3 h4
    rw [h1]
    simp only [h2, Pi.add_apply]
    rw [h3, h4]
    unfold dpartial
    simp only [Submodule.coe_add]
    rw [fderiv_add (φ.2.1.differentiable (by simp)).differentiableAt
      (ψ.2.1.differentiable (by simp)).differentiableAt]
    simp

theorem testToG_smul {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) (a : ℝ)
    (φ : testFns d) : testToG hc hρ (a • φ) = a • testToG hc hρ φ := by
  apply Prod.ext
  · simpa only [Submodule.coe_smul] using! (memLp_wm_of_test hρ φ.2).toLp_const_smul a
  · funext i
    simp only [testToG, Prod.smul_snd, Pi.smul_apply]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_wm_dpartial hc (a • φ).2 i),
      MemLp.coeFn_toLp (memLp_wm_dpartial hc φ.2 i),
      Lp.coeFn_smul a ((memLp_wm_dpartial hc φ.2 i).toLp (dpartial i ↑φ))] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2]
    simp only [dpartial]
    rw [Submodule.coe_smul]
    rw [fderiv_const_smul ((φ.2.1).differentiable (by simp)).differentiableAt]
    rw [smul_apply]

/-- The linear map onto the graph points. -/
def testToGLin {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) :
    testFns d →ₗ[ℝ] GSpace c ρ where
  toFun := testToG hc hρ
  map_add' := testToG_add hc hρ
  map_smul' := testToG_smul hc hρ

/-- The closed graph. -/
def gradGraph {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) :
    Submodule ℝ (GSpace c ρ) := (LinearMap.range (testToGLin hc hρ)).topologicalClosure

theorem isClosed_gradGraph {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) :
    IsClosed (gradGraph hc hρ : Set (GSpace c ρ)) := Submodule.isClosed_topologicalClosure _

theorem memLp_wm_of_cont_compact {w : St d → ℝ} (hw : Continuous w) {a : St d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) : MemLp a 2 (wm w) := by
  have : IsLocallyFiniteMeasure (wm w) := isLocallyFiniteMeasure_wm hw
  exact ha.memLp_of_hasCompactSupport hac

/-- The `L²(w)` vector representing the pairing `f ↦ ∫ a f dx`. -/
def pairVec {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x) {a : St d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) : Lp ℝ 2 (wm w) :=
  (memLp_wm_of_cont_compact hw (a := fun x => a x / w x)
    (ha.div hw fun x => (hpos x).ne') (by simpa [div_eq_mul_inv] using! hac.mul_right)).toLp
      (fun x => a x / w x)

theorem pairVec_inner {w : St d → ℝ} (hw : Continuous w) (hpos : ∀ x, 0 < w x) {a : St d → ℝ}
    (ha : Continuous a) (hac : HasCompactSupport a) (f : Lp ℝ 2 (wm w)) :
    inner ℝ (pairVec hw hpos ha hac) f = ∫ x, a x * f x := by
  rw [L2.inner_def]
  have hcoe : (fun x => pairVec hw hpos ha hac x) =ᵐ[wm w] (fun x => a x / w x) := by
    unfold pairVec
    exact MemLp.coeFn_toLp _
  have step1 : ∫ x, inner ℝ (pairVec hw hpos ha hac x) (f x) ∂wm w
      = ∫ x, inner ℝ (a x / w x) (f x) ∂wm w := by
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx]
  have step2 : ∫ x, inner ℝ (a x / w x) (f x) ∂wm w
      = ∫ x, (ENNReal.ofReal (w x)).toReal • inner ℝ (a x / w x) (f x) ∂volume := by
    show ∫ x, inner ℝ (a x / w x) (f x) ∂volume.withDensity (fun x => ENNReal.ofReal (w x)) = _
    exact integral_withDensity_eq_integral_toReal_smul
      (ENNReal.measurable_ofReal.comp hw.measurable)
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))
      (fun x => inner ℝ (a x / w x) (f x))
  have step3 : ∫ x, (ENNReal.ofReal (w x)).toReal • inner ℝ (a x / w x) (f x) ∂volume
      = ∫ x, a x * f x := by
    apply integral_congr_ae
    filter_upwards with x
    have hreal : inner ℝ (a x / w x) (f x) = (a x / w x) * f x := by
      rw [RCLike.inner_apply]
      simp [mul_comm]
    have hw0 : w x ≠ 0 := ne_of_gt (hpos x)
    rw [hreal, ENNReal.toReal_ofReal (le_of_lt (hpos x)), smul_eq_mul]
    field_simp
  rw [step1, step2, step3]

theorem integral_by_parts_test {φ ψ : St d → ℝ} (hφ : φ ∈ testFns d) (hψ : ψ ∈ testFns d)
    (i : Fin d) : ∫ x, φ x * dpartial i ψ x = -∫ x, dpartial i φ x * ψ x := by
  have hφc : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ := hψ.1
  have hφcs : HasCompactSupport φ := hφ.2
  have hψcs : HasCompactSupport ψ := hψ.2
  set v : St d := Pi.single i 1 with hv
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφc.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψc.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have h1 : Integrable (fun x => fderiv ℝ φ x v * ψ x) :=
    (hdφ.mul hψc.continuous).integrable_of_hasCompactSupport (hφcs.fderiv_apply ℝ v).mul_right
  have h2 : Integrable (fun x => φ x * fderiv ℝ ψ x v) :=
    (hφc.continuous.mul hdψ).integrable_of_hasCompactSupport hφcs.mul_right
  have h3 : Integrable (fun x => φ x * ψ x) :=
    (hφc.continuous.mul hψc.continuous).integrable_of_hasCompactSupport hφcs.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (St d))) (v := v) h1 h2 h3
    (fun x _ => hφc.differentiable (by simp) x) (fun x _ => hψc.differentiable (by simp) x)
  simpa [dpartial, hv] using hibp

theorem eq_zero_of_pairing_zero {c : St d → ℝ} (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (g : Lp ℝ 2 (wm c))
    (h : ∀ ψ ∈ testFns d, ∫ x, ψ x * g x = 0) : g = 0 := by
  have hloc : LocallyIntegrable (fun x => (g : St d → ℝ) x) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    simp only [IntegrableOn]
    by_cases hne : K.Nonempty
    · obtain ⟨x₀, _, hx₀min⟩ := hK.exists_isMinOn hne hc.continuousOn
      set m : ℝ := c x₀ with hm
      have hmpos : 0 < m := by rw [hm]; exact hcpos x₀
      have hmin : ∀ y ∈ K, m ≤ c y := fun y hy => by rw [hm]; exact hx₀min hy
      have hle : volume.restrict K ≤ (ENNReal.ofReal m)⁻¹ • wm c := by
        rw [Measure.le_iff]
        intro s hs
        rw [wm, Measure.restrict_apply hs, Measure.smul_apply, withDensity_apply _ hs,
          smul_eq_mul]
        calc volume (s ∩ K) = ∫⁻ y in s ∩ K, (1 : ℝ≥0∞) ∂volume :=
              (setLIntegral_one _).symm
          _ ≤ ∫⁻ y in s ∩ K, (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal (c y) ∂volume := by
              apply setLIntegral_mono' (hs.inter hK.measurableSet)
              intro y hy
              rw [← ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hmpos).ne'
                ENNReal.ofReal_ne_top]
              exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hmin y hy.2)) _
          _ ≤ ∫⁻ y in s, (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal (c y) ∂volume :=
              lintegral_mono_set inter_subset_left
          _ = (ENNReal.ofReal m)⁻¹ * ∫⁻ y in s, ENNReal.ofReal (c y) ∂volume := by
              rw [lintegral_const_mul]
              exact ENNReal.measurable_ofReal.comp hc.measurable
      have : IsFiniteMeasure (volume.restrict K) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
      have hmem' : MemLp (fun x => (g : St d → ℝ) x) 2 (volume.restrict K) :=
        MemLp.of_measure_le_smul
          (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hmpos).ne') hle
          (by simpa using Lp.memLp g)
      exact hmem'.integrable (by norm_num)
    · rw [not_nonempty_iff_eq_empty.mp hne, Measure.restrict_empty]
      exact integrable_zero_measure
  have hzero : ∀ᵐ x ∂(volume : Measure (St d)), (g : St d → ℝ) x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro ψ hψdiff hψsupp
    have hmem : ψ ∈ testFns d := ⟨hψdiff, hψsupp⟩
    simpa [smul_eq_mul] using h ψ hmem
  have hzero_wm : ∀ᵐ x ∂(wm c), (g : St d → ℝ) x = 0 :=
    ae_wm_of_ae_volume hc hcpos hzero
  apply Lp.ext
  filter_upwards [hzero_wm, Lp.coeFn_zero ℝ 2 (wm c)] with x hx hx0
  simpa using hx.trans hx0.symm

/-- **Closability**: a graph point over the zero function has zero gradient. -/
theorem gradGraph_pairing {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {ψ : St d → ℝ} (hψ : ψ ∈ testFns d)
    (i : Fin d) (z : GSpace c ρ) (hz : z ∈ gradGraph hc hρ) :
    (∫ x, dpartial i ψ x * z.1 x) + ∫ x, ψ x * z.2 i x = 0 := by
  have hψ_cont : Continuous ψ := hψ.1.continuous
  have hψ_cs : HasCompactSupport ψ := hψ.2
  have hdψ_cs : HasCompactSupport (dpartial i ψ) := by
    unfold dpartial
    exact HasCompactSupport.comp_left (g := fun (f : St d →L[ℝ] ℝ) => f (Pi.single i 1))
      (HasCompactSupport.fderiv ℝ hψ_cs) (by simp)
  let L1 : GSpace c ρ →L[ℝ] ℝ :=
    (innerSL ℝ (pairVec hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs)).comp
      (ContinuousLinearMap.fst ℝ _ _)
  let L2 : GSpace c ρ →L[ℝ] ℝ :=
    (innerSL ℝ (pairVec hc hcpos hψ_cont hψ_cs)).comp
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))
  let L : GSpace c ρ →L[ℝ] ℝ := L1 + L2
  have hLz : L z = inner ℝ (pairVec hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs) z.1
      + inner ℝ (pairVec hc hcpos hψ_cont hψ_cs) (z.2 i) := by
    dsimp only [L, L1, L2]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, innerSL_apply_apply]
    rfl
  have hpair : ∀ φ : testFns d,
      L (testToGLin hc hρ φ) =
        (∫ x, dpartial i ψ x * (φ : St d → ℝ) x)
          + (∫ x, ψ x * dpartial i (φ : St d → ℝ) x) := by
    intro φ
    have hL : L (testToGLin hc hρ φ) =
        inner ℝ (pairVec hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs)
          ((memLp_wm_of_test hρ φ.2).toLp (φ : St d → ℝ))
        + inner ℝ (pairVec hc hcpos hψ_cont hψ_cs)
          ((memLp_wm_dpartial hc φ.2 i).toLp (dpartial i (φ : St d → ℝ))) := by
      dsimp only [L, L1, L2, testToGLin, testToG]
      rfl
    have h1 : inner ℝ (pairVec hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs)
          ((memLp_wm_of_test hρ φ.2).toLp (φ : St d → ℝ))
        = ∫ x, dpartial i ψ x * (φ : St d → ℝ) x := by
      calc inner ℝ (pairVec hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs)
            ((memLp_wm_of_test hρ φ.2).toLp (φ : St d → ℝ))
          = ∫ x, dpartial i ψ x *
              (((memLp_wm_of_test hρ φ.2).toLp (φ : St d → ℝ)) : St d → ℝ) x :=
            pairVec_inner hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs _
        _ = ∫ x, dpartial i ψ x * (φ : St d → ℝ) x := by
            refine integral_congr_ae ?_
            filter_upwards [ae_volume_of_ae_wm hρ hρpos
              (MemLp.coeFn_toLp (memLp_wm_of_test hρ φ.2))] with x hx
            rw [hx]
    have h2 : inner ℝ (pairVec hc hcpos hψ_cont hψ_cs)
          ((memLp_wm_dpartial hc φ.2 i).toLp (dpartial i (φ : St d → ℝ)))
        = ∫ x, ψ x * dpartial i (φ : St d → ℝ) x := by
      calc inner ℝ (pairVec hc hcpos hψ_cont hψ_cs)
            ((memLp_wm_dpartial hc φ.2 i).toLp (dpartial i (φ : St d → ℝ)))
          = ∫ x, ψ x *
              (((memLp_wm_dpartial hc φ.2 i).toLp (dpartial i (φ : St d → ℝ))) : St d → ℝ) x :=
            pairVec_inner hc hcpos hψ_cont hψ_cs _
        _ = ∫ x, ψ x * dpartial i (φ : St d → ℝ) x := by
            refine integral_congr_ae ?_
            filter_upwards [ae_volume_of_ae_wm hc hcpos
              (MemLp.coeFn_toLp (memLp_wm_dpartial hc φ.2 i))] with x hx
            rw [hx]
    rw [hL, h1, h2]
  have hpair_zero : ∀ φ : testFns d, L (testToGLin hc hρ φ) = 0 := by
    intro φ
    have h := integral_by_parts_test φ.2 hψ i
    have h1 : ∫ x, dpartial i ψ x * (φ : St d → ℝ) x
        = -∫ x, dpartial i (φ : St d → ℝ) x * ψ x := by
      have hc1 : ∫ x, dpartial i ψ x * (φ : St d → ℝ) x
          = ∫ x, (φ : St d → ℝ) x * dpartial i ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      exact hc1.trans h
    have h2 : ∫ x, ψ x * dpartial i (φ : St d → ℝ) x
        = ∫ x, dpartial i (φ : St d → ℝ) x * ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [hpair φ, h1, h2]
    ring
  have hker : LinearMap.range (testToGLin hc hρ) ≤ LinearMap.ker L.toLinearMap := by
    rintro w ⟨φ, rfl⟩
    exact LinearMap.mem_ker.mpr (hpair_zero φ)
  have hz' : z ∈ (LinearMap.range (testToGLin hc hρ)).topologicalClosure := by
    simpa only [gradGraph] using hz
  have hclosed : IsClosed (↑(LinearMap.ker L.toLinearMap) : Set (GSpace c ρ)) :=
    ContinuousLinearMap.isClosed_ker L
  have hzker : L z = 0 := by
    have hmem := (Submodule.topologicalClosure_minimal
      (LinearMap.range (testToGLin hc hρ)) hker hclosed) hz'
    exact LinearMap.mem_ker.mp hmem
  have h1 := pairVec_inner hρ hρpos (dpartial_mem_test_cont hψ i) hdψ_cs z.1
  have h2 := pairVec_inner hc hcpos hψ_cont hψ_cs (z.2 i)
  rw [← h1, ← h2, ← hLz]
  exact hzker

theorem gradGraph_closable {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {g : Fin d → Lp ℝ 2 (wm c)}
    (h : ((0 : Lp ℝ 2 (wm ρ)), g) ∈ gradGraph hc hρ) : g = 0 := by
  funext i
  apply eq_zero_of_pairing_zero hc hcpos
  intro ψ hψ
  have := gradGraph_pairing hc hρ hcpos hρpos hψ i _ h
  change (∫ x, dpartial i ψ x * ((0 : Lp ℝ 2 (wm ρ)) : St d → ℝ) x) +
    ∫ x, ψ x * (g i : St d → ℝ) x = 0 at this
  have h0 : ∀ᵐ x ∂(volume : Measure (St d)), ((0 : Lp ℝ 2 (wm ρ)) : St d → ℝ) x = 0 :=
    ae_volume_of_ae_wm hρ hρpos (Lp.coeFn_zero ℝ 2 (wm ρ))
  have h1 : (∫ x, dpartial i ψ x * ((0 : Lp ℝ 2 (wm ρ)) : St d → ℝ) x) = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    · filter_upwards [h0] with x hx
      rw [hx, mul_zero]
  rw [h1, zero_add] at this
  exact this

/-- The form domain: first components of the closed graph. -/
def gradDomain {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) :
    Submodule ℝ (Lp ℝ 2 (wm ρ)) := (gradGraph hc hρ).map (LinearMap.fst ℝ _ _)

theorem mem_gradDomain_iff {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (u : Lp ℝ 2 (wm ρ)) : u ∈ gradDomain hc hρ ↔ ∃ g, (u, g) ∈ gradGraph hc hρ := by
  rw [gradDomain, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hy1⟩
    refine ⟨y.2, ?_⟩
    rw [← hy1]
    exact hy
  · rintro ⟨g, hg⟩
    exact ⟨(u, g), hg, rfl⟩

/-- The gradient of a domain element (zero off the domain). -/
def gradOf {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ) (u : Lp ℝ 2 (wm ρ)) :
    Fin d → Lp ℝ 2 (wm c) :=
  open scoped Classical in
  if h : ∃ g, (u, g) ∈ gradGraph hc hρ then Classical.choose h else 0

theorem gradOf_spec {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u : Lp ℝ 2 (wm ρ)}
    {g : Fin d → Lp ℝ 2 (wm c)} (h : (u, g) ∈ gradGraph hc hρ) : gradOf hc hρ u = g := by
  unfold gradOf
  rw [dite_eq_left (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩)]
  have hmem : (u, Classical.choose (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩))
      ∈ gradGraph hc hρ :=
    Classical.choose_spec (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩)
  have hsub : (u, Classical.choose (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩)) - (u, g)
      ∈ gradGraph hc hρ := (gradGraph hc hρ).sub_mem hmem h
  have hzero : ((0 : Lp ℝ 2 (wm ρ)),
      Classical.choose (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩) - g) ∈ gradGraph hc hρ := by
    have hxy : (u, Classical.choose (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩)) - (u, g)
        = ((0 : Lp ℝ 2 (wm ρ)),
            Classical.choose (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩) - g) := by
      ext <;> simp
    rwa [hxy] at hsub
  have hg : Classical.choose (show ∃ g, (u, g) ∈ gradGraph hc hρ from ⟨g, h⟩) - g = 0 :=
    gradGraph_closable hc hρ hcpos hρpos hzero
  exact sub_eq_zero.mp hg

theorem mem_gradGraph_iff {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) (u : Lp ℝ 2 (wm ρ))
    (g : Fin d → Lp ℝ 2 (wm c)) :
    (u, g) ∈ gradGraph hc hρ ↔ u ∈ gradDomain hc hρ ∧ g = gradOf hc hρ u := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [mem_gradDomain_iff]
      exact ⟨g, h⟩
    · exact (gradOf_spec hc hρ hcpos hρpos h).symm
  · rintro ⟨hu, rfl⟩
    obtain ⟨g₀, hg₀⟩ := (mem_gradDomain_iff hc hρ u).mp hu
    rw [gradOf_spec hc hρ hcpos hρpos hg₀]
    exact hg₀

theorem gradOf_add {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u v : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) (hv : v ∈ gradDomain hc hρ) :
    gradOf hc hρ (u + v) = gradOf hc hρ u + gradOf hc hρ v := by
  obtain ⟨gu, hgu⟩ := (mem_gradDomain_iff hc hρ u).mp hu
  obtain ⟨gv, hgv⟩ := (mem_gradDomain_iff hc hρ v).mp hv
  have hgu' : gradOf hc hρ u = gu := gradOf_spec hc hρ hcpos hρpos hgu
  have hgv' : gradOf hc hρ v = gv := gradOf_spec hc hρ hcpos hρpos hgv
  have hsum : (u + v, gu + gv) ∈ gradGraph hc hρ := by
    have := (gradGraph hc hρ).add_mem hgu hgv
    simpa using this
  have hkey : gradOf hc hρ (u + v) = gu + gv := gradOf_spec hc hρ hcpos hρpos hsum
  rw [hkey, hgu', hgv']

theorem gradOf_smul {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) (a : ℝ) {u : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) : gradOf hc hρ (a • u) = a • gradOf hc hρ u := by
  obtain ⟨g, hg⟩ := (mem_gradDomain_iff hc hρ u).mp hu
  have hgu : gradOf hc hρ u = g := gradOf_spec hc hρ hcpos hρpos hg
  have hsmul : (a • u, a • g) ∈ gradGraph hc hρ := by
    rw [← Prod.smul_mk]
    exact Submodule.smul_mem _ a hg
  rw [gradOf_spec hc hρ hcpos hρpos hsmul, hgu]

theorem gradOf_sub {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {u v : Lp ℝ 2 (wm ρ)}
    (hu : u ∈ gradDomain hc hρ) (hv : v ∈ gradDomain hc hρ) :
    gradOf hc hρ (u - v) = gradOf hc hρ u - gradOf hc hρ v := by
  have hneg : -v ∈ gradDomain hc hρ := (gradDomain hc hρ).neg_mem hv
  rw [sub_eq_add_neg, gradOf_add hc hρ hcpos hρpos hu hneg]
  have h2 := gradOf_smul hc hρ hcpos hρpos (-1) hv
  simp only [neg_one_smul] at h2
  rw [h2]
  simp [sub_eq_add_neg]

/-- The energy of a pair: `E(u, v) = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫_{L²(c)}`. -/
def gradForm {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (u v : Lp ℝ 2 (wm ρ)) : ℝ :=
  ∑ i, inner ℝ (gradOf hc hρ u i) (gradOf hc hρ v i)

theorem gradForm_self {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (u : Lp ℝ 2 (wm ρ)) : gradForm hc hρ u u = ∑ i, ‖gradOf hc hρ u i‖ ^ 2 := by
  unfold gradForm
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

theorem dense_gradDomain {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (_hρpos : ∀ x, 0 < ρ x) : Dense (gradDomain hc hρ : Set (Lp ℝ 2 (wm ρ))) := by
  have hlf : IsLocallyFiniteMeasure (wm ρ) := isLocallyFiniteMeasure_wm hρ
  refine Dense.mono ?_ (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (μ := wm ρ) (p := 2) (by norm_num))
  rintro f ⟨g, hfg, hg_cs, hg_cd⟩
  let ψ : testFns d := ⟨g, hg_cd, hg_cs⟩
  refine ⟨testToG hc hρ ψ, Submodule.le_topologicalClosure _ (LinearMap.mem_range.mpr ⟨ψ, rfl⟩), ?_⟩
  exact Lp.ext ((MemLp.coeFn_toLp (memLp_wm_of_test hρ ψ.2)).trans hfg.symm)

theorem gradForm_complete {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) (u : ℕ → Lp ℝ 2 (wm ρ))
    (hu : ∀ n, u n ∈ gradDomain hc hρ)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      gradForm hc hρ (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε) :
    ∃ w ∈ gradDomain hc hρ, Tendsto
      (fun n => gradForm hc hρ (u n - w) (u n - w) + ‖u n - w‖ ^ 2) atTop (𝓝 0) := by
  have : CompleteSpace (GSpace c ρ) := inferInstance
  have hcauchyG : CauchySeq (fun n => ((u n, gradOf hc hρ (u n)) : GSpace c ρ)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hεsq : 0 < (ε / 2) ^ 2 := by nlinarith [sq_nonneg (ε / 2)]
    obtain ⟨N, hN⟩ := hcauchy ((ε / 2) ^ 2) hεsq
    refine ⟨N, fun p hp q hq => ?_⟩
    have hlt := hN p hp q hq
    rw [gradForm_self] at hlt
    have hsum_nonneg : 0 ≤ ∑ i, ‖gradOf hc hρ (u p - u q) i‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hnorm_nonneg : 0 ≤ ‖u p - u q‖ ^ 2 := sq_nonneg _
    have hsum_lt : ∑ i, ‖gradOf hc hρ (u p - u q) i‖ ^ 2 < (ε / 2) ^ 2 := by linarith
    have hnorm_lt : ‖u p - u q‖ ^ 2 < (ε / 2) ^ 2 := by linarith
    have hgrad : gradOf hc hρ (u p - u q) = gradOf hc hρ (u p) - gradOf hc hρ (u q) :=
      gradOf_sub hc hρ hcpos hρpos (hu p) (hu q)
    have hdist_grad : dist (gradOf hc hρ (u p)) (gradOf hc hρ (u q)) < ε := by
      rw [dist_pi_lt_iff hε]
      intro i
      rw [dist_eq_norm]
      have h1 : ‖gradOf hc hρ (u p - u q) i‖ ^ 2 ≤
          ∑ j, ‖gradOf hc hρ (u p - u q) j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖gradOf hc hρ (u p - u q) j‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have h2 : ‖gradOf hc hρ (u p - u q) i‖ ^ 2 < (ε / 2) ^ 2 := by linarith
      have h3 : ‖gradOf hc hρ (u p) i - gradOf hc hρ (u q) i‖ ^ 2 < (ε / 2) ^ 2 := by
        have heqi : gradOf hc hρ (u p) i - gradOf hc hρ (u q) i = gradOf hc hρ (u p - u q) i := by
          rw [← Pi.sub_apply, ← congrFun hgrad i]
        rw [heqi]
        exact h2
      have h4 := (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε2)).mp h3
      linarith
    have hdist_u : dist (u p) (u q) < ε := by
      rw [dist_eq_norm]
      have h5 := (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε2)).mp hnorm_lt
      linarith
    rw [Prod.dist_eq]
    exact max_lt hdist_u hdist_grad
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchyG
  have hzmem : z ∈ gradGraph hc hρ := by
    refine IsClosed.mem_of_tendsto (isClosed_gradGraph hc hρ) hz ?_
    exact Eventually.of_forall fun n =>
      (mem_gradGraph_iff hc hρ hcpos hρpos (u n) (gradOf hc hρ (u n))).mpr ⟨hu n, rfl⟩
  have hz1 : z.1 ∈ gradDomain hc hρ :=
    ((mem_gradGraph_iff hc hρ hcpos hρpos z.1 z.2).mp hzmem).1
  have hz2 : z.2 = gradOf hc hρ z.1 :=
    ((mem_gradGraph_iff hc hρ hcpos hρpos z.1 z.2).mp hzmem).2
  have hlim_u : Tendsto u atTop (𝓝 z.1) := by
    simpa using! (continuous_fst.tendsto z).comp hz
  have hlim_g : Tendsto (fun n => gradOf hc hρ (u n)) atTop (𝓝 z.2) := by
    simpa using! (continuous_snd.tendsto z).comp hz
  have hlim_hi : ∀ i, Tendsto (fun n => gradOf hc hρ (u n) i) atTop (𝓝 (gradOf hc hρ z.1 i)) := by
    intro i
    have h := ((continuous_apply i).tendsto z.2).comp hlim_g
    simpa only [hz2] using! h
  have hlimN : Tendsto (fun n => ‖u n - z.1‖) atTop (𝓝 (0 : ℝ)) := by
    have h := (hlim_u.sub (tendsto_const_nhds (x := z.1))).norm
    simpa using h
  have hlimGi : ∀ i, Tendsto (fun n => ‖gradOf hc hρ (u n) i - gradOf hc hρ z.1 i‖)
      atTop (𝓝 (0 : ℝ)) := by
    intro i
    have h := ((hlim_hi i).sub (tendsto_const_nhds (x := gradOf hc hρ z.1 i))).norm
    simpa using h
  have hlim_sum : Tendsto
      (fun n => ∑ i, ‖gradOf hc hρ (u n) i - gradOf hc hρ z.1 i‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => (hlimGi i).pow 2)
    simpa using h
  have hlim_norm2 : Tendsto (fun n => ‖u n - z.1‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have h := hlimN.pow 2
    simpa using h
  have heq : ∀ n, gradForm hc hρ (u n - z.1) (u n - z.1) + ‖u n - z.1‖ ^ 2 =
      (∑ i, ‖gradOf hc hρ (u n) i - gradOf hc hρ z.1 i‖ ^ 2) + ‖u n - z.1‖ ^ 2 := by
    intro n
    have h1 : gradForm hc hρ (u n - z.1) (u n - z.1) =
        ∑ i, ‖gradOf hc hρ (u n - z.1) i‖ ^ 2 := gradForm_self hc hρ (u n - z.1)
    have h2 : (∑ i, ‖gradOf hc hρ (u n - z.1) i‖ ^ 2) =
        ∑ i, ‖gradOf hc hρ (u n) i - gradOf hc hρ z.1 i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [gradOf_sub hc hρ hcpos hρpos (hu n) hz1, Pi.sub_apply]
    rw [h1, h2]
  refine ⟨z.1, hz1, ?_⟩
  have hfinal : Tendsto
      (fun n => (∑ i, ‖gradOf hc hρ (u n) i - gradOf hc hρ z.1 i‖ ^ 2) + ‖u n - z.1‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hlim_sum.add hlim_norm2
  simpa only [← heq] using hfinal

/-- **The closure of the smooth weighted gradient form**, a closed form on `L²(ρ dx)`. -/
def gradClosedForm {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) :
    _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (wm ρ) where
  domain := gradDomain hc hρ
  form := gradForm hc hρ
  denseDomain := dense_gradDomain hc hρ hρpos
  form_symm := fun u _ v _ => by
    unfold gradForm
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  form_add_left := fun u hu v hv w hw => by
    unfold gradForm
    rw [gradOf_add hc hρ hcpos hρpos hu hv]
    simp [inner_add_left, Finset.sum_add_distrib]
  form_smul_left := fun a u hu v _ => by
    unfold gradForm
    rw [gradOf_smul hc hρ hcpos hρpos a hu]
    simp [inner_smul_left, Finset.mul_sum]
  form_nonneg := fun u _ => by
    unfold gradForm
    exact Finset.sum_nonneg fun i _ => real_inner_self_nonneg
  complete := gradForm_complete hc hρ hcpos hρpos

end SubdiffusiveProcess.E7
