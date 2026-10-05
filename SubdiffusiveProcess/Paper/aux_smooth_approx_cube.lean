module

public import Mathlib

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped BigOperators ContDiff ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! Fine helper (smooth approximation):
mollification of weak-gradient pairs on the open unit cube, the endpoint estimate on `[0,1]`, and the face-trace
inequality for `C^1` functions; consumed by `neumann_boundary_identity_trace_foundation`. -/
/-- The open unit cube `(0,1)^d`. In the sup norm on `Fin d → ℝ` it is `Metric.ball (fun _ => 1/2) (1/2)` (BONUS B1). -/
def aux_openCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)

/-- `(u, g)` is a weak-gradient pair on `Ω`: `∫_Ω φ g_i + ∫_Ω ∂_iφ · u = 0` for all smooth compactly supported tests in `Ω`
(project definition `mem_weakSobolevGraph_iff`, inlined). -/
def aux_IsWeakGradientPair {d : ℕ} (Ω : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℝ) (g : Fin d → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (φ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∀ i : Fin d, (∫ x in Ω, φ x * g i x) + (∫ x in Ω, fderiv ℝ φ x (Pi.single i 1) * u x) = 0

def aux_unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

lemma aux_openCube_eq_ball (d : ℕ) :
    aux_openCube d = Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
  ext x
  rw [Metric.mem_ball,
    dist_pi_lt_iff (show (0 : ℝ) < 1 / 2 by norm_num)]
  constructor
  · intro hx i
    have hi : 0 < x i ∧ x i < 1 := hx i (Set.mem_univ i)
    change dist (x i) (1 / 2 : ℝ) < 1 / 2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hi.1, hi.2]
  · intro hx
    change ∀ i ∈ (Set.univ : Set (Fin d)), x i ∈ Set.Ioo (0 : ℝ) 1
    intro i hi
    have hxi := hx i
    change dist (x i) (1 / 2 : ℝ) < 1 / 2 at hxi
    rw [Real.dist_eq, abs_lt] at hxi
    constructor <;> linarith [hxi.1, hxi.2]

lemma aux_isOpen_openCube (d : ℕ) : IsOpen (aux_openCube d) := by
  rw [aux_openCube_eq_ball]
  exact Metric.isOpen_ball

lemma aux_isCompact_unitCube (d : ℕ) : IsCompact (aux_unitCube d) :=
  isCompact_univ_pi
    (fun _ : Fin d => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))

lemma aux_openCube_subset_unitCube (d : ℕ) : aux_openCube d ⊆ aux_unitCube d := by
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

lemma aux_volume_openCube (d : ℕ) : volume (aux_openCube d) = 1 := by
  change (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))
    (Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)) = 1
  rw [Measure.pi_pi]
  simp only [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

instance aux_finiteMeasure_openCube (d : ℕ) :
    IsFiniteMeasure (volume.restrict (aux_openCube d)) :=
  ⟨by rw [Measure.restrict_apply_univ, aux_volume_openCube]; norm_num⟩

lemma aux_continuous_memLp_unitCube {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (aux_unitCube d)) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable.restrict).2
  exact ContinuousOn.integrableOn_compact (aux_isCompact_unitCube d)
    (hf.pow 2).continuousOn

lemma aux_continuous_memLp_openCube {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (aux_openCube d)) := by
  exact (aux_continuous_memLp_unitCube hf).mono_measure
    (Measure.restrict_mono (aux_openCube_subset_unitCube d) le_rfl)

lemma aux_compact_continuous_memLp {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) : MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  apply (hf.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two, Pi.mul_apply] using (hs.mul_right (f' := f))

lemma aux_integral_sq_eq_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (f x) ^ 2 ∂μ) = ‖MemLp.toLp f hf‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma aux_integral_sq_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) {η : ℝ}
    (hη : 0 ≤ η) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal η) :
    (∫ x, (f x) ^ 2 ∂μ) ≤ η ^ 2 := by
  rw [aux_integral_sq_eq_norm_sq hf, Lp.norm_toLp]
  have hn : (eLpNorm f 2 μ).toReal ≤ η := by
    simpa only [ENNReal.toReal_ofReal hη] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have h0 : 0 ≤ (eLpNorm f 2 μ).toReal := ENNReal.toReal_nonneg
  nlinarith

def aux_radius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k / 2

def aux_scale (k : ℕ) : ℝ := 1 - aux_radius k

lemma aux_radius_pos (k : ℕ) : 0 < aux_radius k := by
  unfold aux_radius
  positivity

lemma aux_radius_le (k : ℕ) : aux_radius k ≤ 1 / 2 := by
  have h : (1 / 2 : ℝ) ^ k ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  dsimp only [aux_radius]
  linarith

lemma aux_scale_bounds (k : ℕ) : 1 / 2 ≤ aux_scale k ∧ aux_scale k < 1 := by
  dsimp only [aux_scale]
  constructor <;> linarith [aux_radius_pos k, aux_radius_le k]

lemma aux_radius_tendsto : Tendsto aux_radius atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  unfold aux_radius
  simpa only [zero_div] using h.div_const 2

lemma aux_scale_tendsto : Tendsto aux_scale atTop (𝓝 1) := by
  have h : Tendsto (fun k => (1 : ℝ) - aux_radius k) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub aux_radius_tendsto
  unfold aux_scale
  simpa only [sub_zero] using h

def aux_inward (d k : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  (fun _ => (1 / 2 : ℝ)) + aux_scale k • (x - fun _ => (1 / 2 : ℝ))

lemma aux_inward_smooth (d k : ℕ) : ContDiff ℝ ∞ (aux_inward d k) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul (aux_scale k))

lemma aux_inward_tendsto (d : ℕ) (x : Fin d → ℝ) :
    Tendsto (fun k => aux_inward d k x) atTop (𝓝 x) := by
  let c : Fin d → ℝ := fun _ => 1 / 2
  have h : Tendsto (fun k => c + aux_scale k • (x - c)) atTop
      (𝓝 (c + (1 : ℝ) • (x - c))) :=
    tendsto_const_nhds.add (aux_scale_tendsto.smul_const (x - c))
  have he : c + (1 : ℝ) • (x - c) = x := by
    rw [one_smul]
    abel
  rw [he] at h
  exact h

def aux_bump (d k : ℕ) : ContDiffBump (0 : Fin d → ℝ) where
  rIn := aux_radius k / 8
  rOut := aux_radius k / 4
  rIn_pos := by have h := aux_radius_pos k; positivity
  rIn_lt_rOut := by have h := aux_radius_pos k; linarith

def aux_kernel (d k : ℕ) : (Fin d → ℝ) → ℝ :=
  (aux_bump d k).normed volume

def aux_conv {d : ℕ} (k : ℕ) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  convolution f (aux_kernel d k) (ContinuousLinearMap.mul ℝ ℝ) volume

def aux_smooth {d : ℕ} (k : ℕ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  aux_conv k f (aux_inward d k x)

lemma aux_conv_continuous {d : ℕ} (k : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f volume) : Continuous (aux_conv k f) :=
  HasCompactSupport.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (aux_bump d k).hasCompactSupport_normed hf.locallyIntegrable
    (aux_bump d k).continuous_normed

lemma aux_smooth_contDiff {d : ℕ} (k : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f volume) : ContDiff ℝ ∞ (aux_smooth k f) := by
  exact (HasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (aux_bump d k).hasCompactSupport_normed
    hf.locallyIntegrable (aux_bump d k).contDiff_normed).comp
      (aux_inward_smooth d k)

lemma aux_kernel_product_integrable {d : ℕ} (k : ℕ)
    {f : (Fin d → ℝ) → ℝ} (hf : Integrable f volume) (z : Fin d → ℝ) :
    Integrable (fun y => f y * aux_kernel d k (z - y)) volume := by
  exact HasCompactSupport.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (aux_bump d k).hasCompactSupport_normed hf.locallyIntegrable
    (aux_bump d k).continuous_normed z

lemma aux_kernel_integral_translate (d k : ℕ) (z : Fin d → ℝ) :
    (∫ y, aux_kernel d k (z - y)) = 1 := by
  rw [integral_sub_left_eq_self]
  exact (aux_bump d k).integral_normed

lemma aux_smooth_sub {d : ℕ} (k : ℕ) {f p : (Fin d → ℝ) → ℝ}
    (hf : Integrable f volume) (hp : Integrable p volume) (x : Fin d → ℝ) :
    aux_smooth k (f - p) x = aux_smooth k f x - aux_smooth k p x := by
  unfold aux_smooth aux_conv
  simp only [convolution_mul, Pi.sub_apply, sub_mul]
  exact integral_sub (aux_kernel_product_integrable k hf _)
    (aux_kernel_product_integrable k hp _)

lemma aux_conv_sq_le {d : ℕ} (k : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) (z : Fin d → ℝ) :
    (aux_conv k f z) ^ 2 ≤ aux_conv k (fun y => (f y) ^ 2) z := by
  let m := aux_conv k f z
  have h0 : Integrable (fun y => aux_kernel d k (z - y)) volume :=
    (aux_bump d k).integrable_normed.comp_sub_left z
  have h1 := aux_kernel_product_integrable k hf z
  have h2 := aux_kernel_product_integrable k hf2.integrable_sq z
  have hnonneg :
      0 ≤ ∫ y, (f y - m) ^ 2 * aux_kernel d k (z - y) :=
    integral_nonneg (fun y => mul_nonneg (sq_nonneg _)
      ((aux_bump d k).nonneg_normed _))
  have heq :
      (fun y => (f y - m) ^ 2 * aux_kernel d k (z - y)) =
      (fun y => (f y) ^ 2 * aux_kernel d k (z - y) -
        (2 * m) * (f y * aux_kernel d k (z - y)) +
        m ^ 2 * aux_kernel d k (z - y)) := by
    funext y
    ring
  have h21 : Integrable (fun y => (f y) ^ 2 * aux_kernel d k (z - y) -
      (2 * m) * (f y * aux_kernel d k (z - y))) volume := h2.sub (h1.const_mul (2 * m))
  rw [heq, integral_add h21 (h0.const_mul (m ^ 2)),
    integral_sub h2 (h1.const_mul (2 * m)), integral_const_mul,
    integral_const_mul, aux_kernel_integral_translate] at hnonneg
  change 0 ≤ aux_conv k (fun y => (f y) ^ 2) z - (2 * m) * m + m ^ 2 * 1
    at hnonneg
  change m ^ 2 ≤ _
  nlinarith only [hnonneg]

lemma aux_integrable_inward {d : ℕ} (k : ℕ)
    {f : (Fin d → ℝ) → ℝ} (hf : Integrable f volume) :
    Integrable (fun x => f (aux_inward d k x)) volume := by
  have ha : aux_scale k ≠ 0 := by linarith [(aux_scale_bounds k).1]
  exact ((hf.comp_add_left (fun _ : Fin d => (1 / 2 : ℝ))).comp_smul ha).comp_sub_right
    (fun _ : Fin d => (1 / 2 : ℝ))

lemma aux_integral_inward (d k : ℕ) (f : (Fin d → ℝ) → ℝ) :
    (∫ x, f (aux_inward d k x)) =
      (aux_scale k ^ Module.finrank ℝ (Fin d → ℝ))⁻¹ * ∫ x, f x := by
  have ha : 0 ≤ aux_scale k := by linarith [(aux_scale_bounds k).1]
  let c : Fin d → ℝ := fun _ => 1 / 2
  change (∫ x, f (c + aux_scale k • (x - c))) = _
  calc
    (∫ x, f (c + aux_scale k • (x - c))) =
        ∫ x, f (c + aux_scale k • x) :=
      integral_sub_right_eq_self (fun x => f (c + aux_scale k • x)) c
    _ = (aux_scale k ^ Module.finrank ℝ (Fin d → ℝ))⁻¹ *
        ∫ x, f (c + x) := by
      simpa only [smul_eq_mul] using
        Measure.integral_comp_smul_of_nonneg volume (fun x => f (c + x))
          (aux_scale k) (hR := ha)
    _ = (aux_scale k ^ Module.finrank ℝ (Fin d → ℝ))⁻¹ * ∫ x, f x := by
      rw [integral_add_left_eq_self]

lemma aux_smooth_sq_bound {d : ℕ} (k : ℕ)
    {f : (Fin d → ℝ) → ℝ} (hf : Integrable f volume) (hf2 : MemLp f 2 volume) :
    (∫ x in aux_openCube d, (aux_smooth k f x) ^ 2) ≤
      (2 : ℝ) ^ Module.finrank ℝ (Fin d → ℝ) * ∫ x, (f x) ^ 2 := by
  have hF : Integrable (aux_conv k (fun x => (f x) ^ 2)) volume :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      hf2.integrable_sq (aux_bump d k).integrable_normed
  have hFT := aux_integrable_inward k hF
  have hnonneg (x : Fin d → ℝ) :
      0 ≤ aux_conv k (fun y => (f y) ^ 2) (aux_inward d k x) := by
    apply integral_nonneg
    intro y
    exact mul_nonneg (sq_nonneg _) ((aux_bump d k).nonneg_normed _)
  have hcoef :
      (aux_scale k ^ Module.finrank ℝ (Fin d → ℝ))⁻¹ ≤
        (2 : ℝ) ^ Module.finrank ℝ (Fin d → ℝ) := by
    rw [← inv_pow]
    apply pow_le_pow_left₀ (inv_nonneg.mpr (by linarith [(aux_scale_bounds k).1]))
    have ha : 0 < aux_scale k := by linarith [(aux_scale_bounds k).1]
    rw [inv_eq_one_div, div_le_iff₀ ha]
    linarith [(aux_scale_bounds k).1]
  calc
    (∫ x in aux_openCube d, (aux_smooth k f x) ^ 2) ≤
        ∫ x in aux_openCube d,
          aux_conv k (fun y => (f y) ^ 2) (aux_inward d k x) := by
      apply integral_mono
        (aux_continuous_memLp_openCube (aux_smooth_contDiff k hf).continuous).integrable_sq
        hFT.integrableOn
      intro x
      exact aux_conv_sq_le k hf hf2 _
    _ ≤ ∫ x, aux_conv k (fun y => (f y) ^ 2) (aux_inward d k x) :=
      setIntegral_le_integral hFT (Filter.Eventually.of_forall hnonneg)
    _ = (aux_scale k ^ Module.finrank ℝ (Fin d → ℝ))⁻¹ *
        ∫ x, (f x) ^ 2 := by
      rw [aux_integral_inward]
      unfold aux_conv aux_kernel
      rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
        hf2.integrable_sq (aux_bump d k).integrable_normed]
      change _ * ((∫ x, (f x) ^ 2) * ∫ x, (aux_bump d k).normed volume x) = _
      rw [(aux_bump d k).integral_normed, mul_one]
    _ ≤ (2 : ℝ) ^ Module.finrank ℝ (Fin d → ℝ) * ∫ x, (f x) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (integral_nonneg (fun x => sq_nonneg _))

lemma aux_conv_swap {d : ℕ} (k : ℕ) (f : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) :
    aux_conv k f z =
      convolution (aux_kernel d k) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
  calc
    aux_conv k f z = ∫ y, f y * aux_kernel d k (z - y) := rfl
    _ = ∫ y, aux_kernel d k (z - y) • f y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => mul_comm _ _)
    _ = convolution (aux_kernel d k) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      (convolution_lsmul_swap (f := aux_kernel d k) (g := f) (x := z)).symm

lemma aux_smooth_pointwise {d : ℕ} {p : (Fin d → ℝ) → ℝ}
    (hp : Continuous p) (x : Fin d → ℝ) :
    Tendsto (fun k => aux_smooth k p x) atTop (𝓝 (p x)) := by
  have hr : Tendsto (fun k => (aux_bump d k).rOut) atTop (𝓝 0) := by
    simpa only [aux_bump, zero_div] using aux_radius_tendsto.div_const 4
  have h := ContDiffBump.convolution_tendsto_right
    (μ := (volume : Measure (Fin d → ℝ)))
    (φ := aux_bump d) (g := fun _ : ℕ => p)
    (k := fun k => aux_inward d k x)
    hr (Filter.Eventually.of_forall (fun _ => hp.aestronglyMeasurable))
    (hp.continuousAt.tendsto.comp tendsto_snd) (aux_inward_tendsto d x)
  simpa only [aux_smooth, aux_conv_swap, aux_kernel] using h

lemma aux_smooth_norm_le {d : ℕ} (k : ℕ) {p : (Fin d → ℝ) → ℝ}
    (hp : Continuous p) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖p x‖ ≤ M)
    (x : Fin d → ℝ) : ‖aux_smooth k p x‖ ≤ M := by
  have hs : Function.support (aux_kernel d k) ⊆
      Metric.ball (0 : Fin d → ℝ) (aux_bump d k).rOut :=
    (aux_bump d k).support_normed_eq.le
  have h := MeasureTheory.dist_convolution_le
    (μ := (volume : Measure (Fin d → ℝ)))
    (x₀ := aux_inward d k x) (z₀ := (0 : ℝ)) hM hs
    (fun y => (aux_bump d k).nonneg_normed y)
    ((aux_bump d k).integral_normed (μ := volume)) hp.aestronglyMeasurable
    (fun y hy => by simpa only [dist_zero_right] using hbound y)
  simpa only [dist_zero_right, aux_smooth, aux_conv_swap] using h

lemma aux_compact_continuous_bound {d : ℕ} {p : (Fin d → ℝ) → ℝ}
    (hp : Continuous p) (hs : HasCompactSupport p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖p x‖ ≤ M := by
  obtain ⟨M, hM⟩ :=
    ((show IsCompact (tsupport p) from hs).image hp.norm).bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport p
  · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · have hp0 : p x = 0 := by
      by_contra h
      exact hx (subset_closure h)
    rw [hp0, norm_zero]
    exact le_max_right _ _

lemma aux_smooth_continuous_L2 {d : ℕ} {p : (Fin d → ℝ) → ℝ}
    (hp : Continuous p) (hs : HasCompactSupport p) :
    Tendsto (fun k => ∫ x in aux_openCube d, (aux_smooth k p x - p x) ^ 2)
      atTop (𝓝 0) := by
  have hpI := hp.integrable_of_hasCompactSupport (μ := volume) hs
  obtain ⟨M, hM, hbound⟩ := aux_compact_continuous_bound hp hs
  have hdom (k : ℕ) : ∀ᵐ x ∂volume.restrict (aux_openCube d),
      ‖(aux_smooth k p x - p x) ^ 2‖ ≤ 4 * M ^ 2 := by
    apply Filter.Eventually.of_forall
    intro x
    have ha := aux_smooth_norm_le k hp hM hbound x
    have hb := hbound x
    have ht : |aux_smooth k p x - p x| ≤ 2 * M := by
      calc
        |aux_smooth k p x - p x| = ‖aux_smooth k p x - p x‖ :=
          (Real.norm_eq_abs _).symm
        _ ≤ ‖aux_smooth k p x‖ + ‖p x‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith
    have hprod :
        0 ≤ (2 * M - |aux_smooth k p x - p x|) *
          (2 * M + |aux_smooth k p x - p x|) :=
      mul_nonneg (by linarith) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [hprod, sq_abs (aux_smooth k p x - p x)]
  have hlim : ∀ᵐ x ∂volume.restrict (aux_openCube d),
      Tendsto (fun k => (aux_smooth k p x - p x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro x
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((aux_smooth_pointwise hp x).sub_const (p x)).pow 2
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (aux_openCube d)) (f := fun _ => (0 : ℝ))
    (fun _ => 4 * M ^ 2)
    (fun k => ((((aux_smooth_contDiff k hpI).continuous.sub hp).pow 2).aestronglyMeasurable).restrict)
    (integrable_const _) hdom hlim
  simpa only [Pi.pow_apply, Pi.sub_apply, integral_zero] using h

lemma aux_tendsto_zero_of_nonneg {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a k < ε) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h ε hε] with k hk
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (ha k)] using hk

lemma aux_smooth_L2 {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Tendsto (fun k => ∫ x in aux_openCube d, (f x - aux_smooth k f x) ^ 2)
      atTop (𝓝 0) := by
  apply aux_tendsto_zero_of_nonneg (fun k => integral_nonneg (fun x => sq_nonneg _))
  intro ε hε
  let C : ℝ := (2 : ℝ) ^ Module.finrank ℝ (Fin d → ℝ)
  have hC : 0 ≤ C := by positivity
  let η : ℝ := min 1 (ε / (12 * (C + 1)))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η * (12 * (C + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 12 * (C + 1))).mp (min_le_right _ _)
  have hηsq : η ^ 2 ≤ η := by
    nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hη1)]
  have hsmall : 3 * (C + 1) * η ^ 2 ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_left hηsq
      (show 0 ≤ 3 * (C + 1) by positivity)
    nlinarith only [h, hηε]
  obtain ⟨p, hpS, hpD, hpdist⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hf2 hη
  have hpI := hpD.continuous.integrable_of_hasCompactSupport (μ := volume) hpS
  have hp2 := aux_compact_continuous_memLp hpD.continuous hpS
  have hdI := hf.sub hpI
  have hd2 := hf2.sub hp2
  have hE : (∫ x, (f x - p x) ^ 2) ≤ η ^ 2 :=
    aux_integral_sq_le_of_eLpNorm_le hd2 hη.le hpdist
  have hlast : (∫ x in aux_openCube d, (p x - f x) ^ 2) ≤ η ^ 2 := by
    calc
      (∫ x in aux_openCube d, (p x - f x) ^ 2) =
          ∫ x in aux_openCube d, (f x - p x) ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ ≤ ∫ x, (f x - p x) ^ 2 :=
        setIntegral_le_integral hd2.integrable_sq
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      _ ≤ η ^ 2 := hE
  have hpLim := aux_smooth_continuous_L2 hpD.continuous hpS
  filter_upwards [hpLim.eventually (gt_mem_nhds (show 0 < ε / 6 by positivity))]
    with k hk
  have hA : (∫ x in aux_openCube d, (aux_smooth k (f - p) x) ^ 2) ≤ C * η ^ 2 :=
    (aux_smooth_sq_bound k hdI hd2).trans
      (mul_le_mul_of_nonneg_left hE hC)
  have hI1 :=
    (aux_continuous_memLp_openCube (aux_smooth_contDiff k hdI).continuous).integrable_sq
  have hI2 := (aux_continuous_memLp_openCube
    ((aux_smooth_contDiff k hpI).continuous.sub hpD.continuous)).integrable_sq
  have hI3 : Integrable (fun x => (p x - f x) ^ 2) (volume.restrict (aux_openCube d)) :=
    ((hp2.sub hf2).mono_measure (Measure.restrict_le_self (s := aux_openCube d))).integrable_sq
  have hIf : Integrable (fun x => (f x - aux_smooth k f x) ^ 2) (volume.restrict (aux_openCube d)) :=
    ((hf2.mono_measure (Measure.restrict_le_self (s := aux_openCube d))).sub
      (aux_continuous_memLp_openCube (aux_smooth_contDiff k hf).continuous)).integrable_sq
  have hpoint (x : Fin d → ℝ) :
      (f x - aux_smooth k f x) ^ 2 ≤
        3 * (aux_smooth k (f - p) x) ^ 2 +
        3 * (aux_smooth k p x - p x) ^ 2 + 3 * (p x - f x) ^ 2 := by
    have heq : f x - aux_smooth k f x =
        -(aux_smooth k (f - p) x + (aux_smooth k p x - p x) + (p x - f x)) := by
      rw [aux_smooth_sub k hf hpI x]
      ring
    rw [heq, neg_sq]
    nlinarith only
      [sq_nonneg (aux_smooth k (f - p) x - (aux_smooth k p x - p x)),
        sq_nonneg (aux_smooth k (f - p) x - (p x - f x)),
        sq_nonneg ((aux_smooth k p x - p x) - (p x - f x))]
  have hA3 : Integrable (fun x => 3 * (aux_smooth k (f - p) x) ^ 2)
      (volume.restrict (aux_openCube d)) := hI1.const_mul 3
  have hB3 : Integrable (fun x => 3 * (aux_smooth k p x - p x) ^ 2)
      (volume.restrict (aux_openCube d)) := hI2.const_mul 3
  have hC3 : Integrable (fun x => 3 * (p x - f x) ^ 2)
      (volume.restrict (aux_openCube d)) := hI3.const_mul 3
  have hineq := integral_mono hIf ((hA3.add hB3).add hC3) hpoint
  have h1 := integral_add (hA3.add hB3) hC3
  have h2 := integral_add hA3 hB3
  simp only [Pi.add_apply] at hineq h1 h2
  rw [h1, h2, integral_const_mul, integral_const_mul, integral_const_mul] at hineq
  nlinarith only [hineq, hA, hlast, hk, hsmall, hε]

lemma aux_zeroExtension_memLp {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (aux_openCube d))) :
    MemLp ((aux_openCube d).indicator f) 2 volume :=
  (memLp_indicator_iff_restrict (aux_isOpen_openCube d).measurableSet).2 hf

lemma aux_zeroExtension_integrable {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (aux_openCube d))) :
    Integrable ((aux_openCube d).indicator f) volume :=
  (integrable_indicator_iff (aux_isOpen_openCube d).measurableSet).2
    (hf.integrable (by norm_num))

lemma aux_zeroExtension_L2 {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (aux_openCube d))) :
    Tendsto (fun k => ∫ x in aux_openCube d,
      (f x - aux_smooth k ((aux_openCube d).indicator f) x) ^ 2) atTop (𝓝 0) := by
  have h := aux_smooth_L2 (aux_zeroExtension_integrable hf) (aux_zeroExtension_memLp hf)
  have he (k : ℕ) :
      (∫ x in aux_openCube d,
        ((aux_openCube d).indicator f x - aux_smooth k ((aux_openCube d).indicator f) x) ^ 2) =
      ∫ x in aux_openCube d,
        (f x - aux_smooth k ((aux_openCube d).indicator f) x) ^ 2 := by
    apply setIntegral_congr_fun (aux_isOpen_openCube d).measurableSet
    intro x hx
    simp only [Set.indicator_of_mem hx]
  simpa only [he] using h

lemma aux_scaled_zeroExtension_L2 {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict (aux_openCube d))) :
    Tendsto (fun k => ∫ x in aux_openCube d,
      (f x - aux_scale k * aux_smooth k ((aux_openCube d).indicator f) x) ^ 2)
      atTop (𝓝 0) := by
  let f₀ := (aux_openCube d).indicator f
  let A : ℕ → ℝ := fun k => ∫ x in aux_openCube d, (f x - aux_smooth k f₀ x) ^ 2
  let E : ℝ := ∫ x in aux_openCube d, (f x) ^ 2
  have hA : Tendsto A atTop (𝓝 0) := aux_zeroExtension_L2 hf
  have hR : Tendsto (fun k => 2 * A k + 2 * (aux_radius k) ^ 2 * E)
      atTop (𝓝 0) := by
    convert (hA.const_mul 2).add
      (((aux_radius_tendsto.pow 2).const_mul 2).mul_const E) using 1 ; norm_num
  apply aux_tendsto_zero_of_nonneg (fun k => integral_nonneg (fun x => sq_nonneg _))
  intro ε hε
  filter_upwards [hR.eventually (gt_mem_nhds hε)] with k hk
  have hAc := (aux_smooth_contDiff k (aux_zeroExtension_integrable hf)).continuous
  have hA2 := aux_continuous_memLp_openCube hAc
  have hI : Integrable
      (fun x => (f x - aux_scale k * aux_smooth k f₀ x) ^ 2)
      (volume.restrict (aux_openCube d)) :=
    (hf.sub (aux_continuous_memLp_openCube
      (continuous_const.mul hAc))).integrable_sq
  have hdiffI : Integrable (fun x => (f x - aux_smooth k f₀ x) ^ 2)
      (volume.restrict (aux_openCube d)) := (hf.sub hA2).integrable_sq
  have hfsq : Integrable (fun x => (f x) ^ 2) (volume.restrict (aux_openCube d)) :=
    hf.integrable_sq
  have hpoint (x : Fin d → ℝ) :
      (f x - aux_scale k * aux_smooth k f₀ x) ^ 2 ≤
        2 * (f x - aux_smooth k f₀ x) ^ 2 +
          (2 * (aux_radius k) ^ 2) * (f x) ^ 2 := by
    have hl0 : 0 ≤ aux_scale k := by linarith [(aux_scale_bounds k).1]
    have hl1 : aux_scale k ≤ 1 := (aux_scale_bounds k).2.le
    have hlsq : (aux_scale k) ^ 2 ≤ 1 := by
      nlinarith only [mul_nonneg hl0 (sub_nonneg.mpr hl1)]
    have hweight := mul_le_mul_of_nonneg_right hlsq
      (sq_nonneg (f x - aux_smooth k f₀ x))
    have he : f x - aux_scale k * aux_smooth k f₀ x =
        aux_scale k * (f x - aux_smooth k f₀ x) + aux_radius k * f x := by
      dsimp only [aux_scale]
      ring
    rw [he]
    nlinarith only [hweight,
      sq_nonneg (aux_scale k * (f x - aux_smooth k f₀ x) - aux_radius k * f x)]
  have h2a : Integrable (fun x => 2 * (f x - aux_smooth k f₀ x) ^ 2)
      (volume.restrict (aux_openCube d)) := hdiffI.const_mul 2
  have h2b : Integrable (fun x => (2 * (aux_radius k) ^ 2) * (f x) ^ 2)
      (volume.restrict (aux_openCube d)) := hfsq.const_mul (2 * (aux_radius k) ^ 2)
  have hi := integral_mono hI (h2a.add h2b) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add h2a h2b, integral_const_mul, integral_const_mul] at hi
  exact hi.trans_lt hk

lemma aux_unitCube_dist {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ aux_unitCube d) :
    dist x (fun _ : Fin d => (1 / 2 : ℝ)) ≤ 1 / 2 := by
  apply (dist_pi_le_iff (show (0 : ℝ) ≤ 1 / 2 by norm_num)).2
  intro i
  have hi := hx i (Set.mem_univ i)
  change dist (x i) (1 / 2 : ℝ) ≤ 1 / 2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hi.1, hi.2]

lemma aux_inward_margin {d : ℕ} (k : ℕ) {x : Fin d → ℝ}
    (hx : x ∈ aux_unitCube d) :
    Metric.closedBall (aux_inward d k x) (aux_radius k / 4) ⊆ aux_openCube d := by
  let c : Fin d → ℝ := fun _ => 1 / 2
  have hl : 0 ≤ aux_scale k := by linarith [(aux_scale_bounds k).1]
  have hd : ‖x - c‖ ≤ 1 / 2 := by
    simpa only [dist_eq_norm] using aux_unitCube_dist hx
  have hz : dist (aux_inward d k x) c ≤ aux_scale k / 2 := by
    calc
      dist (aux_inward d k x) c = ‖aux_scale k • (x - c)‖ := by
        rw [dist_eq_norm]
        congr 1
        dsimp only [aux_inward, c]
        abel
      _ = aux_scale k * ‖x - c‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl]
      _ ≤ aux_scale k * (1 / 2) :=
        mul_le_mul_of_nonneg_left hd hl
      _ = aux_scale k / 2 := by ring
  intro y hy
  rw [aux_openCube_eq_ball, Metric.mem_ball]
  have ht := dist_triangle y (aux_inward d k x) c
  have hy' : dist y (aux_inward d k x) ≤ aux_radius k / 4 := hy
  have hr := aux_radius_pos k
  dsimp only [aux_scale] at hz
  change dist y c < 1 / 2
  linarith

lemma aux_test_support (d k : ℕ) (z : Fin d → ℝ) :
    tsupport (fun y => aux_kernel d k (z - y)) ⊆
      Metric.closedBall z (aux_radius k / 4) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro y hy
  have hm : z - y ∈ Function.support ((aux_bump d k).normed volume) := hy
  rw [(aux_bump d k).support_normed_eq] at hm
  have hn : ‖z - y‖ < aux_radius k / 4 := by
    simpa only [Metric.mem_ball, dist_zero_right, aux_bump] using hm
  change dist y z ≤ aux_radius k / 4
  rw [dist_eq_norm, norm_sub_rev]
  exact hn.le

lemma aux_test_compact (d k : ℕ) (z : Fin d → ℝ) :
    HasCompactSupport (fun y => aux_kernel d k (z - y)) := by
  exact (isCompact_closedBall z (aux_radius k / 4)).of_isClosed_subset
    (isClosed_tsupport _) (aux_test_support d k z)

lemma aux_test_fderiv (d k : ℕ) (z y v : Fin d → ℝ) :
    fderiv ℝ (fun y => aux_kernel d k (z - y)) y v =
      -fderiv ℝ (aux_kernel d k) (z - y) v := by
  have hK : ContDiff ℝ 1 (aux_kernel d k) := (aux_bump d k).contDiff_normed
  have h : HasFDerivAt (fun y => aux_kernel d k (z - y))
      ((fderiv ℝ (aux_kernel d k) (z - y)).comp (-ContinuousLinearMap.id ℝ (Fin d → ℝ))) y :=
    ((hK.differentiable (by norm_num)) (z - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub z)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

lemma aux_conv_fderiv {d : ℕ} (k : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : Integrable f volume) (z v : Fin d → ℝ) :
    fderiv ℝ (aux_conv k f) z v =
      ∫ y, f y * fderiv ℝ (aux_kernel d k) (z - y) v := by
  have hK : ContDiff ℝ 1 (aux_kernel d k) := (aux_bump d k).contDiff_normed
  have h := HasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (aux_bump d k).hasCompactSupport_normed
    hf.locallyIntegrable hK z
  unfold aux_conv aux_kernel
  rw [h.fderiv, convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    hf.locallyIntegrable ((aux_bump d k).hasCompactSupport_normed.fderiv ℝ)
    (hK.continuous_fderiv (by norm_num)) z v]
  rfl

lemma aux_integral_indicator_mul {d : ℕ} (s : Set (Fin d → ℝ))
    (hs : MeasurableSet s) (f q : (Fin d → ℝ) → ℝ) :
    (∫ y, s.indicator f y * q y) = ∫ y in s, f y * q y := by
  classical
  have he : (fun y => s.indicator f y * q y) = s.indicator (fun y => f y * q y) := by
    funext y
    by_cases hy : y ∈ s
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, zero_mul]
  rw [he, integral_indicator hs]

lemma aux_conv_weak_gradient {d : ℕ} (k : ℕ)
    {u : (Fin d → ℝ) → ℝ} {g : Fin d → (Fin d → ℝ) → ℝ}
    (hu : MemLp u 2 (volume.restrict (aux_openCube d)))
    (hpair : aux_IsWeakGradientPair (aux_openCube d) u g)
    {x : Fin d → ℝ} (hx : x ∈ aux_unitCube d) (i : Fin d) :
    fderiv ℝ (aux_conv k ((aux_openCube d).indicator u)) (aux_inward d k x)
      (Pi.single i 1) =
      aux_conv k ((aux_openCube d).indicator (g i)) (aux_inward d k x) := by
  let z := aux_inward d k x
  let ψ : (Fin d → ℝ) → ℝ := fun y => aux_kernel d k (z - y)
  have hψ : ContDiff ℝ ∞ ψ :=
    (aux_bump d k).contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hsψ : tsupport ψ ⊆ aux_openCube d :=
    (aux_test_support d k z).trans (aux_inward_margin k hx)
  have hw := hpair ψ hψ (aux_test_compact d k z) hsψ i
  have hfirst : (∫ y in aux_openCube d, ψ y * g i y) =
      aux_conv k ((aux_openCube d).indicator (g i)) z := by
    unfold aux_conv
    rw [convolution_mul, aux_integral_indicator_mul _ (aux_isOpen_openCube d).measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => mul_comm _ _)
  have hsecond :
      (∫ y in aux_openCube d, fderiv ℝ ψ y (Pi.single i 1) * u y) =
        -fderiv ℝ (aux_conv k ((aux_openCube d).indicator u)) z (Pi.single i 1) := by
    rw [aux_conv_fderiv k (aux_zeroExtension_integrable hu),
      aux_integral_indicator_mul _ (aux_isOpen_openCube d).measurableSet,
      ← integral_neg]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    change fderiv ℝ (fun y => aux_kernel d k (z - y)) y (Pi.single i 1) * u y = _
    rw [aux_test_fderiv]
    ring
  rw [hfirst, hsecond] at hw
  change fderiv ℝ (aux_conv k ((aux_openCube d).indicator u)) z (Pi.single i 1) = _
  linarith

lemma aux_smooth_weak_gradient {d : ℕ} (k : ℕ)
    {u : (Fin d → ℝ) → ℝ} {g : Fin d → (Fin d → ℝ) → ℝ}
    (hu : MemLp u 2 (volume.restrict (aux_openCube d)))
    (hpair : aux_IsWeakGradientPair (aux_openCube d) u g)
    {x : Fin d → ℝ} (hx : x ∈ aux_unitCube d) (i : Fin d) :
    fderiv ℝ (aux_smooth k ((aux_openCube d).indicator u)) x (Pi.single i 1) =
      aux_scale k * aux_smooth k ((aux_openCube d).indicator (g i)) x := by
  let c : Fin d → ℝ := fun _ => 1 / 2
  have hT : HasFDerivAt (aux_inward d k)
      (aux_scale k • ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    (((hasFDerivAt_id x).sub_const c).const_smul (aux_scale k)).const_add c
  have hK : ContDiff ℝ 1 (aux_kernel d k) := (aux_bump d k).contDiff_normed
  have hC := HasCompactSupport.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (aux_bump d k).hasCompactSupport_normed
    (aux_zeroExtension_integrable hu).locallyIntegrable hK (aux_inward d k x)
  have h : HasFDerivAt (fun x => convolution ((aux_openCube d).indicator u)
      ((aux_bump d k).normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume (aux_inward d k x))
      _ x := hC.comp x hT
  unfold aux_smooth aux_conv aux_kernel
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [← hC.fderiv]
  have hw := aux_conv_weak_gradient k hu hpair hx i
  unfold aux_conv aux_kernel at hw
  rw [hw]

/-- TARGET. Every `H¹`-pair on the open unit cube is an `L²`-limit of `C¹` functions (with their classical gradients),
uniformly in the graph norm. -/
theorem aux_exists_contDiff_approx_of_isWeakGradientPair (d : ℕ)
    (u : (Fin d → ℝ) → ℝ) (g : Fin d → (Fin d → ℝ) → ℝ)
    (hu : MemLp u 2 (volume.restrict (aux_openCube d)))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict (aux_openCube d)))
    (hpair : aux_IsWeakGradientPair (aux_openCube d) u g) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ 1 φ ∧
      (∫ x in aux_openCube d, (u x - φ x) ^ 2) < ε ∧
      ∀ i : Fin d, (∫ x in aux_openCube d, (g i x - fderiv ℝ φ x (Pi.single i 1)) ^ 2) < ε := by
  have huLim := aux_zeroExtension_L2 hu
  have hgLim := fun i => aux_scaled_zeroExtension_L2 (hg i)
  have huSmall : ∀ᶠ k in atTop,
      (∫ x in aux_openCube d, (u x - aux_smooth k ((aux_openCube d).indicator u) x) ^ 2) < ε :=
    huLim.eventually (gt_mem_nhds hε)
  have hgSmall : ∀ᶠ k in atTop, ∀ i : Fin d,
      (∫ x in aux_openCube d,
        (g i x - aux_scale k * aux_smooth k ((aux_openCube d).indicator (g i)) x) ^ 2) < ε :=
    Filter.eventually_all.mpr (fun i => (hgLim i).eventually (gt_mem_nhds hε))
  obtain ⟨k, hku, hkg⟩ := (huSmall.and hgSmall).exists
  refine ⟨aux_smooth k ((aux_openCube d).indicator u),
    (aux_smooth_contDiff k (aux_zeroExtension_integrable hu)).of_le (by norm_num),
    hku, ?_⟩
  intro i
  have he :
      (∫ x in aux_openCube d,
        (g i x - fderiv ℝ (aux_smooth k ((aux_openCube d).indicator u)) x (Pi.single i 1)) ^ 2) =
      ∫ x in aux_openCube d,
        (g i x - aux_scale k * aux_smooth k ((aux_openCube d).indicator (g i)) x) ^ 2 := by
    apply setIntegral_congr_fun (aux_isOpen_openCube d).measurableSet
    intro x hx
    dsimp only
    rw [aux_smooth_weak_gradient k hu hpair (aux_openCube_subset_unitCube d hx) i]
  rw [he]
  exact hkg i

theorem aux_openCube_eq_ball_top (d : ℕ) :
    aux_openCube d = Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) :=
  aux_openCube_eq_ball d

theorem aux_exists_contDiff_approx_top (d : ℕ)
    (u : (Fin d → ℝ) → ℝ) (g : Fin d → (Fin d → ℝ) → ℝ)
    (hu : MemLp u 2 (volume.restrict (aux_openCube d)))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict (aux_openCube d)))
    (hpair : ∀ (ψ : (Fin d → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ aux_openCube d → ∀ i : Fin d,
        (∫ x in aux_openCube d, ψ x * g i x) +
          (∫ x in aux_openCube d, fderiv ℝ ψ x (Pi.single i 1) * u x) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ 1 φ ∧
      (∫ x in aux_openCube d, (u x - φ x) ^ 2) < ε ∧
      ∀ i : Fin d, (∫ x in aux_openCube d, (g i x - fderiv ℝ φ x (Pi.single i 1)) ^ 2) < ε :=
  aux_exists_contDiff_approx_of_isWeakGradientPair d u g hu hg hpair ε hε

lemma aux_endpoint_estimate_on (f g : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (side : Bool) :
    (f (if side then 1 else 0)) ^ 2 ≤
      ∫ t in (0 : ℝ)..1, 2 * (f t) ^ 2 + (g t) ^ 2 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hfc : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hwi (a : ℝ) :
      IntervalIntegrable
        (fun t : ℝ => (f t) ^ 2 + (t - a) * (2 * f t * g t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc h01
    exact (hfc.pow 2).add
      ((continuousOn_id.sub continuousOn_const).mul
        ((continuousOn_const.mul hfc).mul hg))
  have hui :
      IntervalIntegrable
        (fun t : ℝ => 2 * (f t) ^ 2 + (g t) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc h01
    exact (continuousOn_const.mul (hfc.pow 2)).add (hg.pow 2)
  have hFTC (a : ℝ) :
      (∫ t in (0 : ℝ)..1, (f t) ^ 2 + (t - a) * (2 * f t * g t)) =
        (1 - a) * (f 1) ^ 2 - (0 - a) * (f 0) ^ 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => (t - a) * (f t) ^ 2) ?_ (hwi a)
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le h01] using ht
    convert ((hasDerivAt_id t).sub_const a).mul ((hf t ht').pow 2) using 1 <;>
      (try funext x) <;> simp only [id, Pi.pow_apply, Pi.mul_apply] ; ring
  have hMono (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      (∫ t in (0 : ℝ)..1, (f t) ^ 2 + (t - a) * (2 * f t * g t)) ≤
        ∫ t in (0 : ℝ)..1, 2 * (f t) ^ 2 + (g t) ^ 2 := by
    refine intervalIntegral.integral_mono_on h01 (hwi a) hui ?_
    intro t ht
    have hFactors : 0 ≤ (1 - (t - a)) * (1 + (t - a)) :=
      mul_nonneg (by linarith [ht.2, ha.1]) (by linarith [ht.1, ha.2])
    have hWeight : (t - a) ^ 2 ≤ 1 := by
      nlinarith only [hFactors]
    have hRemainder : 0 ≤ (1 - (t - a) ^ 2) * (g t) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hWeight) (sq_nonneg (g t))
    nlinarith only [sq_nonneg (f t - (t - a) * g t), hRemainder]
  cases side with
  | false =>
      change (f 0) ^ 2 ≤ _
      simpa only [sub_self, zero_sub, zero_mul, neg_one_mul,
        sub_neg_eq_add, zero_add] using
        (hFTC 1).symm.le.trans (hMono 1 ⟨by norm_num, by norm_num⟩)
  | true =>
      change (f 1) ^ 2 ≤ _
      simpa only [sub_zero, sub_self, one_mul, zero_mul] using
        (hFTC 0).symm.le.trans (hMono 0 ⟨by norm_num, by norm_num⟩)

theorem aux_endpoint_estimate (f g : ℝ → ℝ) (hf : ∀ t : ℝ, HasDerivAt f (g t) t) (hg : Continuous g)
    (side : Bool) :
    (f (if side then 1 else 0)) ^ 2 ≤ ∫ t in (0 : ℝ)..1, 2 * (f t) ^ 2 + (g t) ^ 2 := by
  exact aux_endpoint_estimate_on f g (fun t _ => hf t) hg.continuousOn side

lemma aux_mem_unitCube {k : ℕ} {x : Fin k → ℝ} :
    x ∈ aux_unitCube k ↔ ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · intro hx j
    exact hx j (Set.mem_univ j)
  · intro hx j hj
    exact hx j

lemma aux_insertNth_mem {n : ℕ} (i : Fin (n + 1)) {t : ℝ} {y : Fin n → ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ aux_unitCube n) :
    Fin.insertNth (α := fun _ => ℝ) i t y ∈ aux_unitCube (n + 1) := by
  apply aux_mem_unitCube.mpr
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using ht
  · simpa only [Fin.insertNth_apply_succAbove] using (aux_mem_unitCube.mp hy k)

lemma aux_continuous_insertNth {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => Fin.insertNth (α := fun _ => ℝ) i p.1 p.2) := by
  apply continuous_pi
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using
      (continuous_fst : Continuous (fun p : ℝ × (Fin n → ℝ) => p.1))
  · simpa only [Fin.insertNth_apply_succAbove, Function.comp_def] using
      ((continuous_apply k).comp continuous_snd :
        Continuous (fun p : ℝ × (Fin n → ℝ) => p.2 k))

lemma aux_continuous_face {n : ℕ} (i : Fin (n + 1)) (s : ℝ) :
    Continuous (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i s y) := by
  apply continuous_pi
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => s))
  · simpa only [Fin.insertNth_apply_succAbove] using
      (continuous_apply k : Continuous (fun y : Fin n → ℝ => y k))

lemma aux_hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Fin.insertNth (α := fun _ => ℝ) i s y) (Pi.single i 1) t := by
  apply hasDerivAt_pi.mpr
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [Fin.insertNth_apply_same, Pi.single_eq_same] using hasDerivAt_id' t
  · simpa only [Fin.insertNth_apply_succAbove,
      Pi.single_eq_of_ne (Fin.succAbove_ne i k)] using hasDerivAt_const t (y k)

lemma aux_cube_measure (k : ℕ) :
    (volume : Measure (Fin k → ℝ)).restrict (aux_unitCube k) =
      Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Icc 0 1)) := by
  exact Measure.restrict_pi_pi
    (fun _ : Fin k => (volume : Measure ℝ)) (fun _ => Set.Icc 0 1)

lemma aux_cube_fubini {n : ℕ} (i : Fin (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℝ) (hF : ContinuousOn F (aux_unitCube (n + 1))) :
    IntegrableOn
      (fun y => ∫ t in Set.Icc (0 : ℝ) 1, F (Fin.insertNth (α := fun _ => ℝ) i t y))
      (aux_unitCube n) ∧
    (∫ x in aux_unitCube (n + 1), F x) =
      ∫ y in aux_unitCube n, ∫ t in Set.Icc (0 : ℝ) 1, F (Fin.insertNth (α := fun _ => ℝ) i t y) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let ν : Measure (Fin n → ℝ) := volume.restrict (aux_unitCube n)
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i
  have hp : MeasurePreserving e
      (volume.restrict (aux_unitCube (n + 1))) (μ.prod ν) := by
    dsimp only [μ, ν]
    rw [aux_cube_measure (n + 1), aux_cube_measure n]
    exact measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (volume : Measure ℝ).restrict (Set.Icc 0 1)) i
  have hFprod :
      ContinuousOn
        (fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth (α := fun _ => ℝ) i p.1 p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ aux_unitCube n) := by
    exact hF.comp (aux_continuous_insertNth i).continuousOn
      (fun p hp => aux_insertNth_mem i hp.1 hp.2)
  have hInt :
      Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth (α := fun _ => ℝ) i p.1 p.2))
        (μ.prod ν) := by
    dsimp only [μ, ν]
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).prod
        (aux_isCompact_unitCube n)) hFprod
  refine ⟨?_, ?_⟩
  · exact hInt.integral_prod_right
  · calc
      (∫ x in aux_unitCube (n + 1), F x) =
          ∫ p, F (e.symm p) ∂(μ.prod ν) :=
        ((MeasurePreserving.symm e hp).integral_comp' F).symm
      _ = ∫ y in aux_unitCube n, ∫ t in Set.Icc (0 : ℝ) 1,
          F (Fin.insertNth (α := fun _ => ℝ) i t y) :=
        integral_prod_symm
          (fun p : ℝ × (Fin n → ℝ) => F (Fin.insertNth (α := fun _ => ℝ) i p.1 p.2)) hInt

lemma aux_face_trace_le (n : ℕ) (φ : (Fin (n + 1) → ℝ) → ℝ)
    (i : Fin (n + 1)) (side : Bool)
    (hφc : ContinuousOn φ (aux_unitCube (n + 1)))
    (hφd : ∀ x ∈ aux_unitCube (n + 1), DifferentiableAt ℝ φ x)
    (hDc : ContinuousOn (fun x => fderiv ℝ φ x (Pi.single i 1))
      (aux_unitCube (n + 1))) :
    (∫ y in aux_unitCube n, (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
      ∫ x in aux_unitCube (n + 1), 2 * (φ x) ^ 2 +
        (fderiv ℝ φ x (Pi.single i 1)) ^ 2 := by
  let F : (Fin (n + 1) → ℝ) → ℝ :=
    fun x => 2 * (φ x) ^ 2 + (fderiv ℝ φ x (Pi.single i 1)) ^ 2
  have hFc : ContinuousOn F (aux_unitCube (n + 1)) := by
    exact (continuousOn_const.mul (hφc.pow 2)).add (hDc.pow 2)
  have hs : (if side then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
    cases side <;> constructor <;> norm_num
  have hFaceC :
      ContinuousOn
        (fun y => (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2)
        (aux_unitCube n) := by
    exact (hφc.comp (aux_continuous_face i _).continuousOn
      (fun y hy => aux_insertNth_mem i hs hy)).pow 2
  have hFaceInt :
      IntegrableOn
        (fun y => (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2)
        (aux_unitCube n) :=
    ContinuousOn.integrableOn_compact (aux_isCompact_unitCube n) hFaceC
  have hPoint : ∀ y ∈ aux_unitCube n,
      (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2 ≤
        ∫ t in Set.Icc (0 : ℝ) 1, F (Fin.insertNth (α := fun _ => ℝ) i t y) := by
    intro y hy
    have hLine : Continuous (fun t : ℝ => Fin.insertNth (α := fun _ => ℝ) i t y) := by
      exact continuous_iff_continuousAt.mpr
        (fun t => (aux_hasDerivAt_insertNth i y t).continuousAt)
    have hSliceD : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => φ (Fin.insertNth (α := fun _ => ℝ) i s y))
          (fderiv ℝ φ (Fin.insertNth (α := fun _ => ℝ) i t y) (Pi.single i 1)) t := by
      intro t ht
      exact (hφd _ (aux_insertNth_mem i ht hy)).hasFDerivAt.comp_hasDerivAt t
        (aux_hasDerivAt_insertNth i y t)
    have hSliceC :
        ContinuousOn
          (fun t : ℝ => fderiv ℝ φ (Fin.insertNth (α := fun _ => ℝ) i t y) (Pi.single i 1))
          (Set.Icc (0 : ℝ) 1) := by
      exact hDc.comp hLine.continuousOn
        (fun t ht => aux_insertNth_mem i ht hy)
    have h := aux_endpoint_estimate_on
      (fun t : ℝ => φ (Fin.insertNth (α := fun _ => ℝ) i t y))
      (fun t : ℝ => fderiv ℝ φ (Fin.insertNth (α := fun _ => ℝ) i t y) (Pi.single i 1))
      hSliceD hSliceC side
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      ← integral_Icc_eq_integral_Ioc] at h
    exact h
  obtain ⟨hNested, hFubini⟩ := aux_cube_fubini i F hFc
  calc
    (∫ y in aux_unitCube n, (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
        ∫ y in aux_unitCube n, ∫ t in Set.Icc (0 : ℝ) 1,
          F (Fin.insertNth (α := fun _ => ℝ) i t y) :=
      setIntegral_mono_on hFaceInt hNested
        (aux_isCompact_unitCube n).isClosed.measurableSet hPoint
    _ = ∫ x in aux_unitCube (n + 1), F x := hFubini.symm

theorem aux_face_trace_le_c1 (n : ℕ) (φ : (Fin (n + 1) → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (i : Fin (n + 1)) (side : Bool) :
    (∫ y in aux_unitCube n, (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
      ∫ x in aux_unitCube (n + 1), 2 * (φ x) ^ 2 + (fderiv ℝ φ x (Pi.single i 1)) ^ 2 := by
  refine aux_face_trace_le n φ i side hφ.continuous.continuousOn ?_ ?_
  · intro x hx
    exact (hφ.differentiable (by norm_num)) x
  · exact ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn

theorem aux_face_trace_le_gradient (n : ℕ) (φ : (Fin (n + 1) → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) (i : Fin (n + 1)) (side : Bool) :
    (∫ y in aux_unitCube n,
      (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
      ∫ x in aux_unitCube (n + 1), 2 * (φ x) ^ 2 +
        ∑ j : Fin (n + 1), (fderiv ℝ φ x (Pi.single j 1)) ^ 2 := by
  have hd (j : Fin (n + 1)) :
      Continuous (fun x => (fderiv ℝ φ x (Pi.single j 1)) ^ 2) :=
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  have hLowC :
      Continuous (fun x => 2 * (φ x) ^ 2 +
        (fderiv ℝ φ x (Pi.single i 1)) ^ 2) :=
    (continuous_const.mul (hφ.continuous.pow 2)).add (hd i)
  have hFullC :
      Continuous (fun x => 2 * (φ x) ^ 2 +
        ∑ j : Fin (n + 1), (fderiv ℝ φ x (Pi.single j 1)) ^ 2) :=
    (continuous_const.mul (hφ.continuous.pow 2)).add
      (continuous_finsetSum Finset.univ (fun j _ => hd j))
  refine (aux_face_trace_le_c1 n φ hφ i side).trans ?_
  refine setIntegral_mono_on
    (ContinuousOn.integrableOn_compact (aux_isCompact_unitCube (n + 1))
      hLowC.continuousOn)
    (ContinuousOn.integrableOn_compact (aux_isCompact_unitCube (n + 1))
      hFullC.continuousOn)
    (aux_isCompact_unitCube (n + 1)).isClosed.measurableSet ?_
  intro x hx
  gcongr
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (fderiv ℝ φ x (Pi.single j 1))) (Finset.mem_univ i)

lemma aux_cube_restrict_eq (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (aux_openCube d) =
      volume.restrict (aux_unitCube d) := by
  have hne (a : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ a := by
    rw [ae_iff]
    have he : {t : ℝ | ¬t ≠ a} = {a} := by
      ext t
      simp only [mem_ofPred_eq, not_not, Set.mem_singleton_iff]
    rw [he, measure_singleton]
  have hI : (volume : Measure ℝ).restrict (Set.Ioo 0 1) =
      volume.restrict (Set.Icc 0 1) := by
    apply Measure.restrict_congr_set
    filter_upwards [hne 0, hne 1] with t ht0 ht1
    apply propext
    constructor
    · intro ht
      exact ⟨ht.1.le, ht.2.le⟩
    · intro ht
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  change (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.pi Set.univ (fun _ => Set.Ioo (0 : ℝ) 1)) =
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1))
  rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  simp only [hI]

lemma aux_Lp_dist_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (MemLp.toLp f hf) (MemLp.toLp g hg) ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [dist_eq_norm, ← hf.toLp_sub hg]
  exact (aux_integral_sq_eq_norm_sq (hf.sub hg)).symm

lemma aux_pair_error_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f p q : α → ℝ} (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) (hq : MemLp q 2 μ) :
    (∫ x, (p x - q x) ^ 2 ∂μ) ≤
      2 * (∫ x, (f x - p x) ^ 2 ∂μ) + 2 * (∫ x, (f x - q x) ^ 2 ∂μ) := by
  have hfp : Integrable (fun x => (f x - p x) ^ 2) μ := (hf.sub hp).integrable_sq
  have hfq : Integrable (fun x => (f x - q x) ^ 2) μ := (hf.sub hq).integrable_sq
  have hpq : Integrable (fun x => (p x - q x) ^ 2) μ := (hp.sub hq).integrable_sq
  have h2p : Integrable (fun x => 2 * (f x - p x) ^ 2) μ := hfp.const_mul 2
  have h2q : Integrable (fun x => 2 * (f x - q x) ^ 2) μ := hfq.const_mul 2
  calc
    (∫ x, (p x - q x) ^ 2 ∂μ) ≤
        ∫ x, 2 * (f x - p x) ^ 2 + 2 * (f x - q x) ^ 2 ∂μ := by
      apply integral_mono hpq (h2p.add h2q)
      intro x
      simp only [Pi.add_apply]
      nlinarith only [sq_nonneg ((f x - p x) + (f x - q x))]
    _ = _ := by
      rw [integral_add h2p h2q, integral_const_mul, integral_const_mul]

lemma aux_face_error_le (n : ℕ)
    (u g p q : (Fin (n + 1) → ℝ) → ℝ)
    (hu : MemLp u 2 (volume.restrict (aux_openCube (n + 1))))
    (hg : MemLp g 2 (volume.restrict (aux_openCube (n + 1))))
    (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q)
    (i : Fin (n + 1)) (side : Bool) :
    (∫ y in aux_unitCube n,
      (p (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y) -
        q (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
      4 * (∫ x in aux_openCube (n + 1), (u x - p x) ^ 2) +
      4 * (∫ x in aux_openCube (n + 1), (u x - q x) ^ 2) +
      2 * (∫ x in aux_openCube (n + 1), (g x - fderiv ℝ p x (Pi.single i 1)) ^ 2) +
      2 * (∫ x in aux_openCube (n + 1), (g x - fderiv ℝ q x (Pi.single i 1)) ^ 2) := by
  let dp := fun x => fderiv ℝ p x (Pi.single i 1)
  let dq := fun x => fderiv ℝ q x (Pi.single i 1)
  have hp2 := aux_continuous_memLp_openCube hp.continuous
  have hq2 := aux_continuous_memLp_openCube hq.continuous
  have hdp2 : MemLp dp 2 (volume.restrict (aux_openCube (n + 1))) :=
    aux_continuous_memLp_openCube
      ((hp.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hdq2 : MemLp dq 2 (volume.restrict (aux_openCube (n + 1))) :=
    aux_continuous_memLp_openCube
      ((hq.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hdiff (x : Fin (n + 1) → ℝ) :
      fderiv ℝ (p - q) x (Pi.single i 1) = dp x - dq x := by
    rw [fderiv_sub ((hp.differentiable (by norm_num)) x) ((hq.differentiable (by norm_num)) x)]
    rfl
  have ht := aux_face_trace_le_c1 n (p - q) (hp.sub hq) i side
  have he :
      (∫ x in aux_unitCube (n + 1), 2 * ((p - q) x) ^ 2 +
        (fderiv ℝ (p - q) x (Pi.single i 1)) ^ 2) =
      2 * (∫ x in aux_openCube (n + 1), (p x - q x) ^ 2) +
        (∫ x in aux_openCube (n + 1), (dp x - dq x) ^ 2) := by
    rw [← aux_cube_restrict_eq]
    simp only [Pi.sub_apply, hdiff]
    have hA : Integrable (fun x => 2 * (p x - q x) ^ 2)
        (volume.restrict (aux_openCube (n + 1))) := (hp2.sub hq2).integrable_sq.const_mul 2
    have hB : Integrable (fun x => (dp x - dq x) ^ 2)
        (volume.restrict (aux_openCube (n + 1))) := (hdp2.sub hdq2).integrable_sq
    rw [integral_add hA hB, integral_const_mul]
  rw [he] at ht
  have h0 := aux_pair_error_le hu hp2 hq2
  have h1 := aux_pair_error_le hg hdp2 hdq2
  simp only [Pi.sub_apply] at ht
  dsimp only [dp, dq] at ht h1
  linarith

theorem aux_face_trace_le_of_isWeakGradientPair (n : ℕ)
    (u : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (hu : MemLp u 2 (volume.restrict (aux_openCube (n + 1))))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict (aux_openCube (n + 1))))
    (_hpair : aux_IsWeakGradientPair (aux_openCube (n + 1)) u g)
    (φ : ℕ → (Fin (n + 1) → ℝ) → ℝ)
    (hφ : ∀ k, ContDiff ℝ 1 (φ k))
    (huLim : Tendsto (fun k => ∫ x in aux_openCube (n + 1), (u x - φ k x) ^ 2)
      atTop (𝓝 0))
    (hgLim : ∀ i, Tendsto (fun k => ∫ x in aux_openCube (n + 1),
      (g i x - fderiv ℝ (φ k) x (Pi.single i 1)) ^ 2) atTop (𝓝 0)) :
    ∀ (i : Fin (n + 1)) (side : Bool),
      ∃ T : ℕ → Lp ℝ 2 (volume.restrict (aux_unitCube n)),
        (∀ k, (T k : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict (aux_unitCube n)]
          (fun y => φ k (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y))) ∧
        CauchySeq T ∧
          ∃ t : Lp ℝ 2 (volume.restrict (aux_unitCube n)), Tendsto T atTop (𝓝 t) := by
  intro i side
  let F : ℕ → (Fin n → ℝ) → ℝ :=
    fun k y => φ k (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)
  have hF (k : ℕ) : MemLp (F k) 2 (volume.restrict (aux_unitCube n)) :=
    aux_continuous_memLp_unitCube
      ((hφ k).continuous.comp (aux_continuous_face i _))
  let T : ℕ → Lp ℝ 2 (volume.restrict (aux_unitCube n)) :=
    fun k => MemLp.toLp (F k) (hF k)
  let E : ℕ → ℝ := fun k =>
    4 * (∫ x in aux_openCube (n + 1), (u x - φ k x) ^ 2) +
    2 * (∫ x in aux_openCube (n + 1),
      (g i x - fderiv ℝ (φ k) x (Pi.single i 1)) ^ 2)
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (huLim.const_mul 4).add ((hgLim i).const_mul 2)
  have hbound (k l : ℕ) : dist (T k) (T l) ^ 2 ≤ E k + E l := by
    calc
      dist (T k) (T l) ^ 2 = ∫ y in aux_unitCube n, (F k y - F l y) ^ 2 :=
        aux_Lp_dist_sq (hF k) (hF l)
      _ ≤ 4 * (∫ x in aux_openCube (n + 1), (u x - φ k x) ^ 2) +
          4 * (∫ x in aux_openCube (n + 1), (u x - φ l x) ^ 2) +
          2 * (∫ x in aux_openCube (n + 1),
            (g i x - fderiv ℝ (φ k) x (Pi.single i 1)) ^ 2) +
          2 * (∫ x in aux_openCube (n + 1),
            (g i x - fderiv ℝ (φ l) x (Pi.single i 1)) ^ 2) :=
        aux_face_error_le n u (g i) (φ k) (φ l) hu (hg i) (hφ k) (hφ l) i side
      _ = E k + E l := by dsimp only [E]; ring
  have hC : CauchySeq T := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hE.eventually (gt_mem_nhds (show 0 < ε ^ 2 / 2 by positivity)))
    refine ⟨N, ?_⟩
    intro k hk l hl
    have hkl := hbound k l
    have hkE := hN k hk
    have hlE := hN l hl
    nlinarith [(dist_nonneg : 0 ≤ dist (T k) (T l))]
  exact ⟨T, (fun k => (hF k).coeFn_toLp), hC, cauchySeq_tendsto_of_complete hC⟩


-- #print axioms aux_exists_contDiff_approx_of_isWeakGradientPair
-- #print axioms aux_exists_contDiff_approx_top
-- #print axioms aux_face_trace_le
-- #print axioms aux_face_trace_le_gradient
-- #print axioms aux_face_trace_le_of_isWeakGradientPair
-- #print axioms aux_endpoint_estimate



theorem aux_smooth_approx_cube (n : ℕ) (φ : (Fin (n + 1) → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (i : Fin (n + 1)) (side : Bool) :
    (∫ y in aux_unitCube n, (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
      ∫ x in aux_unitCube (n + 1), 2 * (φ x) ^ 2 + (fderiv ℝ φ x (Pi.single i 1)) ^ 2 :=
  aux_face_trace_le_c1 n φ hφ i side

end SubdiffusiveProcess.Paper
