module

public import SubdiffusiveProcess.Paper.aux_lane4_smooth_approx_cube
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib
public import SubdiffusiveProcess.Paper.aux_lane4_smooth_approx_cube

@[expose] public section

open MeasureTheory TopologicalSpace Set Filter Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped BigOperators ENNReal NNReal ContDiff Distributions

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section
namespace SubdiffusiveProcess.Paper

section AuxTrace
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

theorem aux_L2_inner {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f g : Lp ℝ 2 μ) :
    inner ℝ f g = ∫ x, f x * g x ∂μ := by
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using (L2.inner_def (𝕜 := ℝ) f g)

theorem aux_L2_inner_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f g : Lp ℝ 2 μ) (u w : α → ℝ)
    (hf : (f : α → ℝ) =ᵐ[μ] u) (hg : (g : α → ℝ) =ᵐ[μ] w) :
    inner ℝ f g = ∫ x, u x * w x ∂μ := by
  rw [aux_L2_inner]
  apply integral_congr_ae
  filter_upwards [hf, hg] with x hx hy
  rw [hx, hy]

theorem aux_L2_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℝ 2 μ) (u : α → ℝ)
    (hf : (f : α → ℝ) =ᵐ[μ] u) :
    ‖f‖ ^ 2 = ∫ x, (u x) ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ x, u x * u x ∂μ := aux_L2_inner_ae f f u u hf hf
    _ = ∫ x, (u x) ^ 2 ∂μ := by simp only [pow_two]

theorem aux_L2_sub_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f g : Lp ℝ 2 μ) (u w : α → ℝ)
    (hf : (f : α → ℝ) =ᵐ[μ] u) (hg : (g : α → ℝ) =ᵐ[μ] w) :
    ‖f - g‖ ^ 2 = ∫ x, (u x - w x) ^ 2 ∂μ := by
  apply aux_L2_norm_sq
  filter_upwards [Lp.coeFn_sub f g, hf, hg] with x hsub hx hy
  simpa only [Pi.sub_apply, hx, hy] using hsub

theorem aux_unitNeumannCube_coe (d : ℕ) :
    (unitNeumannCube d : Set (SpatialCoordinates d)) = aux_openCube d := by
  rw [unitNeumannCube, centeredCube_eq_pi]
  norm_num [aux_openCube]

theorem aux_unitCube_eq_Icc (d : ℕ) :
    aux_unitCube d = Set.Icc (0 : SpatialCoordinates d) 1 := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i => (hx i (Set.mem_univ i)).1,
      fun i => (hx i (Set.mem_univ i)).2⟩
  · rintro ⟨h0, h1⟩ i hi
    exact ⟨h0 i, h1 i⟩

theorem aux_openCube_subset_unitCube_tr (d : ℕ) :
    aux_openCube d ⊆ aux_unitCube d := by
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

theorem aux_volume_openCube_tr (d : ℕ) : volume (aux_openCube d) = 1 := by
  simp [aux_openCube, Real.volume_pi_Ioo]

theorem aux_volume_unitCube (d : ℕ) : volume (aux_unitCube d) = 1 := by
  rw [aux_unitCube_eq_Icc, Real.volume_Icc_pi]
  simp

theorem aux_cube_restrict (d : ℕ) :
    volume.restrict (aux_openCube d) = volume.restrict (aux_unitCube d) := by
  let : IsFiniteMeasure (volume.restrict (aux_openCube d)) :=
    isFiniteMeasure_restrict.mpr (by rw [aux_volume_openCube_tr]; norm_num)
  apply Measure.eq_of_le_of_measure_univ_eq
    (Measure.restrict_mono_set volume (aux_openCube_subset_unitCube_tr d))
  simp only [Measure.restrict_apply_univ, aux_volume_openCube_tr, aux_volume_unitCube]

theorem aux_Q_measure (d : ℕ) :
    volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) =
      volume.restrict (aux_unitCube d) := by
  rw [aux_unitNeumannCube_coe, aux_cube_restrict]

instance aux_unitNeumannCube_finite (d : ℕ) :
    IsFiniteMeasure (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  apply isFiniteMeasure_restrict.mpr
  rw [aux_unitNeumannCube_coe, aux_volume_openCube_tr]
  norm_num

theorem aux_memLp_continuous {d : ℕ} {f : SpatialCoordinates d → ℝ}
    (hf : Continuous f) :
    MemLp f 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  rw [aux_Q_measure]
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  change IntegrableOn (fun x => (f x) ^ 2) (aux_unitCube d) volume
  rw [aux_unitCube_eq_Icc]
  exact (hf.pow 2).integrableOn_Icc

noncomputable def aux_continuousL2 (d : ℕ) (f : SpatialCoordinates d → ℝ)
    (hf : Continuous f) : DomainL2 (unitNeumannCube d) :=
  (aux_memLp_continuous hf).toLp f

theorem aux_continuousL2_coeFn (d : ℕ) (f : SpatialCoordinates d → ℝ)
    (hf : Continuous f) :
    (aux_continuousL2 d f hf : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] f :=
  MemLp.coeFn_toLp _

theorem aux_continuousL2_add (d : ℕ) (f g : SpatialCoordinates d → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    aux_continuousL2 d (f + g) (hf.add hg) =
      aux_continuousL2 d f hf + aux_continuousL2 d g hg := by
  exact MemLp.toLp_add (aux_memLp_continuous hf) (aux_memLp_continuous hg)

theorem aux_continuousL2_smul (d : ℕ) (c : ℝ) (f : SpatialCoordinates d → ℝ)
    (hf : Continuous f) :
    aux_continuousL2 d (c • f) (hf.const_smul c) =
      c • aux_continuousL2 d f hf := by
  exact MemLp.toLp_const_smul c (aux_memLp_continuous hf)

theorem aux_continuous_partial {d : ℕ} {φ : SpatialCoordinates d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (i : Fin d) :
    Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
  (hφ.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const)

noncomputable def aux_C1Data {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (hφ : ContDiff ℝ 1 φ) : SobolevData (unitNeumannCube d) :=
  (aux_continuousL2 d φ hφ.continuous,
    fun i => aux_continuousL2 d (fun x => fderiv ℝ φ x (Pi.single i 1))
      (aux_continuous_partial hφ i))

theorem aux_C1Data_fst_ae {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    ((aux_C1Data φ hφ).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] φ :=
  aux_continuousL2_coeFn d φ hφ.continuous

theorem aux_C1Data_snd_ae {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (hφ : ContDiff ℝ 1 φ) (i : Fin d) :
    ((aux_C1Data φ hφ).2 i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
      (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
  aux_continuousL2_coeFn d _ (aux_continuous_partial hφ i)

theorem aux_setIntegral_mul_eq {d : ℕ} {s : Set (SpatialCoordinates d)}
    {φ : SpatialCoordinates d → ℝ} (hφ : tsupport φ ⊆ s)
    (g : SpatialCoordinates d → ℝ) :
    (∫ x in s, φ x * g x) = ∫ x, φ x * g x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : φ x = 0 := by
    by_contra hne
    exact hx (hφ (subset_closure hne))
  rw [hz, zero_mul]

theorem aux_tsupport_fderiv_apply_subset {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (v : SpatialCoordinates d) :
    tsupport (fun x => fderiv ℝ φ x v) ⊆ tsupport φ := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro x hx
  have hx' : fderiv ℝ φ x v ≠ 0 := hx
  intro h
  apply hx'
  rw [show fderiv ℝ φ x = 0 from h]
  rfl

theorem aux_C1Data_mem {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    aux_C1Data φ hφ ∈ weakSobolevGraph (unitNeumannCube d) := by
  apply (mem_weakSobolevGraph_iff _).mpr
  intro ψ i
  have heq₁ :
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        ψ x * (aux_C1Data φ hφ).2 i x) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        ψ x * fderiv ℝ φ x (Pi.single i 1) := by
    apply integral_congr_ae
    filter_upwards [aux_C1Data_snd_ae φ hφ i] with x hx
    rw [hx]
  have heq₂ :
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        fderiv ℝ ψ x (Pi.single i 1) * (aux_C1Data φ hφ).1 x) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        fderiv ℝ ψ x (Pi.single i 1) * φ x := by
    apply integral_congr_ae
    filter_upwards [aux_C1Data_fst_ae φ hφ] with x hx
    rw [hx]
  rw [heq₁, heq₂]
  rw [aux_setIntegral_mul_eq ψ.tsupport_subset,
    aux_setIntegral_mul_eq
      ((aux_tsupport_fderiv_apply_subset ψ (Pi.single i 1)).trans ψ.tsupport_subset)]
  have hcψ : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (ψ.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have h₁ : Integrable (fun x => fderiv ℝ ψ x (Pi.single i 1) * φ x) volume :=
    (hcψ.mul hφ.continuous).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1)).mul_right
  have h₂ : Integrable (fun x => ψ x * fderiv ℝ φ x (Pi.single i 1)) volume :=
    (ψ.contDiff.continuous.mul (aux_continuous_partial hφ i)).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right
  have h₃ : Integrable (fun x => ψ x * φ x) volume :=
    (ψ.contDiff.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    (fun x _ => (ψ.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _ => (hφ.differentiable (by simp)).differentiableAt)
  exact add_eq_zero_iff_eq_neg.mpr hibp

theorem aux_graph_zero_of_fst_zero
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (v : weakSobolevGraph Ω) (h0 : (v : SobolevData Ω).1 = 0) : v = 0 := by
  have hu : ((v : SobolevData Ω).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] (fun _ => 0) := by
    rw [h0]
    exact Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
  have hg (i : Fin d) : (v : SobolevData Ω).2 i = 0 := by
    have hint : IntegrableOn ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ)
        (Ω : Set (SpatialCoordinates d)) volume :=
      (Lp.memLp ((v : SobolevData Ω).2 i)).integrable (by norm_num)
    have hz : ∀ᵐ x ∂volume, x ∈ (Ω : Set (SpatialCoordinates d)) →
        (v : SobolevData Ω).2 i x = 0 := by
      apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hint.locallyIntegrableOn
      intro φ hφ hc hs
      let ψ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hc, hs⟩
      have htest := (mem_weakSobolevGraph_iff (v : SobolevData Ω)).mp v.property ψ i
      change (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * (v : SobolevData Ω).2 i x) +
        (∫ x in (Ω : Set (SpatialCoordinates d)),
          fderiv ℝ φ x (Pi.single i 1) * (v : SobolevData Ω).1 x) = 0 at htest
      have hsecond : (∫ x in (Ω : Set (SpatialCoordinates d)),
          fderiv ℝ φ x (Pi.single i 1) * (v : SobolevData Ω).1 x) = 0 := by
        calc
          _ = ∫ x in (Ω : Set (SpatialCoordinates d)), (0 : ℝ) := by
            apply integral_congr_ae
            filter_upwards [hu] with x hx
            rw [hx, mul_zero]
          _ = 0 := by simp
      rw [hsecond, add_zero] at htest
      have hfull : (∫ x, φ x * (v : SobolevData Ω).2 i x) = 0 :=
        (aux_setIntegral_mul_eq hs _).symm.trans htest
      simpa only [smul_eq_mul] using hfull
    apply Lp.ext
    have hz' : ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))] (fun _ => 0) :=
      (ae_restrict_iff' Ω.isOpen.measurableSet).mpr hz
    exact hz'.trans (Lp.coeFn_zero ℝ 2
      (volume.restrict (Ω : Set (SpatialCoordinates d)))).symm
  apply Subtype.ext
  apply Prod.ext
  · exact h0
  · funext i
    exact hg i

theorem aux_graph_fst_injective
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] :
    Function.Injective (fun v : weakSobolevGraph Ω => (v : SobolevData Ω).1) := by
  intro v w h
  apply sub_eq_zero.mp
  apply aux_graph_zero_of_fst_zero (v - w)
  change (v : SobolevData Ω).1 - (w : SobolevData Ω).1 = 0
  exact sub_eq_zero.mpr h

def aux_C1Functions (d : ℕ) : Submodule ℝ (SpatialCoordinates d → ℝ) where
  carrier := {φ | ContDiff ℝ 1 φ}
  zero_mem' := (contDiff_const : ContDiff ℝ 1 (fun _ : SpatialCoordinates d => (0 : ℝ)))
  add_mem' := fun {f g} hf hg => (show ContDiff ℝ 1 f from hf).add (show ContDiff ℝ 1 g from hg)
  smul_mem' := fun c f hf => (show ContDiff ℝ 1 f from hf).const_smul c

theorem aux_C1_contDiff {d : ℕ} (f : aux_C1Functions d) :
    ContDiff ℝ 1 (f : SpatialCoordinates d → ℝ) := f.2

noncomputable def aux_C1Lift {d : ℕ} (f : aux_C1Functions d) :
    weakSobolevGraph (unitNeumannCube d) :=
  ⟨aux_C1Data f.1 (aux_C1_contDiff f), aux_C1Data_mem f.1 (aux_C1_contDiff f)⟩

noncomputable def aux_C1GraphMap (d : ℕ) :
    aux_C1Functions d →ₗ[ℝ] weakSobolevGraph (unitNeumannCube d) where
  toFun := aux_C1Lift
  map_add' f g := by
    apply aux_graph_fst_injective
    change aux_continuousL2 d (f.1 + g.1)
        ((aux_C1_contDiff f).continuous.add (aux_C1_contDiff g).continuous) =
      aux_continuousL2 d f.1 (aux_C1_contDiff f).continuous +
        aux_continuousL2 d g.1 (aux_C1_contDiff g).continuous
    exact aux_continuousL2_add d f.1 g.1 (aux_C1_contDiff f).continuous
      (aux_C1_contDiff g).continuous
  map_smul' c f := by
    apply aux_graph_fst_injective
    change aux_continuousL2 d (c • f.1) ((aux_C1_contDiff f).continuous.const_smul c) =
      c • aux_continuousL2 d f.1 (aux_C1_contDiff f).continuous
    exact aux_continuousL2_smul d c f.1 (aux_C1_contDiff f).continuous

theorem aux_C1GraphMap_fst_ae {d : ℕ} (f : aux_C1Functions d) :
    (((aux_C1GraphMap d f : weakSobolevGraph (unitNeumannCube d)) :
      SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] f.1 :=
  aux_C1Data_fst_ae f.1 (aux_C1_contDiff f)

theorem aux_C1GraphMap_snd_ae {d : ℕ} (f : aux_C1Functions d) (i : Fin d) :
    (((aux_C1GraphMap d f : weakSobolevGraph (unitNeumannCube d)) :
      SobolevData (unitNeumannCube d)).2 i : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
        (fun x => fderiv ℝ f.1 x (Pi.single i 1)) :=
  aux_C1Data_snd_ae f.1 (aux_C1_contDiff f) i

def aux_faceEmbedding (n : ℕ) (i : Fin (n + 1)) (side : Bool) :
    SpatialCoordinates n → SpatialCoordinates (n + 1) :=
  fun y => Fin.insertNth i (if side then 1 else 0) y

theorem aux_continuous_faceEmbedding (n : ℕ) (i : Fin (n + 1)) (side : Bool) :
    Continuous (aux_faceEmbedding n i side) := by
  apply continuous_pi
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [aux_faceEmbedding, Fin.insertNth_apply_same] using
      (continuous_const : Continuous (fun _ : SpatialCoordinates n =>
        (if side then 1 else 0 : ℝ)))
  · simpa only [aux_faceEmbedding, Fin.insertNth_apply_succAbove] using
      (continuous_apply k : Continuous (fun y : SpatialCoordinates n => y k))

theorem aux_faceEmbedding_mem (n : ℕ) (i : Fin (n + 1)) (side : Bool)
    {y : SpatialCoordinates n} (hy : y ∈ aux_unitCube n) :
    aux_faceEmbedding n i side y ∈ aux_unitCube (n + 1) := by
  intro j hj
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp only [aux_faceEmbedding, Fin.insertNth_apply_same, Set.mem_Icc]
    cases side <;> norm_num
  · simpa only [aux_faceEmbedding, Fin.insertNth_apply_succAbove] using
      hy k (Set.mem_univ k)

noncomputable def aux_FaceMap (n : ℕ) (i : Fin (n + 1)) (side : Bool) :
    aux_C1Functions (n + 1) →ₗ[ℝ] DomainL2 (unitNeumannCube n) where
  toFun f := aux_continuousL2 n (fun y => f.1 (aux_faceEmbedding n i side y))
    ((aux_C1_contDiff f).continuous.comp (aux_continuous_faceEmbedding n i side))
  map_add' f g := by
    exact aux_continuousL2_add n
      (fun y => f.1 (aux_faceEmbedding n i side y))
      (fun y => g.1 (aux_faceEmbedding n i side y))
      ((aux_C1_contDiff f).continuous.comp (aux_continuous_faceEmbedding n i side))
      ((aux_C1_contDiff g).continuous.comp (aux_continuous_faceEmbedding n i side))
  map_smul' c f := by
    exact aux_continuousL2_smul n c
      (fun y => f.1 (aux_faceEmbedding n i side y))
      ((aux_C1_contDiff f).continuous.comp (aux_continuous_faceEmbedding n i side))

theorem aux_FaceMap_coeFn (n : ℕ) (i : Fin (n + 1)) (side : Bool)
    (f : aux_C1Functions (n + 1)) :
    (aux_FaceMap n i side f : SpatialCoordinates n → ℝ) =ᵐ[
      volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))]
      (fun y => f.1 (Fin.insertNth i (if side then 1 else 0) y)) :=
  aux_continuousL2_coeFn n _
    ((aux_C1_contDiff f).continuous.comp (aux_continuous_faceEmbedding n i side))

theorem aux_sq_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have hprod : 0 ≤ (b - a) * (b + a) :=
    mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  nlinarith only [hprod]

theorem aux_lt_of_sq_lt {a b : ℝ} (hb : 0 < b) (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hnot
  have hba : b ≤ a := le_of_not_gt hnot
  have hprod : 0 ≤ (a - b) * (a + b) :=
    mul_nonneg (sub_nonneg.mpr hba) (by linarith)
  nlinarith only [h, hprod]

theorem aux_le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hnot
  have hba : b < a := lt_of_not_ge hnot
  have hprod : 0 < (a - b) * (a + b) :=
    mul_pos (sub_pos.mpr hba) (by linarith)
  nlinarith only [h, hprod]

theorem aux_integrable_sq_continuous {d : ℕ} {f : SpatialCoordinates d → ℝ}
    (hf : Continuous f) :
    Integrable (fun x => (f x) ^ 2) (volume.restrict (aux_unitCube d)) := by
  change IntegrableOn (fun x => (f x) ^ 2) (aux_unitCube d) volume
  rw [aux_unitCube_eq_Icc]
  exact (hf.pow 2).integrableOn_Icc

theorem aux_FaceMap_bound
    (htrace : ∀ (n : ℕ) (φ : (Fin (n + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      ∀ (i : Fin (n + 1)) (side : Bool),
        (∫ y in aux_unitCube n,
          (φ (Fin.insertNth (α := fun _ => ℝ) i (if side then 1 else 0) y)) ^ 2) ≤
        ∫ x in aux_unitCube (n + 1),
          2 * (φ x) ^ 2 + (fderiv ℝ φ x (Pi.single i 1)) ^ 2)
    (n : ℕ) (i : Fin (n + 1)) (side : Bool) (f : aux_C1Functions (n + 1)) :
    ‖aux_FaceMap n i side f‖ ≤ 2 * ‖aux_C1GraphMap (n + 1) f‖ := by
  let v := aux_C1GraphMap (n + 1) f
  have hface : ‖aux_FaceMap n i side f‖ ^ 2 =
      ∫ y in aux_unitCube n, (f.1 (Fin.insertNth i (if side then 1 else 0) y)) ^ 2 := by
    calc
      _ = ∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          (f.1 (Fin.insertNth i (if side then 1 else 0) y)) ^ 2 :=
        aux_L2_norm_sq _ _ (aux_FaceMap_coeFn n i side f)
      _ = _ := by rw [aux_Q_measure]
  have hfst : ‖(v : SobolevData (unitNeumannCube (n + 1))).1‖ ^ 2 =
      ∫ x in aux_unitCube (n + 1), (f.1 x) ^ 2 := by
    calc
      _ = ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (f.1 x) ^ 2 := aux_L2_norm_sq _ _ (aux_C1GraphMap_fst_ae f)
      _ = _ := by rw [aux_Q_measure]
  have hsnd : ‖(v : SobolevData (unitNeumannCube (n + 1))).2 i‖ ^ 2 =
      ∫ x in aux_unitCube (n + 1), (fderiv ℝ f.1 x (Pi.single i 1)) ^ 2 := by
    calc
      _ = ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
          (fderiv ℝ f.1 x (Pi.single i 1)) ^ 2 :=
        aux_L2_norm_sq _ _ (aux_C1GraphMap_snd_ae f i)
      _ = _ := by rw [aux_Q_measure]
  have hif := aux_integrable_sq_continuous (aux_C1_contDiff f).continuous
  have hig := aux_integrable_sq_continuous (aux_continuous_partial (aux_C1_contDiff f) i)
  have hsq : ‖aux_FaceMap n i side f‖ ^ 2 ≤
      2 * ‖(v : SobolevData (unitNeumannCube (n + 1))).1‖ ^ 2 +
        ‖(v : SobolevData (unitNeumannCube (n + 1))).2 i‖ ^ 2 := by
    calc
      _ = ∫ y in aux_unitCube n,
          (f.1 (Fin.insertNth i (if side then 1 else 0) y)) ^ 2 := hface
      _ ≤ ∫ x in aux_unitCube (n + 1),
          2 * (f.1 x) ^ 2 + (fderiv ℝ f.1 x (Pi.single i 1)) ^ 2 :=
        htrace n f.1 (aux_C1_contDiff f) i side
      _ = _ := by
        rw [integral_add (hif.const_mul 2) hig, integral_const_mul, ← hfst, ← hsnd]
  have hb₀ : ‖(v : SobolevData (unitNeumannCube (n + 1))).1‖ ≤ ‖v‖ :=
    norm_fst_le (v : SobolevData (unitNeumannCube (n + 1)))
  have hb₁ : ‖(v : SobolevData (unitNeumannCube (n + 1))).2 i‖ ≤ ‖v‖ :=
    (norm_le_pi_norm (v : SobolevData (unitNeumannCube (n + 1))).2 i).trans
      (norm_snd_le (v : SobolevData (unitNeumannCube (n + 1))))
  have hb₀sq := aux_sq_mono (norm_nonneg _) hb₀
  have hb₁sq := aux_sq_mono (norm_nonneg _) hb₁
  apply aux_le_of_sq_le (mul_nonneg (by norm_num) (norm_nonneg v))
  nlinarith only [hsq, hb₀sq, hb₁sq, sq_nonneg ‖v‖]

theorem aux_C1GraphMap_dense
    (happrox : ∀ (d : ℕ) (u : (Fin d → ℝ) → ℝ) (g : Fin d → (Fin d → ℝ) → ℝ),
      MemLp u 2 (volume.restrict (aux_openCube d)) →
      (∀ i, MemLp (g i) 2 (volume.restrict (aux_openCube d))) →
      (∀ (φ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ aux_openCube d → ∀ i : Fin d,
          (∫ x in aux_openCube d, φ x * g i x) +
            (∫ x in aux_openCube d, fderiv ℝ φ x (Pi.single i 1) * u x) = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ 1 φ ∧
        (∫ x in aux_openCube d, (u x - φ x) ^ 2) < ε ∧
        ∀ i : Fin d,
          (∫ x in aux_openCube d, (g i x - fderiv ℝ φ x (Pi.single i 1)) ^ 2) < ε)
    (d : ℕ) : DenseRange (aux_C1GraphMap d) := by
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let u : SpatialCoordinates d → ℝ := (v : SobolevData (unitNeumannCube d)).1
  let g : Fin d → SpatialCoordinates d → ℝ :=
    fun i => (v : SobolevData (unitNeumannCube d)).2 i
  have huQ : MemLp u 2
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    Lp.memLp (v : SobolevData (unitNeumannCube d)).1
  have hu : MemLp u 2 (volume.restrict (aux_openCube d)) := by
    simpa only [aux_unitNeumannCube_coe] using huQ
  have hg : ∀ i, MemLp (g i) 2 (volume.restrict (aux_openCube d)) := by
    intro i
    have hi : MemLp (g i) 2
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
      Lp.memLp ((v : SobolevData (unitNeumannCube d)).2 i)
    simpa only [aux_unitNeumannCube_coe] using hi
  have hweak : ∀ (ψ : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ aux_openCube d → ∀ i : Fin d,
      (∫ x in aux_openCube d, ψ x * g i x) +
        (∫ x in aux_openCube d, fderiv ℝ ψ x (Pi.single i 1) * u x) = 0 := by
    intro ψ hψ hc hs i
    let η : 𝓓(unitNeumannCube d, ℝ) :=
      ⟨ψ, hψ, hc, by simpa only [aux_unitNeumannCube_coe] using hs⟩
    have h := (mem_weakSobolevGraph_iff
      (v : SobolevData (unitNeumannCube d))).mp v.property η i
    change (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), ψ x * g i x) +
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        fderiv ℝ ψ x (Pi.single i 1) * u x) = 0 at h
    simpa only [aux_unitNeumannCube_coe] using h
  obtain ⟨φ, hφ, h₀, h₁⟩ := happrox d u g hu hg hweak (ε ^ 2) (sq_pos_of_pos hε)
  let f : aux_C1Functions d := ⟨φ, hφ⟩
  have hnorm₀ : ‖(v : SobolevData (unitNeumannCube d)).1 - (aux_C1Data φ hφ).1‖ < ε := by
    apply aux_lt_of_sq_lt hε
    calc
      _ = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), (u x - φ x) ^ 2 :=
        aux_L2_sub_norm_sq _ _ u φ Filter.EventuallyEq.rfl (aux_C1Data_fst_ae φ hφ)
      _ = ∫ x in aux_openCube d, (u x - φ x) ^ 2 := by rw [aux_unitNeumannCube_coe]
      _ < ε ^ 2 := h₀
  have hnorm₁ :
      ‖(v : SobolevData (unitNeumannCube d)).2 - (aux_C1Data φ hφ).2‖ < ε := by
    apply (pi_norm_lt_iff hε).mpr
    intro i
    apply aux_lt_of_sq_lt hε
    change ‖(v : SobolevData (unitNeumannCube d)).2 i - (aux_C1Data φ hφ).2 i‖ ^ 2 < ε ^ 2
    calc
      _ = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          (g i x - fderiv ℝ φ x (Pi.single i 1)) ^ 2 :=
        aux_L2_sub_norm_sq _ _ (g i) _ Filter.EventuallyEq.rfl (aux_C1Data_snd_ae φ hφ i)
      _ = ∫ x in aux_openCube d, (g i x - fderiv ℝ φ x (Pi.single i 1)) ^ 2 := by
        rw [aux_unitNeumannCube_coe]
      _ < ε ^ 2 := h₁ i
  have hdist : dist v (aux_C1GraphMap d f) < ε := by
    rw [dist_eq_norm]
    change max ‖(v : SobolevData (unitNeumannCube d)).1 - (aux_C1Data φ hφ).1‖
      ‖(v : SobolevData (unitNeumannCube d)).2 - (aux_C1Data φ hφ).2‖ < ε
    exact max_lt_iff.mpr ⟨hnorm₀, hnorm₁⟩
  refine ⟨aux_C1GraphMap d f, ⟨f, rfl⟩, ?_⟩
  simpa only [dist_comm] using hdist

end AuxTrace

/-- Standard Sobolev trace and smooth-density construction on the unit cube.
- use coordinate-face restriction and H1 density.
- The concrete weak-gradient graph and restricted face volume are retained.
- Both the bounded trace operators and smooth density are conclusions.
- This source-step supplier adds no assumption to the boundary identity. -/
theorem lane4_neumann_boundary_identity_trace_foundation
    (n : ℕ) (_hn : 1 ≤ n) :
    let Q : Opens (SpatialCoordinates (n + 1)) := unitNeumannCube (n + 1)
    let Qface : Opens (SpatialCoordinates n) := unitNeumannCube n
    (      ∃ (Tr : (i : Fin (n + 1)) → (side : Bool) →
          weakSobolevGraph Q →L[ℝ] DomainL2 Qface) (Ct : ℝ),
        0 < Ct ∧
        (∀ (i : Fin (n + 1)) (side : Bool) (v : weakSobolevGraph Q),
          ‖Tr i side v‖ ≤ Ct * ‖v‖) ∧
        (∀ (φ : SpatialCoordinates (n + 1) → ℝ),
          ContDiff ℝ 1 φ →
            ∀ (v : weakSobolevGraph Q),
              ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
                volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ →
              ∀ (i : Fin (n + 1)) (side : Bool),
                ((Tr i side v : DomainL2 Qface) : SpatialCoordinates n → ℝ) =ᵐ[
                  volume.restrict (Qface : Set (SpatialCoordinates n))]
                  (fun y => φ (Fin.insertNth i (if side then 1 else 0) y)))) ∧ (Dense ({v : weakSobolevGraph Q |
      ∃ (φ : SpatialCoordinates (n + 1) → ℝ),
        ContDiff ℝ 1 φ ∧
          ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ} :
        Set (weakSobolevGraph Q))) := by
  dsimp only
  let e := aux_C1GraphMap (n + 1)
  have hd : DenseRange e := aux_C1GraphMap_dense (fun d u g hu hg hpair ε hε => aux_exists_contDiff_approx_top d u g hu hg hpair ε hε) (n + 1)
  let Tr : (i : Fin (n + 1)) → (side : Bool) →
      weakSobolevGraph (unitNeumannCube (n + 1)) →L[ℝ] DomainL2 (unitNeumannCube n) :=
    fun i side => (aux_FaceMap n i side).extendOfNorm e
  have hb : ∀ (i : Fin (n + 1)) (side : Bool) (f : aux_C1Functions (n + 1)),
      ‖aux_FaceMap n i side f‖ ≤ 2 * ‖e f‖ :=
    fun i side f => aux_FaceMap_bound (fun n φ hφ i side => aux_face_trace_le_c1 n φ hφ i side) n i side f
  refine ⟨⟨Tr, 2, by norm_num, ?_, ?_⟩, ?_⟩
  · intro i side v
    exact LinearMap.norm_extendOfNorm_apply_le (f := aux_FaceMap n i side)
      (e := e) hd 2 (hb i side) v
  · intro φ hφ v hv i side
    let f : aux_C1Functions (n + 1) := ⟨φ, hφ⟩
    have hv_eq : v = e f := by
      apply aux_graph_fst_injective
      apply Lp.ext
      exact hv.trans (aux_C1GraphMap_fst_ae f).symm
    have hTr : Tr i side (e f) = aux_FaceMap n i side f :=
      LinearMap.extendOfNorm_eq hd ⟨2, hb i side⟩ f
    rw [hv_eq, hTr]
    exact aux_FaceMap_coeFn n i side f
  · apply (show Dense (Set.range e) from hd).mono
    rintro v ⟨f, rfl⟩
    exact ⟨f.1, aux_C1_contDiff f, aux_C1GraphMap_fst_ae f⟩

section AuxTraceBonus
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

theorem aux_face_trace_of_C1_on_closed_cube
    (n : ℕ) {φ ψ : SpatialCoordinates (n + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (h : φ =ᵐ[volume.restrict
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))] ψ)
    (i : Fin (n + 1)) (side : Bool) :
    Set.EqOn
      (fun y => φ (Fin.insertNth i (if side then 1 else 0) y))
      (fun y => ψ (Fin.insertNth i (if side then 1 else 0) y)) (aux_unitCube n) ∧
    (fun y => φ (Fin.insertNth i (if side then 1 else 0) y)) =ᵐ[
      volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))]
      (fun y => ψ (Fin.insertNth i (if side then 1 else 0) y)) := by
  classical
  have hinside : Set.EqOn φ ψ
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) :=
    Measure.eqOn_open_of_ae_eq h (unitNeumannCube (n + 1)).isOpen
      hφ.continuous.continuousOn hψ.continuous.continuousOn
  have heqclosed : closure
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) ⊆
      {x | φ x = ψ x} :=
    closure_minimal hinside (isClosed_eq hφ.continuous hψ.continuous)
  have hclosure : aux_unitCube (n + 1) ⊆ closure
      (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))) := by
    rw [aux_unitNeumannCube_coe]
    intro x hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hc (j : Fin (n + 1)) : x j ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact hx j (Set.mem_univ j)
    have hp : ∀ j : Fin (n + 1), ∃ t ∈ Set.Ioo (0 : ℝ) 1,
        dist (x j) t < ε :=
      fun j => (Metric.mem_closure_iff.mp (hc j)) ε hε
    choose y hy hdist using hp
    refine ⟨y, ?_, ?_⟩
    · exact fun j _ => hy j
    · exact (dist_pi_lt_iff hε).mpr hdist
  have hface : Set.EqOn
      (fun y => φ (Fin.insertNth i (if side then 1 else 0) y))
      (fun y => ψ (Fin.insertNth i (if side then 1 else 0) y)) (aux_unitCube n) := by
    intro y hy
    exact heqclosed (hclosure (aux_faceEmbedding_mem n i side hy))
  refine ⟨hface, ?_⟩
  filter_upwards [ae_restrict_mem (unitNeumannCube n).isOpen.measurableSet] with y hy
  apply hface
  apply aux_openCube_subset_unitCube_tr n
  simpa only [aux_unitNeumannCube_coe] using hy

theorem aux_graph_norm_eq (v : weakSobolevGraph Ω) :
    ‖v‖ = max ‖(v : SobolevData Ω).1‖ ‖(v : SobolevData Ω).2‖ := rfl

theorem aux_extend_bounded_linear_of_dense
    {D E F : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : D →ₗ[ℝ] E) (he : DenseRange e)
    (f : D →ₗ[ℝ] F) (Ct : ℝ) (hCt : 0 < Ct)
    (hb : ∀ x, ‖f x‖ ≤ Ct * ‖e x‖) :
    ∃ T : E →L[ℝ] F,
      (∀ x, T (e x) = f x) ∧
      (∀ v, ‖T v‖ ≤ Ct * ‖v‖) ∧ ‖T‖ ≤ Ct := by
  refine ⟨f.extendOfNorm e, ?_, ?_, ?_⟩
  · exact fun x => LinearMap.extendOfNorm_eq he ⟨Ct, hb⟩ x
  · exact LinearMap.norm_extendOfNorm_apply_le he Ct hb
  · exact LinearMap.opNorm_extendOfNorm_le he hCt.le hb

end AuxTraceBonus

end SubdiffusiveProcess.Paper
