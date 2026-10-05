module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import Homogenization.Besov.Duality.ProjectionLimit
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

instance weightedSobolev_normalizedCubeProbability {d : ℕ} (Q : TriadicCube d) : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩

theorem weightedSobolev_coefficient_pos {d : ℕ}
    (U : Set (Homogenization.Vec d)) (b : Homogenization.Vec d → ℝ)
    (hb : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.CoefficientOn U b) :
    ∀ᵐ x ∂volume.restrict U, 0 < b x := by
  obtain ⟨-, ⟨lo, hi, hlo, hbound⟩⟩ := hb
  filter_upwards [hbound] with x hx
  exact hlo.trans_le hx.1

theorem weightedSobolev_coefficient_memLp {d : ℕ}
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)] (b : Vec d → ℝ)
    (hb : CoefficientOn U b) (p : ℝ≥0∞) : MemLp b p (volume.restrict U) := by
  obtain ⟨hmeas, lo, hi, hlo, hbound⟩ := hb
  have hmem : ∀ᵐ x ∂(volume.restrict U), b x ∈ Set.Icc lo hi := by
    filter_upwards [hbound] with x hx
    exact Set.mem_Icc.mpr hx
  exact memLp_of_bounded hmem hmeas p

theorem weightedSobolev_normalized_memLp {d : ℕ} (Q : TriadicCube d)
    (b : Vec d → ℝ) (p : ℝ≥0∞)
    (hb : MemLp b p (volume.restrict (openCubeSet Q))) :
    MemLp b p (normalizedCubeMeasure Q) := by
  have hcube : MemLp b p (cubeMeasure Q) := by
    simpa [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using! hb
  simpa [normalizedCubeMeasure] using! hcube.smul_measure ENNReal.ofReal_ne_top

theorem weightedSobolev_density_memLp {d : ℕ} (Q : TriadicCube d)
    (b : Vec d → ℝ) (p : ℝ≥0∞)
    (hb : MemLp b p (normalizedCubeMeasure Q)) :
    MemLp (fun x => b x / cubeAverage Q b - 1) p (normalizedCubeMeasure Q) := by
  have h3 : MemLp (fun x => (cubeAverage Q b)⁻¹ * b x + (-1 : ℝ)) p
      (normalizedCubeMeasure Q) :=
    (hb.const_mul (cubeAverage Q b)⁻¹).add (memLp_const (-1))
  simpa [div_eq_mul_inv, mul_comm, sub_eq_add_neg, Pi.add_apply] using! h3

theorem weightedSobolev_integral_lower {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (b : α → ℝ) (lo : ℝ)
    (hb : Integrable b μ) (hlo : ∀ᵐ x ∂μ, lo ≤ b x) : lo ≤ ∫ x, b x ∂μ := by
  have h := integral_mono_ae (integrable_const lo) hb hlo
  simpa [integral_const, probReal_univ] using! h

theorem weightedSobolev_positive_average {d : ℕ} (Q : TriadicCube d)
    (b : Vec d → ℝ) (lo : ℝ) (hlo : 0 < lo)
    (hb : Integrable b (normalizedCubeMeasure Q))
    (hbound : ∀ᵐ x ∂normalizedCubeMeasure Q, lo ≤ b x) : 0 < cubeAverage Q b := by
  have hμ : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have h := weightedSobolev_integral_lower (normalizedCubeMeasure Q) b lo hb hbound
  rw [cubeAverage_eq_integral_normalizedCubeMeasure Q b]
  exact hlo.trans_le h




def weightedSobolevMeasure {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) : Measure (Vec d) := (normalizedCubeMeasure Q).withDensity (fun x => ENNReal.ofReal (b x / cubeAverage Q b))

theorem weightedSobolev_normalized_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (havg : (∫ x, b x ∂μ) ≠ 0) : (∫ x, b x / (∫ y, b y ∂μ) ∂μ) = 1 := by
  rw [integral_div]
  exact div_self havg


theorem weightedSobolev_density_nonnegative {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (a : ℝ) (ha : 0 ≤ a) (hb : ∀ᵐ x ∂μ, 0 ≤ b x) : ∀ᵐ x ∂μ, 0 ≤ b x / a := by
  filter_upwards [hb] with x hx
  exact div_nonneg hx ha

theorem weightedSobolev_volume_algebra (A B N : ℝ) (hB : B ≠ 0) (hN : N ≠ 0) (h : A = N * B) : A⁻¹ * B = N⁻¹ := by
  rw [h]
  field_simp


theorem weightedSobolev_mean_sub {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (c : ℝ) (hf : Integrable f μ) (hzero : ∫ x, f x ∂μ = 0) : (∫ x, (f x - c) ∂μ) = -c := by
  rw [integral_sub hf (integrable_const c), hzero, integral_const]
  simp

theorem weightedSobolev_div_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (a : ℝ) (p : ℝ≥0∞) (hb : MemLp b p μ) : MemLp (fun x => b x / a) p μ := by
  simpa [div_eq_mul_inv, mul_comm] using! hb.const_mul a⁻¹

theorem weightedSobolev_ofReal_product (x b a : ℝ) (_hb : 0 ≤ b) (ha : 0 < a) : ENNReal.ofReal (b / a) * ENNReal.ofReal |x| = ENNReal.ofReal (|x| * b) / ENNReal.ofReal a := by
  rw [ENNReal.ofReal_div_of_pos ha, mul_comm, ENNReal.ofReal_mul (abs_nonneg x), mul_div_assoc]


theorem weightedSobolev_mean_enorm {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (c : ℝ) (h : (∫ x, f x ∂μ) = -c) : ‖c‖ₑ = ‖∫ x, f x ∂μ‖ₑ := by
  rw [h, enorm_neg]


theorem weightedSobolev_ofReal_rpow (x : ℝ) (p : ℝ) (hp : 0 ≤ p) : ENNReal.ofReal (|x| ^ p) = ‖x‖ₑ ^ p := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) hp]


theorem weightedSobolev_integral_const_probability {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) : (∫ _ : α, c ∂μ) = c := by
  simp [integral_const]


theorem weightedSobolev_centered_add {α : Type*} (f : α → ℝ) (c : ℝ) : (fun x => f x - c) + (fun _ => c) = f := by
  funext x
  exact sub_add_cancel (f x) c


theorem weightedSobolev_normalized_ae {d : ℕ} (Q : TriadicCube d) {P : Vec d → Prop} (hP : ∀ᵐx∂volume.restrict (openCubeSet Q), P x) : ∀ᵐx∂normalizedCubeMeasure Q, P x := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact Measure.ae_smul_measure hP _


theorem weightedSobolev_coefficient_cube_memLp {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (p : ℝ≥0∞) : MemLp b p (normalizedCubeMeasure Q) := by
  let : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    isFiniteMeasure_restrict.mpr (volume_openCubeSet_lt_top Q).ne
  exact weightedSobolev_normalized_memLp Q b p (weightedSobolev_coefficient_memLp (openCubeSet Q) b hb p)


theorem weightedSobolevMeasure_absolutelyContinuous {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) : weightedSobolevMeasure Q b ≪ normalizedCubeMeasure Q := by
  exact withDensity_absolutelyContinuous _ _



theorem weightedSobolev_probability {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (hb : Integrable b μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ b x) (hone : ∫ x, b x ∂μ = 1) : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (b x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ←ofReal_integral_eq_lintegral_ofReal hb hpos, hone]
  norm_num


theorem weightedSobolev_absolute {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) : μ.withDensity (fun x => ENNReal.ofReal (b x)) ≪ μ := by
  exact withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal (b x))


theorem weightedSobolev_rpow_square (x : ℝ≥0∞) (p : ℝ) : (x ^ p⁻¹) ^ (2 : ℕ) = x ^ (2 / p) := by
  rw [← ENNReal.rpow_natCast (x ^ p⁻¹) 2, ← ENNReal.rpow_mul]
  congr 1
  ring


theorem weightedSobolev_mean_norm {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hf : AEStronglyMeasurable f μ) : ‖∫ x, f x ∂μ‖ₑ ≤ eLpNorm f p μ := by
  exact (enorm_integral_le_lintegral_enorm f).trans (by rw [← eLpNorm_one_eq_lintegral_enorm hf]; exact eLpNorm_le_eLpNorm_of_exponent_le hp)


theorem weightedSobolev_triangle_algebra (x y z : ℝ≥0∞) (h : x ≤ y + z) (hz : z ≤ y) : x ≤ 2 * y := by
  calc x ≤ y+z := h
   _ ≤ y+y := add_le_add le_rfl hz
   _ = 2*y := (two_mul y).symm


theorem weightedSobolev_coefficient_mono {d : ℕ} {U V : Set (Vec d)} {b : Vec d → ℝ} (hVU : V ⊆ U) (hb : CoefficientOn U b) : CoefficientOn V b := by
  obtain ⟨hmeas, lo, hi, hlo, hbounds⟩ := hb
  exact ⟨hmeas.mono_measure (Measure.restrict_mono hVU le_rfl),
         lo, hi, hlo,
         ae_mono (Measure.restrict_mono hVU le_rfl) hbounds⟩


theorem weightedSobolev_norm_const {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (p : ℝ≥0∞) (hp : p ≠ 0) (c : ℝ) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ := by
  have hμ : μ ≠ 0 := by
    intro h
    have hu : μ Set.univ = 1 := measure_univ
    rw [h] at hu
    simp at hu
  rw [eLpNorm_const c hp hμ]
  simp only [measure_univ, ENNReal.one_rpow, mul_one]


theorem weightedSobolev_density_aemeasurable {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (a : ℝ) (hb : AEStronglyMeasurable b μ) : AEMeasurable (fun x => ENNReal.ofReal (b x / a)) μ := by
  exact (hb.aemeasurable.div_const a).ennreal_ofReal


theorem weightedSobolev_average_div_self {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) (hb : cubeAverage Q b ≠ 0) : (∫ x, b x / cubeAverage Q b ∂normalizedCubeMeasure Q) = 1 := by
  rw [integral_div, ← cubeAverage_eq_integral_normalizedCubeMeasure]; exact div_self hb


theorem weightedSobolev_coefficient_average_pos {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) : 0 < cubeAverage Q b := by
  obtain ⟨lo, hi, hlo, hbounds⟩ := hb.2
  have hlower : ∀ᵐ x ∂ normalizedCubeMeasure Q, lo ≤ b x :=
    weightedSobolev_normalized_ae Q (hbounds.mono fun x hx => hx.1)
  exact weightedSobolev_positive_average Q b lo hlo
    ((weightedSobolev_coefficient_cube_memLp Q b hb 1).integrable le_rfl) hlower


theorem weightedSobolevMeasure_isProbabilityMeasure {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) : IsProbabilityMeasure (weightedSobolevMeasure Q b) := by
  apply weightedSobolev_probability
  · exact (weightedSobolev_div_memLp _ b _ 1 (weightedSobolev_coefficient_cube_memLp Q b hb 1)).integrable le_rfl
  · filter_upwards [weightedSobolev_normalized_ae Q (weightedSobolev_coefficient_pos _ b hb)] with x hx
    exact div_nonneg hx.le (weightedSobolev_coefficient_average_pos Q b hb).le
  · exact weightedSobolev_average_div_self Q b (weightedSobolev_coefficient_average_pos Q b hb).ne'


theorem weightedSobolev_volume_factor {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) : ENNReal.ofReal ((cubeVolume Q)⁻¹) = ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((cubeVolume R)⁻¹) := by
  have hc : 0 < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨R, hR⟩
  rw [cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR, mul_inv,
    ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_inv_of_pos hc,
    ENNReal.ofReal_natCast]


theorem weightedSobolevMeasure_apply {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) (S : Set (Vec d)) (hS : MeasurableSet S) : weightedSobolevMeasure Q b S = ∫⁻x in S, ENNReal.ofReal (b x / cubeAverage Q b) ∂normalizedCubeMeasure Q := by
  exact withDensity_apply _ hS


theorem weightedSobolev_average_density {d : ℕ} (Q R : TriadicCube d) (b : Vec d → ℝ) (hb : Integrable b (normalizedCubeMeasure R)) : cubeAverage R (fun x => b x / cubeAverage Q b - 1) = cubeAverage R b / cubeAverage Q b - 1 := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure R (fun x => b x / cubeAverage Q b - 1),
    integral_sub (hb.div_const _) (integrable_const 1),
    integral_div, ← cubeAverage_eq_integral_normalizedCubeMeasure R b,
    integral_const]
  simp [cubeAverage_eq_integral_normalizedCubeMeasure Q b]


theorem weightedSobolev_normalized_restrict_descendant {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) : (normalizedCubeMeasure Q).restrict (cubeSet R) = ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ • normalizedCubeMeasure R := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset (cubeSet_subset_of_mem_descendantsAtDepth hR), weightedSobolev_volume_factor hR, mul_smul]


theorem weightedSobolev_positive_to_nonnegative {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (hb : ∀ᵐ x ∂μ, 0 < b x) : ∀ᵐ x ∂μ, 0 ≤ b x := by
  filter_upwards [hb] with x hx; exact hx.le


theorem weightedSobolev_lintegral_scale {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞) : (∫⁻x,c * g x ∂μ) = c * ∫⁻x,g x ∂μ := by
  exact lintegral_const_mul' c g hc


theorem weightedSobolev_div_product (b a f : ℝ) : b / a * f = (b * f) / a := by
  ring



theorem weightedSobolev_centered_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (c : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hf : MemLp f p μ) (hzero : ∫x,f x ∂μ = 0) : eLpNorm f p μ ≤ 2 * eLpNorm (fun x => f x-c) p μ := by
  have hg : AEStronglyMeasurable (fun x => f x - c) μ :=
    (hf.sub (memLp_const c)).aestronglyMeasurable
  have hm := weightedSobolev_mean_norm μ (fun x=>f x-c) p hp hg
  rw [weightedSobolev_mean_sub μ f c (hf.integrable hp) hzero, enorm_neg] at hm
  have ht := eLpNorm_add_le (f := fun x => f x - c) (g := fun _ => c) (μ := μ) hp
  rw [weightedSobolev_centered_add f c, weightedSobolev_norm_const μ p (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) c] at ht
  exact weightedSobolev_triangle_algebra _ _ _ ht hm


theorem weightedSobolev_integral_density {α : Type*} [MeasurableSpace α] (μ : Measure α) (b f : α → ℝ) (hb : AEMeasurable b μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ b x) : (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (b x))) = ∫ x, b x * f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hb.ennreal_ofReal (ae_of_all _ fun x=>ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  simp [ENNReal.toReal_ofReal hx, smul_eq_mul]


theorem weightedSobolev_eLpNorm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (p : ℝ) (hp : 0 < p) : (SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal p) μ) ^ (2 : ℕ) = (∫⁻x, ENNReal.ofReal (|f x| ^ p) ∂μ) ^ (2 / p) := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  simp_rw [← weightedSobolev_ofReal_rpow _ p hp.le]
  simpa only [one_div] using! weightedSobolev_rpow_square (∫⁻x, ENNReal.ofReal (|f x| ^ p) ∂μ) p

theorem weightedSobolevMeasure_cubeSet_descendant {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (hR : R ∈ descendantsAtDepth Q j) : weightedSobolevMeasure Q b (cubeSet R) = ENNReal.ofReal (cubeAverage R b / cubeAverage Q b) / ((descendantsAtDepth Q j).card : ℝ≥0∞) := by
  have hbR := weightedSobolev_coefficient_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) hb
  have hi := ((weightedSobolev_coefficient_cube_memLp R b hbR 1).integrable le_rfl).div_const (cubeAverage Q b)
  have hn : ∀ᵐ x ∂normalizedCubeMeasure R, 0 ≤ b x / cubeAverage Q b := by
    filter_upwards [weightedSobolev_normalized_ae R (weightedSobolev_coefficient_pos _ b hbR)] with x hx
    exact div_nonneg hx.le (weightedSobolev_coefficient_average_pos Q b hb).le
  rw [weightedSobolevMeasure_apply Q b _ (measurableSet_cubeSet R), weightedSobolev_normalized_restrict_descendant hR, lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div, ← cubeAverage_eq_integral_normalizedCubeMeasure]
  simp [div_eq_mul_inv, mul_comm]


theorem weightedSobolev_lintegral_density {α : Type*} [MeasurableSpace α] (μ : Measure α) (b : α → ℝ) (a : ℝ) (g : α → ℝ≥0∞) (ha : 0 < a) (hb : AEMeasurable b μ) (hg : AEMeasurable g μ) : (∫⁻ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (b x / a))) = ENNReal.ofReal a⁻¹ * ∫⁻ x, ENNReal.ofReal (b x) * g x ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hb.div_const a).ennreal_ofReal hg]
  simp only [Pi.mul_apply, ENNReal.ofReal_div_of_pos ha]
  rw [← lintegral_const_mul' (ENNReal.ofReal a⁻¹) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_inv_of_pos ha, div_eq_mul_inv]
  ac_rfl


theorem weightedSobolev_lintegral_normalized_open {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ≥0∞) : (∫⁻x,g x ∂normalizedCubeMeasure Q) = (volume (openCubeSet Q))⁻¹ * ∫⁻x in openCubeSet Q,g x := by
  have hv : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [volume_openCubeSet_eq_volume_cubeSet]
    simpa only [cubeMeasure_apply_univ] using! cubeMeasure_apply_univ_eq Q
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q, lintegral_smul_measure,
    ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q), hv]
  rfl


theorem weightedSobolev_cubeAverage_open {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : cubeAverage Q f = (cubeVolume Q)⁻¹ * ∫x in openCubeSet Q,f x := by
  unfold cubeAverage; rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]

theorem weightedSobolev_zero_average {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hzero : (∫x in openCubeSet Q,f x*b x)=0) : cubeAverage Q (fun x=>b x*f x)=0 := by
  rw [weightedSobolev_cubeAverage_open]
  have hi : (∫x in openCubeSet Q,b x*f x)=0 := by
    simpa only [mul_comm] using! hzero
  rw [hi,mul_zero]


theorem weightedSobolevMeasure_integral {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) : (∫x,f x ∂weightedSobolevMeasure Q b) = cubeAverage Q (fun x=>b x*f x) / cubeAverage Q b := by
  have hm := (weightedSobolev_coefficient_cube_memLp Q b hb 1).aestronglyMeasurable.aemeasurable
  have hn : ∀ᵐx∂normalizedCubeMeasure Q,0≤b x/cubeAverage Q b := by
    filter_upwards [weightedSobolev_normalized_ae Q (weightedSobolev_coefficient_pos _ b hb)] with x hx
    exact div_nonneg hx.le (weightedSobolev_coefficient_average_pos Q b hb).le
  rw [weightedSobolevMeasure,weightedSobolev_integral_density _ _ f (hm.div_const _) hn]
  simp_rw [weightedSobolev_div_product]
  rw [integral_div,←cubeAverage_eq_integral_normalizedCubeMeasure]


theorem weightedSobolevMeasure_mean_zero {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (hzero : (∫x in openCubeSet Q,f x*b x)=0) : (∫x,f x ∂weightedSobolevMeasure Q b)=0 := by
  rw [weightedSobolevMeasure_integral Q b f hb, weightedSobolev_zero_average Q b f hzero, zero_div]


theorem weightedSobolevMeasure_centered_le {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (p : ℝ≥0∞) (hp : 1 ≤ p) (hf : MemLp f p (weightedSobolevMeasure Q b)) (hz : (∫x in openCubeSet Q,f x*b x)=0) : eLpNorm f p (weightedSobolevMeasure Q b) ≤ 2 * eLpNorm (cubeFluctuation Q f) p (weightedSobolevMeasure Q b) := by
  let := weightedSobolevMeasure_isProbabilityMeasure Q b hb
  exact weightedSobolev_centered_le _ f (cubeAverage Q f) p hp hf (weightedSobolevMeasure_mean_zero Q b f hb hz)


theorem weightedSobolev_increment_constant_on_descendant {d : ℕ} {Q R : TriadicCube d} (j : ℕ) (u : Vec d → ℝ) (hR : R ∈ descendantsAtDepth Q (j + 1)) : ∃ c : ℝ, ∀ x ∈ cubeSet R, cubeIncrement Q (j + 1) u x = c := by
  obtain ⟨S, hS, hRS⟩ := exists_descendant_ancestor_at_depth j 1 hR
  refine ⟨cubeAverage R u - cubeAverage S u, ?_⟩
  intro x hx
  exact cubeIncrement_eq_sub_cubeAverage_of_mem_descendantsAtDepth u hR hS hx (cubeSet_subset_of_mem_descendantsAtDepth hRS hx)


theorem weightedSobolev_normalized_cubeSet_descendant {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) : normalizedCubeMeasure Q (cubeSet R) = ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ := by
  have h := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (weightedSobolev_normalized_restrict_descendant hR)
  simpa [normalizedCubeMeasure_apply_univ] using! h


theorem weightedSobolev_ofReal_power_product (x b p : ℝ) : ENNReal.ofReal b * ENNReal.ofReal (|x| ^ p) = ENNReal.ofReal (|x| ^ p * b) := by
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) p), mul_comm]


theorem weightedSobolev_power_aemeasurable {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (p : ℝ) (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal (|f x| ^ p)) μ := by
  exact (hf.aemeasurable.abs.pow_const p).ennreal_ofReal


theorem weightedSobolevMeasure_power_integral {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (p : ℝ) (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) : (∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂weightedSobolevMeasure Q b) = ENNReal.ofReal ((cubeAverage Q b)⁻¹) * ∫⁻ x, ENNReal.ofReal (|f x| ^ p * b x) ∂normalizedCubeMeasure Q := by
  rw [weightedSobolevMeasure, weightedSobolev_lintegral_density _ b _ _ (weightedSobolev_coefficient_average_pos Q b hb) (weightedSobolev_coefficient_cube_memLp Q b hb 1).aestronglyMeasurable.aemeasurable (weightedSobolev_power_aemeasurable _ f p hf)]
  simp_rw [weightedSobolev_ofReal_power_product]


theorem weightedSobolevMeasure_lp_readout {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (p : ℝ) (hp : 0 < p) (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) : (ENNReal.ofReal ((cubeAverage Q b)⁻¹) * (volume (openCubeSet Q))⁻¹ * ∫⁻ x in openCubeSet Q, ENNReal.ofReal (|f x| ^ p * b x)) ^ (2 / p) = (eLpNorm f (ENNReal.ofReal p) (weightedSobolevMeasure Q b)) ^ (2 : ℕ) := by
  have hfWeighted : AEStronglyMeasurable f (weightedSobolevMeasure Q b) := by
    change AEStronglyMeasurable f ((normalizedCubeMeasure Q).withDensity
      (fun x => ENNReal.ofReal (b x / cubeAverage Q b)))
    exact AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) hf
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfWeighted,
    weightedSobolev_eLpNorm_sq _ f p hp,
    weightedSobolevMeasure_power_integral Q b f hb p hf,
    weightedSobolev_lintegral_normalized_open]
  rw [mul_assoc]


theorem weightedSobolev_normalized_aestronglyMeasurable {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet Q))) : AEStronglyMeasurable f (normalizedCubeMeasure Q) := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact hf.smul_measure _


theorem weightedSobolev_memLp_of_centered {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (c : ℝ) (p : ℝ≥0∞) (hf : MemLp (fun x => f x - c) p μ) : MemLp f p μ := by
  have h := hf.add (memLp_const c)
  rw [weightedSobolev_centered_add f c] at h
  exact h


theorem weightedSobolevMeasure_aestronglyMeasurable {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) : AEStronglyMeasurable f (weightedSobolevMeasure Q b) := by
  exact hf.mono_ac (weightedSobolevMeasure_absolutelyContinuous Q b)


theorem weightedSobolev_density_average_zero {d : ℕ} (Q : TriadicCube d) (b : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) : cubeAverage Q (fun x => b x / cubeAverage Q b - 1) = 0 := by
  rw [weightedSobolev_average_density Q Q b ((weightedSobolev_coefficient_cube_memLp Q b hb 1).integrable le_rfl), div_self (weightedSobolev_coefficient_average_pos Q b hb).ne', sub_self]


end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
