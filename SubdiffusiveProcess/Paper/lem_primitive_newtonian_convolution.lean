module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

namespace aux_newt

abbrev aux_E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def aux_euclidean (d : ℕ) : SpatialCoordinates d ≃L[ℝ] aux_E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm

def aux_radius {d : ℕ} (w : SpatialCoordinates d) : ℝ := ‖aux_euclidean d w‖

lemma aux_radius_eq {d : ℕ} (w : SpatialCoordinates d) :
    aux_radius w = Real.sqrt (∑ j : Fin d, (w j) ^ 2) := by
  change ‖(WithLp.toLp 2 w : aux_E d)‖ = _
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change ‖w j‖ ^ 2 = (w j) ^ 2
  rw [Real.norm_eq_abs, sq_abs]

lemma aux_continuous_radius (d : ℕ) : Continuous (@aux_radius d) :=
  (aux_euclidean d).continuous.norm

lemma aux_radius_nonneg {d : ℕ} (w : SpatialCoordinates d) : 0 ≤ aux_radius w :=
  norm_nonneg _

@[simp] lemma aux_radius_zero (d : ℕ) : aux_radius (0 : SpatialCoordinates d) = 0 := by
  simp [aux_radius]

@[simp] lemma aux_radius_eq_zero {d : ℕ} {w : SpatialCoordinates d} :
    aux_radius w = 0 ↔ w = 0 := by
  simp [aux_radius]

lemma aux_radius_pos {d : ℕ} {w : SpatialCoordinates d} (hw : w ≠ 0) :
    0 < aux_radius w :=
  lt_of_le_of_ne (aux_radius_nonneg w) (Ne.symm (aux_radius_eq_zero.not.mpr hw))

@[simp] lemma aux_radius_neg {d : ℕ} (w : SpatialCoordinates d) :
    aux_radius (-w) = aux_radius w := by
  simp [aux_radius]

lemma aux_radius_add_le {d : ℕ} (u v : SpatialCoordinates d) :
    aux_radius (u + v) ≤ aux_radius u + aux_radius v := by
  simpa [aux_radius] using norm_add_le (aux_euclidean d u) (aux_euclidean d v)

lemma aux_radius_sub_le {d : ℕ} (u v : SpatialCoordinates d) :
    aux_radius (u - v) ≤ aux_radius u + aux_radius v := by
  simpa [sub_eq_add_neg] using aux_radius_add_le u (-v)

lemma aux_radius_sub_comm {d : ℕ} (u v : SpatialCoordinates d) :
    aux_radius (u - v) = aux_radius (v - u) := by
  simpa only [neg_sub] using aux_radius_neg (v - u)

lemma aux_abs_radius_sub_le {d : ℕ} (u v : SpatialCoordinates d) :
    |aux_radius u - aux_radius v| ≤ aux_radius (u - v) := by
  simpa [aux_radius] using abs_norm_sub_norm_le (aux_euclidean d u) (aux_euclidean d v)

lemma aux_coordinate_le_radius {d : ℕ} (w : SpatialCoordinates d) (i : Fin d) :
    |w i| ≤ aux_radius w := by
  rw [aux_radius_eq, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j hj => sq_nonneg (w j)) (Finset.mem_univ i)

lemma aux_radius_smul {d : ℕ} (r : ℝ) (w : SpatialCoordinates d) :
    aux_radius (r • w) = |r| * aux_radius w := by
  simp [aux_radius, norm_smul, Real.norm_eq_abs]

lemma aux_euclidean_measurePreserving (d : ℕ) :
    MeasurePreserving (aux_euclidean d) volume volume := by
  exact PiLp.volume_preserving_toLp (Fin d)

lemma aux_euclidean_symm_measurePreserving (d : ℕ) :
    MeasurePreserving (aux_euclidean d).symm volume volume := by
  exact PiLp.volume_preserving_ofLp (Fin d)

lemma aux_euclidean_measurableEmbedding (d : ℕ) :
    MeasurableEmbedding (aux_euclidean d) :=
  (aux_euclidean d).toHomeomorph.measurableEmbedding

lemma aux_euclidean_symm_measurableEmbedding (d : ℕ) :
    MeasurableEmbedding (aux_euclidean d).symm :=
  (aux_euclidean d).symm.toHomeomorph.measurableEmbedding

lemma aux_integral_radial (d : ℕ) (hd : 1 ≤ d) (F : ℝ → ℝ) :
    (∫ w : SpatialCoordinates d, F (aux_radius w)) =
      ((d : ℝ) * (volume (Metric.ball (0 : aux_E d) 1)).toReal) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * F r := by
  let : NeZero d := ⟨by omega⟩
  calc
    (∫ w : SpatialCoordinates d, F (aux_radius w)) =
        ∫ w : aux_E d, F ‖w‖ :=
      (aux_euclidean_measurePreserving d).integral_comp
        (aux_euclidean_measurableEmbedding d) (fun w : aux_E d => F ‖w‖)
    _ = _ := by
      simpa [Measure.real, finrank_euclideanSpace_fin, smul_eq_mul,
        nsmul_eq_mul, mul_assoc] using
        (integral_fun_norm_addHaar (volume : Measure (aux_E d)) F)

lemma aux_integrable_radial (d : ℕ) (hd : 1 ≤ d) (F : ℝ → ℝ) :
    Integrable (fun w : SpatialCoordinates d => F (aux_radius w)) volume ↔
      IntegrableOn (fun r : ℝ => r ^ (d - 1) * F r) (Ioi 0) volume := by
  let : NeZero d := ⟨by omega⟩
  calc
    Integrable (fun w : SpatialCoordinates d => F (aux_radius w)) volume ↔
        Integrable (fun w : aux_E d => F ‖w‖) volume := by
      have hcomp :
          Integrable ((fun w : aux_E d => F ‖w‖) ∘ aux_euclidean d) volume ↔
            Integrable (fun w : aux_E d => F ‖w‖) volume :=
        (aux_euclidean_measurePreserving d).integrable_comp_emb
          (aux_euclidean_measurableEmbedding d) (g := fun w : aux_E d => F ‖w‖)
      simpa only [Function.comp_def, aux_radius] using hcomp
    _ ↔ _ := by
      have hradial :
          Integrable (fun w : aux_E d => F ‖w‖) volume ↔
            IntegrableOn
              (fun r : ℝ => r ^ (Module.finrank ℝ (aux_E d) - 1) • F r)
              (Ioi 0) volume :=
        integrable_fun_norm_addHaar (volume : Measure (aux_E d)) (f := F)
      simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hradial

def aux_c (d : ℕ) : ℝ :=
  (d : ℝ) * (volume (Metric.ball (0 : aux_E d) 1)).toReal

lemma aux_c_eq (d : ℕ) :
    aux_c d = (d : ℝ) * (volume {w : SpatialCoordinates d |
      Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal := by
  have hset : (aux_euclidean d) ⁻¹' Metric.ball (0 : aux_E d) 1 =
      {w : SpatialCoordinates d | Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1} := by
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, mem_ofPred_eq]
    rw [← aux_radius_eq]
    rfl
  unfold aux_c
  congr 1
  congr 1
  rw [← hset]
  have hb : MeasurableSet (Metric.ball (0 : aux_E d) 1) := measurableSet_ball
  exact ((aux_euclidean_measurePreserving d).measure_preimage hb.nullMeasurableSet).symm

def aux_kernel {d : ℕ} (i : Fin d) (w : SpatialCoordinates d) : ℝ :=
  w i / (aux_radius w) ^ d

def aux_riesz {d : ℕ} (w : SpatialCoordinates d) : ℝ :=
  ((aux_radius w) ^ (d - 1))⁻¹

lemma aux_riesz_nonneg {d : ℕ} (w : SpatialCoordinates d) : 0 ≤ aux_riesz w := by
  exact inv_nonneg.mpr (pow_nonneg (aux_radius_nonneg w) _)

@[simp] lemma aux_kernel_zero {d : ℕ} (i : Fin d) :
    aux_kernel i (0 : SpatialCoordinates d) = 0 := by
  simp [aux_kernel]

lemma aux_kernel_measurable {d : ℕ} (i : Fin d) : Measurable (aux_kernel i) := by
  exact (measurable_pi_apply i).div ((aux_continuous_radius d).measurable.pow_const d)

lemma aux_riesz_measurable (d : ℕ) : Measurable (@aux_riesz d) := by
  exact ((aux_continuous_radius d).measurable.pow_const (d - 1)).inv

lemma aux_abs_kernel_le_riesz {d : ℕ} (hd : 1 ≤ d)
    (i : Fin d) (w : SpatialCoordinates d) : |aux_kernel i w| ≤ aux_riesz w := by
  by_cases hw : w = 0
  · subst w
    simpa only [aux_kernel_zero, abs_zero] using aux_riesz_nonneg (0 : SpatialCoordinates d)
  have hr : 0 < aux_radius w := aux_radius_pos hw
  have hp : aux_radius w ^ d = aux_radius w ^ (d - 1) * aux_radius w := by
    simpa only [Nat.sub_add_cancel hd] using (pow_succ (aux_radius w) (d - 1))
  calc
    |aux_kernel i w| = |w i| / (aux_radius w) ^ d := by
      rw [aux_kernel, abs_div, abs_of_pos (pow_pos hr d)]
    _ ≤ aux_radius w / (aux_radius w) ^ d :=
      div_le_div_of_nonneg_right (aux_coordinate_le_radius w i) (pow_nonneg hr.le d)
    _ = aux_riesz w := by
      unfold aux_riesz
      rw [hp]
      field_simp [hr.ne']

lemma aux_kernel_sub_eq {d : ℕ} (i : Fin d) (x y : SpatialCoordinates d) :
    (if x = y then 0 else
      (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) =
        aux_kernel i (x - y) := by
  by_cases hxy : x = y
  · subst y
    rw [ite_eq_left rfl, sub_self, aux_kernel_zero]
  · simp only [hxy, ite_false, aux_kernel, aux_radius_eq, Pi.sub_apply]

lemma aux_abs_pow_sub_le (n : ℕ) {a b m : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ham : a ≤ m) (hbm : b ≤ m) :
    |a ^ (n + 1) - b ^ (n + 1)| ≤
      (n + 1 : ℝ) * m ^ n * |a - b| := by
  have hm : 0 ≤ m := ha.trans ham
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, one_mul, le_refl]
  | succ n ih =>
      have hp : b ^ (n + 1) ≤ m ^ (n + 1) :=
        pow_le_pow_left₀ hb hbm (n + 1)
      have hid : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
          a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by
        ring
      calc
        |a ^ (n + 1 + 1) - b ^ (n + 1 + 1)| ≤
            |a * (a ^ (n + 1) - b ^ (n + 1))| +
              |(a - b) * b ^ (n + 1)| := by
          rw [hid]
          exact abs_add_le _ _
        _ = a * |a ^ (n + 1) - b ^ (n + 1)| +
            |a - b| * b ^ (n + 1) := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha,
            abs_of_nonneg (pow_nonneg hb _)]
        _ ≤ m * ((n + 1 : ℝ) * m ^ n * |a - b|) +
            |a - b| * m ^ (n + 1) := by
          exact add_le_add
            (mul_le_mul ham ih (abs_nonneg _) hm)
            (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
        _ = (↑(n + 1) + 1 : ℝ) * m ^ (n + 1) * |a - b| := by
          rw [pow_succ]
          push_cast
          ring

lemma aux_c_pos (d : ℕ) (hd : 1 ≤ d) : 0 < aux_c d := by
  unfold aux_c
  apply mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd))
  apply ENNReal.toReal_pos
  · exact (Metric.measure_ball_pos volume (0 : aux_E d) zero_lt_one).ne'
  · exact ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : aux_E d) 1).measure_lt_top).ne

def aux_near (d : ℕ) (r : ℝ) (w : SpatialCoordinates d) : ℝ :=
  (Iio r).indicator (fun t : ℝ => (t ^ (d - 1))⁻¹) (aux_radius w)

def aux_annulus (d : ℕ) (a b : ℝ) (w : SpatialCoordinates d) : ℝ :=
  (Icc a b).indicator (fun t : ℝ => (t ^ d)⁻¹) (aux_radius w)

lemma aux_near_eq_riesz (d : ℕ) (r : ℝ) (w : SpatialCoordinates d)
    (h : aux_radius w < r) : aux_near d r w = aux_riesz w := by
  have hm : aux_radius w ∈ Iio r := h
  simp only [aux_near, indicator_of_mem hm, aux_riesz]

lemma aux_near_nonneg (d : ℕ) (r : ℝ) (w : SpatialCoordinates d) :
    0 ≤ aux_near d r w := by
  by_cases h : aux_radius w < r
  · rw [aux_near_eq_riesz d r w h]
    exact aux_riesz_nonneg w
  · have hm : aux_radius w ∉ Iio r := h
    simp only [aux_near, indicator_of_notMem hm, le_refl]

lemma aux_annulus_nonneg (d : ℕ) (a b : ℝ) (w : SpatialCoordinates d) :
    0 ≤ aux_annulus d a b w := by
  unfold aux_annulus
  by_cases h : aux_radius w ∈ Icc a b
  · simpa only [indicator_of_mem h] using
      inv_nonneg.mpr (pow_nonneg (aux_radius_nonneg w) d)
  · simp [h]

lemma aux_near_radial (d : ℕ) (r t : ℝ) (ht : 0 < t) :
    t ^ (d - 1) * (Iio r).indicator (fun s : ℝ => (s ^ (d - 1))⁻¹) t =
      (Ioo 0 r).indicator (fun _ : ℝ => (1 : ℝ)) t := by
  by_cases htr : t < r <;> simp [htr, ht, pow_ne_zero _ ht.ne']

lemma aux_near_integrable (d : ℕ) (hd : 1 ≤ d) (r : ℝ) :
    Integrable (aux_near d r) volume := by
  unfold aux_near
  rw [aux_integrable_radial d hd]
  have h : Integrable ((Ioo (0 : ℝ) r).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrableOn_const (by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)).integrable_indicator
        measurableSet_Ioo
  exact h.integrableOn.congr_fun (fun t ht => (aux_near_radial d r t ht).symm)
    measurableSet_Ioi

lemma aux_near_integral (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    (∫ w, aux_near d r w) = aux_c d * r := by
  unfold aux_near
  rw [aux_integral_radial d hd]
  change aux_c d * _ = _
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => aux_near_radial d r t ht),
    setIntegral_indicator measurableSet_Ioo]
  have hs : Ioi (0 : ℝ) ∩ Ioo 0 r = Ioo 0 r :=
    inter_eq_right.mpr (fun _ hx => hx.1)
  rw [hs]
  simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hr]

lemma aux_annulus_radial (d : ℕ) (hd : 1 ≤ d) (a b t : ℝ) (ht : 0 < t) :
    t ^ (d - 1) * (Icc a b).indicator (fun s : ℝ => (s ^ d)⁻¹) t =
      (Icc a b).indicator (fun s : ℝ => s⁻¹) t := by
  by_cases h : t ∈ Icc a b
  · simp only [indicator_of_mem h]
    have hp : t ^ d = t ^ (d - 1) * t := by
      simpa only [Nat.sub_add_cancel hd] using pow_succ t (d - 1)
    rw [hp]
    field_simp [ht.ne']
  · simp [h]

lemma aux_annulus_integrable (d : ℕ) (hd : 1 ≤ d) {a b : ℝ} (ha : 0 < a) :
    Integrable (aux_annulus d a b) volume := by
  unfold aux_annulus
  rw [aux_integrable_radial d hd]
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')
  have h : Integrable ((Icc a b).indicator (fun t : ℝ => t⁻¹)) :=
    hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  exact h.integrableOn.congr_fun (fun t ht => (aux_annulus_radial d hd a b t ht).symm)
    measurableSet_Ioi

lemma aux_annulus_integral (d : ℕ) (hd : 1 ≤ d) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ w, aux_annulus d a b w) = aux_c d * Real.log (b / a) := by
  unfold aux_annulus
  rw [aux_integral_radial d hd]
  change aux_c d * _ = _
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => aux_annulus_radial d hd a b t ht),
    setIntegral_indicator measurableSet_Icc]
  have hs : Ioi (0 : ℝ) ∩ Icc a b = Icc a b :=
    inter_eq_right.mpr (fun _ ht => ha.trans_le ht.1)
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_inv_of_pos ha (ha.trans_le hab)

lemma aux_riesz_locallyIntegrable (d : ℕ) (hd : 1 ≤ d) :
    LocallyIntegrable (@aux_riesz d) volume := by
  intro x
  let s : Set (SpatialCoordinates d) := {w | aux_radius w < aux_radius x + 1}
  have hs : IsOpen s := isOpen_lt (aux_continuous_radius d) continuous_const
  refine ⟨s, hs.mem_nhds (by dsimp [s]; linarith), ?_⟩
  apply (aux_near_integrable d hd (aux_radius x + 1)).integrableOn.congr_fun _ hs.measurableSet
  intro w hw
  exact aux_near_eq_riesz d (aux_radius x + 1) w
    (show aux_radius w < aux_radius x + 1 from hw)

lemma aux_essential_bound {d : ℕ} {f : SpatialCoordinates d → ℝ}
    (hf : MemLp f (⊤ : ENNReal) volume) :
    ∀ᵐ x ∂volume, |f x| ≤ (eLpNormEssSup f volume).toReal := by
  have ht : eLpNormEssSup f volume ≠ ⊤ := by
    simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_ne_top
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with x hx
  have h : (‖f x‖ₑ).toReal ≤ (eLpNormEssSup f volume).toReal :=
    ENNReal.toReal_mono ht hx
  simpa only [toReal_enorm, Real.norm_eq_abs] using h

lemma aux_cube_volume {d : ℕ} (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d) :
    (volume (closedCube z R hR : Set (SpatialCoordinates d))).toReal = R ^ d := by
  change (volume (Metric.closedBall z (R / 2))).toReal = _
  rw [Real.volume_pi_closedBall z (by linarith)]
  have h : 2 * (R / 2) = R := by ring
  rw [h, Fintype.card_fin, ENNReal.toReal_ofReal (pow_nonneg hR.le d)]

lemma aux_source_integrable_bound {d : ℕ} (R : ℝ) (hR : 0 < R)
    (z : SpatialCoordinates d) (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (⊤ : ENNReal) volume)
    (hs : ∀ᵐ x ∂volume, x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) :
    Integrable f volume ∧
      (∫ x, |f x|) ≤ (eLpNormEssSup f volume).toReal * R ^ d := by
  let M := (eLpNormEssSup f volume).toReal
  let S : Set (SpatialCoordinates d) := closedCube z R hR
  let B := S.indicator (fun _ : SpatialCoordinates d => M)
  have hS : IsCompact S := (closedCube z R hR).isCompact
  have hB : Integrable B volume :=
    (integrableOn_const hS.measure_ne_top).integrable_indicator hS.measurableSet
  have hbound : ∀ᵐ x ∂volume, |f x| ≤ B x := by
    filter_upwards [aux_essential_bound hf, hs] with x hx hxs
    by_cases hxS : x ∈ S
    · simpa only [B, indicator_of_mem hxS] using hx
    · simp only [B, indicator_of_notMem hxS, hxs hxS, abs_zero, le_refl]
  have hfi : Integrable f volume := hB.mono' hf.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hfi, ?_⟩
  calc
    (∫ x, |f x|) ≤ ∫ x, B x := integral_mono_ae hfi.abs hB hbound
    _ = M * R ^ d := by
      rw [show B = S.indicator (fun _ : SpatialCoordinates d => M) from rfl,
        integral_indicator_const M hS.measurableSet]
      simp only [Measure.real, smul_eq_mul]
      rw [show (volume S).toReal = R ^ d from aux_cube_volume R hR z]
      ring

lemma aux_kernel_mul_majorant {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    {r M a : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (ha : |a| ≤ M)
    (w : SpatialCoordinates d) :
    |aux_kernel i w * a| ≤ M * aux_near d r w + (r ^ (d - 1))⁻¹ * |a| := by
  have hbase : |aux_kernel i w * a| ≤ aux_riesz w * |a| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (aux_abs_kernel_le_riesz hd i w) (abs_nonneg a)
  by_cases hwr : aux_radius w < r
  · have hn : aux_near d r w = aux_riesz w := aux_near_eq_riesz d r w hwr
    calc
      |aux_kernel i w * a| ≤ aux_riesz w * |a| := hbase
      _ ≤ M * aux_near d r w := by
        rw [hn, mul_comm M]
        exact mul_le_mul_of_nonneg_left ha (aux_riesz_nonneg w)
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by positivity) (abs_nonneg a))
  · have hrw : r ≤ aux_radius w := le_of_not_gt hwr
    have hp : r ^ (d - 1) ≤ aux_radius w ^ (d - 1) :=
      pow_le_pow_left₀ hr.le hrw _
    have hi : aux_riesz w ≤ (r ^ (d - 1))⁻¹ := by
      simpa only [aux_riesz, one_div] using
        one_div_le_one_div_of_le (pow_pos hr _) hp
    calc
      |aux_kernel i w * a| ≤ aux_riesz w * |a| := hbase
      _ ≤ (r ^ (d - 1))⁻¹ * |a| := mul_le_mul_of_nonneg_right hi (abs_nonneg a)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hM (aux_near_nonneg d r w))

lemma aux_kernel_integrable_estimate {d : ℕ} (hd : 1 ≤ d)
    {f : SpatialCoordinates d → ℝ} (hf : Integrable f volume)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hbound : ∀ᵐ t ∂volume, |f t| ≤ M) (i : Fin d) (x : SpatialCoordinates d) :
    Integrable (fun t => aux_kernel i (x - t) * f t) volume ∧
      (∫ t, |aux_kernel i (x - t) * f t|) ≤
        M * (aux_c d * r) + (r ^ (d - 1))⁻¹ * ∫ t, |f t| := by
  let B := fun t => M * aux_near d r (x - t) + (r ^ (d - 1))⁻¹ * |f t|
  have hnear : Integrable (fun t => aux_near d r (x - t)) volume :=
    (aux_near_integrable d hd r).comp_sub_left x
  have hB : Integrable B volume := (hnear.const_mul M).add (hf.abs.const_mul _)
  have hmeas : AEStronglyMeasurable (fun t => aux_kernel i (x - t) * f t) volume :=
    ((aux_kernel_measurable i).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  have hle : ∀ᵐ t ∂volume, |aux_kernel i (x - t) * f t| ≤ B t := by
    filter_upwards [hbound] with t ht using aux_kernel_mul_majorant hd i hr hM ht (x - t)
  have hInt : Integrable (fun t : SpatialCoordinates d => aux_kernel i (x - t) * f t)
      volume := hB.mono' hmeas (by simpa only [Real.norm_eq_abs] using hle)
  refine ⟨hInt, (integral_mono_ae hInt.abs hB hle).trans_eq ?_⟩
  rw [show B = (fun t => M * aux_near d r (x - t) + (r ^ (d - 1))⁻¹ * |f t|) from rfl,
    integral_add (hnear.const_mul M) (hf.abs.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub_left_eq_self (aux_near d r) volume x, aux_near_integral d hd hr.le]

@[simp] lemma aux_kernel_neg {d : ℕ} (i : Fin d) (w : SpatialCoordinates d) :
    aux_kernel i (-w) = -aux_kernel i w := by
  simp only [aux_kernel, Pi.neg_apply, aux_radius_neg, neg_div]

lemma aux_kernel_sub_swap {d : ℕ} (i : Fin d) (x y : SpatialCoordinates d) :
    aux_kernel i (x - y) = -aux_kernel i (y - x) := by
  simpa only [neg_sub] using aux_kernel_neg i (y - x)

def aux_convolution {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) (i : Fin d) : ℝ :=
  (aux_c d)⁻¹ * ∫ t, aux_kernel i (x - t) * f t

lemma aux_convolution_eq {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) (i : Fin d) :
    aux_convolution f x i =
      ((d : ℝ) * (volume {w : SpatialCoordinates d |
        Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
      (∫ y, (if x = y then 0 else
        (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y) := by
  simp only [aux_convolution, aux_c_eq, aux_kernel_sub_eq]

lemma aux_convolution_bound {d : ℕ} (hd : 1 ≤ d) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) {f : SpatialCoordinates d → ℝ}
    (hf : Integrable f volume) (hbound : ∀ᵐ t ∂volume, |f t| ≤ M)
    (hL : (∫ t, |f t|) ≤ M * R ^ d) (x : SpatialCoordinates d) (i : Fin d) :
    |aux_convolution f x i| ≤ ((aux_c d)⁻¹ * (aux_c d + 1)) * R * M := by
  have hc : 0 < aux_c d := aux_c_pos d hd
  have hest : (∫ t, |aux_kernel i (x - t) * f t|) ≤
      M * (aux_c d * R) + (R ^ (d - 1))⁻¹ * ∫ t, |f t| :=
    (aux_kernel_integrable_estimate hd hf hM hR hbound i x).2
  have hp : R ^ d = R ^ (d - 1) * R := by
    simpa only [Nat.sub_add_cancel hd] using pow_succ R (d - 1)
  have hprod : (R ^ (d - 1))⁻¹ * (M * R ^ d) = M * R := by
    rw [hp]
    field_simp [hR.ne']
  calc
    |aux_convolution f x i| = (aux_c d)⁻¹ * |∫ t, aux_kernel i (x - t) * f t| := by
      rw [aux_convolution, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    _ ≤ (aux_c d)⁻¹ * ∫ t, |aux_kernel i (x - t) * f t| := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun t => aux_kernel i (x - t) * f t)
    _ ≤ (aux_c d)⁻¹ * (M * (aux_c d * R) + (R ^ (d - 1))⁻¹ * ∫ t, |f t|) :=
      mul_le_mul_of_nonneg_left hest (inv_nonneg.mpr hc.le)
    _ ≤ (aux_c d)⁻¹ * (M * (aux_c d * R) + M * R) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact add_le_add (le_refl _)
        ((mul_le_mul_of_nonneg_left hL (by positivity)).trans_eq hprod)
    _ = _ := by ring

def aux_D (d : ℕ) : ℝ := 1 + (d : ℝ) * 4 ^ (d - 1)

lemma aux_D_pos (d : ℕ) : 0 < aux_D d := by
  unfold aux_D
  positivity

lemma aux_numerical_kernel_difference {d : ℕ} (hd : 1 ≤ d)
    {a b s t ρ : ℝ} (hρ : 0 < ρ) (haρ : 2 * ρ ≤ a)
    (hab : |a - b| ≤ ρ) (hst : |s - t| ≤ ρ) (ht : |t| ≤ b) :
    |s / a ^ d - t / b ^ d| ≤ aux_D d * ρ / a ^ d := by
  have ha : 0 < a := by linarith
  have hab' : -ρ ≤ a - b ∧ a - b ≤ ρ := abs_le.mp hab
  have hb : 0 < b := by linarith [hab'.2]
  have hba : b ≤ 2 * a := by linarith [hab'.1]
  have hab4 : 2 * a ≤ 4 * b := by linarith [hab'.2]
  have hdreal : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hd
  have hpow : |b ^ d - a ^ d| ≤ (d : ℝ) * (2 * a) ^ (d - 1) * ρ := by
    have h : |b ^ ((d - 1) + 1) - a ^ ((d - 1) + 1)| ≤
        (((d - 1 : ℕ) : ℝ) + 1) * (2 * a) ^ (d - 1) * |b - a| :=
      aux_abs_pow_sub_le (d - 1) hb.le ha.le hba (show a ≤ 2 * a by linarith)
    have hdiff : |b - a| ≤ ρ := by rwa [abs_sub_comm]
    have hmul : 0 ≤ (d : ℝ) * (2 * a) ^ (d - 1) := by positivity
    apply le_trans (by simpa only [Nat.sub_add_cancel hd, hdreal] using h)
    exact mul_le_mul_of_nonneg_left hdiff hmul
  have hpow2 : (2 * a) ^ (d - 1) ≤ (4 * b) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) hab4 _
  have hbpow : b ^ d = b ^ (d - 1) * b := by
    simpa only [Nat.sub_add_cancel hd] using pow_succ b (d - 1)
  have hnum : |t| * |b ^ d - a ^ d| ≤
      ((d : ℝ) * 4 ^ (d - 1) * ρ) * b ^ d := by
    calc
      |t| * |b ^ d - a ^ d| ≤ b * ((d : ℝ) * (2 * a) ^ (d - 1) * ρ) :=
        mul_le_mul ht hpow (abs_nonneg _) hb.le
      _ ≤ b * ((d : ℝ) * (4 * b) ^ (d - 1) * ρ) := by
        apply mul_le_mul_of_nonneg_left _ hb.le
        apply mul_le_mul_of_nonneg_right _ hρ.le
        exact mul_le_mul_of_nonneg_left hpow2 (Nat.cast_nonneg d)
      _ = _ := by rw [mul_pow, hbpow]; ring
  have hterm : |t * (b ^ d - a ^ d) / b ^ d| ≤
      (d : ℝ) * 4 ^ (d - 1) * ρ := by
    rw [abs_div, abs_mul, abs_of_pos (pow_pos hb d)]
    exact (div_le_iff₀ (pow_pos hb d)).mpr hnum
  have hid : s / a ^ d - t / b ^ d =
      ((s - t) + t * (b ^ d - a ^ d) / b ^ d) / a ^ d := by
    field_simp [ha.ne', hb.ne']; ring
  rw [hid, abs_div, abs_of_pos (pow_pos ha d)]
  apply div_le_div_of_nonneg_right _ (pow_nonneg ha.le d)
  calc
    |(s - t) + t * (b ^ d - a ^ d) / b ^ d| ≤
        |s - t| + |t * (b ^ d - a ^ d) / b ^ d| := abs_add_le _ _
    _ ≤ ρ + (d : ℝ) * 4 ^ (d - 1) * ρ := add_le_add hst hterm
    _ = aux_D d * ρ := by unfold aux_D; ring

lemma aux_kernel_difference_far {d : ℕ} (hd : 1 ≤ d)
    (i : Fin d) (u v : SpatialCoordinates d)
    (hρ : 0 < aux_radius (u - v)) (hfar : 2 * aux_radius (u - v) ≤ aux_radius u) :
    |aux_kernel i u - aux_kernel i v| ≤ aux_D d * aux_radius (u - v) / aux_radius u ^ d := by
  apply aux_numerical_kernel_difference hd hρ hfar
    (aux_abs_radius_sub_le u v) _ (aux_coordinate_le_radius v i)
  exact aux_coordinate_le_radius (u - v) i

lemma aux_difference_majorant {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    (x y t : SpatialCoordinates d) {R M a : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (ha : |a| ≤ M)
    (hρ : 0 < aux_radius (x - y)) (_hρR : aux_radius (x - y) ≤ R) :
    |(aux_kernel i (x - t) - aux_kernel i (y - t)) * a| ≤
      M * (aux_near d (2 * aux_radius (x - y)) (x - t) +
        aux_near d (3 * aux_radius (x - y)) (y - t)) +
      (aux_D d * aux_radius (x - y) * M) *
        aux_annulus d (2 * aux_radius (x - y)) (2 * R) (x - t) +
      (aux_D d * aux_radius (x - y) / (2 * R) ^ d) * |a| := by
  let ρ : ℝ := aux_radius (x - y)
  have hD : 0 ≤ aux_D d := (aux_D_pos d).le
  have htail : 0 ≤ (aux_D d * ρ / (2 * R) ^ d) * |a| := by positivity
  have hn : 0 ≤ M * (aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t)) :=
    mul_nonneg hM (add_nonneg (aux_near_nonneg _ _ _) (aux_near_nonneg _ _ _))
  have han : 0 ≤ (aux_D d * ρ * M) * aux_annulus d (2 * ρ) (2 * R) (x - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD hρ.le) hM) (aux_annulus_nonneg _ _ _ _)
  have huv : (x - t) - (y - t) = x - y := by abel
  by_cases hnear : aux_radius (x - t) < 2 * ρ
  · have hyn : aux_radius (y - t) < 3 * ρ := by
      have he : y - t = (y - x) + (x - t) := by abel
      have htri : aux_radius ((y - x) + (x - t)) ≤
          aux_radius (y - x) + aux_radius (x - t) := aux_radius_add_le (y - x) (x - t)
      rw [← he, aux_radius_sub_comm y x] at htri
      dsimp [ρ] at hnear ⊢
      linarith
    have hxq : aux_near d (2 * ρ) (x - t) = aux_riesz (x - t) :=
      aux_near_eq_riesz d (2 * ρ) (x - t) hnear
    have hyq : aux_near d (3 * ρ) (y - t) = aux_riesz (y - t) :=
      aux_near_eq_riesz d (3 * ρ) (y - t) hyn
    have hb : |aux_kernel i (x - t) - aux_kernel i (y - t)| ≤
        aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t) := by
      rw [hxq, hyq]
      exact (abs_sub _ _).trans
        (add_le_add (aux_abs_kernel_le_riesz hd i _) (aux_abs_kernel_le_riesz hd i _))
    rw [abs_mul]
    have hmul : |aux_kernel i (x - t) - aux_kernel i (y - t)| * |a| ≤
        (aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t)) * M :=
      mul_le_mul hb ha (abs_nonneg a)
        (add_nonneg (aux_near_nonneg _ _ _) (aux_near_nonneg _ _ _))
    nlinarith
  · have hfar : 2 * ρ ≤ aux_radius (x - t) := le_of_not_gt hnear
    have hb : |aux_kernel i (x - t) - aux_kernel i (y - t)| ≤
        aux_D d * ρ / aux_radius (x - t) ^ d := by
      simpa only [huv] using
        (aux_kernel_difference_far hd i (x - t) (y - t)
          (by simpa only [huv] using hρ) (by simpa only [huv] using hfar))
    have hp : 0 < aux_radius (x - t) := by dsimp [ρ] at hfar; linarith
    by_cases hupper : aux_radius (x - t) ≤ 2 * R
    · have he : aux_annulus d (2 * ρ) (2 * R) (x - t) =
          (aux_radius (x - t) ^ d)⁻¹ := by
        simp only [aux_annulus, indicator_of_mem (show aux_radius (x - t) ∈ Icc (2 * ρ) (2 * R)
          from ⟨hfar, hupper⟩)]
      have hh : |(aux_kernel i (x - t) - aux_kernel i (y - t)) * a| ≤
          (aux_D d * ρ * M) * aux_annulus d (2 * ρ) (2 * R) (x - t) := by
        rw [abs_mul, he]
        have hmul : |aux_kernel i (x - t) - aux_kernel i (y - t)| * |a| ≤
            (aux_D d * ρ / aux_radius (x - t) ^ d) * M :=
          mul_le_mul hb ha (abs_nonneg a)
            (div_nonneg (mul_nonneg hD hρ.le) (pow_nonneg hp.le d))
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
      exact hh.trans (by linarith)
    · have hpow : (2 * R) ^ d ≤ aux_radius (x - t) ^ d :=
        pow_le_pow_left₀ (by positivity) (le_of_not_ge hupper) d
      have hinv : (aux_radius (x - t) ^ d)⁻¹ ≤ ((2 * R) ^ d)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hpow
      have hh : |(aux_kernel i (x - t) - aux_kernel i (y - t)) * a| ≤
          (aux_D d * ρ / (2 * R) ^ d) * |a| := by
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg a)
        apply hb.trans
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hinv (mul_nonneg hD hρ.le)
      exact hh.trans (by linarith)

def aux_A (d : ℕ) : ℝ := (aux_c d)⁻¹ * (5 * aux_c d + aux_D d + aux_D d * aux_c d + 1)

lemma aux_A_pos (d : ℕ) (hd : 1 ≤ d) : 0 < aux_A d := by
  have hc : 0 < aux_c d := aux_c_pos d hd
  have hD : 0 < aux_D d := aux_D_pos d
  unfold aux_A
  positivity

lemma aux_convolution_modulus {d : ℕ} (hd : 1 ≤ d) {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) {f : SpatialCoordinates d → ℝ}
    (hf : Integrable f volume) (hbound : ∀ᵐ t ∂volume, |f t| ≤ M)
    (hL : (∫ t, |f t|) ≤ M * R ^ d)
    (i : Fin d) (x y : SpatialCoordinates d) (hxy : x ≠ y)
    (hρR : aux_radius (x - y) ≤ R) :
    |aux_convolution f x i - aux_convolution f y i| ≤
      aux_A d * M * aux_radius (x - y) * (1 + Real.log (R / aux_radius (x - y))) := by
  let ρ : ℝ := aux_radius (x - y)
  have hρ : 0 < ρ := aux_radius_pos (sub_ne_zero.mpr hxy)
  have hc : 0 < aux_c d := aux_c_pos d hd
  have hD : 0 < aux_D d := aux_D_pos d
  have hlog : 0 ≤ Real.log (R / ρ) :=
    Real.log_nonneg ((le_div_iff₀ hρ).mpr (by simpa only [one_mul] using hρR))
  let B := fun t : SpatialCoordinates d =>
    M * (aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t)) +
    (aux_D d * ρ * M) * aux_annulus d (2 * ρ) (2 * R) (x - t) +
    (aux_D d * ρ / (2 * R) ^ d) * |f t|
  have hnx : Integrable
      (fun t : SpatialCoordinates d => aux_near d (2 * ρ) (x - t)) volume :=
    (aux_near_integrable d hd (2 * ρ)).comp_sub_left x
  have hny : Integrable
      (fun t : SpatialCoordinates d => aux_near d (3 * ρ) (y - t)) volume :=
    (aux_near_integrable d hd (3 * ρ)).comp_sub_left y
  have han : Integrable
      (fun t : SpatialCoordinates d => aux_annulus d (2 * ρ) (2 * R) (x - t)) volume :=
    (aux_annulus_integrable d hd (b := 2 * R)
      (show 0 < 2 * ρ by positivity)).comp_sub_left x
  have h1 : Integrable (fun t : SpatialCoordinates d =>
      M * (aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t))) volume :=
    (hnx.add hny).const_mul M
  have h2 : Integrable (fun t : SpatialCoordinates d =>
      (aux_D d * ρ * M) * aux_annulus d (2 * ρ) (2 * R) (x - t)) volume :=
    han.const_mul (aux_D d * ρ * M)
  have h3 : Integrable (fun t : SpatialCoordinates d =>
      (aux_D d * ρ / (2 * R) ^ d) * |f t|) volume :=
    hf.abs.const_mul (aux_D d * ρ / (2 * R) ^ d)
  have h12 : Integrable (fun t : SpatialCoordinates d =>
      M * (aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t)) +
        (aux_D d * ρ * M) * aux_annulus d (2 * ρ) (2 * R) (x - t)) volume :=
    h1.add h2
  have hB : Integrable B volume := h12.add h3
  have hIntx : Integrable
      (fun t : SpatialCoordinates d => aux_kernel i (x - t) * f t) volume :=
    (aux_kernel_integrable_estimate hd hf hM hR hbound i x).1
  have hInty : Integrable
      (fun t : SpatialCoordinates d => aux_kernel i (y - t) * f t) volume :=
    (aux_kernel_integrable_estimate hd hf hM hR hbound i y).1
  have hdiff : Integrable
      (fun t => (aux_kernel i (x - t) - aux_kernel i (y - t)) * f t) volume := by
    apply (hIntx.sub hInty).congr
    exact Filter.Eventually.of_forall (fun t => by dsimp only; simp only [Pi.sub_apply]; ring)
  have hmajor : ∀ᵐ t ∂volume,
      |(aux_kernel i (x - t) - aux_kernel i (y - t)) * f t| ≤ B t := by
    filter_upwards [hbound] with t ht
    exact aux_difference_majorant hd i x y t hR hM ht hρ hρR
  have hratio : (2 * R) / (2 * ρ) = R / ρ := by
    field_simp [hρ.ne']
  have hBvalue : (∫ t, B t) =
      M * (aux_c d * (2 * ρ) + aux_c d * (3 * ρ)) +
      (aux_D d * ρ * M) * (aux_c d * Real.log (R / ρ)) +
      (aux_D d * ρ / (2 * R) ^ d) * ∫ t, |f t| := by
    change (∫ t, (M * (aux_near d (2 * ρ) (x - t) + aux_near d (3 * ρ) (y - t)) +
      (aux_D d * ρ * M) * aux_annulus d (2 * ρ) (2 * R) (x - t)) +
      (aux_D d * ρ / (2 * R) ^ d) * |f t|) = _
    rw [integral_add h12 h3, integral_add h1 h2]
    simp only [integral_const_mul, integral_add hnx hny]
    rw [integral_sub_left_eq_self (aux_near d (2 * ρ)) volume x,
      integral_sub_left_eq_self (aux_near d (3 * ρ)) volume y,
      integral_sub_left_eq_self (aux_annulus d (2 * ρ) (2 * R)) volume x,
      aux_near_integral d hd (show 0 ≤ 2 * ρ by positivity),
      aux_near_integral d hd (show 0 ≤ 3 * ρ by positivity),
      aux_annulus_integral d hd (show 0 < 2 * ρ by positivity) (show 2 * ρ ≤ 2 * R by linarith),
      hratio]
  have hmass : (∫ t, |f t|) ≤ M * (2 * R) ^ d := by
    apply hL.trans
    apply mul_le_mul_of_nonneg_left _ hM
    exact pow_le_pow_left₀ hR.le (by linarith) d
  have htail : (aux_D d * ρ / (2 * R) ^ d) * (∫ t, |f t|) ≤ aux_D d * ρ * M := by
    calc
      (aux_D d * ρ / (2 * R) ^ d) * (∫ t, |f t|) ≤
          (aux_D d * ρ / (2 * R) ^ d) * (M * (2 * R) ^ d) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by field_simp [hR.ne']
  have hraw : (∫ t, |(aux_kernel i (x - t) - aux_kernel i (y - t)) * f t|) ≤
      (5 * aux_c d + aux_D d) * (M * ρ) + (aux_D d * aux_c d) * (M * ρ * Real.log (R / ρ)) := by
    apply (integral_mono_ae hdiff.abs hB hmajor).trans
    rw [hBvalue]
    calc
      M * (aux_c d * (2 * ρ) + aux_c d * (3 * ρ)) +
          (aux_D d * ρ * M) * (aux_c d * Real.log (R / ρ)) +
          (aux_D d * ρ / (2 * R) ^ d) * (∫ t, |f t|) ≤
        M * (aux_c d * (2 * ρ) + aux_c d * (3 * ρ)) +
          (aux_D d * ρ * M) * (aux_c d * Real.log (R / ρ)) + aux_D d * ρ * M :=
        add_le_add (le_refl _) htail
      _ = _ := by ring
  have hcoeff₁ : 5 * aux_c d + aux_D d ≤ 5 * aux_c d + aux_D d + aux_D d * aux_c d + 1 := by
    nlinarith [mul_pos hD hc]
  have hcoeff₂ : aux_D d * aux_c d ≤ 5 * aux_c d + aux_D d + aux_D d * aux_c d + 1 := by linarith
  have hraw' : (∫ t, |(aux_kernel i (x - t) - aux_kernel i (y - t)) * f t|) ≤
      (5 * aux_c d + aux_D d + aux_D d * aux_c d + 1) * M * ρ * (1 + Real.log (R / ρ)) := by
    apply hraw.trans
    calc
      (5 * aux_c d + aux_D d) * (M * ρ) + (aux_D d * aux_c d) * (M * ρ * Real.log (R / ρ)) ≤
          (5 * aux_c d + aux_D d + aux_D d * aux_c d + 1) * (M * ρ) +
          (5 * aux_c d + aux_D d + aux_D d * aux_c d + 1) * (M * ρ * Real.log (R / ρ)) :=
        add_le_add (mul_le_mul_of_nonneg_right hcoeff₁ (mul_nonneg hM hρ.le))
          (mul_le_mul_of_nonneg_right hcoeff₂ (mul_nonneg (mul_nonneg hM hρ.le) hlog))
      _ = _ := by ring
  have heq : aux_convolution f x i - aux_convolution f y i =
      (aux_c d)⁻¹ * ∫ t, (aux_kernel i (x - t) - aux_kernel i (y - t)) * f t := by
    rw [aux_convolution, aux_convolution, ← mul_sub, ← integral_sub hIntx hInty]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp only; ring)
  calc
    |aux_convolution f x i - aux_convolution f y i| =
        (aux_c d)⁻¹ * |∫ t, (aux_kernel i (x - t) - aux_kernel i (y - t)) * f t| := by
      rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    _ ≤ (aux_c d)⁻¹ * ∫ t, |(aux_kernel i (x - t) - aux_kernel i (y - t)) * f t| := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => (aux_kernel i (x - t) - aux_kernel i (y - t)) * f t)
    _ ≤ (aux_c d)⁻¹ * ((5 * aux_c d + aux_D d + aux_D d * aux_c d + 1) * M * ρ *
        (1 + Real.log (R / ρ))) :=
      mul_le_mul_of_nonneg_left hraw' (inv_nonneg.mpr hc.le)
    _ = _ := by dsimp [aux_A, ρ]; ring

lemma aux_kernel_right_estimate {d : ℕ} (hd : 1 ≤ d)
    {f : SpatialCoordinates d → ℝ} (hf : Integrable f volume)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ t ∂volume, |f t| ≤ M)
    (i : Fin d) (y : SpatialCoordinates d) :
    Integrable (fun t => aux_kernel i (t - y) * f t) volume ∧
      (∫ t, |aux_kernel i (t - y) * f t|) ≤ M * aux_c d + ∫ t, |f t| := by
  have h : Integrable (fun t : SpatialCoordinates d => aux_kernel i (y - t) * f t) volume ∧
      (∫ t, |aux_kernel i (y - t) * f t|) ≤
        M * (aux_c d * 1) + ((1 : ℝ) ^ (d - 1))⁻¹ * ∫ t, |f t| :=
    aux_kernel_integrable_estimate hd hf hM zero_lt_one hb i y
  have he : (fun t => aux_kernel i (t - y) * f t) =
      (fun t => -(aux_kernel i (y - t) * f t)) := by
    funext t
    rw [aux_kernel_sub_swap i t y, neg_mul]
  constructor
  · rw [he]
    exact h.1.neg
  · calc
      (∫ t, |aux_kernel i (t - y) * f t|) = ∫ t, |aux_kernel i (y - t) * f t| := by
        apply integral_congr_ae
        filter_upwards with t
        try dsimp only
        rw [congrFun he t, abs_neg]
      _ ≤ _ := by simpa only [one_pow, inv_one, mul_one, one_mul] using h.2

lemma aux_test_derivative {d : ℕ} {φ : SpatialCoordinates d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (i : Fin d) :
    Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) ∧
      HasCompactSupport (fun x => fderiv ℝ φ x (Pi.single i 1)) ∧
      Integrable (fun x => fderiv ℝ φ x (Pi.single i 1)) volume ∧
      MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) (⊤ : ENNReal) volume := by
  have hc : Continuous (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hk : HasCompactSupport (fun x : SpatialCoordinates d =>
      fderiv ℝ φ x (Pi.single i 1)) := hs.fderiv_apply ℝ (Pi.single i 1)
  exact ⟨hc, hk, hc.integrable_of_hasCompactSupport hk,
    hc.memLp_top_of_hasCompactSupport hk volume⟩

lemma aux_integral_volumeIoiPow (n : ℕ) (F : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), F r ∂Measure.volumeIoiPow n) =
      ∫ r in Ioi (0 : ℝ), r ^ n * F r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ n) • F r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hrpos : 0 < r := hr
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hrpos.le n),
      smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const n).real_toNNReal

lemma aux_polar_integral (d : ℕ) (hd : 1 ≤ d)
    {F : SpatialCoordinates d → ℝ} (hF : Integrable F volume) :
    (∫ w, F w) =
      ∫ θ : Metric.sphere (0 : aux_E d) 1,
        (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * F (r • (aux_euclidean d).symm θ))
          ∂(volume : Measure (aux_E d)).toSphere := by
  let : NeZero d := ⟨by omega⟩
  let H := homeomorphUnitSphereProd (aux_E d)
  let T : Metric.sphere (0 : aux_E d) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => F ((aux_euclidean d).symm (H.symm p).1)
  have hFE : Integrable (fun u : aux_E d => F ((aux_euclidean d).symm u)) volume :=
    ((aux_euclidean_symm_measurePreserving d).integrable_comp_emb
      (aux_euclidean_symm_measurableEmbedding d) (g := F)).mpr hF
  have hsub : Integrable
      (fun u : ({(0 : aux_E d)}ᶜ : Set (aux_E d)) => F ((aux_euclidean d).symm u.1))
      ((volume : Measure (aux_E d)).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hFE.integrableOn
  have hmp : MeasurePreserving H ((volume : Measure (aux_E d)).comap Subtype.val)
      ((volume : Measure (aux_E d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
    simpa only [finrank_euclideanSpace_fin] using
      (volume : Measure (aux_E d)).measurePreserving_homeomorphUnitSphereProd
  have hcomp : Integrable (T ∘ H)
      ((volume : Measure (aux_E d)).comap Subtype.val) := by
    simpa only [Function.comp_def, T, Homeomorph.symm_apply_apply] using hsub
  have hT : Integrable T
      ((volume : Measure (aux_E d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) :=
    (hmp.integrable_comp_emb H.measurableEmbedding (g := T)).mp hcomp
  calc
    (∫ w, F w) = ∫ u : aux_E d, F ((aux_euclidean d).symm u) :=
      ((aux_euclidean_symm_measurePreserving d).integral_comp
        (aux_euclidean_symm_measurableEmbedding d) F).symm
    _ = ∫ u : ({(0 : aux_E d)}ᶜ : Set (aux_E d)), F ((aux_euclidean d).symm u.1)
          ∂((volume : Measure (aux_E d)).comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun u : aux_E d => F ((aux_euclidean d).symm u)), restrict_compl_singleton]
    _ = ∫ p, T p ∂((volume : Measure (aux_E d)).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
      simpa only [T, Homeomorph.symm_apply_apply] using
        hmp.integral_comp H.measurableEmbedding T
    _ = ∫ θ : Metric.sphere (0 : aux_E d) 1,
        (∫ r : Ioi (0 : ℝ), T (θ, r) ∂Measure.volumeIoiPow (d - 1))
          ∂(volume : Measure (aux_E d)).toSphere := integral_prod T hT
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with θ
      calc
        (∫ r : Ioi (0 : ℝ), T (θ, r) ∂Measure.volumeIoiPow (d - 1)) =
            ∫ r : Ioi (0 : ℝ), F ((r : ℝ) • (aux_euclidean d).symm θ)
              ∂Measure.volumeIoiPow (d - 1) := by
          apply integral_congr_ae
          filter_upwards with r
          simp only [T, H, homeomorphUnitSphereProd_symm_apply_coe, map_smul]
        _ = _ := aux_integral_volumeIoiPow (d - 1)
          (fun r : ℝ => F (r • (aux_euclidean d).symm θ))

lemma aux_compact_support_on_ray {d : ℕ} {φ : SpatialCoordinates d → ℝ}
    (hs : HasCompactSupport φ) (u y : SpatialCoordinates d) (hu : aux_radius u = 1) :
    HasCompactSupport (fun r : ℝ => φ (r • u + y)) := by
  obtain ⟨B, hB⟩ := (hs.image (aux_euclidean d).continuous).isBounded.exists_norm_le
  change IsCompact (closure (Function.support (fun r : ℝ => φ (r • u + y))))
  apply (isCompact_Icc : IsCompact (Icc (-(B + aux_radius y)) (B + aux_radius y))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro r hr
  have hφ : r • u + y ∈ tsupport φ := subset_tsupport φ hr
  have hrad : aux_radius (r • u + y) ≤ B :=
    hB _ (mem_image_of_mem (aux_euclidean d) hφ)
  have htri : aux_radius ((r • u + y) - y) ≤ aux_radius (r • u + y) + aux_radius y :=
    aux_radius_sub_le (r • u + y) y
  rw [add_sub_cancel_right, aux_radius_smul, hu, mul_one] at htri
  exact abs_le.mp (htri.trans (add_le_add hrad (le_refl (aux_radius y))))

lemma aux_integral_derivative_on_ray {d : ℕ} {φ : SpatialCoordinates d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (u y : SpatialCoordinates d) (hu : aux_radius u = 1) :
    (∫ r in Ioi (0 : ℝ), fderiv ℝ φ (r • u + y) u) = -φ y := by
  let ψ := fun r : ℝ => φ (r • u + y)
  have hψ : ContDiff ℝ 1 ψ :=
    (hφ.of_le
      (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).comp
        ((contDiff_id.smul contDiff_const).add contDiff_const)
  have hsψ : HasCompactSupport ψ := aux_compact_support_on_ray hs u y hu
  have hderiv (r : ℝ) : HasDerivAt ψ (fderiv ℝ φ (r • u + y) u) r := by
    have hray : HasDerivAt (fun t : ℝ => t • u + y) u r := by
      simpa only [one_smul] using! ((hasDerivAt_id r).smul_const u).add_const y
    exact (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
        r hray
  calc
    (∫ r in Ioi (0 : ℝ), fderiv ℝ φ (r • u + y) u) =
        ∫ r in Ioi (0 : ℝ), deriv ψ r :=
      setIntegral_congr_fun measurableSet_Ioi (fun r _ => (hderiv r).deriv.symm)
    _ = -φ y := by
      simpa only [ψ, zero_smul, zero_add] using
        HasCompactSupport.integral_Ioi_deriv_eq hψ hsψ 0

def aux_radial_test {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (y w : SpatialCoordinates d) : ℝ :=
  fderiv ℝ φ (w + y) w / aux_radius w ^ d

lemma aux_radial_test_sum {d : ℕ} (φ : SpatialCoordinates d → ℝ)
    (y w : SpatialCoordinates d) :
    (∑ i : Fin d, aux_kernel i w * fderiv ℝ φ (w + y) (Pi.single i 1)) =
      aux_radial_test φ y w := by
  have hw : (∑ i : Fin d, (w i) • (Pi.single i 1 : SpatialCoordinates d)) = w := by
    ext j
    simp [Pi.single_apply]
  have hl : fderiv ℝ φ (w + y) w =
      ∑ i : Fin d, w i * fderiv ℝ φ (w + y) (Pi.single i 1) := by
    calc
      fderiv ℝ φ (w + y) w =
          fderiv ℝ φ (w + y) (∑ i : Fin d, (w i) • (Pi.single i 1 : SpatialCoordinates d)) :=
        congrArg (fderiv ℝ φ (w + y)) hw.symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  rw [aux_radial_test, hl, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  unfold aux_kernel
  ring

lemma aux_single_charge {d : ℕ} (hd : 1 ≤ d)
    (y : SpatialCoordinates d) (φ : SpatialCoordinates d → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∑ i : Fin d, ∫ x, aux_kernel i (x - y) * fderiv ℝ φ x (Pi.single i 1)) =
      -(aux_c d) * φ y := by
  have hInt (i : Fin d) :
      Integrable (fun x => aux_kernel i (x - y) * fderiv ℝ φ x (Pi.single i 1)) volume := by
    have hq :
        Continuous (fun x : SpatialCoordinates d => fderiv ℝ φ x (Pi.single i 1)) ∧
          HasCompactSupport (fun x : SpatialCoordinates d =>
            fderiv ℝ φ x (Pi.single i 1)) ∧
          Integrable (fun x : SpatialCoordinates d =>
            fderiv ℝ φ x (Pi.single i 1)) volume ∧
          MemLp (fun x : SpatialCoordinates d =>
            fderiv ℝ φ x (Pi.single i 1)) (⊤ : ENNReal) volume :=
      aux_test_derivative hφ hs i
    exact (aux_kernel_right_estimate hd hq.2.2.1 ENNReal.toReal_nonneg
      (aux_essential_bound hq.2.2.2) i y).1
  have hshift (i : Fin d) :
      Integrable (fun w => aux_kernel i w * fderiv ℝ φ (w + y) (Pi.single i 1)) volume := by
    simpa only [add_sub_cancel_right] using (hInt i).comp_add_right y
  have hF : Integrable (aux_radial_test φ y) volume := by
    apply (integrable_finsetSum Finset.univ (fun i _ => hshift i)).congr
    exact Filter.Eventually.of_forall (fun w => aux_radial_test_sum φ y w)
  calc
    (∑ i : Fin d, ∫ x, aux_kernel i (x - y) * fderiv ℝ φ x (Pi.single i 1)) =
        ∫ x, ∑ i : Fin d, aux_kernel i (x - y) * fderiv ℝ φ x (Pi.single i 1) :=
      (integral_finsetSum Finset.univ (fun i _ => hInt i)).symm
    _ = ∫ w, ∑ i : Fin d, aux_kernel i w * fderiv ℝ φ (w + y) (Pi.single i 1) := by
      symm
      simpa only [add_sub_cancel_right] using integral_add_right_eq_self
        (fun x => ∑ i : Fin d, aux_kernel i (x - y) * fderiv ℝ φ x (Pi.single i 1)) y
    _ = ∫ w, aux_radial_test φ y w :=
      integral_congr_ae (Filter.Eventually.of_forall (fun w => aux_radial_test_sum φ y w))
    _ = ∫ θ : Metric.sphere (0 : aux_E d) 1,
        (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * aux_radial_test φ y (r • (aux_euclidean d).symm θ))
          ∂(volume : Measure (aux_E d)).toSphere := aux_polar_integral d hd hF
    _ = ∫ _ : Metric.sphere (0 : aux_E d) 1, -φ y ∂(volume : Measure (aux_E d)).toSphere := by
      apply integral_congr_ae
      filter_upwards with θ
      have hu : aux_radius ((aux_euclidean d).symm θ) = 1 := by
        simpa only [aux_radius, ContinuousLinearEquiv.apply_symm_apply,
          Metric.mem_sphere, dist_zero_right] using θ.property
      calc
        (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * aux_radial_test φ y (r • (aux_euclidean d).symm θ)) =
            ∫ r in Ioi (0 : ℝ), fderiv ℝ φ (r • (aux_euclidean d).symm θ + y)
              ((aux_euclidean d).symm θ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          dsimp only
          have hrpos : 0 < r := hr
          simp only [aux_radial_test, map_smul, smul_eq_mul, aux_radius_smul, hu,
            abs_of_pos hrpos, mul_one]
          have hp : r ^ d = r ^ (d - 1) * r := by
            simpa only [Nat.sub_add_cancel hd] using pow_succ r (d - 1)
          rw [hp]
          field_simp [hrpos.ne']
        _ = -φ y := aux_integral_derivative_on_ray hφ hs _ y hu
    _ = -(aux_c d) * φ y := by
      rw [integral_const, Measure.toSphere_real_apply_univ]
      simp only [finrank_euclideanSpace_fin, Measure.real, smul_eq_mul, aux_c]
      ring

lemma aux_double_integrable {d : ℕ} (hd : 1 ≤ d)
    {f q : SpatialCoordinates d → ℝ} (hf : Integrable f volume)
    (hq : Integrable q volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂volume, |q x| ≤ M) (i : Fin d) :
    Integrable (fun p : SpatialCoordinates d × SpatialCoordinates d =>
      aux_kernel i (p.2 - p.1) * f p.1 * q p.2) (volume.prod volume) := by
  let H := fun p : SpatialCoordinates d × SpatialCoordinates d =>
    aux_kernel i (p.2 - p.1) * f p.1 * q p.2
  have hm : AEStronglyMeasurable H (volume.prod volume) :=
    (((aux_kernel_measurable i).comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_fst).mul hq.aestronglyMeasurable.comp_snd
  have hsection (y : SpatialCoordinates d) : Integrable (fun x => H (y, x)) volume := by
    apply ((aux_kernel_right_estimate hd hq hM hb i y).1.mul_const (f y)).congr
    exact Filter.Eventually.of_forall (fun x => by dsimp [H]; ring)
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall hsection, ?_⟩
  apply (hf.abs.mul_const (M * aux_c d + ∫ x, |q x|)).mono'
    hm.norm.integral_prod_right'
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg (H (y, x))))]
  calc
    (∫ x, ‖H (y, x)‖) = ∫ x, |f y| * |aux_kernel i (x - y) * q x| := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [H, Real.norm_eq_abs, abs_mul]
      ring
    _ = |f y| * ∫ x, |aux_kernel i (x - y) * q x| := integral_const_mul _ _
    _ ≤ |f y| * (M * aux_c d + ∫ x, |q x|) :=
      mul_le_mul_of_nonneg_left (aux_kernel_right_estimate hd hq hM hb i y).2 (abs_nonneg _)

lemma aux_convolution_pairing {d : ℕ} (hd : 1 ≤ d)
    {f q : SpatialCoordinates d → ℝ} (hf : Integrable f volume)
    (hq : Integrable q volume) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂volume, |q x| ≤ M) (i : Fin d) :
    Integrable (fun y => f y * ∫ x, aux_kernel i (x - y) * q x) volume ∧
      (∫ x, aux_convolution f x i * q x) =
        (aux_c d)⁻¹ * ∫ y, f y * ∫ x, aux_kernel i (x - y) * q x := by
  let H := fun p : SpatialCoordinates d × SpatialCoordinates d =>
    aux_kernel i (p.2 - p.1) * f p.1 * q p.2
  have hH : Integrable H (volume.prod volume) := aux_double_integrable hd hf hq hM hb i
  have hinner (y : SpatialCoordinates d) :
      (∫ x, H (y, x)) = f y * ∫ x, aux_kernel i (x - y) * q x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp [H]; ring)
  refine ⟨hH.integral_prod_left.congr (Filter.Eventually.of_forall hinner), ?_⟩
  calc
    (∫ x, aux_convolution f x i * q x) =
        (aux_c d)⁻¹ * ∫ x, (∫ y, aux_kernel i (x - y) * f y) * q x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by unfold aux_convolution; ring)
    _ = (aux_c d)⁻¹ * ∫ x, ∫ y, H (y, x) := by
      simp only [H, integral_mul_const]
    _ = (aux_c d)⁻¹ * ∫ y, ∫ x, H (y, x) := by
      congr 1
      exact (integral_integral_swap hH).symm
    _ = _ := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hinner)

lemma aux_convolution_distribution {d : ℕ} (hd : 1 ≤ d)
    {f : SpatialCoordinates d → ℝ} (hf : Integrable f volume)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∑ i : Fin d, ∫ x, aux_convolution f x i * fderiv ℝ φ x (Pi.single i 1)) =
      -∫ x, f x * φ x := by
  let F := fun (i : Fin d) (y : SpatialCoordinates d) =>
    f y * ∫ x, aux_kernel i (x - y) * fderiv ℝ φ x (Pi.single i 1)
  have hp (i : Fin d) : Integrable (F i) volume ∧
      (∫ x, aux_convolution f x i * fderiv ℝ φ x (Pi.single i 1)) =
        (aux_c d)⁻¹ * ∫ y, F i y := by
    have hq :
        Continuous (fun x : SpatialCoordinates d => fderiv ℝ φ x (Pi.single i 1)) ∧
          HasCompactSupport (fun x : SpatialCoordinates d =>
            fderiv ℝ φ x (Pi.single i 1)) ∧
          Integrable (fun x : SpatialCoordinates d =>
            fderiv ℝ φ x (Pi.single i 1)) volume ∧
          MemLp (fun x : SpatialCoordinates d =>
            fderiv ℝ φ x (Pi.single i 1)) (⊤ : ENNReal) volume :=
      aux_test_derivative hφ hs i
    exact aux_convolution_pairing hd hf hq.2.2.1 ENNReal.toReal_nonneg
      (aux_essential_bound hq.2.2.2) i
  calc
    (∑ i : Fin d, ∫ x, aux_convolution f x i * fderiv ℝ φ x (Pi.single i 1)) =
        ∑ i : Fin d, (aux_c d)⁻¹ * ∫ y, F i y :=
      Finset.sum_congr rfl (fun i _ => (hp i).2)
    _ = (aux_c d)⁻¹ * ∫ y, ∑ i : Fin d, F i y := by
      rw [← Finset.mul_sum, integral_finsetSum Finset.univ (fun i _ => (hp i).1)]
    _ = (aux_c d)⁻¹ * ∫ y, f y * (-(aux_c d) * φ y) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [F]
      rw [← Finset.mul_sum, aux_single_charge hd y φ hφ hs]
    _ = -∫ y, f y * φ y := by
      have hc : aux_c d ≠ 0 := (aux_c_pos d hd).ne'
      calc
        (aux_c d)⁻¹ * (∫ y, f y * (-(aux_c d) * φ y)) =
            (aux_c d)⁻¹ * (-(aux_c d) * ∫ y, f y * φ y) := by
          congr 1
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y => by dsimp only; ring)
        _ = _ := by field_simp [hc]

end aux_newt

lemma aux_lem_primitive_newtonian_convolution_scalar_step
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ aux_A : ℝ, 0 < aux_A ∧
      ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
        (f : SpatialCoordinates d → ℝ),
        MemLp f (⊤ : ENNReal) volume →
        (∀ᵐ x ∂volume,
          x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) →
        let g : SpatialCoordinates d → Fin d → ℝ :=
          (fun x i =>
            ((d : ℝ) * (volume {w : SpatialCoordinates d |
              Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
                (∫ y, (if x = y then 0 else
                  (x i - y i) /
                    (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y))
        (∀ φ : SpatialCoordinates d → ℝ,
          ContDiff ℝ ∞ φ → HasCompactSupport φ →
            (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) =
              -∫ x, f x * φ x) ∧
          (∀ (i : Fin d) (x y : SpatialCoordinates d),
            x ≠ y →
            Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
            |g x i - g y i| ≤
              aux_A * (eLpNormEssSup f volume).toReal *
                Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
                (1 + Real.log
                  (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) := by
  have hd₁ : 1 ≤ d := by omega
  refine ⟨_root_.SubdiffusiveProcess.Paper.aux_newt.aux_A d, _root_.SubdiffusiveProcess.Paper.aux_newt.aux_A_pos d hd₁, ?_⟩
  intro R hR z f hf hs
  have hsource : Integrable f volume ∧
      (∫ x, |f x|) ≤ (eLpNormEssSup f volume).toReal * R ^ d :=
    _root_.SubdiffusiveProcess.Paper.aux_newt.aux_source_integrable_bound R hR z f hf hs
  dsimp only
  constructor
  · intro φ hφ hφs
    simpa only [_root_.SubdiffusiveProcess.Paper.aux_newt.aux_convolution_eq] using
      _root_.SubdiffusiveProcess.Paper.aux_newt.aux_convolution_distribution hd₁ hsource.1 φ hφ hφs
  · intro i x y hxy hρ
    have hρ' : _root_.SubdiffusiveProcess.Paper.aux_newt.aux_radius (x - y) ≤ R := by
      simpa only [_root_.SubdiffusiveProcess.Paper.aux_newt.aux_radius_eq, Pi.sub_apply] using hρ
    simpa only [_root_.SubdiffusiveProcess.Paper.aux_newt.aux_convolution_eq, _root_.SubdiffusiveProcess.Paper.aux_newt.aux_radius_eq,
      Pi.sub_apply] using
      _root_.SubdiffusiveProcess.Paper.aux_newt.aux_convolution_modulus hd₁ hR ENNReal.toReal_nonneg hsource.1
        (_root_.SubdiffusiveProcess.Paper.aux_newt.aux_essential_bound hf) hsource.2 i x y hxy hρ'

lemma aux_sqrt_sum_sq_le (d : ℕ) (v : Fin d → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ i : Fin d, |v i| ≤ B) :
    Real.sqrt (∑ i : Fin d, (v i) ^ 2) ≤ Real.sqrt (d : ℝ) * B := by
  have hsq (i : Fin d) : (v i) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2)
  have hsum : (∑ i : Fin d, (v i) ^ 2) ≤ (d : ℝ) * B ^ 2 := by
    calc
      (∑ i : Fin d, (v i) ^ 2) ≤ ∑ _i : Fin d, B ^ 2 :=
        Finset.sum_le_sum (fun i _hi => hsq i)
      _ = (d : ℝ) * B ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg (d : ℝ)) hB, ?_⟩
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hsum




theorem lem_primitive_newtonian_convolution :
  ∀ (d : ℕ), 2 ≤ d →
  ∃ C_log : ℝ, 0 < C_log ∧
    ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
      (f : SpatialCoordinates d → ℝ),
      MemLp f (⊤ : ENNReal) volume →
      (∀ᵐ x ∂volume, x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) →
      let g : SpatialCoordinates d → Fin d → ℝ :=
        (fun x i =>
          ((d : ℝ) * (volume {w : SpatialCoordinates d |
            Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
            (∫ y, (if x = y then 0 else
              (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y))
      (∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) =
            -∫ x, f x * φ x) ∧
        (∀ x y : SpatialCoordinates d,
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
          Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
            C_log * (eLpNormEssSup f volume).toReal *
              Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
              (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) := by
  intro d hd
  obtain ⟨aux_A, hA, hscalar⟩ := aux_lem_primitive_newtonian_convolution_scalar_step d hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  refine ⟨aux_A * Real.sqrt (d : ℝ), mul_pos hA (Real.sqrt_pos.mpr hdpos), ?_⟩
  intro R hR z f hf hs
  obtain ⟨hdiv, hmod⟩ := hscalar R hR z f hf hs
  dsimp only
  refine ⟨hdiv, ?_⟩
  intro x y hdist
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
      Real.sqrt_zero, mul_zero, zero_mul, le_refl]
  · have hdistpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      simpa only [_root_.SubdiffusiveProcess.Paper.aux_newt.aux_radius_eq, Pi.sub_apply] using
        (_root_.SubdiffusiveProcess.Paper.aux_newt.aux_radius_pos (sub_ne_zero.mpr hxy))
    have hlog : 0 ≤ Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) :=
      Real.log_nonneg ((le_div_iff₀ hdistpos).mpr
        (by simpa only [one_mul] using hdist))
    have hB : 0 ≤ aux_A * (eLpNormEssSup f volume).toReal *
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
          (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg hA.le ENNReal.toReal_nonneg) hdistpos.le)
        (by linarith)
    calc
      _ ≤ Real.sqrt (d : ℝ) *
          (aux_A * (eLpNormEssSup f volume).toReal *
            Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
              (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) := by
        apply aux_sqrt_sum_sq_le d
        · exact hB
        · intro i
          exact hmod i x y hxy hdist
      _ = _ := by ring

end SubdiffusiveProcess.Paper
