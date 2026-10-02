import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.lane4_smoothed_neumann_load

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lane4_smoothed_load_properties :
  ∀ (d : ℕ) (rho : ℝ → ℝ), ContDiff ℝ ∞ rho →
    (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
  ∀ Krho : ℝ, (∀ tau : ℝ, |rho tau| ≤ Krho) →
  ∀ (p : SpatialCoordinates d) (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ContDiff ℝ ∞ (lane4_smoothed_neumann_load p rho eps) ∧
    (∀ x : SpatialCoordinates d,
      |lane4_smoothed_neumann_load p rho eps x| ≤
        (∑ i : Fin d, |p i|) * (2 * Krho) * eps⁻¹) ∧
    (∀ _i : Fin d,
      (∫ tau in Set.Ioo (0 : ℝ) 1,
        (eps⁻¹ * rho ((1 - tau) / eps) - eps⁻¹ * rho (tau / eps))) = 0) ∧ (∫ x in (SubdiffusiveProcess.Lane4.unitNeumannCube d : Set (SpatialCoordinates d)), lane4_smoothed_neumann_load p rho eps x) = 0 := by
  classical
  intro d rho hrho hsupp Krho hK p eps heps heps8
  have hKrho : 0 ≤ Krho := le_trans (abs_nonneg (rho 1)) (hK 1)
  have heps_inv : 0 < eps⁻¹ := inv_pos.mpr heps
  have hcoord (i : Fin d) :
      ContDiff ℝ ∞ (fun x : SpatialCoordinates d => x i) :=
    contDiff_apply ℝ ℝ i
  have hleft (i : Fin d) :
      ContDiff ℝ ∞ (fun x : SpatialCoordinates d => (1 - x i) / eps) := by
    exact (contDiff_const.sub (hcoord i)).div_const eps
  have hright (i : Fin d) :
      ContDiff ℝ ∞ (fun x : SpatialCoordinates d => x i / eps) := by
    exact (hcoord i).div_const eps
  have hbracket_cont (i : Fin d) :
      ContDiff ℝ ∞ (fun x : SpatialCoordinates d =>
        eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)) := by
    exact (contDiff_const.mul (hrho.comp (hleft i))).sub
      (contDiff_const.mul (hrho.comp (hright i)))
  have hscalar_cont :
      Continuous (fun t : ℝ =>
        eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps)) := by
    exact (continuous_const.mul
      (hrho.continuous.comp ((continuous_const.sub continuous_id).div_const eps))).sub
      (continuous_const.mul (hrho.continuous.comp (continuous_id.div_const eps)))
  have hbracket_integrable (i : Fin d) :
    IntegrableOn
        (fun t : ℝ => eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps))
        (Set.Ioo (0 : ℝ) 1) volume := by
    exact hscalar_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hinterval_zero :
      (∫ t in Set.Ioo (0 : ℝ) 1,
        (eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps))) = 0 := by
    have hleft_int :
        IntegrableOn (fun t : ℝ => eps⁻¹ * rho ((1 - t) / eps))
          (Set.Ioo (0 : ℝ) 1) volume := by
      have hc : Continuous (fun t : ℝ => eps⁻¹ * rho ((1 - t) / eps)) := by
        exact continuous_const.mul
          (hrho.continuous.comp ((continuous_const.sub continuous_id).div_const eps))
      exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hright_int :
        IntegrableOn (fun t : ℝ => eps⁻¹ * rho (t / eps))
          (Set.Ioo (0 : ℝ) 1) volume := by
      have hc : Continuous (fun t : ℝ => eps⁻¹ * rho (t / eps)) := by
        exact continuous_const.mul (hrho.continuous.comp (continuous_id.div_const eps))
      exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hto_interval (f : ℝ → ℝ) :
        (∫ t in Set.Ioo (0 : ℝ) 1, f t) = (∫ t in (0 : ℝ)..1, f t) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact integral_Ioc_eq_integral_Ioo.symm
    have hreflect :
        (∫ t in (0 : ℝ)..1, eps⁻¹ * rho ((1 - t) / eps)) =
          (∫ t in (0 : ℝ)..1, eps⁻¹ * rho (t / eps)) := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := 1) (fun t : ℝ => eps⁻¹ * rho (t / eps)) 1)
    rw [integral_sub hleft_int hright_int, hto_interval, hto_interval]
    exact sub_eq_zero.mpr hreflect
  have hterm_bound (i : Fin d) (x : SpatialCoordinates d) :
      |eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)| ≤
        2 * Krho * eps⁻¹ := by
    calc
      |eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)| ≤
          |eps⁻¹ * rho ((1 - x i) / eps)| +
            |eps⁻¹ * rho (x i / eps)| := abs_sub _ _
      _ = eps⁻¹ * |rho ((1 - x i) / eps)| +
            eps⁻¹ * |rho (x i / eps)| := by
          rw [abs_mul, abs_of_pos heps_inv, abs_mul, abs_of_pos heps_inv]
      _ ≤ eps⁻¹ * Krho + eps⁻¹ * Krho := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hK _) (le_of_lt heps_inv))
            (mul_le_mul_of_nonneg_left (hK _) (le_of_lt heps_inv))
      _ = 2 * Krho * eps⁻¹ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lane4_smoothed_neumann_load
    apply ContDiff.sum
    intro i hi
    exact contDiff_const.mul (hbracket_cont i)
  · intro x
    unfold lane4_smoothed_neumann_load
    calc
      |∑ i : Fin d, p i *
          (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps))| ≤
          ∑ i : Fin d, |p i *
            (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin d, |p i| *
          |eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)| := by
        simp_rw [abs_mul]
      _ ≤ ∑ i : Fin d, |p i| * (2 * Krho * eps⁻¹) := by
        exact Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hterm_bound i x) (abs_nonneg _)
      _ = (∑ i : Fin d, |p i|) * (2 * Krho) * eps⁻¹ := by
        rw [← Finset.sum_mul]
        ring
  · intro _i
    exact hinterval_zero
  · have hset :
        (SubdiffusiveProcess.Lane4.unitNeumannCube d : Set (SpatialCoordinates d)) =
          Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1) := by
      rw [SubdiffusiveProcess.Lane4.unitNeumannCube,
        SubdiffusiveProcess.centeredCube_eq_pi]
      congr 1
      funext i
      norm_num
    have hrest :
        (volume : Measure (SpatialCoordinates d)).restrict
            (Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) =
          Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
    letI : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      ⟨by simp⟩
    have hterm_int (i : Fin d) :
        Integrable
          (fun x : SpatialCoordinates d =>
            p i * (eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)))
          (Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1))) := by
      have hi : Integrable
          (fun t : ℝ => eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps))
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hbracket_integrable i
      exact (MeasureTheory.integrable_comp_eval
        (μ := fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1))
        (i := i) (f := fun t : ℝ =>
          eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps)) hi).const_mul (p i)
    have hcoord_integral (i : Fin d) :
        (∫ x : SpatialCoordinates d,
          eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)
          ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1)))) =
          ∫ t in Set.Ioo (0 : ℝ) 1,
            eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps) := by
      have hmeas : AEStronglyMeasurable
          (fun t : ℝ => eps⁻¹ * rho ((1 - t) / eps) - eps⁻¹ * rho (t / eps))
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
        hscalar_cont.stronglyMeasurable.aestronglyMeasurable
      exact MeasureTheory.integral_comp_eval
        (μ := fun _ : Fin d => volume.restrict (Set.Ioo (0 : ℝ) 1)) (i := i)
        hmeas
    rw [hset, hrest]
    unfold lane4_smoothed_neumann_load
    rw [MeasureTheory.integral_finset_sum]
    · simp_rw [MeasureTheory.integral_const_mul, hcoord_integral]
      simp [hinterval_zero]
    · exact fun i hi => hterm_int i

end Paper
