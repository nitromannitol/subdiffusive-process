import SubdiffusiveProcess.Section10.TorsionExitDensity
import MarkovProcess.Trajectory.Equivariance
import MarkovProcess.Killed.Nested

/-! Transport only the survival event along the literal affine/time path map.
No coefficient, speed-measure or clock normalization is changed. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- An ordinary continuous path survives after rescaling exactly when the
original path survives in the image domain at the multiplied time. -/
theorem lt_exitTime_rescale_iff {d : ℕ} (e : Vec d ≃ₜ Vec d)
    (c : ℝ≥0) (hc : 0 < c) {U : Set (Vec d)} (hU : IsOpen U)
    (t : ℝ≥0) (q : ContinuousPath (Vec d)) :
    (t : ℝ≥0∞) < ContinuousPath.exitTime U (ContinuousPath.rescale e.symm c q) ↔
      ((c * t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime (e '' U) q := by
  have hmem (y : Vec d) : e.symm y ∈ U ↔ y ∈ e '' U := by
    constructor
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      simpa only [e.symm_apply_apply] using hx
  rw [lt_iff_not_ge, lt_iff_not_ge,
    ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU,
    ContinuousPath.exitTime_le_iff_mem_hitsSetBy (e '' U) (e.isOpen_image.mpr hU)]
  apply not_congr
  change (∃ r : Iic t, e.symm (q (c * r)) ∉ U) ↔
    ∃ r : Iic (c * t), q r ∉ e '' U
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨⟨c * r, mul_le_mul_right r.property c⟩, fun h => hr ((hmem _).mpr h)⟩
  · rintro ⟨r, hr⟩
    refine ⟨⟨r / c, (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using r.property)⟩, ?_⟩
    have htime : c * (r / c) = (r : ℝ≥0) := by field_simp
    rw [htime]
    exact fun h => hr ((hmem _).mp h)

/-- Every-start survival identity for the mapped continuous-path laws. -/
theorem unitSurvival_rescale_eq {d : ℕ}
    (K J : Kernel (Vec d) (ContinuousPath (Vec d)))
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (hJ : ∀ x, J x = (K (e x)).map (ContinuousPath.rescale e.symm c))
    {U : Set (Vec d)} (hU : IsOpen U) (t : ℝ) (x : Vec d) :
    (J.map LifetimePath.ofContinuousPath) x
        {q | ENNReal.ofReal t < LifetimePath.exitTime U q} =
      (K.map LifetimePath.ofContinuousPath) (e x)
        {q | ENNReal.ofReal ((c : ℝ) * t) < LifetimePath.exitTime (e '' U) q} := by
  rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath, hJ x]
  rw [Measure.map_apply LifetimePath.measurable_ofContinuousPath
      (measurableSet_lt measurable_const (LifetimePath.measurable_exitTime U hU)),
    Measure.map_apply LifetimePath.measurable_ofContinuousPath
      (measurableSet_lt measurable_const
        (LifetimePath.measurable_exitTime (e '' U) (e.isOpen_image.mpr hU)))]
  rw [Measure.map_apply (ContinuousPath.measurable_rescale e.symm c)
    ((measurableSet_lt measurable_const (LifetimePath.measurable_exitTime U hU)).preimage
      LifetimePath.measurable_ofContinuousPath)]
  congr 1
  ext q
  simp only [mem_preimage, mem_setOf_eq, LifetimePath.exitTime_ofContinuousPath]
  have hcoe : ENNReal.ofReal ((c : ℝ) * t) = ((c * Real.toNNReal t : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul c.coe_nonneg]
    simp only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
    rfl
  rw [hcoe]
  exact lt_exitTime_rescale_iff e c hc hU (Real.toNNReal t) q

/-- Density of the original actual law suffices for lower semicontinuity of
occupation under any positive affine/time transport. No density Jacobian is
needed: transport survival at time c*t and use the same two Fatou steps. -/
theorem discountedUnitOccupation_lowerSemicontinuousOn_of_rescaled_density {d : ℕ}
    (K J : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel J]
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (hJ : ∀ x, J x = (K (e x)).map (ContinuousPath.rescale e.symm c))
    {b : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (hdensity : HasContinuousKilledDensityOn b (K.map LifetimePath.ofContinuousPath) (e '' U))
    (s : ℝ) :
    LowerSemicontinuousOn
      (discountedUnitOccupation (J.map LifetimePath.ofContinuousPath) U s) U := by
  letI : IsMarkovKernel (J.map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  obtain ⟨p, hp, hpc⟩ := hdensity
  apply lowerSemicontinuousOn_of_seq_le_liminf
  intro x hx xs hxs hlim
  let F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (Real.exp (-t / s)) *
    (J.map LifetimePath.ofContinuousPath) (xs n)
      {q | ENNReal.ofReal t < LifetimePath.exitTime U q}
  have hF (n : ℕ) : Measurable (F n) :=
    (Real.measurable_exp.comp (measurable_id.neg.div_const s)).ennreal_ofReal.mul
      (measurable_unitSurvival _ hU (xs n))
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), liminf (fun n => F n t) atTop := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp only [F]
      simp_rw [unitSurvival_rescale_eq K J e c hc hJ hU]
      exact weighted_unitSurvival_le_liminf_of_density (e.isOpen_image.mpr hU) hp hpc
        (mul_pos (by exact_mod_cast hc) ht) ⟨x, hx, rfl⟩
        (fun n => ⟨xs n, hxs n, rfl⟩) (e.continuous.tendsto x |>.comp hlim) _
        ENNReal.ofReal_ne_top
    _ ≤ _ := lintegral_liminf_le hF

end SubdiffusiveProcess.Section10
