import SubdiffusiveProcess.MeyersRegularity.Basic
import Homogenization.Sobolev.W1p.Dilation
import Homogenization.Sobolev.H1.Translation

/-! Measure and norm transport under a positive scalar dilation and translation. -/

open MeasureTheory Filter Set Homogenization
open scoped ENNReal NNReal Topology Pointwise

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

/-- The affine coordinate change is nonsingular on the corresponding restricted measures. -/
theorem quasiMeasurePreserving_affine {d : ℕ} {R : ℝ} (hR : 0 < R)
    (z : Vec d) (U : Set (Vec d)) :
    Measure.QuasiMeasurePreserving (fun x => R • x+z) (volume.restrict U)
      (volume.restrict (translateSet z (R • U))) := by
  have hscale : Measure.QuasiMeasurePreserving (fun x : Vec d => R • x)
      (volume.restrict U) (volume.restrict (R • U)) := by
    refine ⟨measurable_const_smul R, ?_⟩
    rw [map_smul_volume_restrict hR U]
    exact Measure.smul_absolutelyContinuous
  exact (measurePreserving_addRight_restrict_translateSet z (R • U)).quasiMeasurePreserving.comp hscale

/-- Pull back finite norm data through the affine coordinate change. -/
theorem memLp_comp_affine {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) (U : Set (Vec d))
    {f : Vec d → ℝ} {q : ℝ≥0∞}
    (hf : MemLp f q (volume.restrict (translateSet z (R • U)))) :
    MemLp (fun x => f (R • x+z)) q (volume.restrict U) := by
  have ht := hf.comp_measurePreserving (measurePreserving_addRight_restrict_translateSet z (R • U))
  have hm : MemLp (fun y => f (y+z)) q
      (Measure.map (fun x : Vec d => R • x) (volume.restrict U)) := by
    rw [map_smul_volume_restrict hR U]
    exact ht.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (measurable_const_smul R).aemeasurable

/-- Exact ENNReal norm transport, also allowing zero and infinite exponents. -/
theorem eLpNorm_comp_affine {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) (U : Set (Vec d))
    {f : Vec d → ℝ} (q : ℝ≥0∞)
    (hf : AEStronglyMeasurable f (volume.restrict (translateSet z (R • U)))) :
    eLpNorm (fun x => f (R • x+z)) q (volume.restrict U) =
      (ENNReal.ofReal ((R^d)⁻¹))^((1/q).toReal) *
        eLpNorm f q (volume.restrict (translateSet z (R • U))) := by
  have htr := measurePreserving_addRight_restrict_translateSet z (R • U)
  have ht : AEStronglyMeasurable (fun y => f (y+z)) (volume.restrict (R • U)) :=
    hf.comp_measurePreserving htr
  have hm : AEStronglyMeasurable (fun y => f (y+z))
      (Measure.map (fun x : Vec d => R • x) (volume.restrict U)) := by
    rw [map_smul_volume_restrict hR U]
    exact ht.mono_ac Measure.smul_absolutelyContinuous
  have hc0 : ENNReal.ofReal ((R^d)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have he := eLpNorm_map_measure (p := q) hm (measurable_const_smul R).aemeasurable
  rw [map_smul_volume_restrict hR U, eLpNorm_smul_measure_of_ne_zero hc0,
    smul_eq_mul] at he
  have hetr : eLpNorm (fun y => f (y+z)) q (volume.restrict (R • U)) =
      eLpNorm f q (volume.restrict (translateSet z (R • U))) := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := q) hf htr
  rw [hetr] at he
  exact he.symm

/-- Exact real finite-exponent norm factor for the affine coordinate change. -/
theorem norm_comp_affine {d : ℕ} {R p : ℝ} (hR : 0 < R) (hp : 0 < p)
    (z : Vec d) (U : Set (Vec d)) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (translateSet z (R • U)))) :
    (eLpNorm (fun x => f (R • x+z)) (ENNReal.ofReal p) (volume.restrict U)).toReal =
      R^(-(d : ℝ)/p)*(eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (translateSet z (R • U)))).toReal := by
  rw [eLpNorm_comp_affine hR z U (ENNReal.ofReal p) hf, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity : 0 ≤ (R^d)⁻¹)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp.le]
  have hfactor : ((R^d)⁻¹)^(1/p) = R^(-(d : ℝ)/p) := by
    rw [Real.inv_rpow (pow_nonneg hR.le _), ← Real.rpow_neg (pow_nonneg hR.le _),
      ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hfactor]

/-- Membership is equivalent under the invertible affine coordinate change. -/
theorem memLp_comp_affine_iff {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) (U : Set (Vec d))
    {f : Vec d → ℝ} {q : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (volume.restrict (translateSet z (R • U)))) :
    MemLp (fun x => f (R • x+z)) q (volume.restrict U) ↔
      MemLp f q (volume.restrict (translateSet z (R • U))) := by
  constructor
  · intro hcomp
    refine ⟨hf, ?_⟩
    have he := eLpNorm_comp_affine hR z U q hf
    have hc : (ENNReal.ofReal ((R^d)⁻¹))^((1/q).toReal) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top).ne'
    apply ENNReal.lt_top_of_mul_ne_top_right _ hc
    rw [← he]
    exact hcomp.eLpNorm_ne_top
  · exact memLp_comp_affine hR z U

theorem norm_const_mul {α : Type*} [MeasurableSpace α] {c : ℝ} (hc : 0 ≤ c)
    (f : α → ℝ) (q : ℝ≥0∞) (μ : Measure α) :
    (eLpNorm (fun x => c*f x) q μ).toReal = c*(eLpNorm f q μ).toReal := by
  change (eLpNorm (c • f) q μ).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal hc,
    ENNReal.toReal_ofReal hc]

end SubdiffusiveProcess.MeyersRegularity
