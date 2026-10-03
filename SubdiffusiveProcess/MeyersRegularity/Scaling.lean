module

public import SubdiffusiveProcess.MeyersRegularity.AffineH1
public import SubdiffusiveProcess.MeyersRegularity.UnitScalar
public import SubdiffusiveProcess.MeyersRegularity.BallGeometry
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Book.Ch01.Theorems.NormScaling

@[expose] public section

/-! Interior Meyers regularity: Scaling. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators Pointwise

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem scaling_cancel {d : ℕ} {p R : ℝ} (hR : 0 < R) :
    R^((d : ℝ)/p)*R^(-(d : ℝ)/p) = 1 := by
  rw [← Real.rpow_add hR]
  convert Real.rpow_zero R using 1 <;> ring

theorem scaling_value_factor {d : ℕ} {p R : ℝ} (hR : 0 < R) :
    R^((d : ℝ)/p)*(R⁻¹*R^(-(d : ℝ)/2)) = R^((d : ℝ)*(1/p-1/2)-1) := by
  have hi : R⁻¹ = R^(-1 : ℝ) := by rw [Real.rpow_neg hR.le, Real.rpow_one]
  rw [hi]
  calc
    R^((d : ℝ)/p)*(R^(-1 : ℝ)*R^(-(d : ℝ)/2)) =
        (R^((d : ℝ)/p)*R^(-1 : ℝ))*R^(-(d : ℝ)/2) := by ring
    _ = R^((d : ℝ)/p+(-1)+(-(d : ℝ)/2)) := by rw [← Real.rpow_add hR, ← Real.rpow_add hR]
    _ = _ := by congr 1; ring

theorem scaling_source_factor {d : ℕ} {p R : ℝ} (hR : 0 < R) :
    R^((d : ℝ)/p)*(R*R^(-(d : ℝ)/p)) = R := by
  calc
    _ = R*(R^((d : ℝ)/p)*R^(-(d : ℝ)/p)) := by ring
    _ = R := by rw [scaling_cancel hR, mul_one]

def gradientMagnitude {d : ℕ} {U : Set (Vec d)} (u : H1Function U) : Vec d → ℝ :=
  fun x => Real.sqrt (∑ i : Fin d, (u.grad x i)^2)

theorem gradientMagnitude_eq_norm {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    gradientMagnitude u = fun x => ‖gradientField u x‖ := by
  funext x
  exact (norm_gradientField u x).symm

theorem gradientMagnitude_aestronglyMeasurable {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    AEStronglyMeasurable (gradientMagnitude u) (volume.restrict U) := by
  rw [gradientMagnitude_eq_norm]
  exact (gradientField_memLp_two u).norm.aestronglyMeasurable

theorem meyersEstimate_of_unit {d : ℕ} (hd : 2 ≤ d) {p epsilon C : ℝ}
    (hp : 2 ≤ p) (h : UnitMeyersEstimate d p epsilon C) :
    Meyers.MeyersEstimate d p epsilon C := by
  intro x0 R hR a hsrc ha hclose hh u heq
  have hp0 : 0 < p := by linarith only [hp]
  have hB3 : Meyers.eBall x0 (3*R) = translateSet x0 (R • unitBall d 3) :=
    eBall_eq_translate_smul x0 hR (by norm_num)
  have hB2 : Meyers.eBall x0 (2*R) = translateSet x0 (R • unitBall d 2) :=
    eBall_eq_translate_smul x0 hR (by norm_num)
  have hB1 : Meyers.eBall x0 R = translateSet x0 (R • unitBall d 1) := by
    simpa only [one_mul] using eBall_eq_translate_smul x0 hR (by norm_num : (0 : ℝ) < 1)
  let uA : H1Function (translateSet x0 (R • unitBall d 3)) := hB3 ▸ u
  have huAf : uA.toFun = u.toFun := cast_h1_toFun hB3 u
  have huAg : uA.grad = u.grad := cast_h1_grad hB3 u
  have heqA : ScalarEquation a hsrc uA := scalarEquation_cast hB3 u a hsrc heq
  let w := affinePullback hR x0 uA
  let a0 : Vec d → ℝ := fun x => a (R • x+x0)
  let h0 : Vec d → ℝ := fun x => R*hsrc (R • x+x0)
  have hwf : w.toFun = fun x => R⁻¹*u.toFun (R • x+x0) := by
    funext x
    rw [affinePullback_toFun, huAf]
  have hwg : w.grad = fun x => u.grad (R • x+x0) := by
    funext x
    rw [affinePullback_grad, huAg]
  have hwmag : gradientMagnitude w = fun x => gradientMagnitude u (R • x+x0) := by
    funext x
    change Real.sqrt (∑ i : Fin d, (w.grad x i)^2) = _
    rw [hwg]
    rfl
  have haA : AEMeasurable a (volume.restrict (translateSet x0 (R • unitBall d 3))) := by
    rw [← hB3]
    exact ha
  have hcloseA : ∀ᵐ x ∂volume.restrict (translateSet x0 (R • unitBall d 3)), |a x-1| ≤ epsilon := by
    rw [← hB3]
    exact hclose
  have hhA : MemLp hsrc (ENNReal.ofReal p) (volume.restrict (translateSet x0 (R • unitBall d 3))) := by
    rw [← hB3]
    exact hh
  have hqmp := quasiMeasurePreserving_affine hR x0 (unitBall d 3)
  have ha0 : AEMeasurable a0 (volume.restrict (unitBall d 3)) := haA.comp_quasiMeasurePreserving hqmp
  have hclose0 : ∀ᵐ x ∂volume.restrict (unitBall d 3), |a0 x-1| ≤ epsilon := hqmp.ae hcloseA
  have hh0 : MemLp h0 (ENNReal.ofReal p) (volume.restrict (unitBall d 3)) :=
    (memLp_comp_affine hR x0 (unitBall d 3) hhA).const_mul R
  have heq0 : ScalarEquation a0 h0 w := scalarEquation_affinePullback hR x0 uA a hsrc heqA
  obtain ⟨hmemw, hnormw⟩ := h a0 h0 ha0 hclose0 hh0 w heq0
  change MemLp (gradientMagnitude w) (ENNReal.ofReal p) (volume.restrict (unitBall d 1)) at hmemw
  change (eLpNorm (gradientMagnitude w) (ENNReal.ofReal p) (volume.restrict (unitBall d 1))).toReal ≤
    C*((eLpNorm w.toFun 2 (volume.restrict (unitBall d 2))).toReal+
      (eLpNorm h0 (ENNReal.ofReal p) (volume.restrict (unitBall d 2))).toReal) at hnormw
  have h13 : Meyers.eBall x0 R ⊆ Meyers.eBall x0 (3*R) :=
    Meyers.eBall_mono x0 hR.le (by linarith only [hR])
  have h23 : Meyers.eBall x0 (2*R) ⊆ Meyers.eBall x0 (3*R) :=
    Meyers.eBall_mono x0 (by positivity) (by linarith only [hR])
  have hm13 : volume.restrict (Meyers.eBall x0 R) ≤ volume.restrict (Meyers.eBall x0 (3*R)) :=
    Measure.restrict_mono h13 le_rfl
  have hm23 : volume.restrict (Meyers.eBall x0 (2*R)) ≤ volume.restrict (Meyers.eBall x0 (3*R)) :=
    Measure.restrict_mono h23 le_rfl
  have hmagAES : AEStronglyMeasurable (gradientMagnitude u) (volume.restrict (Meyers.eBall x0 R)) :=
    (gradientMagnitude_aestronglyMeasurable u).mono_measure hm13
  have hmagAES' : AEStronglyMeasurable (gradientMagnitude u)
      (volume.restrict (translateSet x0 (R • unitBall d 1))) := by rw [← hB1]; exact hmagAES
  have hmem : MemLp (gradientMagnitude u) (ENNReal.ofReal p) (volume.restrict (Meyers.eBall x0 R)) := by
    rw [hB1]
    apply (memLp_comp_affine_iff hR x0 (unitBall d 1) hmagAES').mp
    rw [← hwmag]
    exact hmemw
  have hgradnorm : (eLpNorm (gradientMagnitude w) (ENNReal.ofReal p)
      (volume.restrict (unitBall d 1))).toReal =
      R^(-(d : ℝ)/p)*(eLpNorm (gradientMagnitude u) (ENNReal.ofReal p)
        (volume.restrict (Meyers.eBall x0 R))).toReal := by
    rw [hwmag]
    simpa only [← hB1] using norm_comp_affine hR hp0 x0 (unitBall d 1) hmagAES'
  have huAES : AEStronglyMeasurable u.toFun (volume.restrict (Meyers.eBall x0 (2*R))) :=
    u.memL2.aestronglyMeasurable.mono_measure hm23
  have huAES' : AEStronglyMeasurable u.toFun (volume.restrict (translateSet x0 (R • unitBall d 2))) := by
    rw [← hB2]
    exact huAES
  have hucomp := norm_comp_affine (p := 2) hR (by norm_num) x0 (unitBall d 2) huAES'
  norm_num only [ENNReal.ofReal_ofNat] at hucomp
  have hvaluenorm : (eLpNorm w.toFun 2 (volume.restrict (unitBall d 2))).toReal =
      R⁻¹*R^(-(d : ℝ)/2)*(eLpNorm u.toFun 2 (volume.restrict (Meyers.eBall x0 (2*R)))).toReal := by
    rw [hwf, norm_const_mul (inv_nonneg.mpr hR.le), hucomp, ← hB2]
    ring
  have hhAES' : AEStronglyMeasurable hsrc (volume.restrict (translateSet x0 (R • unitBall d 2))) := by
    rw [← hB2]
    exact hh.aestronglyMeasurable.mono_measure hm23
  have hhcomp := norm_comp_affine hR hp0 x0 (unitBall d 2) hhAES'
  have hsourcenorm : (eLpNorm h0 (ENNReal.ofReal p) (volume.restrict (unitBall d 2))).toReal =
      R*R^(-(d : ℝ)/p)*(eLpNorm hsrc (ENNReal.ofReal p)
        (volume.restrict (Meyers.eBall x0 (2*R)))).toReal := by
    change (eLpNorm (fun x => R*hsrc (R • x+x0)) _ _).toReal = _
    rw [norm_const_mul hR.le, hhcomp, ← hB2]
    ring
  rw [hgradnorm, hvaluenorm, hsourcenorm] at hnormw
  refine ⟨hmem, ?_⟩
  change (eLpNorm (gradientMagnitude u) (ENNReal.ofReal p) (volume.restrict (Meyers.eBall x0 R))).toReal ≤ _
  calc
    (eLpNorm (gradientMagnitude u) (ENNReal.ofReal p) (volume.restrict (Meyers.eBall x0 R))).toReal =
        R^((d : ℝ)/p)*(R^(-(d : ℝ)/p)*(eLpNorm (gradientMagnitude u) (ENNReal.ofReal p)
          (volume.restrict (Meyers.eBall x0 R))).toReal) := by
      rw [← mul_assoc, scaling_cancel hR, one_mul]
    _ ≤ R^((d : ℝ)/p)*
        (C*(R⁻¹*R^(-(d : ℝ)/2)*(eLpNorm u.toFun 2 (volume.restrict (Meyers.eBall x0 (2*R)))).toReal+
          R*R^(-(d : ℝ)/p)*(eLpNorm hsrc (ENNReal.ofReal p)
            (volume.restrict (Meyers.eBall x0 (2*R)))).toReal)) :=
      mul_le_mul_of_nonneg_left hnormw (Real.rpow_nonneg hR.le _)
    _ = C*((R^((d : ℝ)/p)*(R⁻¹*R^(-(d : ℝ)/2)))*
        (eLpNorm u.toFun 2 (volume.restrict (Meyers.eBall x0 (2*R)))).toReal+
        (R^((d : ℝ)/p)*(R*R^(-(d : ℝ)/p)))*
          (eLpNorm hsrc (ENNReal.ofReal p) (volume.restrict (Meyers.eBall x0 (2*R)))).toReal) := by ring
    _ = _ := by rw [scaling_value_factor hR, scaling_source_factor hR]


end SubdiffusiveProcess.MeyersRegularity
