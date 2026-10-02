import SubdiffusiveProcess.MeyersRegularity.InteriorVector
import SubdiffusiveProcess.MeyersRegularity.ScalarLift
import SubdiffusiveProcess.MeyersRegularity.Caccioppoli

/-! Interior Meyers regularity: UnitScalar. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem exists_unit_meyers_estimate (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1/2 ∧ 0 < C ∧
      UnitMeyersEstimate d p epsilon C := by
  obtain ⟨epsilon, Cv, hepsilon, hepsilonhalf, hCv, hvector⟩ := exists_interior_vector_estimate d hd p hp
  obtain ⟨Cl, hCl, hlift⟩ := exists_scalar_divergence_lift d hd p hp
  obtain ⟨Ce, hCe, henergy⟩ := exists_caccioppoli_value_estimate d hd
  let μ2 := volume.restrict (unitBall d 2)
  letI : IsFiniteMeasure μ2 := isFiniteMeasure_restrict.mpr
    (unitBall_volume_lt_top d (by norm_num : (0 : ℝ) < 2)).ne
  let V := (μ2 univ ^ (1/2-1/p)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let C := Cv*(Ce*(1+V)+Cl)+1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨epsilon, C, hepsilon, hepsilonhalf, hC, ?_⟩
  intro a h ha hclose hh u heq
  have h23 : unitBall d 2 ⊆ unitBall d 3 := Meyers.eBall_mono 0 (by norm_num) (by norm_num)
  have hS3 : unitBall d (3/2) ⊆ unitBall d 3 := Meyers.eBall_mono 0 (by norm_num) (by norm_num)
  have hm23 : μ2 ≤ volume.restrict (unitBall d 3) := Measure.restrict_mono h23 le_rfl
  have hmS3 : volume.restrict (unitBall d (3/2)) ≤ volume.restrict (unitBall d 3) :=
    Measure.restrict_mono hS3 le_rfl
  have hh2 : MemLp h (ENNReal.ofReal p) μ2 := hh.mono_measure hm23
  have hpENN : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have h := ENNReal.ofReal_le_ofReal hp
    norm_num only [ENNReal.ofReal_ofNat] at h
    exact h
  have hh2two : MemLp h 2 μ2 := hh2.mono_exponent hpENN
  have hdown := two_norm_le_lp_norm hp hh2
  obtain ⟨H, hH, hHnorm, hHweak⟩ := hlift h hh2
  let us := u.restrict (Meyers.isOpen_eBall 0 (3/2)) hS3
  have hes : ScalarEquation a h us := scalarEquation_restrict (Meyers.isOpen_eBall 0 3)
    (Meyers.isOpen_eBall 0 (3/2)) hS3 a h u heq
  have hvec : VectorEquation a (fun x => -H x) us := by
    intro phi
    have hs := hes phi
    rw [hHweak phi, neg_neg] at hs
    simp only [vecDot_neg_left, integral_neg, neg_neg]
    exact hs
  have hHN : MemLp (hilbertifyVecField (fun x => -H x)) (ENNReal.ofReal p)
      (volume.restrict (unitBall d (3/2))) := by
    change MemLp (-hilbertifyVecField H) _ _
    exact hH.neg
  have hHNnorm : eLpNorm (hilbertifyVecField (fun x => -H x)) (ENNReal.ofReal p)
      (volume.restrict (unitBall d (3/2))) =
      eLpNorm (hilbertifyVecField H) (ENNReal.ofReal p) (volume.restrict (unitBall d (3/2))) := by
    change eLpNorm (-hilbertifyVecField H) _ _ = _
    exact eLpNorm_neg (hilbertifyVecField H) (ENNReal.ofReal p) (volume.restrict (unitBall d (3/2)))
  have hac : ∀ᵐ x ∂volume.restrict (unitBall d 3), |a x-1| ≤ 1/2 :=
    hclose.mono (fun x hx => hx.trans hepsilonhalf)
  have hgrad := henergy a h ha hac hh2two u heq
  obtain ⟨hmem, hnorm⟩ := hvector a (fun x => -H x)
    (ha.mono' (Measure.absolutelyContinuous_of_le hmS3))
    (hclose.filter_mono (ae_mono hmS3)) hHN us hvec
  have hnorm' : (eLpNorm (gradientField us) (ENNReal.ofReal p) (volume.restrict (unitBall d 1))).toReal ≤
      Cv*((eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal +
        (eLpNorm (hilbertifyVecField H) (ENNReal.ofReal p) (volume.restrict (unitBall d (3/2)))).toReal) := by
    simpa only [vectorDataSize, hHNnorm, gradientField, H1Function.restrict] using hnorm
  have hcombined : (eLpNorm (gradientField us) (ENNReal.ofReal p)
      (volume.restrict (unitBall d 1))).toReal ≤
      C*((eLpNorm u.toFun 2 μ2).toReal+(eLpNorm h (ENNReal.ofReal p) μ2).toReal) := by
    have hu0 : 0 ≤ (eLpNorm u.toFun 2 μ2).toReal := ENNReal.toReal_nonneg
    have hh0 : 0 ≤ (eLpNorm h (ENNReal.ofReal p) μ2).toReal := ENNReal.toReal_nonneg
    change (eLpNorm h 2 μ2).toReal ≤ (eLpNorm h (ENNReal.ofReal p) μ2).toReal*V at hdown
    change (eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal ≤
      Ce*((eLpNorm u.toFun 2 μ2).toReal+(eLpNorm h 2 μ2).toReal) at hgrad
    let S := (eLpNorm u.toFun 2 μ2).toReal+(eLpNorm h (ENNReal.ofReal p) μ2).toReal
    have hS : 0 ≤ S := add_nonneg hu0 hh0
    have hsum : (eLpNorm u.toFun 2 μ2).toReal+(eLpNorm h 2 μ2).toReal ≤ (1+V)*S := by
      calc
        _ ≤ (eLpNorm u.toFun 2 μ2).toReal+(eLpNorm h (ENNReal.ofReal p) μ2).toReal*V :=
          add_le_add le_rfl hdown
        _ ≤ _ := by dsimp only [S]; nlinarith only [hu0, hh0, mul_nonneg hV hu0]
    have hGe : (eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal ≤
        Ce*((1+V)*S) := hgrad.trans (mul_le_mul_of_nonneg_left hsum hCe.le)
    have hLe : (eLpNorm (hilbertifyVecField H) (ENNReal.ofReal p) (volume.restrict (unitBall d (3/2)))).toReal ≤ Cl*S :=
      hHnorm.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hu0) hCl.le)
    calc
      _ ≤ Cv*((eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal +
          (eLpNorm (hilbertifyVecField H) (ENNReal.ofReal p) (volume.restrict (unitBall d (3/2)))).toReal) := hnorm'
      _ ≤ Cv*(Ce*((1+V)*S)+Cl*S) := mul_le_mul_of_nonneg_left (add_le_add hGe hLe) hCv.le
      _ = (C-1)*S := by dsimp only [C]; ring
      _ ≤ C*S := by nlinarith only [hS]
  have hfield : gradientField us = gradientField u := rfl
  have hmag : (fun x => ‖gradientField us x‖) =
      (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i)^2)) := by
    funext x
    rw [hfield, norm_gradientField]
  constructor
  · rw [← hmag]
    exact hmem.norm
  · rw [← hmag, eLpNorm_norm]
    exact hcombined


end SubdiffusiveProcess.MeyersRegularity
