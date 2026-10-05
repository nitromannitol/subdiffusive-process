module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicLogPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserCubeCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLocalBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction

@[expose] public section

/-! # Essential logarithmic energy for bounded H¹ weak solutions -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Logarithmic energy on the half of a unit cube is uniform in the
positive regularization and the weak-harmonic function. -/
theorem exists_essential_harmonic_log_energy (d : ℕ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : H1Function (centeredAxisCube z 1), IsWeaklyHarmonicOn a (centeredAxisCube z 1) h →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 0 ≤ h.toFun x ∧ h.toFun x ≤ 1) →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ u : H1Function (centeredAxisCube z (1 / 2)),
        (∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 2)),
          u.toFun x = Real.log (h.toFun x + epsilon)) ∧
        (∫ x in centeredAxisCube z (1 / 2), vecNormSq (u.grad x)) ≤ E := by
  refine ⟨64 * (d : ℝ) * 256 ^ 2 + 1, by positivity, ?_⟩
  intro a z hab ha h hh hh0 epsilon hepsilon
  let W := centeredAxisCube z (3 / 4)
  let B := centeredAxisCube z (1 / 2)
  have hW := isOpenBoundedConvexDomain_axisCube (fun i => z i - (3 / 4) / 2) (3 / 4 : ℝ)
  let : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  have hBW : B ⊆ W := centeredAxisCube_mono (by norm_num)
  have hWQ : W ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  obtain ⟨eta, heta, hetac, hetasub, hetaRange, hetaOne, hetaGrad⟩ :=
    exists_moser_cube_cutoff z (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  let hWfun : H1Function W := h.restrict hW.isOpen hWQ
  let v := hWfun.addConst epsilon
  have hv : IsWeaklyHarmonicOn a W v := by
    have hweak := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      (isOpen_axisCube _ _) hW.isOpen hWQ hh
    intro phi
    simpa only [v, hWfun, H1Function.grad_addConst] using! hweak phi
  have h01 := hh0.filter_mono (ae_mono (Measure.restrict_mono hWQ le_rfl))
  have hvb : ∀ᵐ x ∂volume.restrict W, epsilon ≤ v.toFun x ∧ |v.toFun x| ≤ 1 + epsilon := by
    filter_upwards [h01] with x hx
    change epsilon ≤ h.toFun x + epsilon ∧ |h.toFun x + epsilon| ≤ 1 + epsilon
    rw [abs_of_nonneg (by linarith : 0 ≤ h.toFun x + epsilon)]
    constructor <;> linarith
  obtain ⟨w, hwf, _, henergy⟩ := interior_log_caccioppoli_cutoff hW
    (by norm_num : (0 : ℝ) < 1 / 4) (ha.mono_set hWQ)
    (hab.filter_mono (ae_mono (Measure.restrict_mono hWQ le_rfl))) v hv
    hepsilon (by positivity : 0 ≤ 1 + epsilon) hvb heta hetac hetasub hetaRange
  have hw : ∀ᵐ x ∂volume.restrict W, w.toFun x = Real.log (h.toFun x + epsilon) := by
    filter_upwards with x
    rw [hwf]
    rfl
  let u : H1Function B := w.restrict (isOpen_axisCube _ _) hBW
  refine ⟨u, hw.filter_mono (ae_mono (Measure.restrict_mono hBW le_rfl)), ?_⟩
  change (∫ x in B, vecNormSq (u.grad x)) ≤ 64 * (d : ℝ) * 256 ^ 2 + 1
  have hcutint : IntegrableOn (fun x => vecNormSq (euclideanGradient eta x)) W :=
    ((continuous_vecNormSq_euclideanGradient_of_contDiff heta).integrable_of_hasCompactSupport
      (hasCompactSupport_vecNormSq_euclideanGradient hetac)).restrict
  have hcutbound : (∫ x in W, vecNormSq (euclideanGradient eta x)) ≤
      (d : ℝ) * 256 ^ 2 := by
    have hi := integral_mono_ae hcutint (integrable_const ((d : ℝ) * 256 ^ 2))
      (Eventually.of_forall fun x => show vecNormSq (euclideanGradient eta x) ≤ (d : ℝ) * 256 ^ 2 by
        norm_num at hetaGrad ⊢
        exact hetaGrad x)
    rw [integral_const, smul_eq_mul] at hi
    have hvolume : (volume W).toReal ≤ 1 := by
      change (volume (centeredAxisCube z (3 / 4))).toReal ≤ 1
      rw [SubdiffusiveProcess.Section9.volume_centeredAxisCube_toReal z (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hi
    exact hi.trans ((mul_le_mul_of_nonneg_right hvolume
      (by positivity : 0 ≤ (d : ℝ) * 256 ^ 2)).trans_eq (one_mul _))
  have heta2compact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [Pi.mul_apply, pow_two] using! hetac.mul_right (f' := eta)
  have henergyInt : IntegrableOn (fun x => eta x ^ 2 * vecNormSq (w.grad x)) W :=
    WeakPoissonEquationOn.integrableOn_mul_left_of_continuous_hasCompactSupport
      (heta.continuous.pow 2) heta2compact (integrableOn_vecNormSq_h1Grad w)
  have hinner : (∫ x in B, vecNormSq (u.grad x)) ≤
      ∫ x in W, eta x ^ 2 * vecNormSq (w.grad x) := by
    calc
      (∫ x in B, vecNormSq (u.grad x)) = ∫ x in B, eta x ^ 2 * vecNormSq (w.grad x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (isOpen_axisCube _ _).measurableSet] with x hx
        change vecNormSq (w.grad x) = _
        rw [hetaOne x hx, one_pow, one_mul]
      _ ≤ _ := setIntegral_mono_set henergyInt
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
        (Eventually.of_forall hBW)
  rw [show (4 * (4 : ℝ) / (1 / 4)) = 64 by norm_num] at henergy
  have hfinal := hinner.trans (henergy.trans (mul_le_mul_of_nonneg_left hcutbound (by norm_num)))
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
