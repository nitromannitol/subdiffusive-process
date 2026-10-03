module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicLogPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserCubeCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLocalBoundedness

@[expose] public section

/-!
# Uniform logarithmic control on interior half-cubes

The regularized logarithm of a nonnegative harmonic function has a
dimensional gradient-energy bound on the half-cube. A half-measure lower
level set then anchors its square integral.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Logarithmic energy on the half of a unit cube is uniform in the
positive regularization and the weak-harmonic function. -/
theorem exists_harmonic_unit_log_energy (d : ℕ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ x ∈ centeredAxisCube z 1, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z 1) h →
      (∀ x ∈ centeredAxisCube z 1, 0 ≤ h x) →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ u : H1Function (centeredAxisCube z (1 / 2)),
        (∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 2)),
          u.toFun x = Real.log (h x + epsilon)) ∧
        (∫ x in centeredAxisCube z (1 / 2), vecNormSq (u.grad x)) ≤ E := by
  refine ⟨64 * (d : ℝ) * 256 ^ 2 + 1, by positivity, ?_⟩
  intro a z hab ha h hh hh0 epsilon hepsilon
  let W := centeredAxisCube z (3 / 4)
  let B := centeredAxisCube z (1 / 2)
  have hW := isOpenBoundedConvexDomain_axisCube (fun i => z i - (3 / 4) / 2) (3 / 4 : ℝ)
  letI : IsFiniteMeasure (volume.restrict W) := hW.isFiniteMeasure_restrict_volume
  have hBW : B ⊆ W := centeredAxisCube_mono (by norm_num)
  have hWQ : W ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  obtain ⟨eta, heta, hetac, hetasub, hetaRange, hetaOne, hetaGrad⟩ :=
    exists_moser_cube_cutoff z (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  obtain ⟨w, hw, henergy⟩ := interior_weakHarmonic_log_energy hW
    (closure_centeredAxisCube_subset (by norm_num : (3 / 4 : ℝ) < 1))
    (by norm_num : (0 : ℝ) < 1 / 4) (ha.mono_set hWQ)
    (show ∀ᵐ x ∂volume.restrict W, 1 / 4 ≤ a x ∧ a x ≤ 4 from by
      filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with x hx
      exact hab x (hWQ hx))
    hh hh0 hepsilon heta hetac hetasub hetaRange
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

/-- The logarithm is bounded on the fixed interval used to anchor it. -/
theorem harmonic_abs_log_le_log_two {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 2) :
    |Real.log t| ≤ Real.log 2 := by
  apply abs_le.mpr
  constructor
  · rw [← Real.log_inv]
    apply Real.log_le_log (by norm_num)
    simpa only [one_div] using ht0
  · exact Real.log_le_log (by linarith) ht1

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
