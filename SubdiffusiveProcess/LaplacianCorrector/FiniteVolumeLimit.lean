import SubdiffusiveProcess.LaplacianCorrector.Dilation
import SubdiffusiveProcess.LaplacianCorrector.WindowMeasurability

/-! # Exhaustion of every finite layer window

The law-preserving shift sends an arbitrary window to a suffix starting at
layer one. Dilation and weak-solution uniqueness identify the expected energy
with that of the canonical suffix corrector on the next larger cube.
-/

open MeasureTheory Filter Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.LaplacianCorrector

/-- Shift and dilation identify the expected energy of any Dirichlet solution. -/
theorem integral_windowDirichletEnergy_eq {d : ℕ} [NeZero d]
    (M : Model d) (a h : ℕ) (p : Vec d) (hh : 0 < h) (K : ℕ)
    (u : Sample d → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hu : ∀ omega, IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d (K : ℤ))) (u omega)
      (fun x => -windowMultiplier M a h omega x • p)) :
    (∫ omega, cubeAverage (originCube d (K : ℤ))
      (fun x => vecNormSq ((u omega).toH1Function.grad x)) ∂M.P.toMeasure) =
    ∫ omega, oneStepDirichletCorrectorEnergy M a h p
      (originCube d ((K : ℤ) + 1)) omega hh ∂M.P.toMeasure := by
  let E := fun omega => cubeAverage (originCube d (K : ℤ))
    (fun x => vecNormSq ((u omega).toH1Function.grad x))
  have hE : Measurable E := by
    have hm := (measurable_windowDirichletGradL2 M a h p _ u hu).norm.pow_const 2
    have heq : E = fun omega => (cubeVolume (originCube d (K : ℤ)))⁻¹ *
        ‖(u omega).toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
      funext omega
      exact cubeAverage_grad_sq_eq _ _
    rw [heq]
    exact measurable_const.mul hm
  have hcomp := integral_comp_eq_of_map_eq measurable_shiftSample
    (measurePreserving_shiftSample M).map_eq E hE.aestronglyMeasurable
  change (∫ omega, E omega ∂M.P.toMeasure) = _
  rw [← hcomp]
  apply integral_congr_ae
  filter_upwards with omega
  let v := dilateZeroTrace (by norm_num : (0 : ℝ) < 3)
    (openCubeSet_originCube_succ (K : ℤ)) (u (shiftSample omega))
  have hv : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d ((K : ℤ) + 1))) v
      (fun x => -oneStepMultiplierAt M a h x omega • p) := by
    have hdilate := IsZeroTraceDirichletRhsWeakSolution.dilate_identity
      (by norm_num : (0 : ℝ) < 3) (openCubeSet_originCube_succ (K : ℤ))
      (hu (shiftSample omega))
    simpa only [windowMultiplier_shiftSample M a h hh, smul_smul,
      mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul, v] using hdilate
  have hgrad := dirichlet_grad_eq_of_same_rhs _ hv
    (oneStepTriadicDirichletSolution_isWeakSolution M a h p _ omega hh)
  calc
    E (shiftSample omega) = cubeAverage (originCube d ((K : ℤ) + 1))
        (fun x => vecNormSq (v.toH1Function.grad x)) := by
      simpa only [v, dilateZeroTrace_grad, E] using
        (cubeAverage_succ_pullback (K : ℤ)
          (fun x => vecNormSq ((u (shiftSample omega)).toH1Function.grad x))).symm
    _ = oneStepDirichletCorrectorEnergy M a h p _ omega hh := by
      rw [cubeAverage_grad_sq_eq, hgrad]
      rfl

/-- The positive Neumann datum is the canonical datum for the vector `-p`. -/
theorem integral_windowNeumannEnergy_eq {d : ℕ} [NeZero d]
    (M : Model d) (a h : ℕ) (p : Vec d) (hh : 0 < h) (K : ℕ)
    (u : Sample d → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hu : ∀ omega, IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d (K : ℤ))) (u omega)
      (fun x => windowMultiplier M a h omega x • p)) :
    (∫ omega, cubeAverage (originCube d (K : ℤ))
      (fun x => vecNormSq ((u omega).toH1Function.grad x)) ∂M.P.toMeasure) =
    ∫ omega, oneStepNeumannCorrectorEnergy M a h (-p)
      (originCube d ((K : ℤ) + 1)) omega hh ∂M.P.toMeasure := by
  let E := fun omega => cubeAverage (originCube d (K : ℤ))
    (fun x => vecNormSq ((u omega).toH1Function.grad x))
  have hE : Measurable E := by
    have hm := (measurable_windowNeumannGradL2 M a h p _ u hu).norm.pow_const 2
    have heq : E = fun omega => (cubeVolume (originCube d (K : ℤ)))⁻¹ *
        ‖(u omega).gradToHilbertVectorL2‖ ^ 2 := by
      funext omega
      exact cubeAverage_grad_sq_eq _ _
    rw [heq]
    exact measurable_const.mul hm
  have hcomp := integral_comp_eq_of_map_eq measurable_shiftSample
    (measurePreserving_shiftSample M).map_eq E hE.aestronglyMeasurable
  change (∫ omega, E omega ∂M.P.toMeasure) = _
  rw [← hcomp]
  apply integral_congr_ae
  filter_upwards with omega
  let v := dilateMeanZero (by norm_num : (0 : ℝ) < 3)
    (openCubeSet_originCube_succ (K : ℤ)) (u (shiftSample omega))
  have hv : IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d ((K : ℤ) + 1))) v
      (fun x => -oneStepMultiplierAt M a h x omega • (-p)) := by
    have hdilate := IsMeanZeroNeumannRhsWeakSolution.dilate_identity
      (by norm_num : (0 : ℝ) < 3) (openCubeSet_originCube_succ (K : ℤ))
      (hu (shiftSample omega))
    simpa only [windowMultiplier_shiftSample M a h hh, smul_smul,
      mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul,
      smul_neg, neg_smul, neg_neg, v] using hdilate
  have hgrad := neumann_grad_eq_of_same_rhs _ hv
    (oneStepTriadicNeumannSolution_isWeakSolution M a h (-p) _ omega hh)
  calc
    E (shiftSample omega) = cubeAverage (originCube d ((K : ℤ) + 1))
        (fun x => vecNormSq (v.toH1Function.grad x)) := by
      simpa only [v, dilateMeanZero_grad, E] using
        (cubeAverage_succ_pullback (K : ℤ)
          (fun x => vecNormSq ((u (shiftSample omega)).toH1Function.grad x))).symm
    _ = oneStepNeumannCorrectorEnergy M a h (-p) _ omega hh := by
      rw [cubeAverage_grad_sq_eq]
      change _ = (cubeVolume (originCube d ((K : ℤ) + 1)))⁻¹ * _
      rw [show v.toH1Function.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 from rfl,
        hgrad]

/-- Expected Dirichlet energy exhausts the stationary projected energy for
any finite layer window, without a measurability assumption on the solutions. -/
theorem tendsto_integral_windowDirichletEnergy {d : ℕ} [NeZero d]
    (M : Model d) (a h : ℕ) (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (w : (K : ℕ) → Sample d → H10Function (openCubeSet (originCube d (K : ℤ))))
    (hw : ∀ (K : ℕ) omega, IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d (K : ℤ))) (w K omega)
      (fun x => -windowMultiplier M a h omega x • p)) :
    Tendsto (fun K : ℕ => ∫ omega, cubeAverage (originCube d (K : ℤ))
      (fun x => vecNormSq ((w K omega).toH1Function.grad x)) ∂M.P.toMeasure)
      atTop (𝓝 (oneStepProjectedEnergy M a h p hh)) := by
  have hlim := (tendsto_integral_oneStepCorrectorEnergies_originCube M a h p hh hp).1.comp
    (tendsto_add_atTop_nat 1)
  have heq : (fun K : ℕ => ∫ omega, cubeAverage (originCube d (K : ℤ))
      (fun x => vecNormSq ((w K omega).toH1Function.grad x)) ∂M.P.toMeasure) =
      fun K : ℕ => ∫ omega, oneStepDirichletCorrectorEnergy M a h p
        (originCube d ((K + 1 : ℕ) : ℤ)) omega hh ∂M.P.toMeasure := by
    funext K
    simpa only [Nat.cast_add, Nat.cast_one] using
      integral_windowDirichletEnergy_eq M a h p hh K (w K) (hw K)
  rw [heq]
  exact hlim

theorem projectedEnergy_neg_eq_of_unit {d : ℕ} (M : Model d) (a h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    oneStepProjectedEnergy M a h (-p) hh = oneStepProjectedEnergy M a h p hh := by
  have hpneg : vecNormSq (-p) = 1 := by
    simpa only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg] using hp
  rw [oneStepProjectedEnergy_eq_suffixVariance_div_dimension_unit M a h (-p) hh hpneg,
    oneStepProjectedEnergy_eq_suffixVariance_div_dimension_unit M a h p hh hp]

/-- Expected positive-datum Neumann energy exhausts the stationary energy. -/
theorem tendsto_integral_windowNeumannEnergy {d : ℕ} [NeZero d]
    (M : Model d) (a h : ℕ) (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (w : (K : ℕ) → Sample d → H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ))))
    (hw : ∀ (K : ℕ) omega, IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d (K : ℤ))) (w K omega)
      (fun x => windowMultiplier M a h omega x • p)) :
    Tendsto (fun K : ℕ => ∫ omega, cubeAverage (originCube d (K : ℤ))
      (fun x => vecNormSq ((w K omega).toH1Function.grad x)) ∂M.P.toMeasure)
      atTop (𝓝 (oneStepProjectedEnergy M a h p hh)) := by
  have hpneg : vecNormSq (-p) = 1 := by simpa only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg] using hp
  have hlim := (tendsto_integral_oneStepCorrectorEnergies_originCube M a h (-p) hh hpneg).2.comp
    (tendsto_add_atTop_nat 1)
  have heq : (fun K : ℕ => ∫ omega, cubeAverage (originCube d (K : ℤ))
      (fun x => vecNormSq ((w K omega).toH1Function.grad x)) ∂M.P.toMeasure) =
      fun K : ℕ => ∫ omega, oneStepNeumannCorrectorEnergy M a h (-p)
        (originCube d ((K + 1 : ℕ) : ℤ)) omega hh ∂M.P.toMeasure := by
    funext K
    simpa only [Nat.cast_add, Nat.cast_one] using
      integral_windowNeumannEnergy_eq M a h p hh K (w K) (hw K)
  rw [heq]
  rw [projectedEnergy_neg_eq_of_unit M a h p hh hp] at hlim
  exact hlim

end SubdiffusiveProcess.LaplacianCorrector
