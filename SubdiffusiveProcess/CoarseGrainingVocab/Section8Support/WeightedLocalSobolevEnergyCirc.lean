module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyLocal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.OscillationPoincare
public import Homogenization.Besov.Poincare.HarmonicGradient.FullCirc

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped ENNReal
variable {d : ℕ} [NeZero d]

theorem h1Gradient_circPartialNorm_le_energy_of_scalarParent
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q))
    (r : ℝ) (hr : 0 < r) (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => u.grad x i) ≤
      (cubeBesovScaleWeight (-r) Q *
        ((geometricDiscount r 1)⁻¹ *
          Real.rpow
            (lambdaSq Q r (.finite 1)
              (publicCoeffField Q A))
            (-1 / 2 : ℝ))) *
        Real.sqrt (cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q A) u.grad)) := by
  let a := publicCoeffField Q A
  let energy := coefficientEnergyDensity a u.grad
  have hEll := publicCoeffField_isEllipticFieldOn_cubeSet Q A
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad x hx
  have henergy_int : IntegrableOn energy (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      (by
        rw [MemVectorL2, volumeMeasureOn,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
        exact u.grad_memVectorL2)
  have hgrad : CubeAverageGradientEnergyControl Q a u.grad energy := by
    simpa only [a, energy] using
      cubeAverageGradientEnergyControl_of_h1Function_of_scalarParent Q A b hb u
  have hsum :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a r hr hEll (publicCoeffField_openCubeDescendantDeterministicCoarseData Q A)
  simpa only [a, energy] using
    cubeBesovCircPartialNorm_component_le_local_canonicalGradientAcirc
      Q a r hr henergy_nonneg henergy_int hgrad hsum i N


theorem h1Gradient_circNorm_le_energy_of_scalarParent
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q)) (r : ℝ) (hr : 0 < r) (i : Fin d) :
    cubeBesovCircNorm Q r (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤
      cubeBesovScaleWeight (-r) Q * ((geometricDiscount r 1)⁻¹ * (d : ℝ)) *
        Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) A)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q A) u.grad)) := by
  have hBdd := cubeBesovCircNormValueSet_bddAbove_of_memLp Q r
    (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) hr
    (u.grad_memL2_normalizedCubeMeasure i) (by norm_num) (by norm_num) (by norm_num)
  have hlim := tendsto_cubeBesovCircPartialNorm_one_succ_to_cubeBesovCircNorm
    Q r (2 : ℝ≥0∞) (fun x => u.grad x i) hBdd
  have hraw := le_of_tendsto hlim (Filter.Eventually.of_forall fun N =>
    h1Gradient_circPartialNorm_le_energy_of_scalarParent Q A b hb u r hr i (N + 1))
  have hbridge :=
    sqrt_lambdaSq_publicCoeffField_finite_one_inv_le_dim_mul_poincareLowerEllipticityFactor
      Q A hr
  have hdetEq : Real.rpow (lambdaSq Q r (.finite 1) (publicCoeffField Q A))
      (-1 / 2 : ℝ) = Real.sqrt ((lambdaSq Q r (.finite 1) (publicCoeffField Q A))⁻¹) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_eq_pow]
    ring_nf
  have hpubEq : poincareLowerEllipticityFactor Q A r (.finite 1) =
      Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) A)⁻¹) := by
    unfold poincareLowerEllipticityFactor
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_eq_pow]
  rw [hpubEq] at hbridge
  rw [hdetEq] at hraw
  have hdisc : 0 ≤ (geometricDiscount r 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hr)).le
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbridge hdisc)
      (cubeBesovScaleWeight_nonneg (-r) Q))
    (Real.sqrt_nonneg (cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q A) u.grad)))
  have hL : 0 ≤ (Ch02.lambdaSq Q r (.finite 1) A)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_pos Q A hr (by norm_num)).le
  calc
    _ ≤ _ := hraw.trans hscaled
    _ = _ := by rw [Real.sqrt_mul hL]; ring

omit [NeZero d] in
/-- Scalar energy is independent of the pointwise representative used internally. -/
theorem cubeAverage_energy_eq_scalar_volumeAverage
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q)) :
    cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q A) u.grad) =
      volumeAverage (openCubeSet Q) (fun x => b x * vecDot (u.grad x) (u.grad x)) := by
  have hae : coefficientEnergyDensity (publicCoeffField Q A) u.grad
      =ᵐ[volume.restrict (openCubeSet Q)]
        (fun x => b x * vecDot (u.grad x) (u.grad x)) := by
    filter_upwards [publicCoeffField_ae_eq_openCubeSet Q A, hb] with x hx hb'
    rw [coefficientEnergyDensity_eq_unsymmetrized, hx, hb',
      matVecMul_scalarMatrix, vecDot_smul_right]
  calc
    _ = volumeAverage (openCubeSet Q)
        (coefficientEnergyDensity (publicCoeffField Q A) u.grad) := by
      simp [cubeAverage, volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
        volume_cubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ = _ := volumeAverage_eq_of_ae_eq hae

/-- The positive half-order depth seminorm is controlled by coarse ellipticity. -/
theorem h1_depthSeminorm_half_le_energy_of_scalarParent
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q)) (j : ℕ) :
    cubeBesovDepthSeminorm Q (1 / 2) (2 : ℝ≥0∞) u.toFun j ≤
      (oscillationMultiscalePoincareConstant d * (d : ℝ) *
        ((geometricDiscount (1 / 2) 1)⁻¹ * (d : ℝ))) *
      cubeBesovScaleWeight (-1 / 2) Q *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
        volumeAverage (openCubeSet Q) (fun x => b x * vecDot (u.grad x) (u.grad x))) := by
  have hdepth := cubeBesovDepthSeminorm_two_le_sum_circNorm_of_vector_local_full_circ_bound
    Q (1 / 2) (oscillationMultiscalePoincareConstant d) u.toFun u.grad j
    (by norm_num) (by norm_num) (oscillationMultiscalePoincareConstant_nonneg d)
    u.grad_memL2_normalizedCubeMeasure (by
      intro R hR
      exact cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
        R (u.restrictToOpenSubcube hR))
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hdepth
  have hsum := Finset.sum_le_sum fun (i : Fin d) (_ : i ∈ Finset.univ) =>
    h1Gradient_circNorm_le_energy_of_scalarParent Q A b hb u (1 / 2) (by norm_num) i
  have hmul := mul_le_mul_of_nonneg_left hsum
    (oscillationMultiscalePoincareConstant_nonneg d)
  have henergy := cubeAverage_energy_eq_scalar_volumeAverage Q A b hb u
  calc
    _ ≤ _ := hdepth.trans hmul
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, henergy]; ring_nf

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
