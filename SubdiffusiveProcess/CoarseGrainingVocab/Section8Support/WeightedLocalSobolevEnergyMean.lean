module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevEnergyCirc

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal
variable {d : ℕ} [NeZero d]

theorem weightedEnergy_rpow_sqrt (x : ℝ) : Real.rpow x (-1 / 2 : ℝ) = Real.sqrt (x⁻¹) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_eq_pow]
  ring_nf

theorem weightedEnergy_factor {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d) (r : ℝ) : poincareLowerEllipticityFactor Q a r (.finite 1) = Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) a)⁻¹) := by
  unfold poincareLowerEllipticityFactor
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
  rw [← Real.rpow_eq_pow]

/-- The vector negative norm uses the same coarse energy control. -/
theorem h1Gradient_negativeVectorSeminormTwo_le_energy_of_scalarParent
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H1Function (openCubeSet Q)) (r : ℝ) (hr : 0 < r) :
    cubeBesovNegativeVectorSeminormTwo Q r u.grad ≤
      ((geometricDiscount r 1)⁻¹ * (d : ℝ)) *
        Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) A)⁻¹ *
          volumeAverage (openCubeSet Q) (fun x => b x * vecDot (u.grad x) (u.grad x))) := by
  let a := publicCoeffField Q A
  let energy := coefficientEnergyDensity a u.grad
  have hEll := publicCoeffField_isEllipticFieldOn_cubeSet Q A
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x :=
    coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad
  have henergy_int : IntegrableOn energy (cubeSet Q) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll (by
      rw [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      exact u.grad_memVectorL2)
  have hgrad : CubeAverageGradientEnergyControl Q a u.grad energy :=
    cubeAverageGradientEnergyControl_of_h1Function_of_scalarParent Q A b hb u
  have hsum :=
    summable_qone_maxDescendantSigmaStarInvNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      Q a r hr hEll (publicCoeffField_openCubeDescendantDeterministicCoarseData Q A)
  have hraw := cubeBesovNegativeVectorSeminormTwo_le_of_qone_partialBound Q r u.grad
    (fun N => coarseCaccioppoli_gradient_qone_partialBound_of_cubeAverageEnergyControl
      Q a r hr u.grad energy N henergy_nonneg henergy_int hgrad hsum)
  have hbridge :=
    sqrt_lambdaSq_publicCoeffField_finite_one_inv_le_dim_mul_poincareLowerEllipticityFactor
      Q A hr
  rw [weightedEnergy_factor] at hbridge
  rw [weightedEnergy_rpow_sqrt] at hraw
  have hdisc : 0 ≤ (geometricDiscount r 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hr)).le
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbridge hdisc)
    (Real.sqrt_nonneg (cubeAverage Q energy))
  have hL : 0 ≤ (Ch02.lambdaSq Q r (.finite 1) A)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_pos Q A hr (by norm_num)).le
  have henergy := cubeAverage_energy_eq_scalar_volumeAverage Q A b hb u
  calc
    _ ≤ _ := hraw.trans hscaled
    _ = _ := by
      change (geometricDiscount r 1)⁻¹ *
        ((d : ℝ) * Real.sqrt ((Ch02.lambdaSq Q r (.finite 1) A)⁻¹)) *
        Real.sqrt (cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q A) u.grad)) = _
      rw [henergy, Real.sqrt_mul hL]
      ring

theorem weightedEnergy_zero_prefactor_nonneg (d : ℕ) : 0 ≤ (2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * Real.sqrt ((1 - Real.rpow (3 : ℝ) (-1))⁻¹) := by
  positivity

theorem weightedEnergy_scale_cancel (S T X B : ℝ) (hT : 0 ≤ T) (hST : S * T = 1) (h : S * X ≤ B) : X ≤ T * B := by
  have hh := mul_le_mul_of_nonneg_left h hT
  have heq : T * (S * X) = X := by
    calc T * (S * X) = (S * T) * X := by ring
      _ = X := by rw [hST, one_mul]
  rwa [heq] at hh

theorem weightedEnergy_mean_rewrite {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H10Function (openCubeSet Q)) : cubeBesovScaleWeight 1 Q * |cubeAverage Q u.toH1Function.toFun| ≤ ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * Real.sqrt ((1 - Real.rpow (3 : ℝ) (-1))⁻¹)) * cubeBesovNegativeVectorSeminormTwo Q (1 / 2) u.toH1Function.grad := by
  have h := cubeBesovScaleWeight_one_mul_abs_cubeAverage_h10_le_grad_negativeBesovTwo Q (t := 1 / 4) u.toCubeSet (by norm_num) (by norm_num)
  rw [show (-2:ℝ)*(1-2*(1/4)) = -1 by norm_num] at h
  simpa only [H10Function.toCubeSet_toH1Function_grad,
    H10Function.toCubeSet_toH1Function_toFun,
    Real.norm_eq_abs,
    show (2:ℝ)*(1/4) = 1/2 by norm_num] using h

/-- The zero-trace average pays only the same half-order coarse ellipticity. -/
theorem h10_scaled_average_le_energy_of_scalarParent
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H10Function (openCubeSet Q)) :
    cubeBesovScaleWeight 1 Q * |cubeAverage Q u.toH1Function.toFun| ≤
      (((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (-1))⁻¹)) *
        ((geometricDiscount (1 / 2) 1)⁻¹ * (d : ℝ))) *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
        volumeAverage (openCubeSet Q)
          (fun x => b x * vecDot (u.toH1Function.grad x) (u.toH1Function.grad x))) := by
  have hmean := weightedEnergy_mean_rewrite Q u
  have henergy := h1Gradient_negativeVectorSeminormTwo_le_energy_of_scalarParent
    Q A b hb u.toH1Function (1 / 2) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left henergy (weightedEnergy_zero_prefactor_nonneg d)
  exact hmean.trans (by simpa only [mul_assoc] using hmul)

/-- Unscaled zero-trace average bound. -/
theorem h10_average_le_energy_of_scalarParent
    (Q : TriadicCube d) (A : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (A.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    (u : H10Function (openCubeSet Q)) :
    |cubeAverage Q u.toH1Function.toFun| ≤
      cubeBesovScaleWeight (-1) Q *
      ((((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        Real.sqrt ((1 - Real.rpow (3 : ℝ) (-1))⁻¹)) *
        ((geometricDiscount (1 / 2) 1)⁻¹ * (d : ℝ))) *
      Real.sqrt ((Ch02.lambdaSq Q (1 / 2) (.finite 1) A)⁻¹ *
        volumeAverage (openCubeSet Q)
          (fun x => b x * vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)))) := by
  apply weightedEnergy_scale_cancel (cubeBesovScaleWeight 1 Q)
    (cubeBesovScaleWeight (-1) Q) _ _ (cubeBesovScaleWeight_nonneg (-1) Q)
  · rw [mul_comm]
    exact cubeBesovScaleWeight_neg_one_mul_cubeBesovScaleWeight_one_eq_one Q
  · exact h10_scaled_average_le_energy_of_scalarParent Q A b hb u

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

