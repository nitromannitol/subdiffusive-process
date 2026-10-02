import SubdiffusiveProcess.Paper.killed_zero_extension_bound
import SubdiffusiveProcess.Paper.car_variational
import SubdiffusiveProcess.Lnorm.CoercivityNormalization

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- A deterministic cube factor converts the produced normalized coercivity
constant to all physical norm and zero-extension estimates used below. -/
theorem aux_mfd_prop_uniform_resolvent_coercivity_scale {d : ℕ} (hd : 2 ≤ d)
    (Sf : SobolevFoundationalInput d hd) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a : PositiveCoefficient (centeredCube z r hr)) (K : ℝ), 0 ≤ K →
      (∀ v : killedSobolevGraph (centeredCube z r hr),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder v.val.1 ≤
          K * sobolevCoefficientForm a v.val v.val) →
      ∀ v : killedSobolevGraph (centeredCube z r hr),
        (‖v.val.1‖ ^ 2 ≤ (D * K) * sobolevCoefficientForm a v.val v.val) ∧
        (globalFractionalSqNorm (3 / 4)
          ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator (fun x => v.val.1 x)) ≤
          ENNReal.ofReal ((D * K) * sobolevCoefficientForm a v.val v.val)) ∧
        ∃ v3 : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
          v3.val 0 = v.val.1 ∧ cubeFractionalL2Norm hd z r hr threeQuarterOrder v3 ^ 2 ≤
            (D * K) * sobolevCoefficientForm a v.val v.val := by
  obtain ⟨Cext, hCext, hext, -⟩ := killed_zero_extension_bound hd Sf z r hr
  let V := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  let D := V + Cext + (1 + r ^ (-(3 / 2 : ℝ))) + 1
  have hV : 0 ≤ V := measureReal_nonneg
  have hpow : 0 ≤ r ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hr.le _
  have hD : 0 < D := by dsimp [D]; linarith
  have hVD : V ≤ D := by dsimp [D]; linarith
  have hCD : Cext ≤ D := by dsimp [D]; linarith
  have hPD : 1 + r ^ (-(3 / 2 : ℝ)) ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD, fun a K hK hc v => ?_⟩
  have he : 0 ≤ sobolevCoefficientForm a v.val v.val := sobolevCoefficientForm_nonneg _ _
  have hnorm := Lnorm.fractional_coercivity_unnormalized hd z r hr v.val.1 K _ (hc v)
  have hn : ‖v.val.1‖ ^ 2 ≤ (V * K) * sobolevCoefficientForm a v.val v.val := by
    exact (le_add_of_nonneg_right (mul_nonneg hV (sq_nonneg _))).trans hnorm
  obtain ⟨v3, hv3, hb⟩ := aux_car_variational_hcoer3_of_hc1 hd Sf z r hr a K hK v (hc v)
  refine ⟨hn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hVD hK) he), ?_, v3, hv3, ?_⟩
  · refine (hext v).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      Cext * cubeFractionalSqNorm hd z r hr threeQuarterOrder v.val.1 ≤
          Cext * (K * sobolevCoefficientForm a v.val v.val) :=
        mul_le_mul_of_nonneg_left (hc v) hCext.le
      _ ≤ (D * K) * sobolevCoefficientForm a v.val v.val := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hK) he
  · refine hb.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPD hK) he

end Paper
