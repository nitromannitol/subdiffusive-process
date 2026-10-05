module

public import SubdiffusiveProcess.Paper.lem_as_regularity_scaled_folded_error
public import SubdiffusiveProcess.EllipticRegularity.CutoffCoefficientRepresentative

@[expose] public section

/-! The physical good-scale bound for the actual cutoff coefficient gives the
native folded error input without an infrared truncation. The good-scale bound
is consumed explicitly; no prefix or solution estimate is asserted.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The physical and native scale exponents give exactly the cutoff dilation. -/
theorem aux_lem_as_regularity_actual_native_error_scale (N j : ℕ) :
    (3 : ℝ) ^ (-((N : ℤ) - (j : ℤ))) * ((3 : ℝ) ^ (j : ℤ))⁻¹ =
      (3 : ℝ) ^ (-(N : ℤ)) := by
  rw [← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

/-- A physical good-scale estimate bounds the corresponding actual folded native error. -/
theorem lem_as_regularity_actual_native_error (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N j : ℕ) (w : SpatialCoordinates d) (I P : Finset (Fin d)) (ref bound : ℝ)
    (href : 0 < ref)
    (herr : E.err w ((3 : ℝ) ^ (-((N : ℤ) - (j : ℤ)))) (by positivity)
        (cutoffPositiveCoefficient M H omega N w (by positivity))
        w ((3 : ℝ) ^ (-((N : ℤ) - (j : ℤ)))) ref (1 / 32) 2 ≤ bound)
    (data : ScalarTriadicCoeffData (fun y => cutoffCoefficient M H omega N
      (coordinateFold w I P ((3 : ℝ) ^ (-(N : ℤ)) • (y + 0) + w)))) :
    paperHomogenizationError (originCube d (j : ℤ)) (j : ℤ) (1 / 32)
      Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily ref ≤ ENNReal.ofReal
        ((1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1)) * bound) := by
  have hrep := cutoffPositiveCoefficient_representative M H omega N w
    (r := (3 : ℝ) ^ (-((N : ℤ) - (j : ℤ)))) (by positivity)
  have h := lem_as_regularity_scaled_folded_error d hd E w _ _ (by positivity) (by positivity)
    (j : ℤ) (aux_lem_as_regularity_actual_native_error_scale N j) I P
    (cutoffPositiveCoefficient M H omega N w (by positivity)) _ hrep.1 hrep.2.1 hrep.2.2.2
    data ref (1 / 32) href (by norm_num) (by norm_num)
  have hden : 0 < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hfac : 0 ≤ 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) := by positivity
  exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left herr hfac))

end SubdiffusiveProcess.Paper
