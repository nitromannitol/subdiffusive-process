module

public import SubdiffusiveProcess.Sobolev.CoordinateL2Integral
public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

@[expose] public section

/-! The Euclidean length of a native Hilbert gradient has exactly its Hilbert L2 norm.
This module supplies norm identities only; it asserts no regularity of a solution. -/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- The Euclidean length of finitely many scalar L2 coordinates belongs to L2. -/
theorem gradientLength_memLp_two {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (g : HilbertGradient Ω) :
    MemLp (fun x => Real.sqrt (∑ i : Fin d, (g i x) ^ 2)) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have hsum : Integrable (fun x => ∑ i : Fin d, (g i x) ^ 2)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    integrable_finset_sum Finset.univ (fun i _ => (Lp.memLp (g i)).integrable_sq)
  have hmeas := hsum.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  simpa only [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (g i _)))] using hsum

/-- The L2 norm of the Euclidean gradient length is the native Hilbert gradient norm. -/
theorem eLpNorm_gradientLength_two {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (g : HilbertGradient Ω) :
    (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (g i x) ^ 2)) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d)))).toReal = ‖g‖ := by
  have hsum : Integrable (fun x => ∑ i : Fin d, (g i x) ^ 2)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    integrable_finset_sum Finset.univ (fun i _ => (Lp.memLp (g i)).integrable_sq)
  have hint : (∫ x in (Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, (g i x) ^ 2) = ‖g‖ ^ 2 := by
    have h := congrArg ENNReal.toReal (lintegral_coordinate_sq_eq_sum_norm_sq (fun i => g i))
    rw [← ofReal_integral_eq_lintegral_ofReal hsum
      (ae_of_all _ (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg (g i x)))),
      ENNReal.toReal_ofReal (integral_nonneg (fun x =>
        Finset.sum_nonneg (fun i _ => sq_nonneg (g i x)))),
      ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => sq_nonneg ‖g i‖))] at h
    exact h.trans (PiLp.norm_sq_eq_of_L2 _ g).symm
  rw [(gradientLength_memLp_two g).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.rpow_two, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (g i _))), hint]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _), ENNReal.toReal_ofReal (norm_nonneg _)]

/-- On the full cube, the normalized L2 gradient norm divides by the square root of its volume. -/
theorem normalizedGradientLpNorm_two_cube {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : HilbertGradient (centeredCube z r hr)) :
    Lane4.normalizedGradientLpNorm 2 (centeredCube z r hr : Set (SpatialCoordinates d)) g =
      ‖g‖ / Real.sqrt (r ^ d) := by
  unfold Lane4.normalizedGradientLpNorm
  rw [Measure.restrict_restrict (centeredCube z r hr).isOpen.measurableSet, inter_self,
    eLpNorm_gradientLength_two, centeredCube_volume_real]
  simp only [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow]

end SubdiffusiveProcess
