module

public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph

@[expose] public section

/-! # Energy measure of a zero-extended Sobolev datum

This file proves that extending Sobolev data by zero preserves its energy
measure on the original open set when the coefficients agree there. It does
not claim any energy identity outside that set.
-/

open MeasureTheory Set TopologicalSpace

noncomputable section
namespace SubdiffusiveProcess

/-- The energy measure of a zero extension is the original energy measure when
the coefficients agree almost everywhere on the subdomain. -/
theorem gradientEnergyMeasure_zeroExtensionSobolevData
    {d : ℕ} {V Q : Opens (SpatialCoordinates d)} (hVQ : V ≤ Q)
    (a : PositiveCoefficient Q) (b : PositiveCoefficient V)
    (hab : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] b.val)
    (v : SobolevData V) :
    gradientEnergyMeasure a (sobolevGradient (zeroExtensionSobolevData hVQ v)) =
      gradientEnergyMeasure b (sobolevGradient v) := by
  rw [gradientEnergyMeasure, gradientEnergyMeasure]
  let μQ := volume.restrict (Q : Set (SpatialCoordinates d))
  let μV := volume.restrict (V : Set (SpatialCoordinates d))
  let gQ := sobolevGradient (zeroExtensionSobolevData hVQ v)
  let gV := sobolevGradient v
  have hcoord : ∀ᵐ x ∂μQ, ∀ i : Fin d,
      gQ i x = (V : Set (SpatialCoordinates d)).indicator (gV i) x := by
    apply ae_all_iff.mpr
    intro i
    exact zeroExtensionLp_coeFn hVQ (v.2 i)
  have hdensity :
      (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (gQ i x) ^ 2)) =ᵐ[μQ]
        (V : Set (SpatialCoordinates d)).indicator
          (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (gV i x) ^ 2)) := by
    filter_upwards [hcoord] with x hxcoord
    by_cases hxV : x ∈ (V : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hxV]
      have hsum : ∑ i : Fin d, (gQ i x) ^ 2 = ∑ i : Fin d, (gV i x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hxcoord i, Set.indicator_of_mem hxV]
      rw [hsum]
    · rw [Set.indicator_of_notMem hxV]
      have hzero : ∀ i : Fin d, gQ i x = 0 := by
        intro i
        rw [hxcoord i, Set.indicator_of_notMem hxV]
      have hsumzero : ∑ i : Fin d, (gQ i x) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i]
        exact zero_pow (Nat.succ_ne_zero 1)
      rw [hsumzero]
      simp only [mul_zero, ENNReal.ofReal_zero]
  calc
    μQ.withDensity (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (gQ i x) ^ 2)) =
        μQ.withDensity ((V : Set (SpatialCoordinates d)).indicator
          (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (gV i x) ^ 2))) :=
      withDensity_congr_ae hdensity
    _ = (μQ.restrict (V : Set (SpatialCoordinates d))).withDensity
          (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (gV i x) ^ 2)) :=
      withDensity_indicator V.isOpen.measurableSet _
    _ = μV.withDensity (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (gV i x) ^ 2)) := by
      rw [Measure.restrict_restrict_of_subset hVQ]
    _ = μV.withDensity (fun x => ENNReal.ofReal (b.val x * ∑ i : Fin d, (gV i x) ^ 2)) := by
      apply withDensity_congr_ae
      filter_upwards [hab] with x hx
      rw [hx]

end SubdiffusiveProcess
