module

public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Geometry.TriadicFinitePartition
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Exact energy splitting on the actual finite adaptive partition

The restricted coefficient and each L2 gradient coordinate are restrictions
of the same root objects. Lebesgue integration therefore splits exactly
across the actual disjoint adaptive cubes. This is a finite-cutoff identity;
it does not assert gluing or energy-measure convergence for limiting forms.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Coordinatewise restriction of an actual square-integrable gradient field. -/
def domainGradientRestrict (hU : U ≤ Ω) (g : HilbertGradient Ω) : HilbertGradient U :=
  WithLp.toLp 2 (fun i => domainLpRestrict hU (g i))

/-- Each coordinate is the original coordinate almost everywhere on the subdomain. -/
theorem domainGradientRestrict_coeFn (hU : U ≤ Ω) (g : HilbertGradient Ω) (i : Fin d) :
    (domainGradientRestrict hU g i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] g i :=
  domainLpRestrict_coeFn hU (g i)

/-- The real coordinate integrand in the gradient form is integrable. -/
theorem integrable_weighted_coordinates
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (g h : HilbertGradient Ω) (i : Fin d) :
    Integrable (fun x => a x * (g i x * h i x))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm (h i _) (g i _)] using
    integrable_weighted_inner a (g i) (h i)

/-- The restricted form is the literal subdomain integral of the original root fields. -/
theorem weightedGradientForm_restrict (hU : U ≤ Ω) (a : PositiveCoefficient Ω)
    (g h : HilbertGradient Ω) :
    weightedGradientForm (positiveCoefficientRestrict hU a).val
      (domainGradientRestrict hU g) (domainGradientRestrict hU h) =
      ∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)), a.val x * (g i x * h i x) := by
  rw [weightedGradientForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [positiveCoefficientRestrict_coeFn hU a,
    domainGradientRestrict_coeFn hU g i, domainGradientRestrict_coeFn hU h i] with x ha hg hh
  rw [ha, hg, hh]

/-- An integrable root function splits over the literal finite adaptive family. -/
theorem integral_triadicAdaptiveCells (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ) {f : SpatialCoordinates d → ℝ}
    (hf : IntegrableOn f (centeredCube z r hr : Set (SpatialCoordinates d)) volume) :
    (∑ t ∈ triadicAdaptiveLabels I J,
      ∫ x in (triadicAdaptiveCell z r hr J t : Set (SpatialCoordinates d)), f x) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x := by
  rw [← integral_biUnion_finset (triadicAdaptiveLabels I J)
    (fun t _ => (triadicAdaptiveCell z r hr J t).isOpen.measurableSet)
    (triadicAdaptiveCells_pairwiseDisjoint z hr I J)
    (fun t _ => hf.mono_set (triadicAdaptiveCell_subset_root z hr J t))]
  exact setIntegral_congr_set (triadicAdaptiveCells_union_ae_eq z hr hI J)

/-- The bilinear finite-cutoff energy is exactly the sum of its actual cell restrictions. -/
theorem weightedGradientForm_triadicAdaptiveCells (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ)
    (a : PositiveCoefficient (centeredCube z r hr))
    (g h : HilbertGradient (centeredCube z r hr)) :
    (∑ t ∈ triadicAdaptiveLabels I J,
      weightedGradientForm
        (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a).val
        (domainGradientRestrict (triadicAdaptiveCell_subset_root z hr J t) g)
        (domainGradientRestrict (triadicAdaptiveCell_subset_root z hr J t) h)) =
      weightedGradientForm a.val g h := by
  have hU (t : TriadicAdaptiveIndex d J) :
      triadicAdaptiveCell z r hr J t ≤ centeredCube z r hr :=
    triadicAdaptiveCell_subset_root z hr J t
  change (∑ t ∈ triadicAdaptiveLabels I J,
    weightedGradientForm (positiveCoefficientRestrict (hU t) a).val
      (domainGradientRestrict (hU t) g) (domainGradientRestrict (hU t) h)) =
    weightedGradientForm a.val g h
  simp_rw [weightedGradientForm_restrict]
  rw [weightedGradientForm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_triadicAdaptiveCells z hr hI J (integrable_weighted_coordinates a.val g h i)

end SubdiffusiveProcess
