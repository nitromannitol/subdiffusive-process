import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Variational.PotentialWeight

/-! # Actual exponential coefficients of bounded potentials

Potentials are L∞ classes for restricted Lebesgue measure. Their exponential
coefficients are constructed by `MemLp.toLp`, with the exact almost-everywhere
formula. No coefficient or response is assigned an off-support default.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- An L∞ potential is almost everywhere bounded by its actual essential-supremum norm. -/
theorem boundedPotential_ae_bound
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |g x| ≤ ‖g‖ := by
  have ht : eLpNormEssSup (⇑g) (volume.restrict (Ω : Set (SpatialCoordinates d))) = ‖g‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_exponent_top]
  simpa only [ht, enorm_le_iff_norm_le, Real.norm_eq_abs] using
    enorm_ae_le_eLpNormEssSup (⇑g) (volume.restrict (Ω : Set (SpatialCoordinates d)))

/-- Exponentiation of an actual bounded potential is again essentially bounded. -/
theorem boundedPotential_exp_memLp
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    MemLp (fun x => Real.exp (g x)) ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  apply memLp_top_of_bound (Real.continuous_exp.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g))
    (Real.exp ‖g‖)
  filter_upwards [boundedPotential_ae_bound g] with x hx
  simpa only [Real.norm_eq_abs, Real.abs_exp] using
    Real.exp_monotone ((le_abs_self (g x)).trans hx)

/-- The actual exponential coefficient of an L∞ potential, bounded away from zero. -/
def expPotentialCoefficient
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) : PositiveCoefficient Ω := by
  refine ⟨(boundedPotential_exp_memLp g).toLp (fun x => Real.exp (g x)),
    Real.exp (-‖g‖), Real.exp_pos _, ?_⟩
  filter_upwards [(boundedPotential_exp_memLp g).coeFn_toLp, boundedPotential_ae_bound g] with x he hx
  rw [he]
  exact Real.exp_monotone (abs_le.mp hx).1

/-- The coefficient definition retains the exact pointwise exponential almost everywhere. -/
theorem expPotentialCoefficient_coeFn
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (expPotentialCoefficient g).val x = Real.exp (g x) :=
  (boundedPotential_exp_memLp g).coeFn_toLp

/-- Supremum-norm closeness of potentials gives both coefficient inequalities. -/
theorem expPotentialCoefficient_comparison
    (g h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-‖g - h‖) * (expPotentialCoefficient g).val x ≤ (expPotentialCoefficient h).val x) ∧
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (expPotentialCoefficient h).val x ≤ Real.exp ‖g - h‖ * (expPotentialCoefficient g).val x) := by
  have hb : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), |g x - h x| ≤ ‖g - h‖ := by
    filter_upwards [boundedPotential_ae_bound (g - h), Lp.coeFn_sub g h] with x hx he
    simpa only [he, Pi.sub_apply] using hx
  constructor
  · filter_upwards [hb, expPotentialCoefficient_coeFn g, expPotentialCoefficient_coeFn h] with x hx hg hh
    rw [hg, hh, ← Real.exp_add]
    apply Real.exp_monotone
    linarith [(abs_le.mp hx).2]
  · filter_upwards [hb, expPotentialCoefficient_coeFn g, expPotentialCoefficient_coeFn h] with x hx hg hh
    rw [hg, hh, ← Real.exp_add]
    apply Real.exp_monotone
    linarith [(abs_le.mp hx).1]

end SubdiffusiveProcess
