module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Step approximation of a test integral

The vague limit of the cutoff measures is obtained by comparing `∫ f dnu` with
the step sum `∑ f(c i) nu(Q i)` over a finite disjoint family covering the
support of `f`.  The comparison is uniform in the measure: it costs only the
oscillation of `f` on the pieces, times the total mass of the family.  That
uniformity is what lets the growth bound, which is uniform in the cutoff, turn
the convergence of finitely many masses into convergence of the integral.
-/

open MeasureTheory

noncomputable section
namespace SubdiffusiveProcess

/-- Replacing `f` by its value at a point of each piece costs at most the
oscillation of `f` on the pieces, times the total mass. -/
theorem integral_sub_step_le
    {d : ℕ} {iota : Type*} (nu : Measure (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ)
    (s : Finset iota) (Q : iota → Set (SpatialCoordinates d))
    (c : iota → SpatialCoordinates d)
    (hmeas : ∀ i ∈ s, MeasurableSet (Q i))
    (hdisj : (s : Set iota).PairwiseDisjoint Q)
    (hzero : ∀ x, x ∉ (⋃ i ∈ s, Q i) → f x = 0)
    (hint : Integrable f nu)
    (hfin : ∀ i ∈ s, nu (Q i) ≠ ⊤)
    (om : ℝ) (_hom : 0 ≤ om)
    (happrox : ∀ i ∈ s, ∀ x ∈ Q i, |f x - f (c i)| ≤ om) :
    |∫ x, f x ∂nu - ∑ i ∈ s, f (c i) * (nu (Q i)).toReal|
      ≤ om * ∑ i ∈ s, (nu (Q i)).toReal := by
  classical
  have hsplit : ∫ x, f x ∂nu = ∑ i ∈ s, ∫ x in Q i, f x ∂nu := by
    have h1 : ∫ x, f x ∂nu = ∫ x in ⋃ i ∈ s, Q i, f x ∂nu :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    rw [h1]
    exact integral_biUnion_finset s hmeas hdisj (fun i _ => hint.integrableOn)
  have hpiece : ∀ i ∈ s,
      |(∫ x in Q i, f x ∂nu) - f (c i) * (nu (Q i)).toReal|
        ≤ om * (nu (Q i)).toReal := by
    intro i hi
    have : IsFiniteMeasure (nu.restrict (Q i)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_ne le_top (hfin i hi)
    have hconst : ∫ _x in Q i, f (c i) ∂nu = f (c i) * (nu (Q i)).toReal := by
      simp [Measure.real, mul_comm]
    have hsub : (∫ x in Q i, f x ∂nu) - f (c i) * (nu (Q i)).toReal
        = ∫ x in Q i, (f x - f (c i)) ∂nu := by
      rw [← hconst, integral_sub hint.integrableOn (integrable_const _)]
    rw [hsub]
    have hbd : ∀ x ∈ Q i, ‖f x - f (c i)‖ ≤ om := fun x hx => happrox i hi x hx
    calc |∫ x in Q i, (f x - f (c i)) ∂nu|
        ≤ ∫ x in Q i, ‖f x - f (c i)‖ ∂nu := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ _x in Q i, om ∂nu := by
          refine setIntegral_mono_on ?_ (integrable_const om) (hmeas i hi) ?_
          · exact (hint.integrableOn.sub (integrable_const _)).norm
          · intro x hx
            exact hbd x hx
      _ = om * (nu (Q i)).toReal := by
          simp [Measure.real, mul_comm]
  calc |∫ x, f x ∂nu - ∑ i ∈ s, f (c i) * (nu (Q i)).toReal|
      = |∑ i ∈ s, ((∫ x in Q i, f x ∂nu) - f (c i) * (nu (Q i)).toReal)| := by
        rw [Finset.sum_sub_distrib, hsplit]
    _ ≤ ∑ i ∈ s, |(∫ x in Q i, f x ∂nu) - f (c i) * (nu (Q i)).toReal| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, om * (nu (Q i)).toReal := Finset.sum_le_sum hpiece
    _ = om * ∑ i ∈ s, (nu (Q i)).toReal := by rw [Finset.mul_sum]

end SubdiffusiveProcess
