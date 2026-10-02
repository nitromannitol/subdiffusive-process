import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.Algebra.MvPolynomial

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

/-! Bounded coordinates determine finite measures through their monomial integrals.
Polish spaces need not be compact. -/

namespace SubdiffusiveProcess

theorem measure_eq_of_bounded_monomial_integrals
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {k : ℕ}
    (coord : Fin k → (X →ᵇ ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ i : Fin k, coord i x ≠ coord i y)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ m : Fin k → ℕ,
      (∫ x, ∏ i : Fin k, (coord i x) ^ (m i) ∂μ) =
        ∫ x, ∏ i : Fin k, (coord i x) ^ (m i) ∂ν) :
    μ = ν := by
  let φ : MvPolynomial (Fin k) ℝ →ₐ[ℝ]
      (BoundedContinuousFunction X ℝ) := MvPolynomial.aeval coord
  let A : StarSubalgebra ℝ (BoundedContinuousFunction X ℝ) :=
    ⟨φ.range, fun {_} h => by simpa only [star_trivial] using h⟩
  apply MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish
      (A := A)
  · intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    have hcoord : coord i ∈ A := by
      change coord i ∈ φ.range
      exact ⟨MvPolynomial.X i, by simp [φ]⟩
    refine ⟨fun z => coord i z, ?_, hi⟩
    exact ⟨(coord i).toContinuousMap, ⟨coord i, hcoord, rfl⟩, rfl⟩
  · intro g hg
    change g ∈ φ.range at hg
    obtain ⟨p, rfl⟩ := hg
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
        simpa [φ, MvPolynomial.aeval_monomial,
          Finsupp.prod_fintype, integral_const_mul] using congrArg (a * ·) (hm fun i => m i)
    | add p q hp hq =>
        rw [map_add]
        change (∫ x, φ p x + φ q x ∂μ) = ∫ x, φ p x + φ q x ∂ν
        rw [integral_add ((φ p).integrable μ) ((φ q).integrable μ),
          integral_add ((φ p).integrable ν) ((φ q).integrable ν)]
        exact congrArg₂ (· + ·) hp hq

theorem measure_eq_of_unitCube_monomial_integrals
    {k : ℕ}
    (μ ν : Measure (Fin k → Set.Icc (0 : ℝ) 1))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ m : Fin k → ℕ,
      (∫ x, ∏ i : Fin k, (x i : ℝ) ^ (m i) ∂μ) =
        ∫ x, ∏ i : Fin k, (x i : ℝ) ^ (m i) ∂ν) :
    μ = ν := by
  let coord : Fin k → BoundedContinuousFunction (Fin k → Set.Icc (0 : ℝ) 1) ℝ := fun i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => (x i : ℝ), (continuous_apply i).subtype_val⟩
  refine measure_eq_of_bounded_monomial_integrals coord ?_ μ ν ?_
  · intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact ⟨i, fun h => hi (Subtype.ext h)⟩
  · intro m
    exact hm m

end SubdiffusiveProcess
