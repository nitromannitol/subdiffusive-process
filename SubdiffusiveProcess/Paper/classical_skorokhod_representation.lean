import SubdiffusiveProcess.Probability.SkorokhodRepresentation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Polish

/-! Classical input (frozen leaf): **Skorokhod's representation theorem** for a weakly convergent sequence
of probability measures on a Polish space: there are random elements on one probability space with the given
laws that converge almost surely.
Kallenberg, *Foundations of Modern Probability*, 2nd ed. (2002), Theorem 4.30;
Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), Theorem 6.7, p. 70
("`P_n ⇒ P` and `P` has a separable support ⇒ there exist random elements `X_n`, `X` on a common probability
space with laws `P_n`, `P` and `X_n → X` almost surely").
The statement is a weaker special case (Polish space in place of a separable support; the a.s. form). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory
open scoped Topology
universe u
namespace Paper

theorem classical_skorokhod_representation
    {X : Type u} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure X)
    (h : Tendsto mu atTop (𝓝 nu)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (Xn : ℕ → Ω → X) (X0 : Ω → X),
      IsProbabilityMeasure P ∧ (∀ n, Measurable (Xn n)) ∧ Measurable X0 ∧
      (∀ n, P.map (Xn n) = (mu n : Measure X)) ∧ P.map X0 = (nu : Measure X) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => Xn n ω) atTop (𝓝 (X0 ω)) := by
  exact SubdiffusiveProcess.Probability.skorokhod_representation mu nu h

end Paper
