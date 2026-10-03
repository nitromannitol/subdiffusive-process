module

public import Mathlib
public import SubdiffusiveProcess.RareIntervals.Main

@[expose] public section

universe u v

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Paper

open Classical in


theorem l_concentration_rare_intervals :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} {β : Type v} [MeasurableSpace Ω] [MeasurableSpace β]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℤ → Ω → β), iIndepFun ξ μ →
        (∀ i, Measurable (ξ i)) → ∀ (lam : ℝ), 0 < lam → ∀ (E : ℤ → ℕ → Set Ω),
        ((∀ (k : ℤ) (j : ℕ), MeasurableSet[⨆ i ∈ Set.Icc k (k + (j : ℤ)), MeasurableSpace.comap (ξ i) inferInstance]
            (E k j)) ∨
          (∀ (k : ℤ) (j : ℕ), MeasurableSet[⨆ i ∈ Set.Icc (k - (j : ℤ)) (k + (j : ℤ)),
            MeasurableSpace.comap (ξ i) inferInstance] (E k j))) →
        (∀ (k : ℤ) (j : ℕ), μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1))))) →
        ∀ (θ : ℝ), 0 < θ → θ ≤ 1 → C ≤ lam * θ →
        ∀ (a : ℤ) (N : ℕ), 1 ≤ N →
          μ {ω | θ * N ≤ ((Finset.Icc a (a + (N : ℤ) - 1)).filter
              (fun k => ∃ j : ℕ, ω ∈ E k j)).card} ≤
            ENNReal.ofReal (Real.exp (-(c * lam * θ * N))) := by
  refine ⟨1 / 24, 100, by norm_num, by norm_num, ?_⟩
  intro Ω β _ _ μ hμ ξ hind hmeas lam hlam E hcase hP θ hθ0 hθ1 hC a N hN
  have hind' : iIndep (fun i => MeasurableSpace.comap (ξ i) inferInstance) μ :=
    hind.iIndep
  have hm : ∀ i, MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace β) ≤
      (inferInstance : MeasurableSpace Ω) := fun i => (hmeas i).comap_le
  rcases hcase with h | h
  · exact SubdiffusiveProcess.RareIntervals.rare_intervals_scheme
      SubdiffusiveProcess.RareIntervals.Scheme.oneSided hind' hm E
      (fun k j => by
        convert h k j using 1 <;> simp only [SubdiffusiveProcess.RareIntervals.Scheme.oneSided,
          SubdiffusiveProcess.RareIntervals.Scheme.centered, Finset.mem_Icc, Set.mem_Icc]) lam hP θ hθ0 hθ1 hC a N hN
  · exact SubdiffusiveProcess.RareIntervals.rare_intervals_scheme
      SubdiffusiveProcess.RareIntervals.Scheme.centered hind' hm E
      (fun k j => by
        convert h k j using 1 <;> simp only [SubdiffusiveProcess.RareIntervals.Scheme.oneSided,
          SubdiffusiveProcess.RareIntervals.Scheme.centered, Finset.mem_Icc, Set.mem_Icc]) lam hP θ hθ0 hθ1 hC a N hN

end Paper
