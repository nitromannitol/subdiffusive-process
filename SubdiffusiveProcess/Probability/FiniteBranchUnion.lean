module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import SubdiffusiveProcess.Main.BranchManyBadNodes

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SubdiffusiveProcess

theorem union_bound_finitely_many_bad_branches
    {β : Type*} [Fintype β]
    (J : ℕ)
    (A θ : ℝ)
    (hA : 0 < A)
    (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1)
    (Ω X : Type*)
    [mΩ : MeasurableSpace Ω]
    [mX : MeasurableSpace X]
    (P : Measure Ω)
    [hP : IsProbabilityMeasure P]
    (g : ℤ → Ω → X)
    (hg_meas : ∀ j : ℤ, Measurable (g j))
    (hg_indep : iIndepFun g P)
    (n : β → Fin J → ℤ)
    (hn : ∀ b : β, Function.Injective (n b))
    (failure : β → Fin J → Set Ω)
    (W : β → Fin J → ℕ+ → Set Ω)
    (hW_meas : ∀ (b : β) (i : Fin J) (h : ℕ+),
      @MeasurableSet Ω
        (⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (n b i - (h : ℤ)) (n b i + 2 * (h : ℤ))),
          MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))
        (W b i h))
    (hW_prob : ∀ (b : β) (i : Fin J) (h : ℕ+),
      P (W b i h) ≤ ENNReal.ofReal (Real.exp (-A * (h : ℝ))))
    (hfailure : ∀ (b : β) (i : Fin J), failure b i ⊆ ⋃ h : ℕ+, W b i h) :
    P { ω | ∃ b : β, θ * (J : ℝ) ≤
        (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ) } ≤
      (Fintype.card β : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (-((A * θ / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ))) := by
  classical
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (-((A * θ / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ)))
  let E : β → Set Ω := fun b => {ω | θ * (J : ℝ) ≤
    (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ)}
  have hE : { ω | ∃ b : β, θ * (J : ℝ) ≤
      (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ) } = ⋃ b : β, E b := by
    ext ω
    simp [E]
  have hbranch : ∀ b : β, P (E b) ≤ C := by
    intro b
    simpa [E, C] using
      (branch_many_bad_nodes J A θ hA hθ₀ hθ₁ Ω X P g hg_meas hg_indep
        (n b) (hn b) (failure b) (W b) (hW_meas b) (hW_prob b) (hfailure b))
  rw [hE]
  calc
    P (⋃ b : β, E b) ≤ ∑' b : β, P (E b) := measure_iUnion_le _
    _ ≤ ∑' b : β, C := ENNReal.tsum_le_tsum hbranch
    _ = (Fintype.card β : ℝ≥0∞) * C := by
      simp [tsum_fintype]


end SubdiffusiveProcess
