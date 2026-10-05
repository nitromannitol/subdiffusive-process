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

namespace SubdiffusiveProcess.Paper

open Classical in
/-- **Lemma `l.concentration.rare.intervals`**.

Universal `c > 0`, `C < ∞` (proved with `c = 1/24`, `C = 100`).  `(ξ_i)_{i∈ℤ}` independent random elements, `λ > 0`; `E_{k,j}` events that depend
only on `ξ_i` with `i ∈ [k,k+j]`, or only on those with `i ∈ [k-j,k+j]` (same convention for all `k, j`), with
`P[E_{k,j}] ≤ e^{-λ(j+1)}`.  If `0 < θ ≤ 1` and `λθ ≥ C`, every integer interval `I` of cardinality `N ≥ 1` satisfies
`P[#{k ∈ I : E_{k,j} occurs for some j} ≥ θN] ≤ e^{-cλθN}`.  ("`E` depends only on `ξ_S`" is
`MeasurableSet[⨆_{i∈S} σ(ξ_i)] E`.)
Proof (`SubdiffusiveProcess.RareIntervals`): union bound for `j ≥ N`; greedy retention of separated intervals (total length `≥ θN/3`);
`≤ 2^{3N}` separated configurations in a window of `3N` integers (a separated family is determined by its union); independence
factorization for a fixed configuration; final arithmetic. -/
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
        convert h k j using 1 ; simp only [SubdiffusiveProcess.RareIntervals.Scheme.oneSided,
          Finset.mem_Icc, Set.mem_Icc]) lam hP θ hθ0 hθ1 hC a N hN
  · exact SubdiffusiveProcess.RareIntervals.rare_intervals_scheme
      SubdiffusiveProcess.RareIntervals.Scheme.centered hind' hm E
      (fun k j => by
        convert h k j using 1 ; simp only [SubdiffusiveProcess.RareIntervals.Scheme.centered, Finset.mem_Icc, Set.mem_Icc]) lam hP θ hθ0 hθ1 hC a N hN

end SubdiffusiveProcess.Paper
