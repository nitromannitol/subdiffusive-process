module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Probability.SummableComparison
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_tail
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_completion

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/--
Docstring tick list: `P` is a probability measure; `I` is countable; `Z` and
`L` are the measurable finite and limiting response families; `hTail` is the
limit-relative geometric tail supplied by
`prop_as_response_bank_limit_tail`, and measurability of the limit is supplied
by `prop_as_response_bank_limit_completion`. The almost-everywhere full-sequence
convergence conclusion is the Borel--Cantelli step in paper 4477--4478.
-/
theorem prop_as_response_bank_borel_cantelli
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Countable I]
    (Z : I → ℕ → Ω → ℝ) (L : I → Ω → ℝ)
    (hZ : ∀ i N, Measurable (Z i N))
    (hL : ∀ i, Measurable (L i))
    (hTail : ∀ i : I, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          P {ω |
                eps * L i ω +
                  Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |Z i N ω - L i ω|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) :
    ∀ᵐ ω ∂P, ∀ i : I,
      Tendsto (fun N : ℕ => Z i N ω) atTop (nhds (L i ω)) := by
  rw [ae_all_iff]
  intro i
  apply SubdiffusiveProcess.ae_tendsto_of_geometric_relative_comparison
  intro eps heps
  obtain ⟨Ce, ce, Ne, hCe, hce, hbound⟩ := hTail i eps heps
  refine ⟨Ce, hCe.le, (3 : ℝ) ^ (-ce), ?_, ?_, Ne, ?_⟩
  · exact Real.rpow_nonneg (by norm_num) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  · intro N hN
    have hpow : (3 : ℝ) ^ (-(ce * (N : ℝ))) =
        ((3 : ℝ) ^ (-ce)) ^ N := by
      convert (Real.rpow_mul_natCast (x := (3 : ℝ)) (by norm_num) (-ce) N) using 1 <;>
        ring
    calc
      P {ω |
          eps * (|L i ω| + 1) +
              Ce * ((3 : ℝ) ^ (-ce)) ^ N <
            |Z i N ω - L i ω|} ≤
          P {ω |
              eps * L i ω +
                  Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |Z i N ω - L i ω|} := by
            apply measure_mono
            intro ω hω
            have hthreshold : eps * L i ω + Ce * ((3 : ℝ) ^ (-ce)) ^ N ≤
                eps * (|L i ω| + 1) + Ce * ((3 : ℝ) ^ (-ce)) ^ N := by
              apply add_le_add_left
              apply mul_le_mul_of_nonneg_left
              · linarith [le_abs_self (L i ω)]
              · exact heps.le
            rw [hpow]
            exact lt_of_le_of_lt hthreshold hω
      _ ≤ ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) :=
        hbound N hN
      _ = ENNReal.ofReal (Ce * ((3 : ℝ) ^ (-ce)) ^ N) := by rw [hpow]

end Paper
