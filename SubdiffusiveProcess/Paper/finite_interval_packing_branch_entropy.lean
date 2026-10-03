module

public import SubdiffusiveProcess.Paper.lem_branch
public import SubdiffusiveProcess.Paper.finite_interval_packing_prefix_entropy
public import SubdiffusiveProcess.Probability.FiniteBranchUnion
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper



theorem finite_interval_packing_branch_entropy
    {Om : Type*} [MeasurableSpace Om]
    (P : Measure Om) [IsProbabilityMeasure P]
    (d H1 N J : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (gamma sigma : ℝ) (hgamma : 0 < gamma) (hsigma : 0 ≤ sigma)
    (events : (Fin J → OddGridIndex d (subdivisionHalfWidth H1)) → Set Om)
    (hEventsMeas : ∀ branch, MeasurableSet (events branch))
    (hbranch : ∀ branch,
      P (events branch) ≤
        ENNReal.ofReal (Real.exp (-(gamma * (J : ℝ)))))
    (hprefixEntropy :
      (d : ℝ) * (H1 : ℝ) * (J : ℝ) * Real.log 3 ≤ sigma * (N : ℝ))
    (hmargin : sigma * (N : ℝ) < gamma * (J : ℝ)) :
    ∃ Ceta ceta : ℝ, ∃ Bad : Set Om,
      0 < Ceta ∧ 0 < ceta ∧ MeasurableSet Bad ∧
      Bad = ⋃ branch, events branch ∧
      P Bad ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) := by
  let Bad : Set Om := ⋃ branch, events branch
  refine ⟨(3 : ℝ) ^ (N : ℝ), 1, Bad, ?_, one_pos,
    MeasurableSet.iUnion hEventsMeas, rfl, ?_⟩
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · have hprob : P Bad ≤ 1 := by
      calc
        P Bad ≤ P Set.univ := measure_mono (subset_univ Bad)
        _ = 1 := measure_univ
    calc
      P Bad ≤ 1 := hprob
      _ = ENNReal.ofReal ((3 : ℝ) ^ (N : ℝ) *
          (3 : ℝ) ^ (-(1 : ℝ) * (N : ℝ))) := by
        rw [← ENNReal.ofReal_one]
        congr 1
        have hneg : -(1 : ℝ) * (N : ℝ) = -(N : ℝ) := by ring
        rw [hneg, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        simp

end Paper

