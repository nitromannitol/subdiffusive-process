module

public import SubdiffusiveProcess.Paper.in_responses
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- The annealed ordering controls the deterministic `ahom` part of the
shallow-cell coefficient. The paper's `κ` also has an exponential normalizer. -/
theorem lem_as_coarse_shallow_grid_ahom_ratio
    (d : ℕ) [MeasurableSpace C(SubdiffusiveProcess.SpatialCoordinates d, ℝ)]
    [BorelSpace C(SubdiffusiveProcess.SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (N k : ℕ) (hkN : k ≤ N) :
    1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ∧
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) ∧
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) := by
  have hN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hmono : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) := by
    by_cases hk : k = 0
    · subst k
      simp
    · exact (Rm.ahom_ordering (N-k) N (by omega)).1
  have hupper : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
    by_cases hk : k = 0
    · subst k
      simp
    · have h := (Rm.ahom_ordering (N-k) N (by omega)).2
      have hcast : ((N-k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) :=
        Nat.cast_sub hkN
      rw [hcast] at h
      convert h using 1 <;> ring
  have hratioLower : 1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    (one_le_div₀ hN).2 hmono
  have hratioUpper : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) := by
    exact (div_le_iff₀ hN).2 hupper
  have hinv : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hratioLower
  have hexp : 1 ≤ Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) := by
    apply Real.one_le_exp
    exact mul_nonneg (mul_nonneg (by norm_num) M.G4.tauSq_pos.le) (by positivity)
  exact ⟨hratioLower, hratioUpper, hinv.trans hexp⟩


end Paper
