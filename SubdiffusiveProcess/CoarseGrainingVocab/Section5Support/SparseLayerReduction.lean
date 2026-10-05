module

public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational

@[expose] public section

/-!
# Sparse-layer reduction for the strict-decay proposition

Step 4 of the strict-decay proof  produces its
bound through the sparse index `N = floor(m / R)` only: the full coefficient is
compared with the sparse product `A_N^{(R)}`, and the sparse induction
`e.strict.decay.sparse.induction` supplies `q_R^{N+1}`.  The dependence on `m`
beyond `floor(m / R)` is therefore vacuous.

This file isolates that observation.  Given the bound at the sparse indices
`N * R` alone, monotonicity of the infinite-volume coefficient in the cutoff
(`ahom_antitone_cutoff`, proved) recovers the printed estimate at every `m`.
The remaining premise is thereby narrowed to a family indexed by the sparse
layer count, which is exactly the object the paper's induction constructs.

The file also records the deterministic selection performed in Step 2 : once the conforming piecewise-affine energies
converge to a limit below one, some positive integer spacing already lies
below one.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Non-strict form of the proved cutoff monotonicity. -/
theorem ahom_le_ahom_of_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ}
    (hnm : n ≤ m) : ahom M m ≤ ahom M n := by
  rcases eq_or_lt_of_le hnm with rfl | hlt
  · exact le_rfl
  · exact ahom_antitone_cutoff M hlt

/-- **Sparse-index reduction.**  A geometric bound on the sparse subsequence
`m = N * R` already gives the printed bound `q^(floor(m/R)+1)` at every cutoff,
because `ahom` is nonincreasing and `(m / R) * R <= m`. -/
theorem ahom_le_pow_div_of_sparse_index
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {q : ℝ} {R : ℕ}
    (hsparse : ∀ N : ℕ, ahom M (N * R) ≤ q ^ (N + 1)) (m : ℕ) :
    ahom M m ≤ q ^ (m / R + 1) :=
  le_trans (ahom_le_ahom_of_le M (Nat.div_mul_le_self m R)) (hsparse (m / R))

/-- **Step 2 selection.**  If the conforming piecewise-affine constants
converge to a limit strictly below one, then some positive spacing is already
strictly below one.  This is the deterministic content. -/
theorem exists_pos_index_lt_one_of_tendsto {qs : ℕ → ℝ} {L : ℝ}
    (hlim : Filter.Tendsto qs Filter.atTop (nhds L)) (hL : L < 1)
    (hpos : ∀ R : ℕ, 0 < qs R) :
    ∃ R : ℕ, 0 < R ∧ 0 < qs R ∧ qs R < 1 := by
  have hev : ∀ᶠ R : ℕ in Filter.atTop, qs R < 1 :=
    hlim.eventually (eventually_lt_nhds hL)
  obtain ⟨R, hR⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨R, hR.2, hpos R, hR.1⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
