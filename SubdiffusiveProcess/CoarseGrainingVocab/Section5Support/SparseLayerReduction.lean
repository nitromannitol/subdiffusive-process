import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Non-strict form of the proved cutoff monotonicity. -/
theorem ahom_le_ahom_of_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n m : ℕ}
    (hnm : n ≤ m) : ahom M m ≤ ahom M n := by
  rcases eq_or_lt_of_le hnm with rfl | hlt
  · exact le_rfl
  · exact ahom_antitone_cutoff M hlt

/-- **Sparse-index reduction.**  A geometric bound on the sparse subsequence
`m = N * R` already gives the printed bound `q^(floor(m/R)+1)` at every cutoff,
because `ahom` is nonincreasing and `(m / R) * R <= m`. -/
theorem ahom_le_pow_div_of_sparse_index
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {q : ℝ} {R : ℕ}
    (hsparse : ∀ N : ℕ, ahom M (N * R) ≤ q ^ (N + 1)) (m : ℕ) :
    ahom M m ≤ q ^ (m / R + 1) :=
  le_trans (ahom_le_ahom_of_le M (Nat.div_mul_le_self m R)) (hsparse (m / R))



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
