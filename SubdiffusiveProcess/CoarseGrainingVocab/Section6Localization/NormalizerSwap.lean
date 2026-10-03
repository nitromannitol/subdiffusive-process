module

public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The centered logarithmic annealed-normalizer error `rho_{m,n}` from Step 2. -/
def normalizerLogError (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m n : ℕ) : ℝ :=
  Real.log (ahom M n / ahom M m) -
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ)

/-- Display `e.rho.m.n.bound`, directly from the two annealed ordering clauses. -/
theorem abs_normalizerLogError_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m n : ℕ} (hnm : n < m) :
    |normalizerLogError M m n| ≤
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ) := by
  let u : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ)
  have hu : 0 ≤ u := mul_nonneg M.G4.tauSq_pos.le (by positivity)
  have hm : 0 < ahom M m := ahom_pos M m
  have hn : 0 < ahom M n := ahom_pos M n
  obtain ⟨hlower, hupper⟩ :=
    (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 M m n hnm
  have hratioPos : 0 < ahom M n / ahom M m := div_pos hn hm
  have hratioOne : 1 ≤ ahom M n / ahom M m :=
    (one_le_div₀ hm).2 hlower
  have hratioExp : ahom M n / ahom M m ≤ Real.exp (2 * u) := by
    rw [div_le_iff₀ hm]
    simpa only [u, mul_assoc] using hupper
  have hlogLower : 0 ≤ Real.log (ahom M n / ahom M m) :=
    Real.log_nonneg hratioOne
  have hlogUpper : Real.log (ahom M n / ahom M m) ≤ 2 * u := by
    rw [← Real.log_exp (2 * u)]
    exact Real.log_le_log hratioPos hratioExp
  rw [abs_le]
  dsimp [normalizerLogError, u] at hlogLower hlogUpper ⊢
  constructor <;> linarith

/-- The weak-order form of `abs_normalizerLogError_le`, including the zero gap. -/
theorem abs_normalizerLogError_le_of_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m n : ℕ} (hnm : n ≤ m) :
    |normalizerLogError M m n| ≤
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ) := by
  rcases hnm.eq_or_lt with rfl | hnm
  · simp [normalizerLogError]
  · exact abs_normalizerLogError_le M hnm

/-- The exact exponential form of the normalizer ratio. -/
theorem ahom_ratio_eq_exp_normalizerLogError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) :
    ahom M n / ahom M m =
      Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ) +
        normalizerLogError M m n) := by
  have hm : 0 < ahom M m := ahom_pos M m
  have hn : 0 < ahom M n := ahom_pos M n
  rw [normalizerLogError]
  conv_rhs =>
    congr
    ring_nf
  exact (Real.exp_log (div_pos hn hm)).symm

/-- Swap an arbitrary positive global normalizer to `ahom_n`, retaining the
paper's centered logarithmic error exactly. -/
theorem div_ahom_eq_div_ahom_mul_exp_neg_normalizerLogError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ)
    {b : ℝ} (_hb : 0 < b) :
    b / ahom M n = b / ahom M m *
      Real.exp (-(SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ) +
        normalizerLogError M m n)) := by
  have hm : 0 < ahom M m := ahom_pos M m
  have hn : 0 < ahom M n := ahom_pos M n
  have hratio := ahom_ratio_eq_exp_normalizerLogError M m n
  rw [Real.exp_neg, ← hratio]
  field_simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
