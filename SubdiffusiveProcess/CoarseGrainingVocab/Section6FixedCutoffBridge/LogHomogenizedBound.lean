import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJSupport
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The homogenized coefficient at cutoff `L` has nonpositive logarithm. -/
theorem log_ahom_nonpos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Real.log (ahom M L) ≤ 0 :=
  Real.log_nonpos (ahom_pos M L).le (ahom_le_one M L)

/-- The homogenized coefficient at cutoff `L` has logarithm at least
`-(L+1) * tauSq`, from the frozen (PROVED) reciprocal lower bound. -/
theorem neg_mul_tauSq_le_log_ahom (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    -(((L : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ Real.log (ahom M L) := by
  have hrec := SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L
  have hlog := Real.log_le_log (Real.exp_pos _) hrec
  rw [Real.log_exp] at hlog
  linarith [hlog]

/-- **The manuscript's `|log D_L|` bound (tex:9591-9592), proved.**

`|log (ahom M L)| <= (log 2 / 2) * delta^2 * (L+1)`.

No `DRAFT_SORRY` conclusion is used: the two-sided control comes from the PROVED
frozen reciprocal lower bound together with `ahom <= 1`, and the `delta^2`
conversion from `tauSq_le_delta_sq`. -/
theorem abs_log_ahom_le (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    |Real.log (ahom M L)| ≤
      (Real.log 2 / 2) * M.delta ^ 2 * ((L : ℝ) + 1) := by
  have hupper : Real.log (ahom M L) ≤ 0 := log_ahom_nonpos M L
  have hlower : -(((L : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
      Real.log (ahom M L) := neg_mul_tauSq_le_log_ahom M L
  have hL : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ (Real.log 2 / 2) * M.delta ^ 2 :=
    tauSq_le_delta_sq M
  have hscaled : ((L : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤
      (Real.log 2 / 2) * M.delta ^ 2 * ((L : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left htau hL
    linarith [this]
  rw [abs_le]
  constructor
  · linarith
  · linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
