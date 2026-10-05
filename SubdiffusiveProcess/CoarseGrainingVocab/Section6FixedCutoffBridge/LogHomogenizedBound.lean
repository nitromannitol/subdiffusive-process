module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# Logarithmic control of the homogenized coefficient

`abs_log_ahom_le` proves
`|log (ahom M L)| ≤ (log 2 / 2) * M.delta² * (L + 1)`.
Its suppliers are `homogenized_coefficient_reciprocal_lower`, `ahom_le_one`
and `tauSq_le_delta_sq`. The sharp asymptotic theorem is not needed for this
fixed-cutoff estimate. Positivity of `ahom` justifies applying the logarithm.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The homogenized coefficient at cutoff `L` has nonpositive logarithm. -/
theorem log_ahom_nonpos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Real.log (ahom M L) ≤ 0 :=
  Real.log_nonpos (ahom_pos M L).le (ahom_le_one M L)

/-- The homogenized coefficient at cutoff `L` has logarithm at least
`-(L+1) * tauSq`, from the frozen (PROVED) reciprocal lower bound. -/
theorem neg_mul_tauSq_le_log_ahom (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    -(((L : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤ Real.log (ahom M L) := by
  have hrec := _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L
  have hlog := Real.log_le_log (Real.exp_pos _) hrec
  rw [Real.log_exp] at hlog
  linarith [hlog]

/-- **The manuscript's `|log D_L|` bound, proved.**

`|log (ahom M L)| <= (log 2 / 2) * delta^2 * (L+1)`.

The two-sided control comes from the reciprocal lower bound and
`ahom_le_one`, with the disorder conversion supplied by `tauSq_le_delta_sq`. -/
theorem abs_log_ahom_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    |Real.log (ahom M L)| ≤
      (Real.log 2 / 2) * M.delta ^ 2 * ((L : ℝ) + 1) := by
  have hupper : Real.log (ahom M L) ≤ 0 := log_ahom_nonpos M L
  have hlower : -(((L : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
      Real.log (ahom M L) := neg_mul_tauSq_le_log_ahom M L
  have hL : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ (Real.log 2 / 2) * M.delta ^ 2 :=
    tauSq_le_delta_sq M
  have hscaled : ((L : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
      (Real.log 2 / 2) * M.delta ^ 2 * ((L : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left htau hL
    linarith [this]
  rw [abs_le]
  constructor
  · linarith
  · linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
