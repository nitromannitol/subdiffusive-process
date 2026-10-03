module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ErrorStoppingDepthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit

@[expose] public section

/-!
# StoppingIndex

A measurable envelope of the first-failure depth gives an index in {-1,...,m}, with pathwise control and an exponential moment for the excess depth.
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

namespace SubdiffusiveProcess.Section6SumErrors

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

/-- Measurable version of the first-failure index, valid for every order. -/
def stoppingIndex {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℤ :=
  (m : ℤ) - (measurableNatEnvelope M.P.toMeasure
    (errorStoppingDepth M lam s m) (m + 1) omega : ℤ)

theorem errorStoppingDepth_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    errorStoppingDepth M lam s m omega ≤ m + 1 := by
  have hb := (errorStoppingIndex M none lam s m omega).property
  obtain ⟨hb0, hb1⟩ := hb
  unfold errorStoppingDepth
  omega

theorem measurable_stoppingIndex {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) : Measurable (stoppingIndex M lam s m) := by
  exact measurable_const.sub
    ((measurable_of_countable (fun n : ℕ => (n : ℤ))).comp
      (measurable_measurableNatEnvelope M.P.toMeasure
        (errorStoppingDepth M lam s m) (m + 1)))

theorem stoppingIndex_bounds {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    -1 ≤ stoppingIndex M lam s m omega ∧ stoppingIndex M lam s m omega ≤ (m : ℤ) := by
  have hb := measurableNatEnvelope_le M.P.toMeasure
    (errorStoppingDepth M lam s m) (m + 1) omega
  unfold stoppingIndex
  omega

theorem stoppingIndex_le_literal {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    stoppingIndex M lam s m omega ≤ errorStoppingIndex M none lam s m omega := by
  have hdom := le_measurableNatEnvelope (mu := M.P.toMeasure) (errorStoppingDepth_le M lam s m omega)
  have hb := (errorStoppingIndex M none lam s m omega).property
  obtain ⟨hb0, hb1⟩ := hb
  unfold stoppingIndex errorStoppingDepth at *
  omega

theorem sum_le_of_le_stoppingIndex {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (n : ℕ) (hn : (n : ℤ) ≤ stoppingIndex M lam s m omega)
    (z : Vec d) (hz : OnTriadicGrid n z) (hzc : z ∈ cube d m) :
    ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s omega ≤
      lam * ((m : ℝ) - (n : ℝ)) := by
  exact accumulatedError_sum_le_of_le_errorStoppingIndex M none lam s m n omega
    (hn.trans (stoppingIndex_le_literal M lam s m omega)) z hz hzc

theorem stoppingIndex_excess_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lam s : ℝ) (m : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    max ((m : ℝ) - (stoppingIndex M lam s m omega : ℝ) - 1) 0 =
      ((measurableNatEnvelope M.P.toMeasure
        (errorStoppingDepth M lam s m) (m + 1) omega - 1 : ℕ) : ℝ) := by
  let R := measurableNatEnvelope M.P.toMeasure (errorStoppingDepth M lam s m) (m + 1) omega
  change max ((m : ℝ) - (((m : ℤ) - (R : ℤ) : ℤ) : ℝ) - 1) 0 = ((R - 1 : ℕ) : ℝ)
  push_cast
  by_cases hR : 1 ≤ R
  · rw [Nat.cast_sub hR]
    have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
    rw [max_eq_left (by linarith)]
    ring
  · have hr : R = 0 := by omega
    rw [hr]
    norm_num

/-- Converts a tail with the precise one-step sentinel into the paper's
exponential-moment bound for the measurable index. -/
theorem lintegral_stoppingIndex_excess_le_of_tail {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lam s : ℝ) (m : ℕ)
    {A : ℝ} (hA : 0 < A)
    (htail : ∀ q : ℕ, 1 ≤ q →
      M.P.toMeasure.real {omega | q < errorStoppingDepth M lam s m omega} ≤
        2 * Real.exp (-((q : ℝ) / A))) :
    ∫⁻ omega, ENNReal.ofReal (Real.exp ((4 * A)⁻¹ *
      max ((m : ℝ) - (stoppingIndex M lam s m omega : ℝ) - 1) 0))
      ∂M.P.toMeasure ≤ 2 := by
  let R := measurableNatEnvelope M.P.toMeasure (errorStoppingDepth M lam s m) (m + 1)
  have hRm : Measurable R := measurable_measurableNatEnvelope _ _ _
  have hRtail : ∀ q : ℕ, 1 ≤ q →
      M.P.toMeasure.real {omega | q < R omega} ≤
        2 * Real.exp (-(((q : ℝ) + 1 - (1 : ℕ)) / A)) := by
    intro q hq
    have hle := measure_measurableNatEnvelope_tail_le M.P.toMeasure
      (errorStoppingDepth M lam s m) (m + 1) q
    have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hle
    exact hreal.trans (by simpa only [Nat.cast_one, add_sub_cancel_right, Measure.real] using! htail q hq)
  have hbound := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_one_of_nat_tail
    (mu := M.P.toMeasure) (h0 := 1) hA hRm hRtail
  have hfun : (fun omega => Real.exp ((4 * A)⁻¹ *
      max ((m : ℝ) - (stoppingIndex M lam s m omega : ℝ) - 1) 0)) =
      (fun omega => Real.exp (((4 * A)⁻¹ *
        max ((R omega - 1 : ℕ) : ℝ) 0) ^ (1 : ℝ))) := by
    funext omega
    rw [stoppingIndex_excess_eq, Real.rpow_one,
      max_eq_left (Nat.cast_nonneg _)]
  change (∫⁻ omega, ENNReal.ofReal ((fun omega => Real.exp ((4 * A)⁻¹ *
    max ((m : ℝ) - (stoppingIndex M lam s m omega : ℝ) - 1) 0)) omega)
    ∂M.P.toMeasure) ≤ 2
  rw [hfun]
  have hnn : ∀ omega, 0 ≤ Real.exp (((4 * A)⁻¹ *
      max ((R omega - 1 : ℕ) : ℝ) 0) ^ (1 : ℝ)) := fun _ => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hbound.1
    (Filter.Eventually.of_forall hnn)]
  exact (ENNReal.ofReal_le_ofReal hbound.2).trans (by norm_num)

end SubdiffusiveProcess.Section6SumErrors
