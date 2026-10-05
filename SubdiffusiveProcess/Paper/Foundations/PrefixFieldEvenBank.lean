module

public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldNumeric
public import SubdiffusiveProcess.PrefixFieldEvenNumeric

@[expose] public section

noncomputable section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper

/-- The exact finite bank under the coupled cutoff law has a fixed-even-order
norm bound linear in moment order and log cell count, independent of cutoff. -/
theorem prefix_eta_bank_raw_window_eLpNorm_even_linear {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j))
    (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
        aux_psf_sigma M) ((2 * q : ℕ) : ENNReal)
      (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * ((q : ℝ) + 1 + prefix_log_card d j)) := by
  have hb : 1 ≤ (q : ℝ) + 1 + prefix_log_card d j := by
    have hL := prefix_log_card_nonneg d j
    have hqcast : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hbank := prefix_eta_bank_raw_window_eLpNorm
    M eta hEta N m j i hi z q hq
  have hroot := prefix_even_root_le_linear
    ((q : ℝ) + 1 + prefix_log_card d j) hb q hq
  exact hbank.trans (by simpa only [prefix_log_card] using hroot)


end SubdiffusiveProcess.Paper
