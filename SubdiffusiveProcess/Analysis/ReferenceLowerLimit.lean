module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

/-! A normalized lower coefficient survives a bounded change of reference scale.
The in-measure passage selects a common subsequence and retains the prefixSeq margin. -/
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A positive reference comparison converts a normalized coefficient lower bound. -/
theorem lower_coefficient_of_reference_le
    (A source reference factor cell : ℝ)
    (href : 0 < reference) (hfactor : 0 < factor) (hcell : 0 ≤ cell)
    (hsource : source ≤ reference * factor) (hA : cell / 2 ≤ A / reference) :
    (cell / (2 * factor)) * source ≤ A := by
  have hlow : (cell / 2) * reference ≤ A := (le_div_iff₀ href).mp hA
  calc
    (cell / (2 * factor)) * source ≤
        (cell / (2 * factor)) * (reference * factor) :=
      mul_le_mul_of_nonneg_left hsource (div_nonneg hcell (by positivity))
    _ = (cell / 2) * reference := by field_simp
    _ ≤ A := hlow

/-- In-measure lower coefficients and prefixSeq margins yield one subsequence with the lower bound in the desired reference scale. -/
theorem exists_seq_eventually_lower_coefficient_of_reference_prefix
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (A source reference prefixSeq : ℕ → Omega → ℝ) (Alim prefixLim : Omega → ℝ)
    (hA : TendstoInMeasure P (fun n om => A n om / reference n om) atTop Alim)
    (hprefix : TendstoInMeasure P prefixSeq atTop prefixLim)
    (tau cell budget : ℝ) (hcell : 0 < cell)
    (hratio : ∀ᵐ om ∂P, ∀ᶠ n in atTop,
      0 < reference n om ∧ source n om ≤ reference n om * Real.exp (tau + 2 * prefixSeq n om)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ ∀ᵐ om ∂P,
      cell ≤ Alim om → prefixLim om < budget →
      ∀ᶠ n in atTop, (cell / (2 * Real.exp (tau + 2 * budget))) * source (seq n) om ≤
        A (seq n) om := by
  obtain ⟨rho, hrho, hPrefixAE⟩ := hprefix.exists_seq_tendsto_ae
  obtain ⟨sigma, hsigma, hLowerAE⟩ :=
    (hA.comp hrho.tendsto_atTop).exists_seq_tendsto_ae
  let seq : ℕ → ℕ := fun n => rho (sigma n)
  have hseq : StrictMono seq := hrho.comp hsigma
  refine ⟨seq, hseq, ?_⟩
  filter_upwards [hPrefixAE, hLowerAE, hratio] with om hp ha hr
  intro hLower hBudget
  have hp' := hp.comp hsigma.tendsto_atTop
  have hLo : ∀ᶠ n in atTop, cell / 2 ≤ A (seq n) om / reference (seq n) om := by
    have hmargin : cell / 2 < Alim om := by linarith only [hcell, hLower]
    exact ((tendsto_order.1 ha).1 _ hmargin).mono (fun _ h => h.le)
  have hPre : ∀ᶠ n in atTop, prefixSeq (seq n) om < budget :=
    (tendsto_order.1 hp').2 _ hBudget
  have hRef : ∀ᶠ n in atTop,
      0 < reference (seq n) om ∧
        source (seq n) om ≤ reference (seq n) om * Real.exp (tau + 2 * prefixSeq (seq n) om) :=
    hseq.tendsto_atTop.eventually hr
  filter_upwards [hLo, hPre, hRef] with n hn hp hnref
  apply lower_coefficient_of_reference_le _ _ _ _ _ hnref.1 (Real.exp_pos _) hcell.le
    _ hn
  exact hnref.2.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith only [hp])) hnref.1.le)

end SubdiffusiveProcess
