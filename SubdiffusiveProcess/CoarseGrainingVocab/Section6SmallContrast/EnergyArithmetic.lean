module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.CoefficientBounds

@[expose] public section

/-!
# Energy-test arithmetic for small contrast

The measure-theoretic weak test and Cauchy--Schwarz estimates feed the first
lemma below with three nonnegative energies.  This file performs the exact
Young/rearrangement step and retains the two printed factors `2`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

/-- Square-root form of the corrected energy test.  The source writes an
incorrect unit coercivity assertion; half-coercivity gives exactly this same
linear estimate without changing either displayed factor `2`. -/
theorem sqrt_energy_le_two_mul_of_half_energy_le
    {E H F delta : ℝ} (hE : 0 ≤ E) (_hH : 0 ≤ H) (_hF : 0 ≤ F)
    (hdelta : 0 ≤ delta)
    (hmain : E / 2 ≤
      delta * Real.sqrt E * Real.sqrt H + Real.sqrt F * Real.sqrt E) :
    Real.sqrt E ≤ 2 * delta * Real.sqrt H + 2 * Real.sqrt F := by
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hsH : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hsF : 0 ≤ Real.sqrt F := Real.sqrt_nonneg F
  have hsqE : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  by_cases hz : Real.sqrt E = 0
  · rw [hz]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hdelta) hsH)
      (mul_nonneg (by norm_num) hsF)
  · have hsEpos : 0 < Real.sqrt E := lt_of_le_of_ne hsE (Ne.symm hz)
    nlinarith



theorem harmonicComparison_energy
    {E H F I perturb forcing delta : ℝ}
    (hE : 0 ≤ E) (hH : 0 ≤ H) (hF : 0 ≤ F) (hdelta : 0 ≤ delta)
    (hcoercive : E / 2 ≤ I)
    (hidentity : I = -perturb - forcing)
    (hperturb : |perturb| ≤ delta * Real.sqrt E * Real.sqrt H)
    (hforcing : |forcing| ≤ Real.sqrt F * Real.sqrt E) :
    Real.sqrt E ≤ 2 * delta * Real.sqrt H + 2 * Real.sqrt F := by
  have hI : I ≤ |perturb| + |forcing| := by
    rw [hidentity]
    have hp := neg_le_abs perturb
    have hf := neg_le_abs forcing
    linarith
  have hmain : E / 2 ≤
      delta * Real.sqrt E * Real.sqrt H + Real.sqrt F * Real.sqrt E := by
    exact hcoercive.trans <| hI.trans (add_le_add hperturb hforcing)
  exact sqrt_energy_le_two_mul_of_half_energy_le hE hH hF hdelta hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
