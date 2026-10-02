import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

/-!
# Moment transfer for the suffix-measurable cutoff-change representative

P-23 selected an everywhere-measurable suffix representative and proved its
almost-everywhere equality with the field representative from shell
sensitivity.  This module transfers the already-proved lognormal moment bound
to that selected representative.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization

noncomputable section

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Provider/Diffusivity/ApproximateRecurrence/PrincipalResponseLegsIndep.lean
theorem cutoffChangeSuffixRepresentative_moment
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (k : ℤ) (p : ℝ) (hp : 1 ≤ p) :
    let A := shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ))
    Integrable (fun omega => cutoffChangeSuffixRepresentative n k omega ^ p)
        M.P.toMeasure ∧
    (∫ omega, cutoffChangeSuffixRepresentative n k omega ^ p
        ∂M.P.toMeasure) ^ p⁻¹ ≤
      2 * Homogenization.Book.Ch04.gammaMomentConst 2 * Real.sqrt (2 * p) * A *
        Real.exp (p * A ^ 2) := by
  dsimp only
  have hsource := infraredhom_approx_cutoffs_large_waves_field M n k p hp
  have heq : (fun omega => cutoffChangeSuffixRepresentative n k omega ^ p) =ᵐ[M.P.toMeasure]
      fun omega => (Real.exp (sensitivityFieldRepresentative n k omega) - 1) ^ p := by
    filter_upwards
      [ae_suffixSensitivityRealRepresentative_eq_sensitivityFieldRepresentative M n k]
      with omega homega
    simp only [cutoffChangeSuffixRepresentative, homega]
  constructor
  · exact hsource.1.congr heq.symm
  · rw [integral_congr_ae heq]
    exact hsource.2.1

end

end SubdiffusiveProcess.CoarseGrainingVocab
