import MarkovProcess.Semigroup.Generator
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope

open MarkovProcess.Semigroup
open scoped NNReal RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Nash

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : StronglyContinuousContractionSemigroup H)

/-- Contractivity makes each orbit norm antitone. -/
theorem orbit_norm_antitone (f : H) : Antitone fun t : ℝ≥0 => ‖S t f‖ := by
  intro s t hst
  change ‖S t f‖ ≤ ‖S s f‖
  have heq : t = (t - s) + s := by exact (tsub_add_cancel_of_le hst).symm
  rw [heq, S.add_apply]
  exact S.norm_apply_le _ _

/-- The derivative of the squared orbit norm is twice the generator pairing. -/
theorem hasDerivAt_orbit_norm_sq (f : S.generatorDomain) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ => ‖S (Real.toNNReal r) (f : H)‖ ^ 2)
      (2 * ⟪S (Real.toNNReal s) (S.generator f), S (Real.toNNReal s) (f : H)⟫) s := by
  convert (S.hasDerivAt_operator_toNNReal f hs).norm_sq using 1
  rw [real_inner_comm]

/-- Dissipation on positive-time domain orbits follows directly from contractivity. -/
theorem orbit_energy_nonneg (f : S.generatorDomain) {s : ℝ} (hs : 0 < s) :
    0 ≤ -⟪S (Real.toNNReal s) (S.generator f), S (Real.toNNReal s) (f : H)⟫ := by
  have ha : Antitone (fun r : ℝ => ‖S (Real.toNNReal r) (f : H)‖ ^ 2) := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _) (orbit_norm_antitone S f (Real.toNNReal_mono hab)) 2
  have hn := (hasDerivAt_orbit_norm_sq S f hs).nonpos_of_antitone ha
  linarith

end SubdiffusiveProcess.Nash
