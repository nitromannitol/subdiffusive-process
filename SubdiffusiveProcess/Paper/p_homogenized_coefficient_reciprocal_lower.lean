module

public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Proposition `p.homogenized.coefficient.reciprocal.lower`.

Correspondence with the live paper statement: for the model `M` and every `m ∈ ℕ_0`,
`exp (-(m+1) τ²) ≤ ahom M m` (`τ² = tauSq M.P = log E exp g0(0)`). -/
theorem p_homogenized_coefficient_reciprocal_lower {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤ ahom M m
    := SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m

end Paper
