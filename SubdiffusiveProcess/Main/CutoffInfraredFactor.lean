module

public import SubdiffusiveProcess.Main.CutoffCoefficient

@[expose] public section

/-! # Separating the infrared multiplier

The cutoff coefficient factors into its zero-infrared coefficient and the
pointwise exponential infrared multiplier. No limiting assertion is made.
-/

namespace SubdiffusiveProcess

/-- The infrared potential acts by pointwise multiplication on every cutoff coefficient. -/
theorem cutoffCoefficient_infrared_factor {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H om N x =
      Real.exp (H om x) * cutoffCoefficient M (fun _ => 0) om N x := by
  unfold cutoffCoefficient cutoffPotential
  simp only [ContinuousMap.zero_apply, zero_add]
  rw [show H om x + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
        H om x + ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) by ring,
    Real.exp_add]
  ring

end SubdiffusiveProcess
