module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452TransferEstimate

@[expose] public section

/-!
# P-452 seed (ii): `sobolevPathLiftGoal` and `pathLiftFromMaximalGoal`, both discharged

The two route targets of item (ii) of `ledger/reports/P-452-agent1.md` §4, restated **verbatim**
from the report (lines 557–575) so that the landed theorems are pinned against the target, and both
proved.

`pathLiftFromMaximalGoal_holds` is the implication B8 §2 plans.  `sobolevPathLiftGoal_holds` is the
unconditional statement, obtained by feeding it `maximalEstimateGoal_holds`
(`Packet452CylinderReversal.lean`), which seed (i) proved unconditionally.

## What the witness is

`Z := pathLift a.fn` where `a : RateApprox d U u` is **one** subsequence of
`global_sobolev_approximation`'s approximants chosen with the geometric `H¹` rate `4^{-k}`
(`exists_rateApprox`).  The four clauses are, in order:

| clause | theorem | B8 step |
| --- | --- | --- |
| `Measurable Z` | `measurable_pathLift` | 4 |
| fixed-time identity | `ae_pathLift_eq` | 5 |
| vanishing at the exit time | `ae_pathLift_exit` | 7 |
| transfer estimate, constant `32` | `lintegral_iSup_sq_sub_pathLift_le` | 8 |

## Departures from B8 §2, all recorded in the files where they occur

* Steps 2–3's **diagonal extraction over horizons is not needed**: the maximal estimate's constant
  is `32(‖φ‖₂² + T·E(φ))`, so one `H¹`-rate subsequence controls every horizon at once
  (`Packet452RateApprox.lean`).
* Step 2's **Borel–Cantelli is not needed**: Tonelli plus `ae_lt_top'` suffices, and that matters
  because the path measure is not finite (`Packet452SummableErrors.lean`).
* Step 4's **null-set caveat is discharged**, not carried: the good event is defined by the
  summability condition rather than by convergence, so it is measurable outright
  (`Packet452PathLiftConstruction.lean`); and `ae_pathMeasure_of_ae_forall` handles the one event
  that genuinely is not measurable -- the one involving `u.zeroExtension`, which is only
  `AEStronglyMeasurable` (`Packet452LiftIdentity.lean`).
* Step 5's **further subsequence is not needed** (`Packet452LiftIdentity.lean`).
* Step 8's **limit of the right-hand side is replaced by a one-sided majorant**, which removes a
  reverse triangle inequality that `ℝ≥0∞` does not support (`Packet452TransferEstimate.lean`).
* Step 6 (sequence independence) is, as B8 itself notes, not part of the existential witness; it is
  landed separately as `ae_eq_of_lintegral_iSup_sq_tendsto_zero` (`Packet452AeLimit.lean`).
-/

set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

/-- Restated verbatim from `ledger/reports/P-452-agent1.md:557-575`. -/
def sobolevPathLiftGoal (d : ℕ) : Prop :=
  ∀ U : Set (Vec d), IsOpen U → ∀ u : H10Function U,
    ∃ Z : ContinuousPath (Vec d) → ContinuousPath ℝ,
      Measurable Z ∧
      (∀ t : ℝ≥0, ∀ᵐ x ∂volume, ∀ᵐ omega ∂laplacianContinuousLaw d x,
        Z omega t = u.zeroExtension (omega t)) ∧
      (∀ᵐ x ∂volume.restrict U, ∀ᵐ omega ∂laplacianContinuousLaw d x,
        ContinuousPath.exitTime U omega ≠ ⊤ →
          Z omega ((ContinuousPath.exitTime U omega).toNNReal) = 0) ∧
      ∀ phi : Vec d → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi → ∀ T : ℝ≥0,
        (∫⁻ x, ∫⁻ omega, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((phi (omega t) - Z omega t) ^ 2))
            ∂laplacianContinuousLaw d x ∂volume) ≤
          ENNReal.ofReal (32 * ((∫ x, (phi x - u.zeroExtension x) ^ 2) + (T : ℝ) *
            ∫ x, ∑ i : Fin d,
              (fderiv ℝ phi x (Pi.single i 1) - u.zeroExtensionGrad x i) ^ 2))

/-- Restated verbatim from `ledger/reports/P-452-agent1.md:574-575`. -/
def pathLiftFromMaximalGoal (d : ℕ) : Prop :=
  maximalEstimateGoal d → sobolevPathLiftGoal d

/-- **P-452 seed (ii), the implication B8 §2 plans.** -/
theorem pathLiftFromMaximalGoal_holds (d : ℕ) : pathLiftFromMaximalGoal d := by
  intro hmax U hU u
  obtain ⟨a⟩ := exists_rateApprox hU u
  exact ⟨pathLift a.fn, measurable_pathLift a.fn,
    fun t => ae_pathLift_eq hmax hU a t,
    ae_pathLift_exit hmax hU a,
    fun phi hphi hphic T => lintegral_iSup_sq_sub_pathLift_le hmax hU a hphi hphic T⟩

/-- **P-452 seed (ii), unconditionally**, since seed (i) discharged `maximalEstimateGoal`. -/
theorem sobolevPathLiftGoal_holds (d : ℕ) : sobolevPathLiftGoal d :=
  pathLiftFromMaximalGoal_holds d (maximalEstimateGoal_holds d)

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
