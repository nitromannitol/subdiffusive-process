import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.RelativeVariation
import SubdiffusiveProcess.Lane3.Forms
import SubdiffusiveProcess.Lane3.UpperDensity
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Fine step of `mfd:lem-relvar`: the summation of the five contributions of the proof. All five bounds are retained; no lower bound on Mc or Cc is needed. The generalized statement remains open in phase 1. -/
theorem lem_relvar_sum
    (Sg Del Mc Cc nuB zeB T1 T2 T3 T4 T5 : ℝ)
    (hSg : 0 ≤ Sg) (hDel : 0 ≤ Del)
    (hnu : 0 ≤ nuB) (hze : 0 ≤ zeB)
    (h1 : |T1| ≤ Sg * Real.exp Sg * Del * nuB)
    (h2 : |T2| ≤ Sg * Real.exp Sg * (2 * Mc) * Real.sqrt (nuB * zeB))
    (h3 : |T3| ≤ Sg * Real.exp Sg * (Cc * Mc) * Real.sqrt (nuB * zeB))
    (h4 : |T4| ≤ Cc * Sg ^ 2 * Real.exp (Cc * Sg) *
      (Del * nuB + 2 * Real.sqrt (nuB * zeB)))
    (h5 : |T5| ≤ Cc * Sg * Real.exp (Cc * Sg) * Del * nuB) :
    |T1 + T2 + T3 + T4 + T5| ≤
      (Sg * Real.exp Sg + Cc * Sg ^ 2 * Real.exp (Cc * Sg) +
          Cc * Sg * Real.exp (Cc * Sg)) * (Del * nuB) +
        (Sg * Real.exp Sg * (2 * Mc + Cc * Mc) +
          2 * Cc * Sg ^ 2 * Real.exp (Cc * Sg)) * Real.sqrt (nuB * zeB) := by
  have b4 := abs_add_le T1 T2
  have b3 := abs_add_le (T1 + T2) T3
  have b2 := abs_add_le (T1 + T2 + T3) T4
  have b1 := abs_add_le (T1 + T2 + T3 + T4) T5
  linarith


end Paper
