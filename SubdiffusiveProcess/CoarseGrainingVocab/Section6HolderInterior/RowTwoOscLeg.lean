import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationLegCompose
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneArithmetic

/-!
# Row 2's oscillation leg, from row 1's arithmetic

`interiorRowOne_arith` is stated on abstract reals: it takes the full-domain
estimate at top depth `m - 5`, the top-window transfer and the exponential
absorption, and returns the frozen row-1 shape.  Nothing in it is specific to a
grid-centred window.

Row 2 needs the same passage for the **off-grid** oscillation at the gate's
window scale.  `oscillationLeg_of_gridCentre` supplies exactly the same `hfull`
hypothesis with one extra factor `oscillationLegPrice d` on the right, so the
passage is reused verbatim by absorbing that factor into the ladder constant:
`Aexp := oscillationLegPrice d * Aexp` and `Cabs := oscillationLegPrice d * Cabs`.
Since `oscillationLegPrice d` is dimension-only, no gap-dependence enters and the
constant table is unchanged apart from that factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- **The row-1 passage applied to the off-grid oscillation.**  `oscJ` is the
oscillation on the gate's window at scale `jsel`, centred at the arbitrary base
point; `hfull` is the composed leg of `oscillationLeg_of_gridCentre`. -/
theorem interiorRowTwo_oscLeg {d : ℕ}
    {alpha jsel n m Aexp Cabs Kforce exponential oscJ oscTop global data : ℝ}
    (halpha : alpha ≤ 1) (hjm : jsel ≤ m)
    (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (hAexp : 0 ≤ Aexp) (hKforce : 0 ≤ Kforce) (hexponential : 0 ≤ exponential)
    (hCabs : 0 ≤ Cabs)
    (habs : Aexp ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - jsel) / 4))
    (htop : oscTop ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global)
    (hfull : (3 : ℝ) ^ (-jsel) * oscJ ≤
      oscillationLegPrice d *
        (Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
          5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
            ((3 : ℝ) ^ (m / 2) * data)))) :
    (3 : ℝ) ^ (alpha * (n - jsel)) * oscJ ≤
      rowOneConst d (oscillationLegPrice d * Cabs) Kforce exponential *
        (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  have hprice : 0 ≤ oscillationLegPrice d := oscillationLegPrice_nonneg d
  refine interiorRowOne_arith (d := d) (alpha := alpha) (ell := jsel) (n := n)
    (m := m) (Aexp := oscillationLegPrice d * Aexp)
    (Cabs := oscillationLegPrice d * Cabs) (Kforce := Kforce)
    (exponential := exponential) (oscEll := oscJ) (oscTop := oscTop)
    (global := global) (data := data)
    halpha hjm hglobal hdata (mul_nonneg hprice hAexp) hKforce hexponential
    (mul_nonneg hprice hCabs) ?_ htop ?_
  · calc oscillationLegPrice d * Aexp
        ≤ oscillationLegPrice d *
          (Cabs * (3 : ℝ) ^ ((1 - alpha) * (m - jsel) / 4)) :=
          mul_le_mul_of_nonneg_left habs hprice
      _ = oscillationLegPrice d * Cabs *
          (3 : ℝ) ^ ((1 - alpha) * (m - jsel) / 4) := by ring
  · calc (3 : ℝ) ^ (-jsel) * oscJ
        ≤ oscillationLegPrice d *
          (Aexp * ((3 : ℝ) ^ (-(m - 5)) * oscTop +
            5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
              ((3 : ℝ) ^ (m / 2) * data))) := hfull
      _ = oscillationLegPrice d * Aexp *
          ((3 : ℝ) ^ (-(m - 5)) * oscTop +
            5 / 2 * Kforce * (3 : ℝ) ^ (-(5 / 2 : ℝ)) * exponential *
              ((3 : ℝ) ^ (m / 2) * data)) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
