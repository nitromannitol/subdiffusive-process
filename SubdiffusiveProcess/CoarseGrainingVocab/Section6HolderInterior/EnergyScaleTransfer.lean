import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.NeighbourGate

/-!
# Transferring the energy between scales at a fixed centre

The good-scale machinery does **not** deliver `goodEvent` at a prescribed scale.
`Section6Holder.exists_holderGoodScale_le_card` delivers it at a *selected*
scale `j + 2` with

```text
  n ≤ j ≤ n + card (holderBadNatScales …) ,
```

and the stopped failure row bounds that card by `≈ 1 + λ·(top - n)`.  So Step 6
at a neighbour is available at some scale `j` near `n`, not at `n` itself, and
row 2 — whose left-hand side is at scale `n` — needs to come down from `j` to
`n`.

At a fixed centre that is a plain window inclusion, so the landed cross-centre
restriction applies with both centres equal.  The price `3^{d(j-n+2)/2}` grows
with `j - n`, but `j - n ≲ 1 + λ(m-n)` and the factor is therefore of the same
`exp(Cλ(m-n))` type that `RowOneAbsorption.expAbar_mul_ratio_le` already absorbs
into the frozen gap gain — the same mechanism, reused.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **Energy scale transfer at a fixed centre.**  A smaller window's energy is
controlled by a larger window's, at the window volume ratio. -/
theorem vectorNormalizedL2On_scaleTransfer {m n j : ℤ} {y : Vec d}
    {f : Vec d → Vec d}
    (hy : y ∈ cube d m) (hnm : n - 1 ≤ m) (hjm : j - 1 ≤ m) (hnj : n ≤ j)
    (hint : IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2)
      (truncatedCube d m j y) volume) :
    vectorNormalizedL2On (truncatedCube d m n y) f ≤
      Real.sqrt (((3 : ℝ) ^ (j - n + 2)) ^ d) *
        vectorNormalizedL2On (truncatedCube d m j y) f := by
  have hsub : truncatedCube d m n y ⊆ truncatedCube d m j y :=
    truncatedCube_mono d m y hnj
  exact Section6Holder.normalizedL2On_truncatedCube_crossCentre_le
    (f := fun p => Homogenization.euclideanNorm (f p))
    hy hy hnm hjm hsub hint

/-- The scale-transfer price, as a function of the gap.  Recorded separately so
the absorption step can be stated against it. -/
def scaleTransferPrice (d : ℕ) (gap : ℤ) : ℝ :=
  Real.sqrt (((3 : ℝ) ^ (gap + 2)) ^ d)

theorem scaleTransferPrice_nonneg (d : ℕ) (gap : ℤ) :
    0 ≤ scaleTransferPrice d gap := Real.sqrt_nonneg _

/-- At gap `0` the price is the same `3^d` factor the same-scale cover pays. -/
theorem scaleTransferPrice_zero (d : ℕ) :
    scaleTransferPrice d 0 = Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) := by
  unfold scaleTransferPrice
  norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
