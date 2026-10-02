import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyIntegrability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyScaleTransfer

/-!
# The cover and the transfer, with their side conditions discharged

`vectorNormalizedL2On_offGrid_le_of_gridNeighbours` and
`vectorNormalizedL2On_scaleTransfer` are stated for a general vector field and
therefore carry the integrability binder.  At the weighted gradient
`sqrt (aCutoff M L omega) • u.grad` that binder is unconditionally true
(`integrableOn_weightedGrad_sq`), so both specialize to hypothesis-free forms.

These are the two shapes row 2's assembly actually consumes: the transfer moves
the energy gate's conclusion from the selected scale down to the cover scale, and
the cover moves it from the grid centres to the off-grid base point.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The weighted gradient field of a cutoff solution. -/
def weightedGrad (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) : Vec d → Vec d :=
  fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p

/-- **The scale transfer at the weighted gradient**, with no side condition. -/
theorem weightedGrad_scaleTransfer
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {m n j : ℤ} {y : Vec d}
    (u : H1Function (openCubeSet (originCube d m)))
    (hy : y ∈ cube d m) (hnm : n - 1 ≤ m) (hjm : j - 1 ≤ m) (hnj : n ≤ j) :
    vectorNormalizedL2On (truncatedCube d m n y) (weightedGrad M L omega u) ≤
      scaleTransferPrice d (j - n) *
        vectorNormalizedL2On (truncatedCube d m j y) (weightedGrad M L omega u) := by
  have h := vectorNormalizedL2On_scaleTransfer (d := d) (m := m) (n := n) (j := j)
    (y := y) (f := weightedGrad M L omega u) hy hnm hjm hnj
    (integrableOn_weightedGrad_sq M L omega m u j y)
  simpa [scaleTransferPrice] using h

/-- **The energy cover at the weighted gradient**, with no side condition. -/
theorem weightedGrad_offGrid_le_of_gridNeighbours
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (j m : ℕ) (x : Vec d)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) {N : ℝ}
    (hjm : j ≤ m) (hx : x ∈ cube d (m : ℤ))
    (hN : ∀ y ∈ gridNeighbours d j m x,
      vectorNormalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) y)
        (weightedGrad M L omega u) ≤ N)
    (hN0 : 0 ≤ N) :
    vectorNormalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) x)
        (weightedGrad M L omega u) ≤
      Real.sqrt (((gridNeighbours d j m x).card : ℝ) *
        ((3 : ℝ) ^ (2 : ℤ)) ^ d) * N :=
  vectorNormalizedL2On_offGrid_le_of_gridNeighbours d j m x
    (weightedGrad M L omega u) hjm hx
    (fun y ↦ integrableOn_weightedGrad_sq M L omega (m : ℤ) u (j : ℤ) y)
    hN hN0

/-- **Cover then transfer, composed.**  This is exactly the shape row 2's
assembly consumes: a uniform bound at the grid centres at the *selected* scale
`jsel` yields a bound at the off-grid base point at the *cover* scale `n`. -/
theorem weightedGrad_offGrid_le_of_neighbourBounds
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (n m : ℕ) (x : Vec d)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) {N : ℝ} {jsel : ℤ}
    (hnm : n ≤ m) (hx : x ∈ cube d (m : ℤ))
    (hjm : jsel - 1 ≤ (m : ℤ)) (hnj : (n : ℤ) ≤ jsel)
    (hmem : ∀ y ∈ gridNeighbours d n m x, y ∈ cube d (m : ℤ))
    (hN : ∀ y ∈ gridNeighbours d n m x,
      vectorNormalizedL2On (truncatedCube d (m : ℤ) jsel y)
        (weightedGrad M L omega u) ≤ N)
    (hN0 : 0 ≤ N) :
    vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
        (weightedGrad M L omega u) ≤
      Real.sqrt (((gridNeighbours d n m x).card : ℝ) *
          ((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (scaleTransferPrice d (jsel - (n : ℤ)) * N) := by
  have hn1m : (n : ℤ) - 1 ≤ (m : ℤ) := by
    have : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hnm
    omega
  refine weightedGrad_offGrid_le_of_gridNeighbours M L omega n m x u hnm hx
    ?_ ?_
  · intro y hy
    refine (weightedGrad_scaleTransfer M L omega u (hmem y hy) hn1m hjm hnj).trans ?_
    exact mul_le_mul_of_nonneg_left (hN y hy) (scaleTransferPrice_nonneg d _)
  · exact mul_nonneg (scaleTransferPrice_nonneg d _) hN0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
