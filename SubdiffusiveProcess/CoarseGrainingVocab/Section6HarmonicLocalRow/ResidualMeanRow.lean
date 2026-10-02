import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.FaceTiles
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.SlabMeanSplit

/-!
# The boundary residual mean with a free parameter

This is the capstone of the P-118 chain.  Composing

* the slab mean split
  (`SlabMeanSplit.sq_averageOn_le_slab_add_oscillation`), which trades the
  parent mean for the `L²` size on an interior slab plus the parent
  oscillation, and
* the face slab Poincare
  (`FaceTiles.volumeAverage_sq_faceInnerSlab_le`), which prices that slab term
  by the gradient with a constant proportional to `L²`,

gives the boundary residual scalar `|(u)_U - (h)_{P_q}|²` of
`ledger/reports/provider-37-harmonic-local-row.md` §2 in the shape the radius
recurrence consumes:

```text
(mean)^2  ≤  (free small factor) * (gradient energy)
            + (budget multiplier) * (parent oscillation)^2
```

The first coefficient is proportional to `L²`, and `L` is chosen freely — this
is the free Young parameter that the face-trace route was supposed to supply
and could not, there being no surface measure in either repository.  The second
coefficient is a pure volume ratio, which is what the four budgets absorb.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

theorem measurableSet_faceDoubledSlab (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ)
    (M : ℕ) : MeasurableSet (faceDoubledSlab j0 a b L M) :=
  MeasurableSet.iUnion fun _ => (isOpen_axisCube _ _).measurableSet

theorem measurableSet_faceInnerSlab (j0 : Fin d) (a : ℝ) (b : Vec d) (L : ℝ)
    (M : ℕ) : MeasurableSet (faceInnerSlab j0 a b L M) := by
  refine (measurableSet_faceDoubledSlab j0 a b L M).inter ?_
  exact measurableSet_lt measurable_const (measurable_pi_apply j0)

/-- **Boundary residual mean with a free parameter.**  The gradient term
carries `tilePoincareConst d L ^ 2`, proportional to `L²`, so it can be made
as small as required by shrinking the tile side; the oscillation term carries
only volume ratios. -/
theorem sq_averageOn_le_slabPoincare
    (j0 : Fin d) (a : ℝ) (b : Vec d) {L : ℝ} (hL : 0 < L) {M : ℕ}
    {P : Set (Vec d)} {f : Vec d → ℝ} {G : Vec d → Vec d}
    (hsub : faceInnerSlab j0 a b L M ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hSpos : 0 < (volume (faceInnerSlab j0 a b L M)).toReal)
    (hWpos : 0 < (volume (faceDoubledSlab j0 a b L M)).toReal)
    (hf : IntegrableOn f P) (hf2 : IntegrableOn (fun x ↦ f x ^ 2) P)
    (hH1 : ∀ k : FaceIndex d j0 M,
      ∃ v : H1Function (axisCube (faceTileCorner j0 a b L k) L),
        v.toFun = f ∧ v.grad = G)
    (hfzero : ∀ x : Vec d, x j0 < a → f x = 0)
    (hgW : IntegrableOn (fun x => vecNormSq (G x))
      (faceDoubledSlab j0 a b L M)) :
    averageOn P f ^ 2 ≤
      2 * ((tilePoincareConst d L ^ 2 * d) *
            ((volume (faceDoubledSlab j0 a b L M)).toReal /
              (volume (faceInnerSlab j0 a b L M)).toReal)) *
          volumeAverage (faceDoubledSlab j0 a b L M)
            (fun x => vecNormSq (G x))
        + 2 * ((volume P).toReal /
              (volume (faceInnerSlab j0 a b L M)).toReal) *
          normalizedL2On P (fun x ↦ f x - averageOn P f) ^ 2 := by
  have hsplit := sq_averageOn_le_slab_add_oscillation
    (P := P) (S := faceInnerSlab j0 a b L M) (f := f)
    (measurableSet_faceInnerSlab j0 a b L M) hsub hPtop hPpos hSpos hf hf2
  have hslab := volumeAverage_sq_faceInnerSlab_le j0 a b hL hH1 hfzero hgW
    hSpos hWpos
  have hsq : normalizedL2On (faceInnerSlab j0 a b L M) f ^ 2
      = volumeAverage (faceInnerSlab j0 a b L M) (fun x => f x ^ 2) := by
    unfold normalizedL2On
    exact Real.sq_sqrt (volumeAverage_sq_nonneg _ _)
  rw [hsq] at hsplit
  linarith [hsplit, hslab]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
