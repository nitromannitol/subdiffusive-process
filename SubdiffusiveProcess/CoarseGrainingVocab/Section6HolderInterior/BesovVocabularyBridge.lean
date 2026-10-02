import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.FractionalPoincareLeg

/-!
# The `q = 2` negative-Besov vocabulary seam

Step (1) of row 2's `hO` leg (`normalizedL2On_fluctuation_le_negativeBesovTwo`)
outputs `cubeBesovNegativeVectorSeminormTwo Q s F`, from the
`Deterministic/WeakNormInterfaces` layer.  Step (2)
(`Providers.Section2.coarsePoincareRaw`) consumes
`Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) F`, from the
`Book/Ch03` layer.

These are the **same quantity**.  Both unfold to a supremum over finite depths of
a partial family, and the two partial families are built from depth averages that
are *literally the same expression*,

```text
  descendantsAverage Q j fun R => vecNormSq (cubeAverageVec R F) ,
```

so the depth seminorms agree by `rfl` and only the `q = 2` packaging differs:
`Real.sqrt (∑ x ^ 2)` against `Real.rpow (∑ Real.rpow x 2) (1/2)`.

The seam therefore bridges by an identity, not by a `sSup`-monotonicity estimate
over a subfamily — so no constant is lost here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The two depth seminorms are the same function. -/
theorem cubeBesovNegativeVectorDepthSeminorm_eq (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s F j =
      Ch03.negativeBesovVectorDepthSeminorm Q s F j := rfl

/-- The finite-depth partial families agree at `q = 2`. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_eq (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (F : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N F =
      Ch03.negativeBesovVectorPartialNormFinite Q s 2 N F := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
    Ch03.negativeBesovVectorPartialNormFinite
  rw [Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [cubeBesovNegativeVectorDepthSeminorm_eq,
    ← Real.rpow_natCast (Ch03.negativeBesovVectorDepthSeminorm Q s F j) 2]
  norm_num

/-- **The seam, as an identity.**  No constant is lost crossing it. -/
theorem cubeBesovNegativeVectorSeminormTwo_eq_scaleNormalized
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    cubeBesovNegativeVectorSeminormTwo Q s F =
      Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 2) F := by
  unfold cubeBesovNegativeVectorSeminormTwo
    Ch03.scaleNormalizedNegativeBesovVectorNorm
  congr 1
  ext y
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N, (cubeBesovNegativeVectorPartialSeminormTwo_eq Q s N F).symm⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N, cubeBesovNegativeVectorPartialSeminormTwo_eq Q s N F⟩

/-- **Step (1) composed with the seam**: the oscillation is bounded by the
`Book/Ch03` scale-normalized negative Besov norm that `coarsePoincareRaw`
consumes. -/
theorem normalizedL2On_fluctuation_le_scaleNormalized [NeZero d]
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        normalizedL2On (openCubeSet Q)
          (fun y ↦ u.toFun y - volumeAverage (openCubeSet Q) u.toFun) ≤
      interiorFractionalPoincareConst d *
        Ch03.scaleNormalizedNegativeBesovVectorNorm Q (1 / 2 : ℝ)
          (.finite 2) u.grad := by
  have h := normalizedL2On_fluctuation_le_negativeBesovTwo Q u
  rwa [cubeBesovNegativeVectorSeminormTwo_eq_scaleNormalized] at h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
