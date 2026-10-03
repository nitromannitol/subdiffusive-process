module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProfileReadout

@[expose] public section

/-!
# Finite assembly of the depth-two cell cover

The manuscript partitions a comparison cube into its `9^d` depth-two
descendants.  Because `descendantsAverage` already contains the reciprocal
cardinality, a common cell bound passes to the parent without an additional
dimension factor.

PROVENANCE: this is the fixed-cover averaging step in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A uniform bound on every depth-two descendant controls their normalized
finite average with no cardinality loss. -/
theorem descendantsAverage_depthTwo_le_of_forall
    (Q : TriadicCube d) (F : TriadicCube d → ℝ) (B : ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q 2, F R ≤ B) :
    descendantsAverage Q 2 F ≤ B := by
  calc
    descendantsAverage Q 2 F ≤
        descendantsAverage Q 2 (fun _ ↦ B) :=
      descendantsAverage_le_descendantsAverage Q 2 hF
    _ = B := descendantsAverage_const_eq Q 2 B

/-- The exact depth-two decomposition followed by a uniform physical-cell
bound.  This is the deterministic finite-cover seam used by the local PDE
energy assembly. -/
theorem normalizedCutoffEnergy_translatedCube_le_of_depthTwo_cell_bounds
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m k : ℤ} {y : Vec d}
    (u : H1Function (openCubeSet (originCube d m)))
    (hparent : translatedCube d k y ⊆ openCubeSet (originCube d m))
    (B : ℝ)
    (hcell : ∀ R ∈ descendantsAtDepth (originCube d k) 2,
      normalizedSetAverage (translateSet y (openCubeSet R)) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤ B) :
    normalizedSetAverage (translatedCube d k y) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤ B := by
  rw [cutoffEnergy_translatedCube_eq_depthTwoDescendantsAverage
    M L omega u hparent]
  exact descendantsAverage_depthTwo_le_of_forall
    (originCube d k) _ B hcell

/-- A depth-two cover may be split cellwise into an interior and a boundary
branch.  Keeping the two bounds separate here is useful because the boundary
branch is priced only after the affine/residual datum decomposition. -/
theorem normalizedCutoffEnergy_translatedCube_le_max_of_depthTwo_split
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m k : ℤ} {y : Vec d}
    (u : H1Function (openCubeSet (originCube d m)))
    (hparent : translatedCube d k y ⊆ openCubeSet (originCube d m))
    (interior : TriadicCube d → Prop) (Binterior Bboundary : ℝ)
    (hinterior : ∀ R ∈ descendantsAtDepth (originCube d k) 2,
      interior R →
      normalizedSetAverage (translateSet y (openCubeSet R)) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
          Binterior)
    (hboundary : ∀ R ∈ descendantsAtDepth (originCube d k) 2,
      ¬ interior R →
      normalizedSetAverage (translateSet y (openCubeSet R)) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
          Bboundary) :
    normalizedSetAverage (translatedCube d k y) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      max Binterior Bboundary := by
  apply normalizedCutoffEnergy_translatedCube_le_of_depthTwo_cell_bounds
    M L omega u hparent
  intro R hR
  by_cases h : interior R
  · exact (hinterior R hR h).trans (le_max_left _ _)
  · exact (hboundary R hR h).trans (le_max_right _ _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
