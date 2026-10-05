module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Geometry

@[expose] public section

/-!
# The interior-branch conditional input for the interior Hölder ladder

`Section6Holder.HolderExcessDecayInput` transcribes the conclusion of
`l.excess.decay.good.scales.GMC` (version 3) verbatim.  That shape is
unusable on the interior branch for one reason only: it is stated for a
*Dirichlet pair* `IsDirichletSolutionOn (aCutoff M L ω) (□_m) u h g` together
with `MemHolder (□_m) (1/2) h.grad`, and the interior anchor
supplies no datum `h` at all
— that is precisely the point of the re-cut (no `H^{1/2}` trace
approximation exists in the source).

`InteriorHolderExcessDecayInput` below is the *interior branch* of that same
conclusion:

* the Dirichlet hypothesis is weakened to the printed weak-harmonicity
  `IsDivFormWeakSolutionOn (aCutoff M L ω) (cube d m) u g` — the re-cut;
* the datum hypothesis `MemHolder (□_m) (1/2) h.grad` is deleted;
* the window is required to be interior,
  `¬ BoundaryTouches (truncatedCube d m n x) (cube d m)`, which is what
  `Geometry.not_boundaryTouches_of_interior` supplies from an interior base
  point; and
* the two `BoundaryTouches` legs of the right-hand side are deleted, since the
  interior binder makes both of them literally `0`.

Every other binder, coefficient and carrier is byte-identical to
`Section6Holder.HolderExcessDecayInput`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The interior branch of `l.excess.decay.good.scales.GMC`
conclusion, with the Dirichlet pair replaced by the weak-harmonicity
hypothesis and both boundary legs deleted. -/
def InteriorHolderExcessDecayInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ ω,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
            (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M none (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                Real.sqrt (vecNormSq ell.slope) +
              C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
