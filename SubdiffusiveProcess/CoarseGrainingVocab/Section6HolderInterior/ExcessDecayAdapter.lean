module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ExcessDecayInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.InteriorWindows

@[expose] public section

/-!
# Adapter: the excess-decay argument's interior binder to the interior Hölder input

`InteriorHolderExcessDecayInput` states its interior hypothesis in the
`BoundaryTouches` form, because that is the form in which the frozen
excess-decay conclusion switches its boundary legs on and off.  The
excess-decay argument's own interior assembly
(`Section6ExcessDecay/AnchorInterior.lean`) instead scopes itself by the
*containment* binder `translatedCube d (n-4) x ⊆ cube d m`, which is the exact
scope of the interior Schauder producer.

`Section6ExcessDecay.boundaryTouches_of_not_translatedCube_subset` shows the two
are the same dichotomy, and in the direction that matters here the containment
binder is the *weaker* one: non-touching at scale `n` implies containment at
every scale `j ≤ n`.  Hence a containment-form interior export is a **stronger**
statement, and `interiorHolderExcessDecayInput_of_containmentForm` below turns
it into `InteriorHolderExcessDecayInput` in one application.

So whichever of the two binder styles the excess-decay argument exports when
`l.excess.decay.good.scales.GMC` seals on the interior branch, the interior
Hölder ladder is one term away.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Non-touching at scale `n` gives containment of every window cube at scale
`j ≤ n`.  This is the contrapositive of
`Section6ExcessDecay.boundaryTouches_of_not_translatedCube_subset`. -/
theorem translatedCube_subset_cube_of_not_boundaryTouches {m n j : ℤ} {x : Vec d}
    (hx : x ∈ cube d m) (hjn : j ≤ n)
    (hnot : ¬ BoundaryTouches (truncatedCube d m n x) (cube d m)) :
    translatedCube d j x ⊆ cube d m :=
  (translatedCube_mono x hjn).trans
    (Section6HarmonicApproximation.translatedCube_subset_domain_of_not_boundaryTouches
      hx hnot)

/-- `InteriorHolderExcessDecayInput` restated with the excess-decay argument's own
interior binder.  Identical in every other byte. -/
def InteriorHolderExcessDecayContainmentForm (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
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

/-- **The adapter.**  A containment-form interior export discharges the
interior Hölder ladder's premise. -/
theorem interiorHolderExcessDecayInput_of_containmentForm
    (h : InteriorHolderExcessDecayContainmentForm d) :
    InteriorHolderExcessDecayInput d := by
  obtain ⟨C, hC, hstep⟩ := h
  refine ⟨C, hC, ?_⟩
  intro M s hs epsilon hepsilon k hk L m n hkn hmL hnm x hx z hz hxz hint ω u g
    hsol hg ell hell
  exact hstep M s hs epsilon hepsilon k hk L m n hkn hmL hnm x hx z hz hxz
    (translatedCube_subset_cube_of_not_boundaryTouches hx (by omega) hint)
    ω u g hsol hg ell hell

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
