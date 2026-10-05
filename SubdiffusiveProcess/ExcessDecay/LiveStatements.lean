module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs

@[expose] public section

/-!
# The live-power finite-cutoff excess-decay statements

Propositions for the one-step excess decay on the finite-cutoff good event at the powers of
`l.excess.decay.good.scales.GMC` as printed in the live manuscript:
`s^{-3/2}` (the `ε`- and error-terms), `s^{-15/2}` (the source tail) and `s^{-3}` (the boundary
Hölder leg), to be compared with the weakened powers `s^{-2}, s^{-2}, s^{-8}, s^{-7/2}` of
`BoundaryCutoffHolderExcessDecayInputV4`.
-/

namespace SubdiffusiveProcess.ExcessDecayLive

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The full live-power finite-cutoff excess decay (third conjunct of
`SubdiffusiveProcess.Paper.cutoff_good_scale_input`), with no gate on the geometry. -/
def CutoffExcessDecayLive (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)


/-- The boundary-touching branch (`¬ translatedCube d (n-4) x ⊆ cube d m`) of the live excess
decay. -/
def CutoffExcessDecayBoundaryLive (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0)


/-- The containment branch (`translatedCube d (n-4) x ⊆ cube d m`) of the live excess decay. -/
def CutoffExcessDecayContainedLive (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M (some L) (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0) 
end

end SubdiffusiveProcess.ExcessDecayLive
