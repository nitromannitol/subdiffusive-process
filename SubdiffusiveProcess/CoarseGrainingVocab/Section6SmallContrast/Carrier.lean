module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Carrier
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Sobolev.Foundations.Cutoff.Euclidean

@[expose] public section

/-!
# Carriers for the small-contrast Schauder estimate

The analytic core is stated on the explicit Euclidean balls
`Homogenization.euclideanBall`.  This choice is substantive: normalized
Dirichlet energy of a harmonic function is monotone on concentric Euclidean
balls, giving the coefficient `1` in the contraction.  Replacing the balls by
sup-norm cubes at this point would spend a dimension factor before the
perturbative term and destroy the contraction as `alpha` tends to one.

The eventual coefficient-sigma-field consumer uses scalar coefficients on
cubes.  It is reached by a separate scalar and ball/cube wrapper; the theorem
family here keeps the source's matrix-valued coefficient and ball geometry.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- Weak `-div(a grad u) = div f` on an arbitrary window, with the source's
sign convention. -/
def IsMatrixDivFormWeakSolutionOn (a : CoeffField d) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function W,
    ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
      -∫ x in W, vecDot (f x) (phi.toH1Function.grad x) ∂volume

/-- The source's `L^infinity` distance of the coefficient from the identity,
written as an a.e. operator-norm bound. -/
def CoefficientIdentityDistanceLE (W : Set (Vec d)) (a : CoeffField d)
    (delta : ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict W,
    matrixOperatorNorm (a x - (1 : Mat d)) ≤ delta

/-- The real-valued Euclidean `L^p` size of a vector field. -/
def vectorLpSizeOn (W : Set (Vec d)) (p : ℝ) (f : Vec d → Vec d) : ℝ :=
  (SubdiffusiveProcess.RawLp.eLpNorm (fun x => euclideanNorm (f x)) (ENNReal.ofReal p)
    (volume.restrict W)).toReal

/-- Membership in the vector `L^p` carrier used by the source. -/
theorem vectorLpSizeOn_eq_guarded_of_aestronglyMeasurable
    {W : Set (Vec d)} {p : ℝ} {f : Vec d → Vec d}
    (hf : AEStronglyMeasurable (fun x => euclideanNorm (f x)) (volume.restrict W)) :
    vectorLpSizeOn W p f =
      (eLpNorm (fun x => euclideanNorm (f x)) (ENNReal.ofReal p)
        (volume.restrict W)).toReal := by
  exact congrArg ENNReal.toReal (SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf)

def MemVectorLpOn (W : Set (Vec d)) (p : ℝ) (f : Vec d → Vec d) : Prop :=
  MemLp (fun x => HilbertVec.ofVec (f x)) (ENNReal.ofReal p)
    (volume.restrict W)

/-- Euclidean Hölder control of a scalar representative. -/
def EuclideanHolderBoundOn (W : Set (Vec d)) (alpha K : ℝ)
    (v : Vec d → ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W,
    |v x - v y| ≤ K * euclideanNorm (x - y) ^ alpha

/-- The source exponent `p = d/(1-alpha)`. -/
def schauderSourceExponent (d : ℕ) (alpha : ℝ) : ℝ :=
  (d : ℝ) / (1 - alpha)

/-- The unit Euclidean ball in the project carrier. -/
def smallContrastUnitBall (d : ℕ) : Set (Vec d) :=
  euclideanBall 0 1

/-- The concentric Euclidean ball of radius `r`. -/
def smallContrastBall (d : ℕ) (r : ℝ) : Set (Vec d) :=
  euclideanBall 0 r

/-- The right-hand side of the Schauder estimate, with the sole
`(1-alpha)^{-1}` price exposed. -/
def smallContrastDataSize (d : ℕ) (alpha : ℝ)
    (u : H1Function (smallContrastUnitBall d)) (f : Vec d → Vec d) : ℝ :=
  vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad +
    (1 - alpha)⁻¹ *
      vectorLpSizeOn (smallContrastUnitBall d) (schauderSourceExponent d alpha) f

/-- The scale-invariant gradient row in the Schauder `C^α` estimate. -/
def HasSmallContrastGradientScaleBound (alpha K : ℝ)
    (u : H1Function (smallContrastUnitBall d)) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    r ^ (1 - alpha) * vectorNormalizedL2On (smallContrastBall d r) u.grad ≤ K

/-- Quotient-safe conclusion of the small-contrast Schauder theorem.  The
continuous representative is explicit, preventing any pointwise claim about
the arbitrary raw representative stored in `H1Function`. -/
def SmallContrastSchauderConclusion (alpha K : ℝ)
    (u : H1Function (smallContrastUnitBall d)) : Prop :=
  HasSmallContrastGradientScaleBound alpha K u ∧
    ∃ uRep : Vec d → ℝ,
      ContinuousOn uRep (smallContrastBall d (1 / 2)) ∧
      uRep =ᵐ[volume.restrict (smallContrastUnitBall d)] u.toFun ∧
      EuclideanHolderBoundOn (smallContrastBall d (1 / 2)) alpha K uRep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
