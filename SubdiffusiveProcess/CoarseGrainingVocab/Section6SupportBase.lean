import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
import Homogenization.Ambient.Euclidean
import Homogenization.Book.Ch01.Definitions
import Homogenization.PDE.DirichletRHS
import Homogenization.Sobolev.Foundations.WeakHessianEuclidean
import Homogenization.Sobolev.Fractional.Definitions

/-!
# Mechanical support for the section 6 frozen surface

This module contains only carrier packaging and literal notation support.  The
meaning-carrying definitions are frozen one per file in
`SubdiffusiveProcess/Frozen/Section6/Defs/`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The centered paper cube at integer scale `m`. -/
def cube (d : ℕ) (m : ℤ) : Set (Vec d) :=
  openCubeSet (originCube d m)

/-- A translate of the centered paper cube. -/
def translatedCube (d : ℕ) (m : ℤ) (z : Vec d) : Set (Vec d) :=
  (fun x ↦ z + x) '' cube d m

/-- Weak `-div(a grad u)=f` on a set. -/
def IsScalarRhsWeakSolutionOn {d : ℕ} (a : CoeffField d) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  ∀ φ : H10Function W,
    ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
        (φ.toH1Function.grad x) ∂volume =
      ∫ x in W, f x * φ.toH1Function.toFun x ∂volume

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean
/-- `u-h ∈ H¹₀(W)`, represented by a zero-trace witness. -/
def HasZeroTraceDifferenceOn {d : ℕ} (W : Set (Vec d))
    (u h : H1Function W) : Prop :=
  ∃ w : H10Function W,
    (∀ x, u.toFun x = h.toFun x + w.toH1Function.toFun x) ∧
      ∀ x, u.grad x = h.grad x + w.toH1Function.grad x

/-- The scalar-forcing weak Dirichlet problem used by Theorem B. -/
def IsScalarDirichletSolutionOn {d : ℕ} (a : CoeffField d)
    (Q : TriadicCube d) (u h : H1Function (openCubeSet Q))
    (f : Vec d → ℝ) : Prop :=
  HasZeroTraceDifferenceOn (openCubeSet Q) u h ∧
    IsScalarRhsWeakSolutionOn a (openCubeSet Q) u f

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean
/-- Weak harmonicity for a scalar coefficient. -/
def IsWeaklyHarmonicOn {d : ℕ} (a : Vec d → ℝ) (W : Set (Vec d))
    (u : H1Function W) : Prop :=
  ∀ φ : H10Function W,
    ∫ x in W, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume = 0

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean
/-- Weak `-div(a grad u)=div g`, with the source weak sign. -/
def IsDivFormWeakSolutionOn {d : ℕ} (a : Vec d → ℝ) (W : Set (Vec d))
    (u : H1Function W) (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function W,
    ∫ x in W, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume =
      -∫ x in W, vecDot (g x) (φ.toH1Function.grad x) ∂volume

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean
/-- The divergence-forcing weak Dirichlet problem used by section 6. -/
def IsDirichletSolutionOn {d : ℕ} (a : Vec d → ℝ) (Q : TriadicCube d)
    (u h : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Prop :=
  HasZeroTraceDifferenceOn (openCubeSet Q) u h ∧
    IsDivFormWeakSolutionOn a (openCubeSet Q) u g

/-- Unnormalized `L²` size. -/
def l2Size {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f 2 (volume.restrict (openCubeSet Q))

/-- An `L²` vector field with the coordinate certificates needed by `H⁻¹`. -/
structure L2VectorField {d : ℕ} (Q : TriadicCube d) where
  toFun : Vec d → Vec d
  memLpCoord : ∀ i : Fin d,
    MemLp (fun x ↦ toFun x i) (ENNReal.conjExponent (2 : ENNReal))
      ((isOpenBoundedConvexDomain_openCubeSet Q).toBoundedMeasurableDomain
        (openCubeSet_nonempty Q)).normalizedVolume

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/NormalizedL2.lean
-- Adapted from Algsuperdiff/Section4/Support/NormalizedL2.lean
/-- The normalized real `L²` seminorm on an arbitrary window. -/
def normalizedL2On {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  Real.sqrt (volumeAverage W (fun x ↦ f x ^ 2))

/-- The normalized Euclidean `L²` seminorm of a vector field. -/
def vectorNormalizedL2On {d : ℕ} (W : Set (Vec d))
    (f : Vec d → Vec d) : ℝ :=
  normalizedL2On W (fun x ↦ Homogenization.euclideanNorm (f x))

/-- Scalar volume average on a window. -/
def averageOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  volumeAverage W f

/-- Coordinatewise vector volume average on a window. -/
def averageVecOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → Vec d) : Vec d :=
  fun i ↦ volumeAverage W (fun x ↦ f x i)

/-- Supremum norm of a scalar field on a window. -/
def supNormOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ W, r = |f x|}

/-- Supremum of the explicit Euclidean magnitude on a window. -/
def vectorSupNormOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → Vec d) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ W, r = Homogenization.euclideanNorm (f x)}

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean
/-- Euclidean Hölder-seminorm bound. -/
def HolderSeminormBoundOn {d : ℕ} (W : Set (Vec d)) (alpha K : ℝ)
    (f : Vec d → Vec d) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W,
    Homogenization.euclideanNorm (f x - f y) ≤
      K * Homogenization.euclideanNorm (x - y) ^ alpha

/-- The explicit Euclidean Hölder seminorm. -/
def holderSeminormOn {d : ℕ} (W : Set (Vec d)) (alpha : ℝ)
    (f : Vec d → Vec d) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
    r = Homogenization.euclideanNorm (f x - f y) /
      Homogenization.euclideanNorm (x - y) ^ alpha}

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Support/Dirichlet.lean
-- Adapted from Algsuperdiff/Section4/Support/Dirichlet.lean
/-- Membership in a Euclidean Hölder class on a window. -/
def MemHolder {d : ℕ} (W : Set (Vec d)) (alpha : ℝ)
    (f : Vec d → Vec d) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ HolderSeminormBoundOn W alpha K f

/-- Kernel for the paper's Euclidean `p = 2` fractional seminorm. -/
def fractionalKernel {d : ℕ} (s : ℝ) (f : Vec d → Vec d)
    (xy : Vec d × Vec d) : ℝ :=
  Homogenization.euclideanNorm (f xy.1 - f xy.2) /
    Homogenization.euclideanNorm (xy.1 - xy.2) ^ (s + (d : ℝ) / 2)

/-- Coordinate gradient of a potential shell, using its stored derivative. -/
def shellGradient {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (x : Vec d) : Vec d :=
  fun i ↦ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x (Pi.single i 1)

/-- The one-vector response at a translated scale cube. -/
def section6Response {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (cubeScale cutoff : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (z e : Vec d) : ℝ :=
  paperScalarProbe (originCube d (cubeScale : ℤ))
    (aCutoffFamily M cutoff (translatePotentialSample z ω)) (ahom M cutoff) e

/-- The local tail-coefficient average on a translated scale cube. -/
def tailAverage {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L m : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (W : Set (Vec d)) : ℝ :=
  volumeAverage W (tailCoefficient M L m ω)

/-- The section 6 error `ℰ_{s,∞,2}` on a translated centered cube. -/
def section6HomogenizationError {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) : ℝ :=
  (paperHomogenizationError (originCube d (m : ℤ)) (m : ℤ) s
    .infinity (.finite 2)
    (aCutoffFamily M L (translatePotentialSample z ω))
    (tailCoefficientCubeAverage M L m (translatePotentialSample z ω))).toReal

/-- Sum of the shells with indices in `[j+1,m]`. -/
def shellBlock {d : ℕ} (m j : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) : ℝ :=
  ∑ i ∈ Finset.Icc (j + 1) m, ω i x

/-- Membership of a point in the scale-`n` triadic grid. -/
def OnTriadicGrid {d : ℕ} (n : ℕ) (z : Vec d) : Prop :=
  ∀ i : Fin d, ∃ k : ℤ, z i = (3 : ℝ) ^ n * k

/-- Source indicator convention for a real random variable. -/
def indicatorValue {Ω : Type*} (E : Set Ω) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  if ω ∈ E then X ω else 0

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/SlopeStabilityEndpoints.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/SlopeStabilityEndpoints.lean
/-- Oscillation of a scalar function on a window. -/
def oscillationOn {d : ℕ} (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, r = |u x - u y|}

/-- The sigma-field generated by coefficient evaluations in a window. -/
def restrictedCoefficientSigma {d : ℕ} {Ω : Type*}
    (a : Ω → Vec d → ℝ) (B : Set (Vec d)) : MeasurableSpace Ω :=
  ⨆ x : B, MeasurableSpace.comap (fun ω ↦ a ω x) (borel ℝ)

/-- Literal closed-window/frontier contact. -/
def BoundaryTouches {d : ℕ} (W V : Set (Vec d)) : Prop :=
  closure W ∩ frontier V ≠ ∅

end

end SubdiffusiveProcess.CoarseGrainingVocab
