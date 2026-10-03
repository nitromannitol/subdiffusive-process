module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
public import SubdiffusiveProcess.Frozen.Section6.Defs.OrdinaryVectorHMinusOne
public import Homogenization.Book.Ch03.ABK26.FluxComparisonDefinitions
public import Homogenization.Sobolev.Foundations.CubeBesovPoincare.W12NormalizedPartition

@[expose] public section

/-!
# Literal difference-field carriers for the cutoff Dirichlet theorem

The Chapter-3 coarse-graining estimate packages its gradient and flux
differences on the physical cube.  This file pulls those genuine `L²`
carriers back to the unit cube and restores the manuscript dilation factors.
The resulting `L2VectorField`s have exactly the pointwise representatives
printed in the frozen Dirichlet conclusion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Forget the Euclidean `L²` packaging while retaining all coordinatewise
certificates used by the ordinary vector `H⁻¹` carrier. -/
noncomputable def cubeEuclideanL2FieldToL2VectorField {d : ℕ}
    (Q : TriadicCube d)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) : L2VectorField Q where
  toFun := F.toField
  memLpCoord := by
    have hF := F.euclideanMemLp
    rw [memLp_piLp_iff] at hF
    intro i
    have hconj : ENNReal.conjExponent (2 : ENNReal) = 2 :=
      ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ENNReal)) (q := (2 : ENNReal))
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply,
      FiniteLpExponent.two_exponent, hconj,
      openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      hF i

/-- Repackage the coordinatewise frozen `L²` carrier for use by the
Euclidean fractional-dual API. -/
noncomputable def l2VectorFieldToCubeEuclideanL2Field {d : ℕ}
    (Q : TriadicCube d) (F : L2VectorField Q) :
    CubeEuclideanLpField Q FiniteLpExponent.two where
  toField := F.toFun
  euclideanMemLp := by
    rw [memLp_piLp_iff]
    intro i
    have hconj : ENNReal.conjExponent (2 : ENNReal) = 2 :=
      ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ENNReal)) (q := (2 : ENNReal))
    have hFi := F.memLpCoord i
    rw [hconj,
      openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] at hFi
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply,
      FiniteLpExponent.two_exponent] using hFi

@[simp] theorem l2VectorFieldToCubeEuclideanL2Field_toField {d : ℕ}
    (Q : TriadicCube d) (F : L2VectorField Q) :
    (l2VectorFieldToCubeEuclideanL2Field Q F).toField = F.toFun :=
  rfl

/-- Pull a physical centered-cube `L²` carrier to the unit cube and multiply
by a deterministic amplitude. -/
noncomputable def scaledCenteredCubePullbackL2VectorField {d : ℕ}
    (m : ℤ) (c : ℝ)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two) :
    L2VectorField (originCube d 0) where
  toFun := fun x ↦ c • F.toField (centeredCubeScale m • x)
  memLpCoord := by
    intro i
    have hF := F.euclideanMemLp
    rw [memLp_piLp_iff] at hF
    have hFi : MemLp (fun x ↦ F.toField x i) 2
        (centeredCubeDomain d m).normalizedVolume := by
      simpa only [centeredCubeDomain, HilbertVec.ofVec, PiLp.toLp_apply,
        FiniteLpExponent.two_exponent,
        cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using hF i
    have hpull := hFi.comp_measurePreserving
      (centeredCubeDilationMeasurePreserving (d := d) m)
    have hconj : ENNReal.conjExponent (2 : ENNReal) = 2 :=
      ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ENNReal)) (q := (2 : ENNReal))
    simpa only [centeredCubeDomain, FiniteLpExponent.two_exponent,
      hconj, openCubeSet_boundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      HilbertVec.ofVec, PiLp.toLp_apply,
      Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      centeredCubeDilation] using! hpull.const_smul c

@[simp] theorem scaledCenteredCubePullbackL2VectorField_toFun {d : ℕ}
    (m : ℤ) (c : ℝ)
    (F : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    (x : Vec d) :
    (scaledCenteredCubePullbackL2VectorField m c F).toFun x =
      c • F.toField (centeredCubeScale m • x) :=
  rfl

/-- The literal unit-cube gradient difference, obtained from the physical
Chapter-3 carrier at cutoff scale `N`. -/
noncomputable def cutoffDirichletGradientDifference {d : ℕ}
    (N : ℕ) (u v : H1Function (openCubeSet (originCube d 0))) :
    L2VectorField (originCube d 0) :=
  scaledCenteredCubePullbackL2VectorField (N : ℤ) (centeredCubeScale (N : ℤ))
    (centeredCubeGradientDifferenceL2Field (N : ℤ)
      (centeredCubeRawDilation (N : ℤ) u)
      (centeredCubeRawDilation (N : ℤ) v))

@[simp] theorem cutoffDirichletGradientDifference_toFun {d : ℕ}
    (N : ℕ) (u v : H1Function (openCubeSet (originCube d 0))) (x : Vec d) :
    (cutoffDirichletGradientDifference N u v).toFun x =
      u.grad x - v.grad x := by
  simp only [cutoffDirichletGradientDifference,
    scaledCenteredCubePullbackL2VectorField_toFun,
    centeredCubeGradientDifferenceL2Field, centeredCubeRawDilation_grad]
  have hR : centeredCubeScale (N : ℤ) ≠ 0 := centeredCubeScale_ne_zero _
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hR,
    inv_mul_cancel₀ hR, one_smul]

/-- The literal unit-cube normalized flux difference.  Its `L²` certificate
is inherited from the physical cutoff `CoeffOn` carrier before pullback. -/
noncomputable def cutoffDirichletFluxDifference {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (u v : H1Function (openCubeSet (originCube d 0))) :
    L2VectorField (originCube d 0) :=
  scaledCenteredCubePullbackL2VectorField (N : ℤ)
    (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹)
    (centeredCubeFluxDifferenceL2Field (N : ℤ)
      ((aCutoffFamily M L omega).coeffOn (originCube d (N : ℤ)))
      (ahom M L)
      (centeredCubeRawDilation (N : ℤ) u)
      (centeredCubeRawDilation (N : ℤ) v))

@[simp] theorem cutoffDirichletFluxDifference_toFun {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (u v : H1Function (openCubeSet (originCube d 0))) (x : Vec d) :
    (cutoffDirichletFluxDifference M L N omega u v).toFun x =
      rescaledCutoffCoefficient M L N omega x • u.grad x - v.grad x := by
  simp only [cutoffDirichletFluxDifference,
    scaledCenteredCubePullbackL2VectorField_toFun,
    centeredCubeFluxDifferenceL2Field, centeredCubeRawDilation_grad,
    aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    matVecMul_scalarMatrix]
  have hR : centeredCubeScale (N : ℤ) ≠ 0 := centeredCubeScale_ne_zero _
  have ha : ahom M L ≠ 0 := (ahom_pos M L).ne'
  simp only [smul_sub, smul_smul]
  unfold rescaledCutoffCoefficient
  simp only [centeredCubeScale, zpow_natCast]
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply]
  field_simp [hR, ha]
  simp only [one_smul]

/-- Simultaneous theorem-facing packaging of the two literal difference
fields.  Later analytic estimates can choose these witnesses without exposing
any carrier-construction premise at the provider boundary. -/
theorem exists_cutoffDirichletDifferenceFields {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (u v : H1Function (openCubeSet (originCube d 0))) :
    ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
      (∀ x, gradDifference.toFun x = u.grad x - v.grad x) ∧
      (∀ x, fluxDifference.toFun x =
        rescaledCutoffCoefficient M L N omega x • u.grad x - v.grad x) := by
  refine ⟨cutoffDirichletGradientDifference N u v,
    cutoffDirichletFluxDifference M L N omega u v, ?_, ?_⟩
  · exact cutoffDirichletGradientDifference_toFun N u v
  · exact cutoffDirichletFluxDifference_toFun M L N omega u v

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
