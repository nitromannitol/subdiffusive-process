module

public import Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionDivergenceRhs
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.WeakEquationHelpers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.EnergyMinimality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ComparisonConvergence

@[expose] public section

/-! # Native variable-coefficient Dirichlet reflection through every cube face -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Odd reflection commutes with addition of vector data. -/
theorem oddReflectionVector_add {d : ℕ} (Q : TriadicCube d)
    (F G : Vec d → Vec d) :
    cubeDirichletOddReflectionVectorField Q (fun x => F x + G x) =
      fun x => cubeDirichletOddReflectionVectorField Q F x +
        cubeDirichletOddReflectionVectorField Q G x := by
  ext x i
  simp only [cubeDirichletOddReflectionVectorField,
    cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  ring

/-- A scalar multiplier is reflected evenly when its vector datum is reflected oddly. -/
theorem oddReflectionVector_scalar_mul {d : ℕ} (Q : TriadicCube d)
    (a : Vec d → ℝ) (G : Vec d → Vec d) :
    cubeDirichletOddReflectionVectorField Q (fun x => a x • G x) =
      fun x => a (cubeCoordinateFold Q x) •
        cubeDirichletOddReflectionVectorField Q G x := by
  ext x i
  simp only [cubeDirichletOddReflectionVectorField,
    cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul]
  ring

/-- The native scalar matrix equation is the scalar flux equation. -/
theorem matrix_scalar_weakEquation_iff {d : ℕ} {W : Set (Vec d)}
    (a : Vec d → ℝ) (u : H1Function W) (F : Vec d → Vec d) :
    IsMatrixDivFormWeakSolutionOn (scalarCoeffField a) W u F ↔
      ∀ phi : H10Function W,
        ∫ x in W, vecDot (a x • u.grad x) (phi.toH1Function.grad x) =
          -∫ x in W, vecDot (F x) (phi.toH1Function.grad x) := by
  simp only [IsMatrixDivFormWeakSolutionOn, scalarCoeffField,
    matVecMul_scalarMatrix]

/-- All-face odd reflection preserves a variable scalar divergence-form equation.
The coefficient is reflected evenly; the forcing and zero-trace unknown are
reflected oddly. The two `L²` premises are the natural weak-equation carriers. -/
theorem exists_harmonicCell_oddReflection {d : ℕ} {m : ℤ}
    (a : Vec d → ℝ) (u : H10Function (openCubeSet (originCube d m)))
    (F : Vec d → Vec d)
    (hflux : MemVectorL2 (openCubeSet (originCube d m))
      (fun x => a x • u.toH1Function.grad x))
    (hF : MemVectorL2 (openCubeSet (originCube d m)) F)
    (hu : IsMatrixDivFormWeakSolutionOn (scalarCoeffField a)
      (openCubeSet (originCube d m)) u.toH1Function F) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun = cubeDirichletOddReflectionScalar (originCube d m) u.toFun ∧
      uP.grad = cubeDirichletOddReflectionVectorField (originCube d m) u.grad ∧
      IsMatrixDivFormWeakSolutionOn
        (scalarCoeffField (fun x => a (cubeCoordinateFold (originCube d m) x)))
        (openCubeSet (originCube d (m + 1))) uP
        (cubeDirichletOddReflectionVectorField (originCube d m) F) := by
  let Q := originCube d m
  let W := openCubeSet Q
  let WP := openCubeSet (originCube d (m + 1))
  let H := fun x => a x • u.toH1Function.grad x + F x
  have hH : MemVectorL2 W H := hflux.add hF
  have hzero : ∀ phi : H10Function W,
      (0 : ℝ) * ∫ x in W, vecDot (u.toH1Function.grad x) (phi.grad x) =
        -∫ x in W, vecDot (H x) (phi.grad x) := by
    intro phi
    have heq := (matrix_scalar_weakEquation_iff a u.toH1Function F).mp hu phi
    have hsplit : (∫ x in W, vecDot (H x) (phi.grad x)) =
        (∫ x in W, vecDot (a x • u.toH1Function.grad x) (phi.grad x)) +
          ∫ x in W, vecDot (F x) (phi.grad x) := by
      simp only [H, vecDot_add_left]
      exact integral_add
        (Homogenization.integrableOn_vecDot_of_memVectorL2 hflux phi.toH1Function.grad_memVectorL2)
        (Homogenization.integrableOn_vecDot_of_memVectorL2 hF phi.toH1Function.grad_memVectorL2)
    rw [hsplit, heq]
    ring
  obtain ⟨uP, hval, hgrad, htest⟩ :=
    exists_h1Function_cubeDirichletOddReflectionParent_divergence_rhs_originCube hH hzero
  refine ⟨uP, hval, hgrad, ?_⟩
  let GP := cubeDirichletOddReflectionVectorField Q
    (fun x => a x • u.toH1Function.grad x)
  let FP := cubeDirichletOddReflectionVectorField Q F
  have hGP : MemVectorL2 WP GP :=
    memVectorL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField hflux
  have hFP : MemVectorL2 WP FP :=
    memVectorL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField hF
  have hGPid : GP = fun x => a (cubeCoordinateFold Q x) • uP.grad x := by
    dsimp only [GP]
    rw [oddReflectionVector_scalar_mul, hgrad]
  have hzeroP : ∀ phi : H10Function WP,
      ∫ x in WP, vecDot (GP x + FP x) (phi.grad x) =
        ∫ x in WP, (0 : ℝ) * phi.toFun x := by
    refine h10WeakEquationOn_of_contDiff_tests (isOpen_openCubeSet _)
      (hGP.add hFP) (by simp [MemScalarL2]) ?_
    intro phi hphi hcompact hsupp
    have h := htest phi hphi hcompact hsupp
    rw [show cubeDirichletOddReflectionVectorField Q H =
      (fun x => GP x + FP x) from oddReflectionVector_add Q _ _] at h
    simp only [zero_mul] at h
    simpa only [Pi.zero_apply, zero_mul, integral_zero] using (neg_eq_zero.mp h.symm)
  apply (matrix_scalar_weakEquation_iff _ uP _).mpr
  intro phi
  have h := hzeroP phi
  simp only [zero_mul, integral_zero] at h
  simp only [vecDot_add_left] at h
  rw [integral_add (Homogenization.integrableOn_vecDot_of_memVectorL2 hGP phi.toH1Function.grad_memVectorL2)
    (Homogenization.integrableOn_vecDot_of_memVectorL2 hFP phi.toH1Function.grad_memVectorL2), hGPid] at h
  linarith

/-- Subtracting the native boundary datum and reflecting its zero-trace
correction gives an interior equation through every face and corner. The
forcing is the reflected boundary flux, so no derivative of the coefficient
is introduced. -/
theorem exists_harmonicCell_boundaryReflection {d : ℕ} {m : ℤ}
    (a : Vec d → ℝ) (u h : H1Function (openCubeSet (originCube d m)))
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) (scalarCoeffField a))
    (hu : IsWeaklyHarmonicOn a (openCubeSet (originCube d m)) u)
    (htr : HasZeroTraceDifferenceOn (openCubeSet (originCube d m)) u h) :
    ∃ vP : H1Function (openCubeSet (originCube d (m + 1))),
      vP.toFun = cubeDirichletOddReflectionScalar (originCube d m)
        (fun x => u.toFun x - h.toFun x) ∧
      vP.grad = cubeDirichletOddReflectionVectorField (originCube d m)
        (fun x => u.grad x - h.grad x) ∧
      IsMatrixDivFormWeakSolutionOn
        (scalarCoeffField (fun x => a (cubeCoordinateFold (originCube d m) x)))
        (openCubeSet (originCube d (m + 1))) vP
        (cubeDirichletOddReflectionVectorField (originCube d m) (fun x => a x • h.grad x)) := by
  obtain ⟨v, hvval, hvgrad⟩ := htr
  have hvval' : v.toFun = fun x => u.toFun x - h.toFun x := by
    funext x
    have h := hvval x
    linarith
  have hvgrad' : v.grad = fun x => u.grad x - h.grad x := by
    funext x i
    have h := congrFun (hvgrad x) i
    simp only [Pi.add_apply] at h
    simp only [Pi.sub_apply]
    linarith
  have hvflux := Section6TheoremC.memVectorL2_smul_grad hEll v.toH1Function
  have hhflux := Section6TheoremC.memVectorL2_smul_grad hEll h
  have hv : IsMatrixDivFormWeakSolutionOn (scalarCoeffField a)
      (openCubeSet (originCube d m)) v.toH1Function (fun x => a x • h.grad x) := by
    apply (matrix_scalar_weakEquation_iff _ _ _).mpr
    intro phi
    have heq := hu phi
    have hsplit : (∫ x in openCubeSet (originCube d m),
        vecDot (a x • u.grad x) (phi.grad x)) =
        (∫ x in openCubeSet (originCube d m), vecDot (a x • h.grad x) (phi.grad x)) +
          ∫ x in openCubeSet (originCube d m), vecDot (a x • v.grad x) (phi.grad x) := by
      simp_rw [hvgrad, smul_add, vecDot_add_left]
      exact integral_add
        (Homogenization.integrableOn_vecDot_of_memVectorL2 hhflux phi.toH1Function.grad_memVectorL2)
        (Homogenization.integrableOn_vecDot_of_memVectorL2 hvflux phi.toH1Function.grad_memVectorL2)
    rw [hsplit] at heq
    linarith
  obtain ⟨vP, hval, hgrad, heq⟩ := exists_harmonicCell_oddReflection a v _ hvflux hhflux hv
  refine ⟨vP, ?_, ?_, heq⟩
  · simpa only [hvval'] using hval
  · simpa only [hvgrad'] using hgrad

end SubdiffusiveProcess.Static
