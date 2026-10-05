module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDirichletCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import SubdiffusiveProcess.Section6.Defs.H2DatumNorm
@[expose] public section

/-!
Centered-cube pullback for unit-forcing torsion, with the amplitude
`alpha / (3^m)^2`. The carrier retains zero trace, and the zero boundary datum
has an explicit weak Hessian and vanishing frozen `H2Datum.norm`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

lemma goodCubeZeroH2Datum_weak_second {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    HasWeakPartialDerivOn (openCubeSet Q) j
      (fun x => (0 : H1Function (openCubeSet Q)).grad x i) 0 := by
  have h0 : HasWeakPartialDerivOn (openCubeSet Q) j (fun _ : Vec d => (0 : ℝ)) 0 := by
    simpa [Pi.zero_apply] using! HasWeakPartialDerivOn.of_contDiff (U := openCubeSet Q) (i := j)
      (f := fun _ : Vec d => (0 : ℝ)) contDiff_const
  have hf : (fun x => (0 : H1Function (openCubeSet Q)).grad x i) = fun _ : Vec d => (0 : ℝ) := by
    funext x
    simp [H1Function.zero_grad]
  rw [hf]
  exact h0

/-- Pull physical torsion to the unit cube with its unit-forcing amplitude. -/
noncomputable def goodCubeTorsionPullback {d : ℕ} {m : ℤ} (alpha : ℝ)
    (e : H10Function (openCubeSet (originCube d m))) :
    H10Function (openCubeSet (originCube d 0)) :=
  (alpha / centeredCubeScale m) • centeredCubeH10Pullback e

/-- The pullback has the exact value `alpha / R² * e(R x)`. -/
@[simp] theorem goodCubeTorsionPullback_toFun {d : ℕ} {m : ℤ} (alpha : ℝ)
    (e : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    (goodCubeTorsionPullback alpha e).toH1Function.toFun x =
      (alpha / (centeredCubeScale m) ^ 2) * e.toH1Function.toFun (centeredCubeScale m • x) := by
  change (alpha / centeredCubeScale m) *
    (centeredCubeH10Pullback e).toH1Function.toFun x = _
  rw [centeredCubeH10Pullback_toFun]
  simp only [div_eq_mul_inv, pow_two, mul_inv]
  ring

/-- The pullback gradient has amplitude `alpha / R`. -/
@[simp] theorem goodCubeTorsionPullback_grad {d : ℕ} {m : ℤ} (alpha : ℝ)
    (e : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    (goodCubeTorsionPullback alpha e).toH1Function.grad x =
      (alpha / centeredCubeScale m) • e.toH1Function.grad (centeredCubeScale m • x) := by
  change (alpha / centeredCubeScale m) •
    (centeredCubeH10Pullback e).toH1Function.grad x = _
  rw [centeredCubeH10Pullback_grad]

/-- The literal zero boundary datum, including its zero weak Hessian. -/
noncomputable def goodCubeZeroH2Datum {d : ℕ} (Q : TriadicCube d) : H2Datum Q :=
  { toH1 := 0
    weakHessian :=
      { hess := fun _ _ _ => (0 : ℝ)
        hess_memL2 := fun _ _ => MemLp.zero
        weak_second := fun i j => goodCubeZeroH2Datum_weak_second Q i j } }

/-- The zero boundary datum has the literal zero Sobolev representative. -/
@[simp] theorem goodCubeZeroH2Datum_toH1 {d : ℕ} (Q : TriadicCube d) :
    (goodCubeZeroH2Datum Q).toH1 = (0 : H1Function (openCubeSet Q)) := rfl

private lemma goodCubeZeroH2Datum_hess {d : ℕ} (Q : TriadicCube d) (i j : Fin d) :
    (goodCubeZeroH2Datum Q).weakHessian.hess i j = fun _ : Vec d => (0 : ℝ) := rfl

/-- Every term of the frozen norm vanishes for the zero boundary datum. -/
@[simp] theorem goodCubeZeroH2Datum_norm {d : ℕ} (Q : TriadicCube d) :
    (goodCubeZeroH2Datum Q).norm = 0 := by
  simp only [H2Datum.norm, goodCubeZeroH2Datum_toH1, goodCubeZeroH2Datum_hess,
    H1Function.zero_toFun, H1Function.zero_grad, Pi.zero_apply]
  simp [l2Size, eLpNorm_zero]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
