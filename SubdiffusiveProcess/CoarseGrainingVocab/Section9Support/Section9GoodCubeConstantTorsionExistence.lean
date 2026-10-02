import SubdiffusiveProcess.CoarseGrainingVocab.DirichletScalarForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
/-! Constant-coefficient zero-trace torsion from the scalar Dirichlet solver. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A positive constant coefficient admits an actual zero-trace unit-forcing solution. -/
theorem goodCube_exists_constantTorsion
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ u : H10Function (openCubeSet Q),
      IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0
        (openCubeSet Q) u.toH1Function (fun _ => 1) := by
  have hW := isOpenBoundedConvexDomain_openCubeSet Q
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    hW.isFiniteMeasure_restrict_volume
  have hf : MemLp (fun _ : Vec d => (1 : ℝ)) 2 (volume.restrict (openCubeSet Q)) :=
    memLp_const 1
  obtain ⟨v, hv⟩ := exists_isScalarDirichletSolutionOn
    (isEllipticFieldOn_scalarCoeffField_const hW.isOpen.measurableSet hsigma)
    (0 : H1Function (openCubeSet Q)) hf
  obtain ⟨w, hval, hgrad⟩ := hv.1
  have hgrad' : v.grad = w.toH1Function.grad := by
    funext x
    simpa only [H1Function.zero_grad, Pi.zero_apply, zero_add] using hgrad x
  refine ⟨w, ?_⟩
  unfold IsMassiveWeakSolutionOn
  intro phi
  have h := hv.2 phi
  rw [hgrad'] at h
  simpa only [scalarCoeffField, matVecMul_scalarMatrix, zero_mul, zero_add, one_mul] using h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
