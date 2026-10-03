module

public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletScalarForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ComparisonConvergence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffDirichletExistence

@[expose] public section

/-! Existence for the divergence-form weak Dirichlet problem with a scalar elliptic coefficient. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open Homogenization hiding Vec
noncomputable section
namespace Paper

variable {d : ℕ}

/-- Existence of a weak solution with prescribed boundary datum and `L²` divergence-form source. -/
theorem lem_as_regularity_dirichlet_exists [NeZero d]
    {Q : Homogenization.TriadicCube d} {b : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) (scalarCoeffField b))
    (h : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ u : H1Function (openCubeSet Q), IsDirichletSolutionOn b Q u h g := by
  have hWgeom : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  have hne : (openCubeSet Q).Nonempty := nonempty_openCubeSet Q
  haveI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hWgeom.isFiniteMeasure_restrict_volume
  have hDatumFlux : MemVectorL2 (openCubeSet Q) (fun x => b x • h.grad x) :=
    memVectorL2_smul_grad hEll h
  have hG : MemVectorL2 (openCubeSet Q) (fun x => -g x - b x • h.grad x) :=
    hg.neg.sub hDatumFlux
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hWgeom
  have hG' : MemVectorL2 (openCubeSet Q)
      (fun x => -g x - matVecMul (scalarCoeffField b x) (h.grad x)) := by
    simpa only [scalarCoeffField, matVecMul_scalarMatrix] using hG
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := scalarCoeffField b) (U := openCubeSet Q)
      (g := fun x => -g x - matVecMul (scalarCoeffField b x) (h.grad x))
      (lam := lam) (Lam := Lam) hG' hRealize hne hEll
  refine ⟨h + w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, fun φ => ?_⟩
  have hDatumInt : IntegrableOn
      (fun x => vecDot (b x • h.grad x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hDatumFlux φ.toH1Function.grad_memVectorL2
  have hCorrFlux : MemVectorL2 (openCubeSet Q) (fun x => b x • w.toH1Function.grad x) :=
    memVectorL2_smul_grad hEll w.toH1Function
  have hCorrInt : IntegrableOn
      (fun x => vecDot (b x • w.toH1Function.grad x) (φ.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hCorrFlux φ.toH1Function.grad_memVectorL2
  have hgInt : IntegrableOn (fun x => vecDot (g x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hg φ.toH1Function.grad_memVectorL2
  have hgInt' : IntegrableOn (fun x => -vecDot (g x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    hgInt.neg
  have hsplit : (fun x => vecDot (b x • (h + w.toH1Function).grad x) (φ.toH1Function.grad x)) =
      fun x => vecDot (b x • h.grad x) (φ.toH1Function.grad x) +
        vecDot (b x • w.toH1Function.grad x) (φ.toH1Function.grad x) := by
    funext x
    simp [H1Function.add_grad, smul_add, vecDot_add_left]
  have hsub : (fun x => vecDot (matVecMul (scalarCoeffField b x) (w.toH1Function.grad x))
      (φ.toH1Function.grad x)) =
      fun x => vecDot (b x • w.toH1Function.grad x) (φ.toH1Function.grad x) := by
    funext x
    simp [scalarCoeffField, matVecMul_scalarMatrix]
  have hrhs : (fun x => vecDot (-g x - matVecMul (scalarCoeffField b x) (h.grad x))
      (φ.toH1Function.grad x)) =
      fun x => -vecDot (g x) (φ.toH1Function.grad x) -
        vecDot (b x • h.grad x) (φ.toH1Function.grad x) := by
    funext x
    simp [scalarCoeffField, matVecMul_scalarMatrix, sub_eq_add_neg, vecDot_add_left,
      vecDot_neg_left]
  have hwφ := hw φ
  simp only [IsZeroTraceDirichletRhsWeakSolution] at hwφ
  rw [hsub, hrhs, integral_sub hgInt' hDatumInt, integral_neg] at hwφ
  show ∫ x in openCubeSet Q, vecDot (b x • (h + w.toH1Function).grad x)
      (φ.toH1Function.grad x) ∂volume = _
  rw [hsplit, integral_add hDatumInt hCorrInt, hwφ]
  ring

end Paper
