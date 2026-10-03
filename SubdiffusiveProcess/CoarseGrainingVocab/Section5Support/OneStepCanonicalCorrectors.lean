module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellW1pPackaging
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.H10Adjoint
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.EnergyDuality

@[expose] public section

/-!
# Canonical finite-volume correctors for the one-step shell

This file instantiates the literal shell forcing in the canonical constant-
coefficient Dirichlet and Neumann solvers.  It deliberately remains a
pointwise-in-the-sample statement: parameter measurability of these canonical
Sobolev-valued solution maps is a separate interface.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- The literal shell datum has a canonical zero-Dirichlet solution and a
`W^{2,4}` gradient representative with the source-facing CZ bound. -/
theorem exists_canonical_oneStepShell_dirichlet_corrector (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p : Vec d) (m : ℤ) (hh : 0 < h),
        ∃ u : H10Function (openCubeSet (originCube d m)),
          CubeDirichletDivergenceProblem (originCube d m) u
            (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField ∧
          ∃ V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent,
            V.toField = u.toH1Function.grad ∧
            eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) 4
                (normalizedCubeMeasure (originCube d m)) ≤
              C * eLpNorm (fun x => HilbertMat.ofMat
                ((oneStepShellForcingW14 M n h omega p
                  (originCube d m) hh).jacobian x)) 4
                (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hCZ⟩ := exists_oneStepShell_scalarDivergence_cz d
  refine ⟨C, hCtop, ?_⟩
  intro M n h omega p m hh
  let G := oneStepShellForcingH1 M n h omega p (originCube d m) hh
  let hG : MemVectorL2 (openCubeSet (originCube d m)) G.toField :=
    G.memVectorL2_toField_openCubeSet
  let u : H10Function (openCubeSet (originCube d m)) :=
    CubeCalderonZygmund.openCubeSetScalarDivergenceSolution
      (originCube d m) (sigma0 := 1) (by norm_num) G.toField hG
  have hu : CubeDirichletDivergenceProblem (originCube d m) u G.toField := by
    intro phi
    simpa [u] using
      (CubeCalderonZygmund.openCubeSetScalarDivergenceSolution_weak
        (originCube d m) (sigma0 := 1) (by norm_num) G.toField hG phi)
  refine ⟨u, by simpa [G] using hu, ?_⟩
  exact hCZ M n h omega p m hh u (by simpa [G] using hu)

/-- The literal shell datum has a canonical centered mean-zero Neumann
solution and satisfies the finite-`4` gradient estimate used for the printed
dual field `exp(H) q - grad W`. -/
theorem exists_canonical_oneStepShell_neumann_corrector (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (q : Vec d) (m : ℤ) (hh : 0 < h),
        ∃ u : H1MeanZeroFunction (openCubeSet (originCube d m)),
          IsMeanZeroNeumannRhsWeakSolution
            (fun _ : Vec d => (1 : Mat d)) (openCubeSet (originCube d m)) u
            (fun x =>
              -(oneStepShellForcingW14 M n h omega q
                (originCube d m) hh).toField x) ∧
          MemLp u.toH1Function.grad 4
              (normalizedCubeMeasure (originCube d m)) ∧
          cubeLpNorm (originCube d m) 4 u.toH1Function.grad ≤
            C * cubeLpNorm (originCube d m) 4
              (oneStepShellForcingW14 M n h omega q
                (originCube d m) hh).toField := by
  obtain ⟨C, hCpos, hCZ⟩ := exists_oneStepShell_neumannDivergence_cz d
  refine ⟨C, hCpos, ?_⟩
  intro M n h omega q m hh
  let G := oneStepShellForcingH1 M n h omega q (originCube d m) hh
  let hG : MemVectorL2 (openCubeSet (originCube d m)) G.toField :=
    G.memVectorL2_toField_openCubeSet
  let u : H1MeanZeroFunction (openCubeSet (originCube d m)) :=
    CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution
      m (sigma0 := 1) (by norm_num) G.toField hG
  have hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Mat d)) (openCubeSet (originCube d m)) u
      (fun x => -G.toField x) := by
    simpa [u, scalarMatrix] using
      (CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
        m (sigma0 := 1) (by norm_num) G.toField hG)
  have hfield : G.toField =
      (oneStepShellForcingW14 M n h omega q (originCube d m) hh).toField :=
    oneStepShellForcing_paired_toField M n h omega q (originCube d m) hh
  have hu' : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Mat d)) (openCubeSet (originCube d m)) u
      (fun x =>
        -(oneStepShellForcingW14 M n h omega q
          (originCube d m) hh).toField x) := by
    simpa only [hfield] using hu
  refine ⟨u, hu', ?_⟩
  exact hCZ M n h omega q (originCube d m) hh u hu'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
