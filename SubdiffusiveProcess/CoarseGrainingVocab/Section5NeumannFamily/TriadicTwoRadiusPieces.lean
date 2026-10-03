module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepTwoRadiusNeumannAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepAxisCubeHarmonicExistence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCanonicalCenteredHessian

@[expose] public section

/-!
# The literal two-radius Neumann pieces on a triadic parent cube

The `delta ^ 68` Neumann apparatus of
`SubdiffusiveProcess/CoarseGrainingVocab/Section5Support/OneStepTwoRadiusNeumannMoments.lean`
is conditional on a term of `OneStepTwoRadiusNeumannHessianFamily` whose
`neumann` field is the literal one-step Neumann corrector.  This module
supplies the deterministic half of that term.

On a triadic parent cube `Q` contained in the large cube `originCube d K` the
three-piece telescope is completely explicit:

```
  u_N|_Q  =  u_D^Q  +  (u_N^Q - u_D^Q)  +  (u_N|_Q - u_N^Q),
```

where `u_N` is the large-cube Neumann corrector, `u_N^Q` and `u_D^Q` are the
canonical translated local Neumann and Dirichlet solutions on `Q` supplied by
`oneStepTriadicNeumannSolution` / `oneStepTriadicDirichletSolution`.  Both
brackets are weakly harmonic on `openCubeSet Q`: the outer one by
`oneStepNeumann_restrict_sub_local_harmonic`, the local one because the two
local solutions carry the *same* shell right-hand side.

Everything here is at the level of `H¹` gradients; no measurability and no
Hessian is used yet.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Sample space of the one-step potential. -/
abbrev NFSample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- The large-cube Neumann corrector restricted to a triadic parent cube. -/
def twoRadiusLargePiece [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (Q : TriadicCube d) (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K))
    (omega : NFSample d) (hh : 0 < h) : H1Function (openCubeSet Q) :=
  (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.restrict
    (isOpen_openCubeSet Q) hQK

/-- The canonical translated local Neumann solution on a triadic parent. -/
def twoRadiusLocalNeumannPiece [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    H1Function (openCubeSet Q) :=
  (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function

/-- The canonical translated local Dirichlet solution on a triadic parent. -/
def twoRadiusLocalDirichletPiece [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    H1Function (openCubeSet Q) :=
  (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function

/-- The local (Neumann minus Dirichlet) harmonic radius on a triadic parent. -/
def twoRadiusLocalHarmonicPiece [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    H1Function (openCubeSet Q) :=
  twoRadiusLocalNeumannPiece M n h p Q omega hh -
    twoRadiusLocalDirichletPiece M n h p Q omega hh

/-- The outer (large minus local Neumann) harmonic radius on a triadic
parent. -/
def twoRadiusOuterHarmonicPiece [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (Q : TriadicCube d) (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K))
    (omega : NFSample d) (hh : 0 < h) : H1Function (openCubeSet Q) :=
  twoRadiusLargePiece M n h p K Q hQK omega hh -
    twoRadiusLocalNeumannPiece M n h p Q omega hh

/-- Both local solutions solve the same weak Poisson equation on the parent:
the shell divergence. -/
theorem twoRadiusLocalDirichletPiece_weakPoisson [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    WeakPoissonEquationOn (openCubeSet Q)
      (twoRadiusLocalDirichletPiece M n h p Q omega hh)
      (oneStepShellForcingH1 M n h omega p Q hh).divergence := by
  apply weakPoissonEquationOn_oneStepShellDirichlet M n h omega p Q hh
  simpa only [oneStepShellForcingW14_toField_apply,
    oneStepShellForcing_paired_toField, neg_smul] using
    oneStepTriadicDirichletSolution_isWeakSolution M n h p Q omega hh

/-- Neumann counterpart of `twoRadiusLocalDirichletPiece_weakPoisson`. -/
theorem twoRadiusLocalNeumannPiece_weakPoisson [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    WeakPoissonEquationOn (openCubeSet Q)
      (twoRadiusLocalNeumannPiece M n h p Q omega hh)
      (oneStepShellForcingH1 M n h omega p Q hh).divergence := by
  apply weakPoissonEquationOn_oneStepShellNeumann M n h omega p Q hh
  simpa only [oneStepShellForcingW14_toField_apply,
    oneStepShellForcing_paired_toField, neg_smul] using
    oneStepTriadicNeumannSolution_isWeakSolution M n h p Q omega hh

/-- The local harmonic radius is weakly harmonic on the parent. -/
theorem twoRadiusLocalHarmonicPiece_harmonic [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    WeakPoissonEquationOn (openCubeSet Q)
      (twoRadiusLocalHarmonicPiece M n h p Q omega hh) (fun _ ↦ 0) :=
  WeakPoissonEquationOn.sub_same_rhs (isOpen_openCubeSet Q)
    (twoRadiusLocalNeumannPiece_weakPoisson M n h p Q omega hh)
    (twoRadiusLocalDirichletPiece_weakPoisson M n h p Q omega hh)

/-- The outer harmonic radius is weakly harmonic on the parent. -/
theorem twoRadiusOuterHarmonicPiece_harmonic [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (Q : TriadicCube d) (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K))
    (omega : NFSample d) (hh : 0 < h) :
    WeakPoissonEquationOn (openCubeSet Q)
      (twoRadiusOuterHarmonicPiece M n h p K Q hQK omega hh) (fun _ ↦ 0) :=
  oneStepNeumann_restrict_sub_local_harmonic M n h omega p K Q hQK hh

/-- The literal three-piece gradient telescope on the parent cube. -/
theorem twoRadius_grad_split [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (Q : TriadicCube d) (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K))
    (omega : NFSample d) (hh : 0 < h) :
    (twoRadiusLargePiece M n h p K Q hQK omega hh).grad = fun x =>
      (twoRadiusLocalDirichletPiece M n h p Q omega hh).grad x +
        ((twoRadiusLocalHarmonicPiece M n h p Q omega hh).grad x +
          (twoRadiusOuterHarmonicPiece M n h p K Q hQK omega hh).grad x) := by
  funext x
  funext i
  simp only [twoRadiusLocalHarmonicPiece, twoRadiusOuterHarmonicPiece,
    H1Function.sub_grad, Pi.sub_apply, Pi.add_apply]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
