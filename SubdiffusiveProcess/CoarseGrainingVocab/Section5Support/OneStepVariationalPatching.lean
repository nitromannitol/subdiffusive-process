import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellObservableMeasurability
import Homogenization.Sobolev.W1p.ZeroExtensionGraph




open Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Extend a zero-trace cell correction to the ambient open cube. -/
def oneStepZeroExtendedCorrection {d : ℕ} (Q R : TriadicCube d)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (u : H10Function (openCubeSet R)) : H10Function (openCubeSet Q) :=
  u.extendByZeroToOpenSuperset
    (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ

@[simp] theorem oneStepZeroExtendedCorrection_toFun {d : ℕ}
    (Q R : TriadicCube d) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (u : H10Function (openCubeSet R)) :
    (oneStepZeroExtendedCorrection Q R hRQ u).toH1Function.toFun =
      u.zeroExtension := by
  rfl

@[simp] theorem oneStepZeroExtendedCorrection_grad {d : ℕ}
    (Q R : TriadicCube d) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (u : H10Function (openCubeSet R)) :
    (oneStepZeroExtendedCorrection Q R hRQ u).toH1Function.grad =
      u.zeroExtensionGrad := by
  rfl

/-- Fold a finite list of already ambient-domain zero-trace corrections. -/
def oneStepFoldCorrections {d : ℕ} {U : Set (Vec d)} :
    List (H10Function U) → H10Function U
  | [] => 0
  | u :: us => u + oneStepFoldCorrections us

@[simp] theorem oneStepFoldCorrections_nil {d : ℕ} {U : Set (Vec d)} :
    oneStepFoldCorrections ([] : List (H10Function U)) = 0 :=
  rfl

@[simp] theorem oneStepFoldCorrections_cons {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) (us : List (H10Function U)) :
    oneStepFoldCorrections (u :: us) = u + oneStepFoldCorrections us :=
  rfl

/-- Pointwise gradient of the finite correction fold. -/
theorem oneStepFoldCorrections_grad {d : ℕ} {U : Set (Vec d)}
    (us : List (H10Function U)) (x : Vec d) :
    (oneStepFoldCorrections us).toH1Function.grad x =
      us.foldr (fun u G => u.toH1Function.grad x + G) 0 := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      change u.toH1Function.grad x +
          (oneStepFoldCorrections us).toH1Function.grad x = _
      rw [ih]
      rfl

/-- Add all interior-cell corrections to a fixed large-cube base
competitor. -/
def oneStepPatchedCompetitor {d : ℕ} {U : Set (Vec d)}
    (w : H10Function U) (us : List (H10Function U)) : H10Function U :=
  w + oneStepFoldCorrections us

/-- Exact gradient formula for the patched competitor. -/
theorem oneStepPatchedCompetitor_grad {d : ℕ} {U : Set (Vec d)}
    (w : H10Function U) (us : List (H10Function U)) (x : Vec d) :
    (oneStepPatchedCompetitor w us).toH1Function.grad x =
      w.toH1Function.grad x +
        us.foldr (fun u G => u.toH1Function.grad x + G) 0 := by
  change w.toH1Function.grad x +
      (oneStepFoldCorrections us).toH1Function.grad x = _
  rw [oneStepFoldCorrections_grad]

/-- The source's literal cell patch: first add the principal and oscillatory
cell correctors, then extend their sum by zero to the ambient cube. -/
def oneStepCellPatch {d : ℕ} (Q R : TriadicCube d)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (chi phi : H10Function (openCubeSet R)) :
    H10Function (openCubeSet Q) :=
  oneStepZeroExtendedCorrection Q R hRQ (chi + phi)

@[simp] theorem oneStepCellPatch_grad {d : ℕ} (Q R : TriadicCube d)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (chi phi : H10Function (openCubeSet R)) :
    (oneStepCellPatch Q R hRQ chi phi).toH1Function.grad =
      (chi + phi).zeroExtensionGrad := by
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
