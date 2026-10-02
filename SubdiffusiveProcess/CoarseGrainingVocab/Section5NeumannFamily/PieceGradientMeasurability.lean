import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.LocalDirichletHessian
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableCorrectors

/-!
# Borel measurability of the four two-radius gradient classes

The `OneStepTwoRadiusNeumannHessianFamily` carrier asks for Borel
measurability of the gradient `L²` classes of all four members.  All four are
built from three solution families -- the large-cube Neumann corrector and the
two canonical local solutions on the parent -- whose gradient classes are
continuous images of the measurable shell forcing
(`measurable_oneStepShellNeumannGradL2`,
`measurable_oneStepShellDirichletGradL2`).  The two harmonic radii are
differences, and restriction to a cell is a continuous linear map.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The gradient class of a difference is the difference of the classes. -/
theorem nfGradToHilbertVectorL2_sub {U : Set (Vec d)} (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  show (u + (-1 : ℝ) • v).gradToHilbertVectorL2 = _
  rw [H1Function.gradToHilbertVectorL2_add,
    H1Function.gradToHilbertVectorL2_smul, neg_one_smul, ← sub_eq_add_neg]

/-- The large Neumann corrector solves the shell problem in the `toField`
normalization used by the measurability layer. -/
theorem twoRadiusLarge_isWeakSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (omega : NFSample d) (hh : 0 < h) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d K))
      (oneStepOriginNeumannSolution M n h p K omega hh)
      (fun x => -(oneStepShellForcingH1 M n h omega p
        (originCube d K) hh).toField x) := by
  simpa only [oneStepShellForcingW14_toField_apply,
    oneStepShellForcing_paired_toField, neg_smul] using
    oneStepOriginNeumannSolution_isWeakSolution M n h p K omega hh

/-- The local Neumann solution on a triadic parent in the same
normalization. -/
theorem twoRadiusLocalNeumann_isWeakSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet Q) (oneStepTriadicNeumannSolution M n h p Q omega hh)
      (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x) := by
  simpa only [oneStepShellForcingW14_toField_apply,
    oneStepShellForcing_paired_toField, neg_smul] using
    oneStepTriadicNeumannSolution_isWeakSolution M n h p Q omega hh

/-- The local Dirichlet solution on a triadic parent solves the literal
divergence problem. -/
theorem twoRadiusLocalDirichlet_divergenceProblem [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    CubeDirichletDivergenceProblem Q
      (oneStepTriadicDirichletSolution M n h p Q omega hh)
      (oneStepShellForcingH1 M n h omega p Q hh).toField := by
  intro phi
  have hweak :=
    oneStepTriadicDirichletSolution_isWeakSolution M n h p Q omega hh phi
  have hfield : ∀ x, (oneStepShellForcingH1 M n h omega p Q hh).toField x =
      oneStepMultiplierAt M n h x omega • p := by
    intro x
    rw [oneStepShellForcing_paired_toField M n h omega p Q hh,
      oneStepShellForcingW14_toField_apply]
  change (∫ x in openCubeSet Q,
      vecDot ((oneStepTriadicDirichletSolution M n h p Q omega hh
        ).toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) = _
  calc
    _ = ∫ x in openCubeSet Q,
        vecDot (-oneStepMultiplierAt M n h x omega • p)
          (phi.toH1Function.grad x) ∂volume := by
      simpa only [matVecMul_identityCoeffField, one_mul] using hweak
    _ = -∫ x in openCubeSet Q,
        vecDot ((oneStepShellForcingH1 M n h omega p Q hh).toField x)
          (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [hfield, neg_smul, vecDot_neg_left]

/-! ## Parent-level gradient measurability -/

/-- Gradient measurability of the large Neumann corrector on the large
cube. -/
theorem measurable_twoRadiusLarge_bigGrad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (oneStepOriginNeumannSolution M n h p K omega hh).gradToHilbertVectorL2 :=
  measurable_oneStepShellNeumannGradL2 M n h p (originCube d K) hh
    (fun omega => oneStepOriginNeumannSolution M n h p K omega hh)
    (fun omega => twoRadiusLarge_isWeakSolution M n h p K omega hh)

/-- Gradient measurability of the local Neumann piece on a triadic parent. -/
theorem measurable_twoRadiusLocalNeumannPiece_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (twoRadiusLocalNeumannPiece M n h p Q omega hh).gradToHilbertVectorL2 :=
  measurable_oneStepShellNeumannGradL2 M n h p Q hh
    (fun omega => oneStepTriadicNeumannSolution M n h p Q omega hh)
    (fun omega => twoRadiusLocalNeumann_isWeakSolution M n h p Q omega hh)

/-- Gradient measurability of the local Dirichlet piece on a triadic
parent. -/
theorem measurable_twoRadiusLocalDirichletPiece_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (twoRadiusLocalDirichletPiece M n h p Q omega hh
        ).gradToHilbertVectorL2 :=
  measurable_oneStepShellDirichletGradL2 M n h p Q hh
    (fun omega => oneStepTriadicDirichletSolution M n h p Q omega hh)
    (fun omega => twoRadiusLocalDirichlet_divergenceProblem M n h p Q omega hh)

/-- Gradient measurability of the large piece after restriction to the
triadic parent. -/
theorem measurable_twoRadiusLargePiece_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (Q : TriadicCube d) (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K))
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (twoRadiusLargePiece M n h p K Q hQK omega hh).gradToHilbertVectorL2 :=
  measurable_gradToHilbertVectorL2_of_grad_eq_restrict hQK
    (fun omega => (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function)
    (fun omega => twoRadiusLargePiece M n h p K Q hQK omega hh)
    (measurable_twoRadiusLarge_bigGrad M n h p K hh)
    (fun _omega => rfl)

/-- Gradient measurability of the local harmonic radius on the parent. -/
theorem measurable_twoRadiusLocalHarmonicPiece_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (twoRadiusLocalHarmonicPiece M n h p Q omega hh
        ).gradToHilbertVectorL2 := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have heq : (fun omega : NFSample d =>
      (twoRadiusLocalHarmonicPiece M n h p Q omega hh
        ).gradToHilbertVectorL2) =
      fun omega =>
        (twoRadiusLocalNeumannPiece M n h p Q omega hh
          ).gradToHilbertVectorL2 -
        (twoRadiusLocalDirichletPiece M n h p Q omega hh
          ).gradToHilbertVectorL2 := by
    funext omega
    exact nfGradToHilbertVectorL2_sub _ _
  rw [heq]
  exact (measurable_twoRadiusLocalNeumannPiece_grad M n h p Q hh).sub
    (measurable_twoRadiusLocalDirichletPiece_grad M n h p Q hh)

/-- Gradient measurability of the outer harmonic radius on the parent. -/
theorem measurable_twoRadiusOuterHarmonicPiece_grad [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (Q : TriadicCube d) (hQK : openCubeSet Q ⊆ openCubeSet (originCube d K))
    (hh : 0 < h) :
    Measurable fun omega : NFSample d =>
      (twoRadiusOuterHarmonicPiece M n h p K Q hQK omega hh
        ).gradToHilbertVectorL2 := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have heq : (fun omega : NFSample d =>
      (twoRadiusOuterHarmonicPiece M n h p K Q hQK omega hh
        ).gradToHilbertVectorL2) =
      fun omega =>
        (twoRadiusLargePiece M n h p K Q hQK omega hh
          ).gradToHilbertVectorL2 -
        (twoRadiusLocalNeumannPiece M n h p Q omega hh
          ).gradToHilbertVectorL2 := by
    funext omega
    exact nfGradToHilbertVectorL2_sub _ _
  rw [heq]
  exact (measurable_twoRadiusLargePiece_grad M n h p K Q hQK hh).sub
    (measurable_twoRadiusLocalNeumannPiece_grad M n h p Q hh)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
