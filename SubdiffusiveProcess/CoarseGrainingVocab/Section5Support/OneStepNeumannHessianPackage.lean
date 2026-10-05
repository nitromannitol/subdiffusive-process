module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHessianObservableMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannInteriorEquation

@[expose] public section

/-!
# Measurable interior Neumann Hessian cells

The constant-coefficient Neumann corrector is globally measurable in its
gradient `L²` class.  The interior difference-quotient construction supplies
a weak Hessian samplewise on the half parent cube.  Continuous restriction of
the gradient class and closed-operator measurability therefore make every
interior-cell `B_z` observable Borel, independently of how the pointwise weak
Hessian representatives are selected.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Borel measurability of the literal Neumann `B_z` on a cell contained in
the canonical half-parent interior region. -/
theorem measurable_oneStepShellNeumann_innerCellB
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (uN : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1MeanZeroFunction (openCubeSet Q))
    (huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uN omega)
        (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
    (uS : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (huSgrad : ∀ omega, (uS omega).grad = (uN omega).toH1Function.grad)
    (H : ∀ omega,
      HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) (uS omega)) :
    Measurable fun omega =>
      oneStepCellB R
        ((H omega).restrict (isOpen_openCubeSet R) hRhalf) := by
  have hhalfQ : scaledOpenCubeSet Q (1 / 2 : ℝ) ⊆ openCubeSet Q :=
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q (1 / 2 : ℝ)).trans
      (scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
        (by norm_num) (by norm_num))
  have hRQ : openCubeSet R ⊆ openCubeSet Q := hRhalf.trans hhalfQ
  let uR : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1Function (openCubeSet R) := fun omega =>
    (uS omega).restrict (isOpen_openCubeSet R) hRhalf
  let HR : ∀ omega, HasWeakHessianOn (openCubeSet R) (uR omega) := fun omega =>
    (H omega).restrict (isOpen_openCubeSet R) hRhalf
  have hgradN : Measurable fun omega =>
      (uN omega).gradToHilbertVectorL2 :=
    measurable_oneStepShellNeumannGradL2 M n h p Q hh uN huN
  have hgradEq : ∀ omega, (uR omega).grad =
      (uN omega).toH1Function.grad := by
    intro omega
    simpa only [uR, H1Function.restrict] using huSgrad omega
  have hgradR : Measurable fun omega =>
      (uR omega).gradToHilbertVectorL2 :=
    measurable_gradToHilbertVectorL2_of_grad_eq_restrict hRQ
      (fun omega => (uN omega).toH1Function) uR hgradN hgradEq
  exact measurable_oneStepCellB R uR HR hgradR

/-- Canonical source-facing package: the literal Neumann corrector, its
selected half-parent weak Hessian, the reduced samplewise bound, and Borel
measurability of every contained-cell `B_z`. -/
theorem exists_measurable_oneStepShellNeumann_innerCellB
    (d : ℕ) [NeZero d] :
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
      (m : ℤ) (R : TriadicCube d) (hh : 0 < h)
      (hRhalf : openCubeSet R ⊆
        scaledOpenCubeSet (originCube d m) (1 / 2 : ℝ)),
      ∃ (uN : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1MeanZeroFunction
            (openCubeSet (originCube d m)))
        (uS : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1Function
            (scaledOpenCubeSet (originCube d m) (1 / 2 : ℝ)))
        (H : ∀ omega,
          HasWeakHessianOn
            (scaledOpenCubeSet (originCube d m) (1 / 2 : ℝ)) (uS omega)),
        (∀ omega,
          IsMeanZeroNeumannRhsWeakSolution
            (identityCoeffField d) (openCubeSet (originCube d m)) (uN omega)
            (fun x => -(oneStepShellForcingH1 M n h omega p
              (originCube d m) hh).toField x)) ∧
        (∀ omega, (uS omega).grad = (uN omega).toH1Function.grad) ∧
        (∀ omega,
          (H omega).hessianCoordL2NormSum ≤
            ∑ i : Fin d, ∑ _j : Fin d,
              @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
                d (originCube d m) (uN omega).toH1Function
                (oneStepShellForcingH1 M n h omega p
                  (originCube d m) hh).divergence i
                (1 / 2 : ℝ) (7 / 12 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                (CubeCalderonZygmund.outerThreeQuarterSevenEighthCutoff
                  (originCube d m))) ∧
        Measurable fun omega =>
          oneStepCellB R
            ((H omega).restrict (isOpen_openCubeSet R) hRhalf) := by
  obtain ⟨_C, _hC, hcanonical⟩ :=
    exists_canonical_oneStepShell_neumann_corrector d
  intro M n h p m R hh hRhalf
  choose uN huN4 _hgrad4 _hgradBound using fun omega =>
    hcanonical M n h omega p m hh
  have huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet (originCube d m)) (uN omega)
        (fun x => -(oneStepShellForcingH1 M n h omega p
          (originCube d m) hh).toField x) := by
    intro omega
    have hfield := oneStepShellForcing_paired_toField M n h omega p
      (originCube d m) hh
    have hcoeff : (fun _ : Vec d => (1 : Mat d)) = identityCoeffField d := by
      funext x i j
      simp [identityCoeffField, scalarMatrix]
    rw [← hcoeff]
    simpa only [hfield] using huN4 omega
  choose uS huSfun huSgrad H hH using fun omega =>
    exists_oneStepShellNeumann_innerHalfWeakHessian_reduced
      M n h omega p (originCube d m) hh (uN omega) (huN omega)
  refine ⟨uN, uS, H, huN, huSgrad, hH, ?_⟩
  exact measurable_oneStepShellNeumann_innerCellB M n h p
    (originCube d m) R hh hRhalf uN huN uS huSgrad H

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
