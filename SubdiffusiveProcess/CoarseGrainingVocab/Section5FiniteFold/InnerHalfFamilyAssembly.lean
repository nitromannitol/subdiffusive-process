module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfCellHessian

@[expose] public section

/-!
# The shared-parent two-radius Neumann Hessian family

Exact mirror of `exists_nfAxisTwoRadiusNeumannHessianFamily`
(`Section5NeumannFamily/AxisFamilyAssembly.lean`) with the *fixed concentric
interior* hypothesis `hinner` deleted: the cells are only required to have
their centres inside the scale-`(mm - 1)` cube around the parent centre.  The
telescope, the persistent Dirichlet Hessian and the four gradient
measurabilities are used verbatim; only the two harmonic cell bounds change,
and they change exactly by the dimension-only factor `((3 : ℝ) ^ d) ^ (1/2)`
of `nfAxisHarmonic_innerHalf_cell_hessian`.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

variable {d : ℕ}

/-- The `a`-free harmonic prefactor of the shared-parent family. -/
def nfInnerHalfHarmonicConst (d : ℕ) (hd : 3 ≤ d) : ℝ :=
  (d : ℝ) ^ 2 * nfAxisHarmonicConst d hd * ((3 : ℝ) ^ d) ^ (1 / 2 : ℝ)

theorem nfInnerHalfHarmonicConst_nonneg (d : ℕ) (hd : 3 ≤ d) :
    0 ≤ nfInnerHalfHarmonicConst d hd := by
  have := (nfAxisHarmonicConst_pos d hd).le
  unfold nfInnerHalfHarmonicConst
  positivity

/-- **The shared-parent two-radius Neumann Hessian family.**  No cell is
required to sit in the parent's fixed concentric interior; only its *centre*
must lie in the scale-`(mm - 1)` cube around the parent centre. -/
theorem exists_nfAxisInnerHalfNeumannHessianFamily
    [NeZero d] (hd : 3 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (K mm : ℤ) (N : ℕ) (hN : nfAxisHarmonicDepth d hd + 2 ≤ N) (hh : 0 < h)
    {ι : Type*} (s : Finset ι) (cell : ι → TriadicCube d)
    (centre : ι → Vec d)
    (hscale : ∀ i, (cell i).scale + (N : ℤ) = mm)
    (hpar : ∀ i, translateSet (centre i)
      (openCubeSet (originCube d mm)) ⊆ openCubeSet (originCube d K))
    (hcentre : ∀ i, cubeCenter (cell i) ∈
      oneStepCenteredParent (centre i) (mm - 1)) :
    ∃ F : OneStepTwoRadiusNeumannHessianFamily d ι (NFSample d) s cell,
      (∀ i omega, (F.neumann i omega).grad =
        (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad) ∧
      (∀ i omega, (F.dirichlet i omega).grad =
        (oneStepDirichletAxisLocalSolution M n h omega p
          (centre i) mm hh).grad) ∧
      (∀ i omega,
        F.toCellFamily.localHarmonic i omega ≤
          nfInnerHalfHarmonicConst d hd *
            oneStepNestedHarmonicWeight d hd
              (nfAxisHarmonicDepth d hd) (N - 1) *
            oneStepNeumannDirichletAxisCoordinateSum M n h p
              (centre i) mm omega hh) ∧
      (∀ i omega,
        F.toCellFamily.outerHarmonic i omega ≤
          nfInnerHalfHarmonicConst d hd *
            oneStepNestedHarmonicWeight d hd
              (nfAxisHarmonicDepth d hd) (N - 1) *
            nfAxisOuterCoordinateSum M n h omega p (centre i)
              K mm (hpar i) hh) := by
  classical
  have hcellParent : ∀ i,
      openCubeSet (cell i) ⊆
        axisCube (oneStepCenteredAxisCorner (centre i) mm)
          (cubeScaleFactor (originCube d mm)) := fun i =>
    openCubeSet_subset_sharedParent (by omega) (hscale i) (hcentre i)
  -- the two harmonic radii on each cell, `a`-free
  have hlocal : ∀ (i : ι) (omega : NFSample d),
      ∃ (v : H1Function (openCubeSet (cell i)))
        (H : HasWeakHessianOn (openCubeSet (cell i)) v),
        (∀ x, v.grad x =
          (oneStepNeumannDirichletAxisRemainder M n h omega p
            (centre i) mm hh).grad x) ∧
        oneStepCellB (cell i) H ≤
          nfInnerHalfHarmonicConst d hd *
            oneStepNestedHarmonicWeight d hd
              (nfAxisHarmonicDepth d hd) (N - 1) *
            oneStepNeumannDirichletAxisCoordinateSum M n h p
              (centre i) mm omega hh := fun i omega =>
    nfAxisHarmonic_innerHalf_cell_hessian d hd (centre i) mm N hN
      (oneStepNeumannDirichletAxisRemainder M n h omega p (centre i) mm hh)
      (oneStepNeumannDirichletAxisRemainder_harmonic M n h omega p
        (centre i) mm hh)
      (cell i) (hscale i) (hcentre i)
  have houter : ∀ (i : ι) (omega : NFSample d),
      ∃ (v : H1Function (openCubeSet (cell i)))
        (H : HasWeakHessianOn (openCubeSet (cell i)) v),
        (∀ x, v.grad x =
          (oneStepNeumannAxisRemainder M n h omega p
            (centre i) K mm (hpar i) hh).grad x) ∧
        oneStepCellB (cell i) H ≤
          nfInnerHalfHarmonicConst d hd *
            oneStepNestedHarmonicWeight d hd
              (nfAxisHarmonicDepth d hd) (N - 1) *
            nfAxisOuterCoordinateSum M n h omega p (centre i)
              K mm (hpar i) hh := fun i omega =>
    nfAxisHarmonic_innerHalf_cell_hessian d hd (centre i) mm N hN
      (oneStepNeumannAxisRemainder M n h omega p (centre i) K mm (hpar i) hh)
      (oneStepNeumannAxisRemainder_harmonic M n h omega p
        (centre i) K mm (hpar i) hh)
      (cell i) (hscale i) (hcentre i)
  choose vLoc HLoc hLocGrad hLocBound using hlocal
  choose vOut HOut hOutGrad hOutBound using houter
  -- the persistent Dirichlet member
  let HDpar : ∀ i, ∀ omega : NFSample d,
      HasWeakHessianOn
        (axisCube (oneStepCenteredAxisCorner (centre i) mm)
          (cubeScaleFactor (originCube d mm)))
        (oneStepDirichletAxisLocalSolution M n h omega p
          (centre i) mm hh) := fun i =>
    (nonempty_nfAxisDirichletLocal_parentHessian d M n h p
      (centre i) mm hh).some
  refine
    ⟨{ neumann := fun i omega =>
          (oneStepNeumannAxisLargeRestriction M n h omega p
            (centre i) K mm (hpar i) hh).restrict
              (isOpen_openCubeSet (cell i)) (hcellParent i),
       dirichlet := fun i omega =>
          (oneStepDirichletAxisLocalSolution M n h omega p
            (centre i) mm hh).restrict
              (isOpen_openCubeSet (cell i)) (hcellParent i),
       localHarmonic := fun i omega => vLoc i omega,
       outerHarmonic := fun i omega => vOut i omega,
       grad_split := ?_,
       dirichletHessian := fun i omega =>
          (HDpar i omega).restrict (isOpen_openCubeSet (cell i))
            (hcellParent i),
       localHarmonicHessian := fun i omega => HLoc i omega,
       outerHarmonicHessian := fun i omega => HOut i omega,
       measurable_neumann_grad := ?_,
       measurable_dirichlet_grad := ?_,
       measurable_localHarmonic_grad := ?_,
       measurable_outerHarmonic_grad := ?_ },
      ?_, ?_, ?_, ?_⟩
  · intro i omega
    have hsplit := nfAxis_grad_split M n h omega p (centre i) K mm
      (hpar i) hh
    show (oneStepNeumannAxisLargeRestriction M n h omega p
        (centre i) K mm (hpar i) hh).grad =
      fun x => (oneStepDirichletAxisLocalSolution M n h omega p
          (centre i) mm hh).grad x +
        ((vLoc i omega).grad x + (vOut i omega).grad x)
    funext x
    rw [hLocGrad i omega x, hOutGrad i omega x]
    exact congrFun hsplit x
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (hcellParent i)
      (fun omega => oneStepNeumannAxisLargeRestriction M n h omega p
        (centre i) K mm (hpar i) hh)
      _
      (measurable_nfAxisLargeRestriction_grad M n h p (centre i)
        K mm (hpar i) hh)
      (fun _omega => rfl)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (hcellParent i)
      (fun omega => oneStepDirichletAxisLocalSolution M n h omega p
        (centre i) mm hh)
      _
      (measurable_nfAxisLocalDirichlet_grad M n h p (centre i) mm hh)
      (fun _omega => rfl)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (hcellParent i)
      (fun omega => oneStepNeumannDirichletAxisRemainder M n h omega p
        (centre i) mm hh)
      _
      (measurable_nfAxisNeumannDirichletRemainder_grad M n h p
        (centre i) mm hh)
      (fun omega => funext (hLocGrad i omega))
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (hcellParent i)
      (fun omega => oneStepNeumannAxisRemainder M n h omega p
        (centre i) K mm (hpar i) hh)
      _
      (measurable_nfAxisNeumannRemainder_grad M n h p (centre i)
        K mm (hpar i) hh)
      (fun omega => funext (hOutGrad i omega))
  · intro i omega
    exact oneStepNeumannAxisLargeRestriction_grad M n h omega p
      (centre i) K mm (hpar i) hh
  · intro i omega
    rfl
  · intro i omega
    rw [toCellFamily_localHarmonic_eq]
    exact hLocBound i omega
  · intro i omega
    rw [toCellFamily_outerHarmonic_eq]
    exact hOutBound i omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
