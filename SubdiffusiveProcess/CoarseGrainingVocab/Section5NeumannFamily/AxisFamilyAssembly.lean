import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.AxisTwoRadiusFamily

/-!
# Assembly of the concentric-parent two-radius Neumann Hessian family

Everything is now in place: the telescope (`nfAxis_grad_split`), the
persistent Dirichlet Hessian
(`nonempty_nfAxisDirichletLocal_parentHessian`), the four gradient
measurabilities, and the interior harmonic Hessian package
(`nfAxisHarmonic_cell_hessian`).

The parametrization matters.  The **parent scale `mm` is held fixed** and the
*cell* shrinks as the auxiliary radius `N` grows: `cell.scale + N = mm`.  That
is the only parametrization for which the two stochastic budgets are
`N`-independent — the geometric gain `3⁻ᴺ` is then produced entirely by the
cell/parent side quotient, exactly as in
`oneStepNeumannDirichletAxisHarmonicGain` and
`oneStepNeumannOverlapHarmonicGain`, whose parent scales (`K - j` and
`S.scale + 1`) do not move with the radius either.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Normalized parent coordinate sum of the outer (large minus local Neumann)
harmonic radius on a concentric parent. -/
def nfAxisOuterCoordinateSum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : NFSample d) (p z : Vec d) (K m : ℤ)
    (hsub : translateSet z (openCubeSet (originCube d m)) ⊆
      openCubeSet (originCube d K)) (hh : 0 < h) : ℝ :=
  ∑ k : Fin d,
    (eLpNorm (fun x =>
        (oneStepNeumannAxisRemainder M n h omega p z K m hsub hh).grad x k) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (oneStepCenteredAxisCorner z m)
        (cubeScaleFactor (originCube d m)))).toReal

/-- The fixed concentric interior sits inside the parent. -/
theorem nfAxisConcentric_subset_parent (d : ℕ) (z : Vec d) (L : ℝ)
    (hL : 0 < L) (a : ℕ) :
    axisCube (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide L a) ⊆
      axisCube z L := by
  have hsub := concentricDepthAxisCube_subset_of_le z L hL
    (a := 0) (b := a) (Nat.zero_le _)
  simpa using hsub

/-- The concentric-parent two-radius Neumann Hessian family, with both
harmonic cell bounds in nested-weight form.

`mm` is the fixed parent scale and `N = mm - cell.scale` the auxiliary
radius. -/
theorem exists_nfAxisTwoRadiusNeumannHessianFamily
    [NeZero d] (hd : 3 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (K mm : ℤ) (N : ℕ) (hh : 0 < h)
    {ι : Type*} (s : Finset ι) (cell : ι → TriadicCube d)
    (centre : ι → Vec d)
    (hscale : ∀ i, (cell i).scale + (N : ℤ) = mm)
    (hpar : ∀ i, translateSet (centre i)
      (openCubeSet (originCube d mm)) ⊆ openCubeSet (originCube d K))
    (hhalf : ∀ i, openCubeSet (cell i) ⊆
      axisCubeInnerHalf (oneStepCenteredAxisCorner (centre i) mm)
        (cubeScaleFactor (originCube d mm)))
    (hinner : ∀ i, openCubeSet (cell i) ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (centre i) mm)
          (cubeScaleFactor (originCube d mm))
          (nfAxisHarmonicDepth d hd + 1))
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d mm))
          (nfAxisHarmonicDepth d hd + 1))) :
    ∃ F : OneStepTwoRadiusNeumannHessianFamily d ι (NFSample d) s cell,
      (∀ i omega, (F.neumann i omega).grad =
        (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad) ∧
      (∀ i omega, (F.dirichlet i omega).grad =
        (oneStepDirichletAxisLocalSolution M n h omega p
          (centre i) mm hh).grad) ∧
      (∀ i omega,
        F.toCellFamily.localHarmonic i omega ≤
          ((d : ℝ) ^ 2 * nfAxisHarmonicConst d hd) *
            oneStepNestedHarmonicWeight d hd (nfAxisHarmonicDepth d hd) N *
            oneStepNeumannDirichletAxisCoordinateSum M n h p
              (centre i) mm omega hh) ∧
      (∀ i omega,
        F.toCellFamily.outerHarmonic i omega ≤
          ((d : ℝ) ^ 2 * nfAxisHarmonicConst d hd) *
            oneStepNestedHarmonicWeight d hd (nfAxisHarmonicDepth d hd) N *
            nfAxisOuterCoordinateSum M n h omega p (centre i)
              K mm (hpar i) hh) := by
  classical
  set depth := nfAxisHarmonicDepth d hd with hdepth
  have hL : (0 : ℝ) < cubeScaleFactor (originCube d mm) :=
    nfAxisParent_side_pos d mm
  have hcellParent : ∀ i,
      openCubeSet (cell i) ⊆
        axisCube (oneStepCenteredAxisCorner (centre i) mm)
          (cubeScaleFactor (originCube d mm)) := fun i =>
    (hinner i).trans (nfAxisConcentric_subset_parent d _ _ hL (depth + 1))
  -- the two harmonic radii on each cell
  have hlocal : ∀ (i : ι) (omega : NFSample d),
      ∃ uS : H1Function
          (axisCubeInnerHalf (oneStepCenteredAxisCorner (centre i) mm)
            (cubeScaleFactor (originCube d mm))),
        uS.toFun = (oneStepNeumannDirichletAxisRemainder M n h omega p
            (centre i) mm hh).toFun ∧
        uS.grad = (oneStepNeumannDirichletAxisRemainder M n h omega p
            (centre i) mm hh).grad ∧
        ∃ H : HasWeakHessianOn _ uS,
          oneStepCellB (cell i)
              (H.restrict (isOpen_openCubeSet (cell i)) (hhalf i)) ≤
            cubeScaleFactor (cell i) * (d : ℝ) ^ 2 *
              ((triadicAxisNormalizedMeasureRatio (cell i)
                (CubeCalderonZygmund.axisCubeConcentricDepthSide
                  (cubeScaleFactor (originCube d mm)) (depth + 1))) ^
                (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
              (nfAxisHarmonicConst d hd *
                (cubeScaleFactor (originCube d mm))⁻¹ *
                oneStepNeumannDirichletAxisCoordinateSum M n h p
                  (centre i) mm omega hh) := fun i omega =>
    nfAxisHarmonic_cell_hessian d hd _ _ hL
      (oneStepNeumannDirichletAxisRemainder M n h omega p
        (centre i) mm hh)
      (oneStepNeumannDirichletAxisRemainder_harmonic M n h omega p
        (centre i) mm hh)
      (cell i) (hhalf i) (hinner i)
  have houter : ∀ (i : ι) (omega : NFSample d),
      ∃ uS : H1Function
          (axisCubeInnerHalf (oneStepCenteredAxisCorner (centre i) mm)
            (cubeScaleFactor (originCube d mm))),
        uS.toFun = (oneStepNeumannAxisRemainder M n h omega p
            (centre i) K mm (hpar i) hh).toFun ∧
        uS.grad = (oneStepNeumannAxisRemainder M n h omega p
            (centre i) K mm (hpar i) hh).grad ∧
        ∃ H : HasWeakHessianOn _ uS,
          oneStepCellB (cell i)
              (H.restrict (isOpen_openCubeSet (cell i)) (hhalf i)) ≤
            cubeScaleFactor (cell i) * (d : ℝ) ^ 2 *
              ((triadicAxisNormalizedMeasureRatio (cell i)
                (CubeCalderonZygmund.axisCubeConcentricDepthSide
                  (cubeScaleFactor (originCube d mm)) (depth + 1))) ^
                (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal *
              (nfAxisHarmonicConst d hd *
                (cubeScaleFactor (originCube d mm))⁻¹ *
                nfAxisOuterCoordinateSum M n h omega p (centre i)
                  K mm (hpar i) hh) := fun i omega =>
    nfAxisHarmonic_cell_hessian d hd _ _ hL
      (oneStepNeumannAxisRemainder M n h omega p (centre i) K mm
        (hpar i) hh)
      (oneStepNeumannAxisRemainder_harmonic M n h omega p
        (centre i) K mm (hpar i) hh)
      (cell i) (hhalf i) (hinner i)
  choose uLoc _hLocFun hLocGrad HLoc hLocBound using hlocal
  choose uOut _hOutFun hOutGrad HOut hOutBound using houter
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
       localHarmonic := fun i omega =>
          (uLoc i omega).restrict (isOpen_openCubeSet (cell i)) (hhalf i),
       outerHarmonic := fun i omega =>
          (uOut i omega).restrict (isOpen_openCubeSet (cell i)) (hhalf i),
       grad_split := ?_,
       dirichletHessian := fun i omega =>
          (HDpar i omega).restrict (isOpen_openCubeSet (cell i))
            (hcellParent i),
       localHarmonicHessian := fun i omega =>
          (HLoc i omega).restrict (isOpen_openCubeSet (cell i)) (hhalf i),
       outerHarmonicHessian := fun i omega =>
          (HOut i omega).restrict (isOpen_openCubeSet (cell i)) (hhalf i),
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
        ((uLoc i omega).grad x + (uOut i omega).grad x)
    rw [hLocGrad i omega, hOutGrad i omega]
    exact hsplit
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
      (measurable_nfAxisLocalDirichlet_grad M n h p (centre i)
        mm hh)
      (fun _omega => rfl)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (hcellParent i)
      (fun omega => oneStepNeumannDirichletAxisRemainder M n h omega p
        (centre i) mm hh)
      _
      (measurable_nfAxisNeumannDirichletRemainder_grad M n h p
        (centre i) mm hh)
      (fun omega => hLocGrad i omega)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict
      (hcellParent i)
      (fun omega => oneStepNeumannAxisRemainder M n h omega p
        (centre i) K mm (hpar i) hh)
      _
      (measurable_nfAxisNeumannRemainder_grad M n h p (centre i)
        K mm (hpar i) hh)
      (fun omega => hOutGrad i omega)
  · intro i omega
    exact oneStepNeumannAxisLargeRestriction_grad M n h omega p
      (centre i) K mm (hpar i) hh
  · intro i omega
    rfl
  · intro i omega
    rw [toCellFamily_localHarmonic_eq]
    refine (hLocBound i omega).trans_eq ?_
    exact nfAxisHarmonic_prefactor_eq_nestedWeight' d hd N (cell i)
      (hscale i)
      (oneStepNeumannDirichletAxisCoordinateSum M n h p
        (centre i) mm omega hh)
  · intro i omega
    rw [toCellFamily_outerHarmonic_eq]
    refine (hOutBound i omega).trans_eq ?_
    exact nfAxisHarmonic_prefactor_eq_nestedWeight' d hd N (cell i)
      (hscale i)
      (nfAxisOuterCoordinateSum M n h omega p (centre i) K mm
        (hpar i) hh)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
