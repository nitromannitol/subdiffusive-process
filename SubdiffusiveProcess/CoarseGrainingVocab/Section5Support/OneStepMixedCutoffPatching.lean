module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepConcreteCellCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedFiniteSplit

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The source's cell patch with its principal correction selected for
`aLow` and its oscillatory correction selected for `aHigh`. -/
def oneStepSelectedMixedCutoffDirichletPatchList {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (j : ℕ) (aLow aHigh : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet R) aLow)
    (hHigh : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet R) aHigh)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R)) :
    List (H10Function (openCubeSet Q)) :=
  (descendantsAtDepth Q j).attach.toList.map fun R ↦
    oneStepCellPatch Q R.1
      (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
      (oneStepSelectedDirichletCell aLow P hLow hP R.1 R.2).correction
      (oneStepSelectedDirichletCell aHigh F hHigh hF R.1 R.2).correction

/-- Inside a descendant, the mixed-cutoff correction fold is exactly the
sum of that descendant's two selected correction gradients. -/
theorem oneStepSelectedMixedCutoffDirichletPatchFold_grad_eq_of_mem
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (aLow aHigh : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S) aLow)
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S) aHigh)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    (oneStepFoldCorrections
      (oneStepSelectedMixedCutoffDirichletPatchList Q j aLow aHigh
        P F hLow hHigh hP hF)).toH1Function.grad x =
      (oneStepSelectedDirichletCell aLow P hLow hP R hR
        ).correction.toH1Function.grad x +
      (oneStepSelectedDirichletCell aHigh F hHigh hF R hR
        ).correction.toH1Function.grad x := by
  classical
  rw [oneStepSelectedMixedCutoffDirichletPatchList,
    oneStepFoldCorrections_grad_attach_map]
  rw [Finset.sum_eq_single ⟨R, hR⟩]
  · simp only [oneStepCellPatch_grad]
    rw [((oneStepSelectedDirichletCell aLow P hLow hP R hR).correction +
      (oneStepSelectedDirichletCell aHigh F hHigh hF R hR).correction
      ).zeroExtensionGrad_apply_of_mem hx]
    rfl
  · intro S _hS hSR
    simp only [oneStepCellPatch_grad]
    rw [((oneStepSelectedDirichletCell aLow P hLow hP S.1 S.2).correction +
      (oneStepSelectedDirichletCell aHigh F hHigh hF S.1 S.2).correction
      ).zeroExtensionGrad_apply_of_not_mem]
    intro hxS
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j S.2 hR
        (fun h ↦ hSR (Subtype.ext h))) hxS hx
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Literal cellwise gradient identity for the two-cutoff patched
Dirichlet competitor. -/
theorem oneStepPatchedCompetitor_mixedCutoff_grad_eq_of_mem
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (aLow aHigh : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S) aLow)
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S) aHigh)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (w : H10Function (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R)
    (hbase : w.toH1Function.grad x = P R x + F R x) :
    (oneStepPatchedCompetitor w
      (oneStepSelectedMixedCutoffDirichletPatchList Q j aLow aHigh
        P F hLow hHigh hP hF)).toH1Function.grad x =
      (oneStepSelectedDirichletCell aLow P hLow hP R hR).field x +
      (oneStepSelectedDirichletCell aHigh F hHigh hF R hR).field x := by
  change w.toH1Function.grad x +
      (oneStepFoldCorrections
        (oneStepSelectedMixedCutoffDirichletPatchList Q j aLow aHigh
          P F hLow hHigh hP hF)).toH1Function.grad x = _
  rw [oneStepSelectedMixedCutoffDirichletPatchFold_grad_eq_of_mem
    aLow aHigh P F hLow hHigh hP hF hR hx, hbase]
  unfold OneStepDirichletCellMinimizer.field
  abel

/-- Concrete mixed-cutoff form of the preceding patch identity.  The
principal correction is selected with `aLow`, the fluctuation correction
with `aHigh`, and the outer affine probe cancels against the cell mean exactly
as in the manuscript's Step 2 competitor. -/
theorem oneStepDirichlet_mixedCutoff_patchedTotalSlope_eq_of_mem
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (aLow aHigh : CoeffField d)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S) aLow)
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S) aHigh)
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    let P := fun S ↦
      oneStepDirichletCellMeanField M n h p Q S omega hh
    let F := fun S ↦
      oneStepDirichletCellFluctuationField M n h p Q S omega hh
    p + (oneStepPatchedCompetitor
        (oneStepTriadicDirichletSolution M n h p Q omega hh)
        (oneStepSelectedMixedCutoffDirichletPatchList Q j aLow aHigh
          P F hLow hHigh
          (oneStepDirichletCellMeanField_memVectorL2_of_descendant
            M n h p Q omega hh)
          (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
            M n h p Q omega hh))).toH1Function.grad x =
      (oneStepSelectedDirichletCell aLow P hLow
          (oneStepDirichletCellMeanField_memVectorL2_of_descendant
            M n h p Q omega hh) R hR).field x +
      (oneStepSelectedDirichletCell aHigh F hHigh
          (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
            M n h p Q omega hh) R hR).field x := by
  dsimp only
  change p +
      ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x +
        (oneStepFoldCorrections
          (oneStepSelectedMixedCutoffDirichletPatchList
            Q j aLow aHigh _ _ hLow hHigh _ _)).toH1Function.grad x) = _
  rw [oneStepSelectedMixedCutoffDirichletPatchFold_grad_eq_of_mem
      aLow aHigh _ _ hLow hHigh
        (oneStepDirichletCellMeanField_memVectorL2_of_descendant
          M n h p Q omega hh)
        (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
          M n h p Q omega hh) hR hx]
  have hbase :
      p + (oneStepTriadicDirichletSolution M n h p Q omega hh
        ).toH1Function.grad x =
        oneStepDirichletCellMeanField M n h p Q R omega hh x +
          oneStepDirichletCellFluctuationField M n h p Q R omega hh x :=
    (oneStepDirichletCellMean_add_fluctuation
      M n h p Q R omega hh x).symm
  rw [← add_assoc, hbase]
  unfold OneStepDirichletCellMinimizer.field
  abel

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
