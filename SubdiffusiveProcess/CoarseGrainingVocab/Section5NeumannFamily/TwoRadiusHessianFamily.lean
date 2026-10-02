import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.PieceGradientMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout

/-!
# The two-radius Neumann Hessian family, constructed

This module builds a term of

```
OneStepTwoRadiusNeumannHessianFamily d ι (PotentialSample d) s cell
```

whose `neumann` field is the literal one-step Neumann corrector on the large
cube `originCube d K`, restricted to each source cell.  The three-piece
telescope, the weak Hessians, the Borel measurability of the four gradient
classes, and the two harmonic cell bounds are all supplied.

Geometric input: each cell sits inside the fixed concentric high-exponent
region of its own triadic parent, and each parent sits inside the large cube.
Everything else is derived.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-! ## The fixed harmonic depth and constant -/

/-- The interior depth selected by the arbitrary-centre harmonic package. -/
def twoRadiusHarmonicDepth (d : ℕ) (hd : 3 ≤ d) : ℕ :=
  (exists_twoRadius_harmonic_cell_hessian d hd).choose

/-- The constant selected by the arbitrary-centre harmonic package. -/
def twoRadiusHarmonicConst (d : ℕ) (hd : 3 ≤ d) : ℝ :=
  (exists_twoRadius_harmonic_cell_hessian d hd).choose_spec.choose

theorem twoRadiusHarmonicConst_pos (d : ℕ) (hd : 3 ≤ d) :
    0 < twoRadiusHarmonicConst d hd :=
  (exists_twoRadius_harmonic_cell_hessian d hd).choose_spec.choose_spec.1

/-- Endpoint form of the arbitrary-centre harmonic cell package. -/
theorem twoRadiusHarmonic_cell_hessian (d : ℕ) (hd : 3 ≤ d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (hu : WeakPoissonEquationOn (openCubeSet Q) u (fun _ ↦ 0))
    (R : TriadicCube d)
    (hRhalf : openCubeSet R ⊆ twoRadiusInnerHalf Q)
    (hRinner : openCubeSet R ⊆
      twoRadiusConcentric Q (twoRadiusHarmonicDepth d hd)) :
    ∃ (w : H1Function (openCubeSet R))
      (H : HasWeakHessianOn (openCubeSet R) w),
      w.grad = u.grad ∧
      oneStepCellB R H ≤
        twoRadiusHarmonicCellFactor d hd (twoRadiusHarmonicDepth d hd) Q R *
          (twoRadiusHarmonicConst d hd * (cubeScaleFactor Q)⁻¹ *
            twoRadiusParentCoordinateSum Q u) :=
  (exists_twoRadius_harmonic_cell_hessian d hd).choose_spec.choose_spec.2
    Q u hu R hRhalf hRinner

/-! ## Geometry of the concentric region -/

/-- The concentric high-exponent region sits in the inner half. -/
theorem twoRadiusConcentric_subset_innerHalf (Q : TriadicCube d) (depth : ℕ) :
    twoRadiusConcentric Q depth ⊆ twoRadiusInnerHalf Q :=
  concentricDepthAxisCube_subset_axisCubeInnerHalf (twoRadiusAxisCorner Q)
    (cubeScaleFactor Q) (twoRadius_cubeScaleFactor_pos Q) (depth + 1)
    (Nat.succ_le_succ (Nat.zero_le _))

/-- The concentric high-exponent region sits in the parent cube. -/
theorem twoRadiusConcentric_subset_parent (Q : TriadicCube d) (depth : ℕ) :
    twoRadiusConcentric Q depth ⊆ openCubeSet Q := by
  rw [openCubeSet_eq_axisCube_twoRadius Q]
  have hsub := concentricDepthAxisCube_subset_of_le (twoRadiusAxisCorner Q)
    (cubeScaleFactor Q) (twoRadius_cubeScaleFactor_pos Q)
    (a := 0) (b := depth + 1) (Nat.zero_le _)
  simpa [twoRadiusConcentric] using hsub

/-! ## The family -/

/-- The literal two-radius Neumann Hessian family.

`neumann` is the large-cube one-step Neumann corrector restricted to the
cell; `dirichlet` is the canonical translated local Dirichlet solution on the
cell's triadic parent; `localHarmonic` and `outerHarmonic` are the two
harmonic radii, with the interior weak Hessians supplied by the
arbitrary-centre harmonic package. -/
theorem exists_twoRadiusNeumannHessianFamily
    [NeZero d] (hd : 3 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (hh : 0 < h)
    {ι : Type*} (s : Finset ι) (parent cell : ι → TriadicCube d)
    (hparentK : ∀ i, openCubeSet (parent i) ⊆ openCubeSet (originCube d K))
    (hcellInner : ∀ i, openCubeSet (cell i) ⊆
      twoRadiusConcentric (parent i) (twoRadiusHarmonicDepth d hd)) :
    ∃ F : OneStepTwoRadiusNeumannHessianFamily d ι (NFSample d) s cell,
      (∀ i omega, (F.neumann i omega).grad =
        (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad) ∧
      (∀ i omega, (F.dirichlet i omega).grad =
        (twoRadiusLocalDirichletPiece M n h p (parent i) omega hh).grad) ∧
      (∀ i omega, (F.localHarmonic i omega).grad =
        (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh).grad) ∧
      (∀ i omega, (F.outerHarmonic i omega).grad =
        (twoRadiusOuterHarmonicPiece M n h p K (parent i)
          (hparentK i) omega hh).grad) ∧
      (∀ i omega,
        oneStepCellB (cell i) (F.localHarmonicHessian i omega) ≤
          twoRadiusHarmonicCellFactor d hd (twoRadiusHarmonicDepth d hd)
              (parent i) (cell i) *
            (twoRadiusHarmonicConst d hd * (cubeScaleFactor (parent i))⁻¹ *
              twoRadiusParentCoordinateSum (parent i)
                (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh))) ∧
      (∀ i omega,
        oneStepCellB (cell i) (F.outerHarmonicHessian i omega) ≤
          twoRadiusHarmonicCellFactor d hd (twoRadiusHarmonicDepth d hd)
              (parent i) (cell i) *
            (twoRadiusHarmonicConst d hd * (cubeScaleFactor (parent i))⁻¹ *
              twoRadiusParentCoordinateSum (parent i)
                (twoRadiusOuterHarmonicPiece M n h p K (parent i)
                  (hparentK i) omega hh))) := by
  classical
  have hcellHalf : ∀ i, openCubeSet (cell i) ⊆ twoRadiusInnerHalf (parent i) :=
    fun i => (hcellInner i).trans
      (twoRadiusConcentric_subset_innerHalf (parent i) _)
  have hcellParent : ∀ i, openCubeSet (cell i) ⊆ openCubeSet (parent i) :=
    fun i => (hcellInner i).trans
      (twoRadiusConcentric_subset_parent (parent i) _)
  -- the two harmonic radii, with their interior weak Hessians
  have hlocal : ∀ (i : ι) (omega : NFSample d),
      ∃ (w : H1Function (openCubeSet (cell i)))
        (H : HasWeakHessianOn (openCubeSet (cell i)) w),
        w.grad = (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh).grad ∧
        oneStepCellB (cell i) H ≤
          twoRadiusHarmonicCellFactor d hd (twoRadiusHarmonicDepth d hd)
              (parent i) (cell i) *
            (twoRadiusHarmonicConst d hd * (cubeScaleFactor (parent i))⁻¹ *
              twoRadiusParentCoordinateSum (parent i)
                (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh)) :=
    fun i omega =>
      twoRadiusHarmonic_cell_hessian d hd (parent i)
        (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh)
        (twoRadiusLocalHarmonicPiece_harmonic M n h p (parent i) omega hh)
        (cell i) (hcellHalf i) (hcellInner i)
  have houter : ∀ (i : ι) (omega : NFSample d),
      ∃ (w : H1Function (openCubeSet (cell i)))
        (H : HasWeakHessianOn (openCubeSet (cell i)) w),
        w.grad = (twoRadiusOuterHarmonicPiece M n h p K (parent i)
          (hparentK i) omega hh).grad ∧
        oneStepCellB (cell i) H ≤
          twoRadiusHarmonicCellFactor d hd (twoRadiusHarmonicDepth d hd)
              (parent i) (cell i) *
            (twoRadiusHarmonicConst d hd * (cubeScaleFactor (parent i))⁻¹ *
              twoRadiusParentCoordinateSum (parent i)
                (twoRadiusOuterHarmonicPiece M n h p K (parent i)
                  (hparentK i) omega hh)) :=
    fun i omega =>
      twoRadiusHarmonic_cell_hessian d hd (parent i)
        (twoRadiusOuterHarmonicPiece M n h p K (parent i) (hparentK i) omega hh)
        (twoRadiusOuterHarmonicPiece_harmonic M n h p K (parent i)
          (hparentK i) omega hh)
        (cell i) (hcellHalf i) (hcellInner i)
  choose wLoc HLoc hwLocGrad hwLocBound using hlocal
  choose wOut HOut hwOutGrad hwOutBound using houter
  -- the persistent Dirichlet member
  let HDpar : ∀ i, ∀ omega : NFSample d,
      HasWeakHessianOn (openCubeSet (parent i))
        (twoRadiusLocalDirichletPiece M n h p (parent i) omega hh) := fun i =>
    (nonempty_twoRadiusLocalDirichletPiece_parentHessian d M n h p
      (parent i) hh).some
  let uDir : ∀ i, NFSample d → H1Function (openCubeSet (cell i)) :=
    fun i omega =>
      (twoRadiusLocalDirichletPiece M n h p (parent i) omega hh).restrict
        (isOpen_openCubeSet (cell i)) (hcellParent i)
  let HDir : ∀ i, ∀ omega, HasWeakHessianOn (openCubeSet (cell i))
      (uDir i omega) := fun i omega =>
    (HDpar i omega).restrict (isOpen_openCubeSet (cell i)) (hcellParent i)
  let uNeu : ∀ i, NFSample d → H1Function (openCubeSet (cell i)) :=
    fun i omega =>
      (twoRadiusLargePiece M n h p K (parent i) (hparentK i) omega hh).restrict
        (isOpen_openCubeSet (cell i)) (hcellParent i)
  refine ⟨{ neumann := uNeu
            dirichlet := uDir
            localHarmonic := wLoc
            outerHarmonic := wOut
            grad_split := ?_
            dirichletHessian := HDir
            localHarmonicHessian := HLoc
            outerHarmonicHessian := HOut
            measurable_neumann_grad := ?_
            measurable_dirichlet_grad := ?_
            measurable_localHarmonic_grad := ?_
            measurable_outerHarmonic_grad := ?_ },
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i omega
    show (twoRadiusLargePiece M n h p K (parent i) (hparentK i) omega hh).grad =
      fun x => _
    rw [twoRadius_grad_split M n h p K (parent i) (hparentK i) omega hh]
    funext x
    rw [hwLocGrad i omega, hwOutGrad i omega]
    rfl
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict (hcellParent i)
      (fun omega =>
        twoRadiusLargePiece M n h p K (parent i) (hparentK i) omega hh)
      (fun omega => uNeu i omega)
      (measurable_twoRadiusLargePiece_grad M n h p K (parent i)
        (hparentK i) hh)
      (fun _omega => rfl)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict (hcellParent i)
      (fun omega => twoRadiusLocalDirichletPiece M n h p (parent i) omega hh)
      (fun omega => uDir i omega)
      (measurable_twoRadiusLocalDirichletPiece_grad M n h p (parent i) hh)
      (fun _omega => rfl)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict (hcellParent i)
      (fun omega => twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh)
      (fun omega => wLoc i omega)
      (measurable_twoRadiusLocalHarmonicPiece_grad M n h p (parent i) hh)
      (fun omega => hwLocGrad i omega)
  · intro i _hi
    exact measurable_gradToHilbertVectorL2_of_grad_eq_restrict (hcellParent i)
      (fun omega =>
        twoRadiusOuterHarmonicPiece M n h p K (parent i) (hparentK i) omega hh)
      (fun omega => wOut i omega)
      (measurable_twoRadiusOuterHarmonicPiece_grad M n h p K (parent i)
        (hparentK i) hh)
      (fun omega => hwOutGrad i omega)
  · intro i omega
    rfl
  · intro i omega
    rfl
  · intro i omega
    exact hwLocGrad i omega
  · intro i omega
    exact hwOutGrad i omega
  · intro i omega
    exact hwLocBound i omega
  · intro i omega
    exact hwOutBound i omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
