import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedCellMinimizers
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVariationalPatching
import Homogenization.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarInvAveraged
import Homogenization.Geometry.BoundaryLayer




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Extension by zero preserves vector `L²` membership across a measurable
subset inclusion. -/
theorem oneStep_memVectorL2_indicator_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ U)
    {f : Vec d → Vec d} (hf : MemVectorL2 V f) :
    MemVectorL2 U (V.indicator f) := by
  refine (memLp_indicator_iff_restrict hV).2 ?_
  rwa [Measure.restrict_restrict hV, Set.inter_eq_self_of_subset_left hVU]

/-- A zero-normal-trace field on a cell remains zero-normal-trace after
extension by zero to an ambient domain. -/
theorem oneStep_isSolenoidalZeroNormalTraceOn_indicator_of_subset {d : ℕ}
    {U V : Set (Vec d)} (hVopen : IsOpen V) (hVU : V ⊆ U)
    {g : Vec d → Vec d} (hg : IsSolenoidalZeroNormalTraceOn V g) :
    IsSolenoidalZeroNormalTraceOn U (V.indicator g) := by
  intro phi
  have hfun : (fun x => vecDot (V.indicator g x) (phi.grad x)) =
      V.indicator (fun y => vecDot (g y) (phi.grad y)) := by
    funext x
    by_cases hx : x ∈ V
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  calc
    ∫ x in U, vecDot (V.indicator g x) (phi.grad x) ∂volume =
        ∫ x in U, V.indicator (fun y => vecDot (g y) (phi.grad y)) x ∂volume := by
          rw [hfun]
    _ = ∫ x in U ∩ V, vecDot (g x) (phi.grad x) ∂volume :=
      setIntegral_indicator hVopen.measurableSet
    _ = ∫ x in V, vecDot (g x) (phi.grad x) ∂volume := by
      rw [Set.inter_eq_self_of_subset_right hVU]
    _ = 0 := hg (phi.restrict hVopen hVU)

/-- The pointwise sum of a finite family of vector `L²` fields is in vector
`L²`. -/
theorem oneStep_memVectorL2_finsetSum {d : ℕ} {U : Set (Vec d)}
    {I : Type*} (s : Finset I) (f : I → Vec d → Vec d)
    (hf : ∀ i ∈ s, MemVectorL2 U (f i)) :
    MemVectorL2 U (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact MeasureTheory.MemLp.zero
  | @insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hf
      simpa [Finset.sum_insert hi] using hf.1.add (ih hf.2)

/-- The pointwise sum of finitely many vector-`L²`, zero-normal-trace fields
is again zero-normal-trace. -/
theorem oneStep_isSolenoidalZeroNormalTraceOn_finsetSum {d : ℕ}
    {U : Set (Vec d)} {I : Type*} (s : Finset I)
    (f : I → Vec d → Vec d)
    (hfL2 : ∀ i ∈ s, MemVectorL2 U (f i))
    (hfSol : ∀ i ∈ s, IsSolenoidalZeroNormalTraceOn U (f i)) :
    IsSolenoidalZeroNormalTraceOn U (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isSolenoidalZeroNormalTraceOn_zero (U := U) (d := d))
  | @insert i s hi ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hfL2 hfSol
      simpa [Finset.sum_insert hi] using
        isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
          hfL2.1 (oneStep_memVectorL2_finsetSum s f hfL2.2)
          hfSol.1 (ih hfL2.2 hfSol.2)

/-! ## Direct insertion into the dual variational problem -/

/-- Any `L²` flux in the affine zero-normal-trace class is an admissible
competitor for the starred coarse coefficient.  This is the nonconstant-flux
counterpart of CoarseGraining's averaged constant-flux bound and is the exact
variational insertion needed after gluing the cell Neumann minimizers. -/
theorem vecDot_sigmaStarInvCoarse_le_volumeAverage_lowerRight_energy
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hvol : (volume U).toReal ≠ 0)
    (hMuResp : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a)
    (q : Vec d) (g : Vec d → Vec d)
    (hg : MemVectorL2 U g)
    (hgSol : IsSolenoidalZeroNormalTraceOn U (fun x => g x - q)) :
    vecDot q (matVecMul (sigmaStarInvCoarse U a) q) ≤
      volumeAverage U (fun x =>
        vecDot (g x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (g x))) := by
  let P : BlockVec d := (0, q)
  let X : BlockState d :=
    { potential := fun _ => 0
      flux := g }
  have hX : IsBlockMuAdmissible U P X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hzero : (fun x => X.potential x - P.1) =
          (0 : Vec d → Vec d) := by
        funext x
        simp [X, P]
      rw [hzero]
      exact MemLp.zero
    · have hzero : (fun x => X.potential x - P.1) =
          (0 : Vec d → Vec d) := by
        funext x
        simp [X, P]
      rw [hzero]
      exact isPotentialZeroTraceOn_zero (U := U)
    · simpa [X, P] using hg.sub (memLp_const q)
    · simpa [X, P] using hgSol
  have hBddBelow : BddBelow (muValueSet U P a) := by
    refine ⟨0, ?_⟩
    intro value hvalue
    rcases hvalue with ⟨Y, hY, rfl⟩
    have hLower : vecDot P.1 P.2 ≤ blockEnergyAverage U a Y :=
      hY.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
        (hY.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll)
        hEll
        (by
          simpa [sub_eq_add_neg] using
            IsPotentialZeroTraceOn.integral_eq_zero hY.isPotentialZeroTrace)
        (by
          simpa [sub_eq_add_neg] using
            IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU
              hY.isSolenoidalZeroNormalTrace)
        hvol
    have hLower' : 0 ≤ blockEnergyAverage U a Y := by
      simpa [P, vecDot_zero_left] using hLower
    simpa [blockEnergyAverage] using hLower'
  have hMuLe : Mu U P a ≤ volumeAverage U (blockEnergyDensity a X) := by
    unfold Mu
    exact csInf_le hBddBelow (muValueSet_mem hX)
  have hAc : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  have hMuEq : Mu U P a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
    calc
      Mu U P a =
          (1 / 2 : ℝ) * blockVecDot P
            (blockMatVecMul (coarseBlockMatrix U a) P) := by
              rw [hAc.2 P]
      _ = (1 / 2 : ℝ) * vecDot q
          (matVecMul ((coarseBlockMatrix U a).lowerRight) q) := by
            simp [P, blockVecDot, matVecMul_zero, vecDot_zero_left]
      _ = (1 / 2 : ℝ) * vecDot q
          (matVecMul (sigmaStarInvCoarse U a) q) := by
            rw [coarseBlockMatrix_lowerRight_eq_sigmaStarInvCoarse_of_mu_zero_right_eq_responseJ_zero
              (U := U) (a := a) hex hMuResp]
  have hEnergy : blockEnergyDensity a X = fun x =>
      (1 / 2 : ℝ) * vecDot (g x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (g x)) := by
    funext x
    simp [X, blockEnergyDensity, BlockState.eval, blockCoeffField,
      blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
  rw [hMuEq, hEnergy] at hMuLe
  have hAvgHalf :
      volumeAverage U (fun x => (1 / 2 : ℝ) * vecDot (g x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (g x))) =
        (1 / 2 : ℝ) * volumeAverage U (fun x => vecDot (g x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (g x))) := by
    simpa [smul_eq_mul] using volumeAverage_smul U (1 / 2 : ℝ)
      (fun x => vecDot (g x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (g x)))
  rw [hAvgHalf] at hMuLe
  linarith

/-- The finite sum of the selected cell residuals, each extended by zero to
the parent cube. -/
def oneStepGluedNeumannResidual {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (residual : TriadicCube d → Vec d → Vec d) :
    Vec d → Vec d :=
  fun x => ∑ R ∈ descendantsAtDepth Q j,
    (openCubeSet R).indicator (residual R) x

/-- A point inside one descendant cell sees exactly that cell's residual. -/
theorem oneStepGluedNeumannResidual_eq_of_mem {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (residual : TriadicCube d → Vec d → Vec d)
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    oneStepGluedNeumannResidual Q j residual x = residual R x := by
  classical
  unfold oneStepGluedNeumannResidual
  rw [Finset.sum_eq_single R]
  · exact Set.indicator_of_mem hx _
  · intro S hS hSR
    refine Set.indicator_of_notMem (fun hxS => ?_) _
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j hS hR hSR) hxS hx
  · intro h
    exact (h hR).elim

/-- Cellwise vector `L²` residuals glue to a parent-domain vector `L²`
field. -/
theorem oneStepGluedNeumannResidual_memVectorL2 {d : ℕ}
    (Q : TriadicCube d) (j : ℕ)
    (residual : TriadicCube d → Vec d → Vec d)
    (hL2 : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (residual R)) :
    MemVectorL2 (openCubeSet Q) (oneStepGluedNeumannResidual Q j residual) := by
  unfold oneStepGluedNeumannResidual
  apply oneStep_memVectorL2_finsetSum
  intro R hR
  exact oneStep_memVectorL2_indicator_of_subset
    (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR) (hL2 R hR)

/-- Cellwise zero-normal-trace residuals glue to a zero-normal-trace residual
on the parent cube. -/
theorem oneStepGluedNeumannResidual_zeroNormalTrace {d : ℕ}
    (Q : TriadicCube d) (j : ℕ)
    (residual : TriadicCube d → Vec d → Vec d)
    (hL2 : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (residual R))
    (hSol : ∀ R ∈ descendantsAtDepth Q j,
      IsSolenoidalZeroNormalTraceOn (openCubeSet R) (residual R)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (oneStepGluedNeumannResidual Q j residual) := by
  unfold oneStepGluedNeumannResidual
  apply oneStep_isSolenoidalZeroNormalTraceOn_finsetSum
  · intro R hR
    exact oneStep_memVectorL2_indicator_of_subset
      (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR) (hL2 R hR)
  · intro R hR
    exact oneStep_isSolenoidalZeroNormalTraceOn_indicator_of_subset
      (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR) (hSol R hR)

/-! ## Selected cell minimizers and their literal finite glues -/

/-- The selected primal minimizer on a descendant cell.  Keeping the
membership proof explicit avoids any junk-value branch in the actual
variational carrier. -/
def oneStepSelectedDirichletCell {d : ℕ} [NeZero d]
    {Q : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (F : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
    OneStepDirichletCellMinimizer R a (F R) :=
  oneStepDirichletCellMinimizer R (hEll R hR) (F R) (hF R hR)

/-- The selected dual minimizer on a descendant cell. -/
def oneStepSelectedNeumannCell {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R))
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
    OneStepNeumannCellMinimizer R a (G R) :=
  oneStepNeumannCellMinimizer R (hEll R hR) (G R) (hG R hR)

/-- The literal list of zero-extended selected primal corrections.  This is
the list inserted into `oneStepPatchedCompetitor`. -/
def oneStepSelectedDirichletPatchList {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (F : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R)) :
    List (H10Function (openCubeSet Q)) :=
  (descendantsAtDepth Q j).attach.toList.map fun R =>
    oneStepZeroExtendedCorrection Q R.1
      (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
      (oneStepSelectedDirichletCell a F hEll hF R.1 R.2).correction

/-- The source's paired primal patch `chi_z + phi_z`, selected separately for
the cell mean and centered fluctuation and then extended by zero. -/
def oneStepSelectedDirichletTwoPatchList {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R)) :
    List (H10Function (openCubeSet Q)) :=
  (descendantsAtDepth Q j).attach.toList.map fun R =>
    oneStepCellPatch Q R.1
      (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
      (oneStepSelectedDirichletCell a P hEll hP R.1 R.2).correction
      (oneStepSelectedDirichletCell a F hEll hF R.1 R.2).correction

/-- Exact selected primal cell energy.  This specializes the minimizer
identity to a concrete descendant and is the deterministic input for the
`A_z/B_z` Besov estimate. -/
theorem oneStepSelectedDirichletCell_energy_identity {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (F : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) :
    ∫ x in openCubeSet R,
        vecDot
          ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)
          (matVecMul (a x)
            ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)) ∂volume =
      ∫ x in openCubeSet R,
        vecDot (F R x)
          (matVecMul (a x)
            ((oneStepSelectedDirichletCell a F hEll hF R hR).field x)) ∂volume := by
  exact (oneStepSelectedDirichletCell a F hEll hF R hR).energy_identity
    (hEll R hR) (hF R hR)

/-- Totalized selected dual residual family.  Only the descendant branch is
used by the glue; outside the finite family it is definitionally zero. -/
def oneStepSelectedNeumannResidualFamily {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R)) :
    TriadicCube d → Vec d → Vec d :=
  fun R => if hR : R ∈ descendantsAtDepth Q j then
    (oneStepSelectedNeumannCell a G hEll hG R hR).residual
  else 0

theorem oneStepSelectedNeumannResidualFamily_eq {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hG : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (G S))
    (hR : R ∈ descendantsAtDepth Q j) :
    oneStepSelectedNeumannResidualFamily a G hEll hG R =
      (oneStepSelectedNeumannCell a G hEll hG R hR).residual := by
  simp only [oneStepSelectedNeumannResidualFamily, dif_pos hR]

/-- The selected dual residuals glue to a parent-domain vector `L²` field. -/
theorem oneStepSelectedGluedNeumannResidual_memVectorL2 {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R)) :
    MemVectorL2 (openCubeSet Q)
      (oneStepGluedNeumannResidual Q j
        (oneStepSelectedNeumannResidualFamily a G hEll hG)) := by
  apply oneStepGluedNeumannResidual_memVectorL2
  intro R hR
  rw [oneStepSelectedNeumannResidualFamily_eq a G hEll hG hR]
  exact (oneStepSelectedNeumannCell a G hEll hG R hR).flux_memVectorL2
      (hEll R hR) |>.sub (hG R hR)

/-- The literal dual cell glue is an admissible zero-normal-trace correction
on the parent cube. -/
theorem oneStepSelectedGluedNeumannResidual_zeroNormalTrace {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (oneStepGluedNeumannResidual Q j
        (oneStepSelectedNeumannResidualFamily a G hEll hG)) := by
  apply oneStepGluedNeumannResidual_zeroNormalTrace
  · intro R hR
    rw [oneStepSelectedNeumannResidualFamily_eq a G hEll hG hR]
    exact (oneStepSelectedNeumannCell a G hEll hG R hR).flux_memVectorL2
        (hEll R hR) |>.sub (hG R hR)
  · intro R hR
    rw [oneStepSelectedNeumannResidualFamily_eq a G hEll hG hR]
    exact (oneStepSelectedNeumannCell a G hEll hG R hR).residual_zeroNormalTrace
      (hEll R hR) (hG R hR)

/-- The actual glued dual competitor: a supplied parent-domain background is
corrected by the selected cell residuals. -/
def oneStepSelectedGluedNeumannFlux {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R)) : Vec d → Vec d :=
  background + oneStepGluedNeumannResidual Q j
    (oneStepSelectedNeumannResidualFamily a G hEll hG)

/-- The selected glued dual competitor is a parent-domain vector `L²`
field.  Together with
`oneStepSelectedGluedNeumannFlux_sub_const_zeroNormalTrace`, this is the
literal admissibility package for the manuscript's patched Neumann flux. -/
theorem oneStepSelectedGluedNeumannFlux_memVectorL2 {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background) :
    MemVectorL2 (openCubeSet Q)
      (oneStepSelectedGluedNeumannFlux Q j a G background hEll hG) := by
  exact hBackgroundL2.add
    (oneStepSelectedGluedNeumannResidual_memVectorL2 Q j a G hEll hG)

/-- Adding the glued cell residuals preserves the parent's prescribed flux
class.  This is the exact dual admissibility statement used before inserting
the localized field into the Neumann variational problem. -/
theorem oneStepSelectedGluedNeumannFlux_sub_const_zeroNormalTrace {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    (q : Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => background x - q)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => oneStepSelectedGluedNeumannFlux Q j a G background hEll hG x - q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let residual := oneStepGluedNeumannResidual Q j
    (oneStepSelectedNeumannResidualFamily a G hEll hG)
  have hresL2 : MemVectorL2 (openCubeSet Q) residual :=
    oneStepSelectedGluedNeumannResidual_memVectorL2 Q j a G hEll hG
  have hbaseL2 : MemVectorL2 (openCubeSet Q) (fun x => background x - q) :=
    hBackgroundL2.sub (MeasureTheory.memLp_const q)
  have hadd := isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
    hbaseL2 hresL2 hBackground
    (oneStepSelectedGluedNeumannResidual_zeroNormalTrace Q j a G hEll hG)
  convert hadd using 1
  funext x
  simp only [oneStepSelectedGluedNeumannFlux, Pi.add_apply]
  abel

/-- Insert the selected glued flux into the parent starred variational
problem.  The remaining source calculation is now solely the partition of
this displayed inverse energy into the principal, mixed, and oscillatory cell
terms. -/
theorem vecDot_sigmaStarInvCoarse_le_selectedGluedNeumannFluxEnergy {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    (q : Vec d) {lam Lam : ℝ}
    (hEllParent : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hG : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (G R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => background x - q))
    (hex : ∃ Abar : BlockMat d,
      IsCoarseBlockMatrix (openCubeSet Q) a Abar)
    (hMuResp : ∀ r : Vec d,
      Mu (openCubeSet Q) (0, r) a = ResponseJ (openCubeSet Q) 0 r a) :
    vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) ≤
      volumeAverage (openCubeSet Q) (fun x =>
        let flux := oneStepSelectedGluedNeumannFlux
          Q j a G background hEll hG x
        vecDot flux
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) flux)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 := by
    simpa [volume_openCubeSet_toReal] using (cubeVolume_pos Q).ne'
  apply vecDot_sigmaStarInvCoarse_le_volumeAverage_lowerRight_energy
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain
    hEllParent hex hvol hMuResp
  · exact oneStepSelectedGluedNeumannFlux_memVectorL2
      Q j a G background hEll hG hBackgroundL2
  · exact oneStepSelectedGluedNeumannFlux_sub_const_zeroNormalTrace
      Q j a G background q hEll hG hBackgroundL2 hBackground

/-- On a cell where the supplied background equals its local prescribed
field, the glued dual competitor is exactly the selected cell flux. -/
theorem oneStepSelectedGluedNeumannFlux_eq_of_mem {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hG : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (G S))
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R) (hbackground : background x = G R x) :
    oneStepSelectedGluedNeumannFlux Q j a G background hEll hG x =
      (oneStepSelectedNeumannCell a G hEll hG R hR).flux x := by
  rw [oneStepSelectedGluedNeumannFlux, Pi.add_apply,
    oneStepGluedNeumannResidual_eq_of_mem _ hR hx,
    oneStepSelectedNeumannResidualFamily_eq a G hEll hG hR,
    hbackground]
  unfold OneStepNeumannCellMinimizer.residual
  abel

/-- Exact selected dual cell energy identity. -/
theorem oneStepSelectedNeumannCell_energy_identity {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (G : TriadicCube d → Vec d → Vec d) {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hG : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (G S))
    (hR : R ∈ descendantsAtDepth Q j) :
    ∫ x in openCubeSet R,
        vecDot
          ((oneStepSelectedNeumannCell a G hEll hG R hR).potential.toH1Function.grad x)
          ((oneStepSelectedNeumannCell a G hEll hG R hR).flux x) ∂volume =
      ∫ x in openCubeSet R,
        vecDot (G R x)
          ((oneStepSelectedNeumannCell a G hEll hG R hR).potential.toH1Function.grad x)
          ∂volume := by
  exact (oneStepSelectedNeumannCell a G hEll hG R hR).energy_identity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
