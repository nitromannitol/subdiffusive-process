import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedEnergyIdentification
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteVolumeAssembly




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## Primal list-fold localization -/

private theorem oneStep_foldr_grad_eq_map_sum {d : ℕ}
    {U : Set (Vec d)} (l : List (H10Function U)) (x : Vec d) :
    l.foldr (fun u G => u.toH1Function.grad x + G) 0 =
      (l.map fun u => u.toH1Function.grad x).sum := by
  induction l with
  | nil => rfl
  | cons u us ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]

/-- The gradient of a correction fold indexed by a finite set is the
corresponding finite sum. -/
theorem oneStepFoldCorrections_grad_attach_map {d : ℕ}
    {U : Set (Vec d)} {I : Type*} [DecidableEq I]
    (s : Finset I) (f : s → H10Function U) (x : Vec d) :
    (oneStepFoldCorrections (s.attach.toList.map f)).toH1Function.grad x =
      ∑ i : s, (f i).toH1Function.grad x := by
  rw [oneStepFoldCorrections_grad]
  rw [oneStep_foldr_grad_eq_map_sum, List.map_map]
  let g : s → Vec d := fun i => (f i).toH1Function.grad x
  change (List.map g s.attach.toList).sum = ∑ i : s, g i
  calc
    (List.map g s.attach.toList).sum = s.attach.sum g :=
      Finset.sum_map_toList s.attach g
    _ = ∑ i : s, g i := by rw [Finset.attach_eq_univ]

/-- On the interior of one descendant, every zero-extended selected patch
except that descendant's patch vanishes. -/
theorem oneStepSelectedDirichletTwoPatchFold_grad_eq_of_mem
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    (oneStepFoldCorrections
      (oneStepSelectedDirichletTwoPatchList Q j a P F hEll hP hF)
      ).toH1Function.grad x =
      (oneStepSelectedDirichletCell a P hEll hP R hR
        ).correction.toH1Function.grad x +
      (oneStepSelectedDirichletCell a F hEll hF R hR
        ).correction.toH1Function.grad x := by
  classical
  rw [oneStepSelectedDirichletTwoPatchList,
    oneStepFoldCorrections_grad_attach_map]
  rw [Finset.sum_eq_single ⟨R, hR⟩]
  · simp only [oneStepCellPatch_grad]
    rw [((oneStepSelectedDirichletCell a P hEll hP R hR).correction +
      (oneStepSelectedDirichletCell a F hEll hF R hR).correction
      ).zeroExtensionGrad_apply_of_mem hx]
    rfl
  · intro S _hS hSR
    simp only [oneStepCellPatch_grad]
    rw [((oneStepSelectedDirichletCell a P hEll hP S.1 S.2).correction +
      (oneStepSelectedDirichletCell a F hEll hF S.1 S.2).correction
      ).zeroExtensionGrad_apply_of_not_mem]
    intro hxS
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j S.2 hR
        (fun h => hSR (Subtype.ext h))) hxS hx
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Literal cellwise gradient identity for the source's patched Dirichlet
competitor. -/
theorem oneStepPatchedCompetitor_selectedTwo_grad_eq_of_mem
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (w : H10Function (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R)
    (hbase : w.toH1Function.grad x = P R x + F R x) :
    (oneStepPatchedCompetitor w
      (oneStepSelectedDirichletTwoPatchList Q j a P F hEll hP hF)
      ).toH1Function.grad x =
      (oneStepSelectedDirichletCell a P hEll hP R hR).field x +
      (oneStepSelectedDirichletCell a F hEll hF R hR).field x := by
  change w.toH1Function.grad x +
      (oneStepFoldCorrections
        (oneStepSelectedDirichletTwoPatchList Q j a P F hEll hP hF)
        ).toH1Function.grad x = _
  rw [
    oneStepSelectedDirichletTwoPatchFold_grad_eq_of_mem
      a P F hEll hP hF hR hx, hbase]
  unfold OneStepDirichletCellMinimizer.field
  abel

/-! ## Exact local quadratic split -/

/-- Polarization of a symmetric matrix quadratic form in the precise
half-principal plus mixed plus half-oscillatory normalization of the source. -/
theorem oneStep_half_quadratic_add_eq {d : ℕ} (A : Mat d)
    (hA : A.IsSymm) (u v : Vec d) :
    (1 / 2 : ℝ) * vecDot (u + v) (matVecMul A (u + v)) =
      (1 / 2 : ℝ) * vecDot u (matVecMul A u) +
        vecDot u (matVecMul A v) +
        (1 / 2 : ℝ) * vecDot v (matVecMul A v) := by
  rw [matVecMul_add, vecDot_add_left, vecDot_add_right,
    vecDot_add_right, vecDot_matVecMul_comm_of_isSymm hA v u]
  ring



theorem oneStepSelectedDirichletTwoCell_half_energy_eq
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) (x : Vec d)
    (ha : (a x).IsSymm) :
    let principal := oneStepSelectedDirichletCell a P hEll hP R hR
    let oscillatory := oneStepSelectedDirichletCell a F hEll hF R hR
    (1 / 2 : ℝ) * vecDot (principal.field x + oscillatory.field x)
        (matVecMul (a x) (principal.field x + oscillatory.field x)) =
      (1 / 2 : ℝ) * vecDot (principal.field x)
          (matVecMul (a x) (principal.field x)) +
        vecDot (principal.field x)
          (matVecMul (a x) (oscillatory.field x)) +
        (1 / 2 : ℝ) * vecDot (oscillatory.field x)
          (matVecMul (a x) (oscillatory.field x)) := by
  exact oneStep_half_quadratic_add_eq (a x) ha _ _



theorem oneStepSelectedNeumannTwoCell_half_energy_eq
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) (x : Vec d) :
    let principal := oneStepSelectedNeumannCell a P hEll hP R hR
    let oscillatory := oneStepSelectedNeumannCell a F hEll hF R hR
    let Ainv := (blockMatrixOfCoeff (a x)).lowerRight
    (1 / 2 : ℝ) * vecDot (principal.flux x + oscillatory.flux x)
        (matVecMul Ainv (principal.flux x + oscillatory.flux x)) =
      (1 / 2 : ℝ) * vecDot (principal.flux x)
          (matVecMul Ainv (principal.flux x)) +
        vecDot (principal.flux x)
          (matVecMul Ainv (oscillatory.flux x)) +
        (1 / 2 : ℝ) * vecDot (oscillatory.flux x)
          (matVecMul Ainv (oscillatory.flux x)) := by
  exact oneStep_half_quadratic_add_eq _
    (blockMatrixOfCoeff_lowerRight_isSymm (a x)) _ _

/-! ## Dual two-family glue -/

/-- The source's dual patched flux, with the principal and oscillatory cell
residuals retained as separate finite sums. -/
def oneStepSelectedGluedNeumannTwoFlux {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R)) : Vec d → Vec d :=
  background +
    oneStepGluedNeumannResidual Q j
      (oneStepSelectedNeumannResidualFamily a P hEll hP) +
    oneStepGluedNeumannResidual Q j
      (oneStepSelectedNeumannResidualFamily a F hEll hF)

theorem oneStepSelectedGluedNeumannTwoFlux_memVectorL2 {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackground : MemVectorL2 (openCubeSet Q) background) :
    MemVectorL2 (openCubeSet Q)
      (oneStepSelectedGluedNeumannTwoFlux Q j a P F background hEll hP hF) := by
  exact (hBackground.add
    (oneStepSelectedGluedNeumannResidual_memVectorL2 Q j a P hEll hP)).add
    (oneStepSelectedGluedNeumannResidual_memVectorL2 Q j a F hEll hF)

/-- The two-family glue remains in the prescribed parent flux class. -/
theorem oneStepSelectedGluedNeumannTwoFlux_sub_const_zeroNormalTrace
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    (q : Vec d) {lam Lam : ℝ}
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => background x - q)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => oneStepSelectedGluedNeumannTwoFlux
        Q j a P F background hEll hP hF x - q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let pResidual := oneStepGluedNeumannResidual Q j
    (oneStepSelectedNeumannResidualFamily a P hEll hP)
  let fResidual := oneStepGluedNeumannResidual Q j
    (oneStepSelectedNeumannResidualFamily a F hEll hF)
  have hbaseL2 : MemVectorL2 (openCubeSet Q) (fun x => background x - q) :=
    hBackgroundL2.sub (MeasureTheory.memLp_const q)
  have hpL2 : MemVectorL2 (openCubeSet Q) pResidual :=
    oneStepSelectedGluedNeumannResidual_memVectorL2 Q j a P hEll hP
  have hfL2 : MemVectorL2 (openCubeSet Q) fResidual :=
    oneStepSelectedGluedNeumannResidual_memVectorL2 Q j a F hEll hF
  have hpSol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) pResidual :=
    oneStepSelectedGluedNeumannResidual_zeroNormalTrace Q j a P hEll hP
  have hfSol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) fResidual :=
    oneStepSelectedGluedNeumannResidual_zeroNormalTrace Q j a F hEll hF
  have hfirst := isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
    hbaseL2 hpL2 hBackground hpSol
  have htotal := isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
    (hbaseL2.add hpL2) hfL2 hfirst hfSol
  convert htotal using 1
  funext x
  simp only [oneStepSelectedGluedNeumannTwoFlux, Pi.add_apply]
  abel

/-- On an interior descendant, the two-family glue is exactly the sum of the
selected principal and oscillatory Neumann fluxes. -/
theorem oneStepSelectedGluedNeumannTwoFlux_eq_of_mem {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (a : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d}
    (hx : x ∈ openCubeSet R)
    (hbackground : background x = P R x + F R x) :
    oneStepSelectedGluedNeumannTwoFlux
      Q j a P F background hEll hP hF x =
      (oneStepSelectedNeumannCell a P hEll hP R hR).flux x +
      (oneStepSelectedNeumannCell a F hEll hF R hR).flux x := by
  change background x +
      oneStepGluedNeumannResidual Q j
        (oneStepSelectedNeumannResidualFamily a P hEll hP) x +
      oneStepGluedNeumannResidual Q j
        (oneStepSelectedNeumannResidualFamily a F hEll hF) x = _
  rw [
    oneStepGluedNeumannResidual_eq_of_mem
      (residual := oneStepSelectedNeumannResidualFamily a P hEll hP) hR hx,
    oneStepSelectedNeumannResidualFamily_eq a P hEll hP hR,
    oneStepGluedNeumannResidual_eq_of_mem
      (residual := oneStepSelectedNeumannResidualFamily a F hEll hF) hR hx,
    oneStepSelectedNeumannResidualFamily_eq a F hEll hF hR,
    hbackground]
  unfold OneStepNeumannCellMinimizer.residual
  abel

/-- Insert the literal two-family flux into the parent starred variational
problem. -/
theorem vecDot_sigmaStarInvCoarse_le_selectedGluedNeumannTwoFluxEnergy
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (a : CoeffField d)
    (P F : TriadicCube d → Vec d → Vec d) (background : Vec d → Vec d)
    (q : Vec d) {lam Lam : ℝ}
    (hEllParent : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hP : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (P R))
    (hF : ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R) (F R))
    (hBackgroundL2 : MemVectorL2 (openCubeSet Q) background)
    (hBackground : IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => background x - q))
    (hex : ∃ Abar : BlockMat d,
      IsCoarseBlockMatrix (openCubeSet Q) a Abar)
    (hMuResp : ∀ r : Vec d,
      Mu (openCubeSet Q) (0, r) a = ResponseJ (openCubeSet Q) 0 r a) :
    vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) ≤
      volumeAverage (openCubeSet Q) (fun x =>
        let flux := oneStepSelectedGluedNeumannTwoFlux
          Q j a P F background hEll hP hF x
        vecDot flux
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) flux)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 := by
    simpa [volume_openCubeSet_toReal] using (cubeVolume_pos Q).ne'
  apply vecDot_sigmaStarInvCoarse_le_volumeAverage_lowerRight_energy
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain
    hEllParent hex hvol hMuResp
  · exact oneStepSelectedGluedNeumannTwoFlux_memVectorL2
      Q j a P F background hEll hP hF hBackgroundL2
  · exact oneStepSelectedGluedNeumannTwoFlux_sub_const_zeroNormalTrace
      Q j a P F background q hEll hP hF hBackgroundL2 hBackground

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
