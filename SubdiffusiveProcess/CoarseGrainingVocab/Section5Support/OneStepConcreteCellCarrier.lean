module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedFiniteSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualBoundaryDiscard

@[expose] public section

/-!
# Concrete one-step cell fields

This module identifies the abstract mean/fluctuation fields used by the
localized variational gluing with the measurable Dirichlet and Neumann
solution operators of `OneStepFinalSpecialization`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A finite-cutoff coefficient admits common pointwise ellipticity constants
on every member of a finite descendant family. -/
theorem exists_isEllipticFieldOn_aCutoff_descendants
    {d j : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (Q : TriadicCube d) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ R ∈ descendantsAtDepth Q j,
        IsEllipticFieldOn lam Lam (openCubeSet R)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) := by
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  have ha : Continuous a :=
    _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega
  have hcompact : IsCompact (closure (openCubeSet Q)) :=
    (Homogenization.Book.Ch02.cubeDomain Q).isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hnonempty : (closure (openCubeSet Q)).Nonempty :=
    (Homogenization.Book.Ch02.cubeDomain Q).nonempty.closure
  obtain ⟨xmin, _hxmin, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ha.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty ha.continuousOn
  have hEllQ : IsEllipticFieldOn (a xmin) (a xmax) (openCubeSet Q)
      (scalarCoeffField a) := by
    constructor
    · have hmatrix : Continuous fun x : Vec d ↦ scalarCoeffField a x :=
        ha.smul continuous_const
      refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun k ↦ ?_
      have hentry : Measurable fun x : Vec d ↦ scalarCoeffField a x i k :=
        (continuous_apply k).comp ((continuous_apply i).comp hmatrix) |>.measurable
      exact hentry.ite (measurableSet_openCubeSet Q) measurable_const
    · intro x hx
      exact (isEllipticMatrix_scalarMatrix
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x)).mono
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega xmin)
          (hmin (subset_closure hx)) (hmax (subset_closure hx))
  refine ⟨a xmin, a xmax,
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega xmin, ?_⟩
  intro R hR
  exact hEllQ.mono (measurableSet_openCubeSet R)
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)

/-- Constant cell mean of the primal large-cube slope. -/
def oneStepDirichletCellMeanField {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun _ ↦ oneStepDirichletCellSlope M n h p Q R omega hh

/-- Centered cell fluctuation of the primal large-cube slope. -/
def oneStepDirichletCellFluctuationField {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun x ↦ oneStepDirichletSlopeField M n h p Q omega hh x -
    oneStepDirichletCellSlope M n h p Q R omega hh

/-- Constant cell mean of the dual large-cube slope. -/
def oneStepNeumannCellMeanField {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun _ ↦ oneStepNeumannCellSlope M n h q Q R omega hh

/-- Centered cell fluctuation of the dual large-cube slope. -/
def oneStepNeumannCellFluctuationField {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun x ↦ oneStepNeumannSlopeField M n h q Q omega hh x -
    oneStepNeumannCellSlope M n h q Q R omega hh

/-- The constant affine probe cancels from the primal cell fluctuation. -/
theorem oneStepDirichletCellFluctuationField_eq_centeredTriadicGrad
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth Q j) :
    oneStepDirichletCellFluctuationField M n h p Q R omega hh =
      fun x ↦
        (oneStepTriadicDirichletSolution M n h p Q omega hh
          ).toH1Function.grad x -
        cubeAverageVec R
          (oneStepTriadicDirichletSolution M n h p Q omega hh
            ).toH1Function.grad := by
  let u := (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
  have huQ : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      u.grad_memVectorL2
  have huR : MemVectorL2 (cubeSet R) u.grad :=
    huQ.mono_measure <|
      Measure.restrict_mono_set volume
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have havg := cubeAverageVec_add R (fun _ : Vec d ↦ p) u.grad
    (memVectorL2_const p) huR
  rw [cubeAverageVec_const] at havg
  unfold oneStepDirichletCellFluctuationField
  rw [oneStepDirichletCellSlope_eq_cubeAverageVec M n h p Q R hR omega hh]
  funext x
  change p + u.grad x - cubeAverageVec R (fun y ↦ p + u.grad y) =
    u.grad x - cubeAverageVec R u.grad
  rw [havg]
  abel

@[simp] theorem oneStepDirichletCellMean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) (x : Vec d) :
    oneStepDirichletCellMeanField M n h p Q R omega hh x +
        oneStepDirichletCellFluctuationField M n h p Q R omega hh x =
      oneStepDirichletSlopeField M n h p Q omega hh x := by
  simp [oneStepDirichletCellMeanField,
    oneStepDirichletCellFluctuationField]

@[simp] theorem oneStepNeumannCellMean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) (x : Vec d) :
    oneStepNeumannCellMeanField M n h q Q R omega hh x +
        oneStepNeumannCellFluctuationField M n h q Q R omega hh x =
      oneStepNeumannSlopeField M n h q Q omega hh x := by
  simp [oneStepNeumannCellMeanField,
    oneStepNeumannCellFluctuationField]

theorem oneStepDirichletCellMeanField_memVectorL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemVectorL2 (openCubeSet R)
      (oneStepDirichletCellMeanField M n h p Q R omega hh) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  exact MeasureTheory.memLp_const _

theorem oneStepDirichletCellFluctuationField_memVectorL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    MemVectorL2 (openCubeSet R)
      (oneStepDirichletCellFluctuationField M n h p Q R omega hh) := by
  have hslope :=
    (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh).mono_measure
      (Measure.restrict_mono hRQ le_rfl)
  have hconst : MemVectorL2 (openCubeSet R)
      (fun _ ↦ oneStepDirichletCellSlope M n h p Q R omega hh) := by
    let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
      isFiniteMeasure_volumeMeasureOn_openCubeSet R
    exact MeasureTheory.memLp_const _
  exact hslope.sub hconst

theorem oneStepNeumannCellMeanField_memVectorL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemVectorL2 (openCubeSet R)
      (oneStepNeumannCellMeanField M n h q Q R omega hh) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  exact MeasureTheory.memLp_const _

theorem oneStepNeumannCellFluctuationField_memVectorL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    MemVectorL2 (openCubeSet R)
      (oneStepNeumannCellFluctuationField M n h q Q R omega hh) := by
  have hslope :=
    (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh).mono_measure
      (Measure.restrict_mono hRQ le_rfl)
  have hconst : MemVectorL2 (openCubeSet R)
      (fun _ ↦ oneStepNeumannCellSlope M n h q Q R omega hh) := by
    let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
      isFiniteMeasure_volumeMeasureOn_openCubeSet R
    exact MeasureTheory.memLp_const _
  exact hslope.sub hconst

/-! ## Descendant-family certificates -/

theorem oneStepDirichletCellMeanField_memVectorL2_of_descendant
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R)
        (oneStepDirichletCellMeanField M n h p Q R omega hh) := by
  intro R _hR
  exact oneStepDirichletCellMeanField_memVectorL2 M n h p Q R omega hh

theorem oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R)
        (oneStepDirichletCellFluctuationField M n h p Q R omega hh) := by
  intro R hR
  exact oneStepDirichletCellFluctuationField_memVectorL2
    M n h p Q R omega hh (openCubeSet_subset_of_mem_descendantsAtDepth hR)

theorem oneStepNeumannCellMeanField_memVectorL2_of_descendant
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R)
        (oneStepNeumannCellMeanField M n h q Q R omega hh) := by
  intro R _hR
  exact oneStepNeumannCellMeanField_memVectorL2 M n h q Q R omega hh

theorem oneStepNeumannCellFluctuationField_memVectorL2_of_descendant
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R)
        (oneStepNeumannCellFluctuationField M n h q Q R omega hh) := by
  intro R hR
  exact oneStepNeumannCellFluctuationField_memVectorL2
    M n h q Q R omega hh (openCubeSet_subset_of_mem_descendantsAtDepth hR)

/-! ## Literal patched-field identities -/

/-- On a source cell, the affine slope plus the patched zero-trace
correction is exactly the sum of the selected mean and fluctuation fields.
This is the concrete competitor identity used in the primal finite-volume
variational comparison. -/
theorem oneStepDirichlet_patchedTotalSlope_eq_of_mem
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    let P := fun S ↦
      oneStepDirichletCellMeanField M n h p Q S omega hh
    let F := fun S ↦
      oneStepDirichletCellFluctuationField M n h p Q S omega hh
    p + (oneStepPatchedCompetitor
        (oneStepTriadicDirichletSolution M n h p Q omega hh)
        (oneStepSelectedDirichletTwoPatchList Q j a P F hEll
          (oneStepDirichletCellMeanField_memVectorL2_of_descendant
            M n h p Q omega hh)
          (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
            M n h p Q omega hh))).toH1Function.grad x =
      (oneStepSelectedDirichletCell a P hEll
          (oneStepDirichletCellMeanField_memVectorL2_of_descendant
            M n h p Q omega hh) R hR).field x +
      (oneStepSelectedDirichletCell a F hEll
          (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
            M n h p Q omega hh) R hR).field x := by
  dsimp only
  change p +
      ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x +
        (oneStepFoldCorrections
          (oneStepSelectedDirichletTwoPatchList Q j a _ _ hEll _ _)
          ).toH1Function.grad x) = _
  rw [oneStepSelectedDirichletTwoPatchFold_grad_eq_of_mem
      a _ _ hEll
        (oneStepDirichletCellMeanField_memVectorL2_of_descendant
          M n h p Q omega hh)
        (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
          M n h p Q omega hh) hR hx]
  unfold OneStepDirichletCellMinimizer.field
  have hbase :
      p + (oneStepTriadicDirichletSolution M n h p Q omega hh
        ).toH1Function.grad x =
        oneStepDirichletCellMeanField M n h p Q R omega hh x +
          oneStepDirichletCellFluctuationField M n h p Q R omega hh x := by
    exact (oneStepDirichletCellMean_add_fluctuation
      M n h p Q R omega hh x).symm
  rw [← add_assoc, hbase]
  abel

/-- On a source cell, the concrete two-family Neumann glue is the sum of the
selected mean and fluctuation fluxes. -/
theorem oneStepNeumann_gluedFlux_eq_of_mem
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (a : CoeffField d) {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    let P := fun S ↦
      oneStepNeumannCellMeanField M n h q Q S omega hh
    let F := fun S ↦
      oneStepNeumannCellFluctuationField M n h q Q S omega hh
    oneStepSelectedGluedNeumannTwoFlux Q j a P F
        (oneStepNeumannSlopeField M n h q Q omega hh) hEll
        (oneStepNeumannCellMeanField_memVectorL2_of_descendant
          M n h q Q omega hh)
        (oneStepNeumannCellFluctuationField_memVectorL2_of_descendant
          M n h q Q omega hh) x =
      (oneStepSelectedNeumannCell a P hEll
          (oneStepNeumannCellMeanField_memVectorL2_of_descendant
            M n h q Q omega hh) R hR).flux x +
      (oneStepSelectedNeumannCell a F hEll
          (oneStepNeumannCellFluctuationField_memVectorL2_of_descendant
            M n h q Q omega hh) R hR).flux x := by
  dsimp only
  apply oneStepSelectedGluedNeumannTwoFlux_eq_of_mem
  · exact hx
  · exact (oneStepNeumannCellMean_add_fluctuation
      M n h q Q R omega hh x).symm

/-! ## Constant-cell energy readouts -/

/-- A cutoff-ratio supremum dominates the corresponding scalar quadratic
energy on its domain.  This is the coefficient-level insertion used for both
the principal and oscillatory selected cell fields. -/
theorem volumeAverage_cutoff_energy_le_ratioSup_mul
    {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (numerator denominator : ℕ) (U : Homogenization.Book.Ch02.Domain d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (U : Set (Vec d)) F)
    {lamNum LamNum lamDen LamDen : ℝ}
    (hNum : IsEllipticFieldOn lamNum LamNum (U : Set (Vec d))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega)))
    (hDen : IsEllipticFieldOn lamDen LamDen (U : Set (Vec d))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M denominator omega))) :
    volumeAverage (U : Set (Vec d)) (fun x ↦
        vecDot (F x) (matVecMul
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega) x) (F x))) ≤
      cutoffRatioSup M numerator denominator U omega *
        volumeAverage (U : Set (Vec d)) (fun x ↦
          vecDot (F x) (matVecMul
            (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M denominator omega) x)
            (F x))) := by
  let aNum := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega)
  let aDen := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M denominator omega)
  let W := cutoffRatioSup M numerator denominator U omega
  have hNumFlux : MemVectorL2 (U : Set (Vec d))
      (fun x ↦ matVecMul (aNum x) (F x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hNum hF
  have hDenFlux : MemVectorL2 (U : Set (Vec d))
      (fun x ↦ matVecMul (aDen x) (F x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hDen hF
  have hNumInt : IntegrableOn
      (fun x ↦ vecDot (F x) (matVecMul (aNum x) (F x)))
      (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hF hNumFlux
  have hDenInt : IntegrableOn
      (fun x ↦ vecDot (F x) (matVecMul (aDen x) (F x)))
      (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hF hDenFlux
  have hpoint : ∀ x ∈ (U : Set (Vec d)),
      vecDot (F x) (matVecMul (aNum x) (F x)) ≤
        W * vecDot (F x) (matVecMul (aDen x) (F x)) := by
    intro x hx
    have hratio := cutoffRatio_le_cutoffRatioSup
      M numerator denominator U omega hx
    have hdenPos := _root_.SubdiffusiveProcess.Model.aCutoff_pos
      M denominator omega x
    have hnorm0 := vecNormSq_nonneg (F x)
    have hcoeff :
        _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x ≤
          W * _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x := by
      have heq :
          _root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x =
            (_root_.SubdiffusiveProcess.Model.aCutoff M numerator omega x /
              _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x) *
                _root_.SubdiffusiveProcess.Model.aCutoff M denominator omega x := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right hratio hdenPos.le
    dsimp only [aNum, aDen, scalarCoeffField]
    rw [matVecMul_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_right, vecDot_smul_right]
    simpa only [vecNormSq, mul_assoc] using!
      mul_le_mul_of_nonneg_right hcoeff hnorm0
  unfold volumeAverage
  calc
    (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)),
          vecDot (F x) (matVecMul (aNum x) (F x)) ∂volume ≤
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)),
          W * vecDot (F x) (matVecMul (aDen x) (F x)) ∂volume := by
            apply mul_le_mul_of_nonneg_left
            · apply integral_mono_ae hNumInt (hDenInt.const_mul W)
              filter_upwards [ae_restrict_mem U.measurableSet] with x hx
              exact hpoint x hx
            · positivity
    _ = W * ((volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)),
          vecDot (F x) (matVecMul (aDen x) (F x)) ∂volume) := by
            rw [MeasureTheory.integral_const_mul]
            ring

/-- Dual scalar counterpart of `volumeAverage_cutoff_energy_le_ratioSup_mul`:
the lower-cutoff flux measured in the inverse higher-cutoff metric is
controlled by the reciprocal cutoff-ratio supremum. -/
theorem volumeAverage_cutoff_flux_inverseEnergy_le_ratioSup_mul
    {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (low high : ℕ) (U : Homogenization.Book.Ch02.Domain d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (G : Vec d → Vec d)
    (hG : MemVectorL2 (U : Set (Vec d)) G)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : IsEllipticFieldOn lamLow LamLow (U : Set (Vec d))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M low omega)))
    (hHigh : IsEllipticFieldOn lamHigh LamHigh (U : Set (Vec d))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M high omega))) :
    let aLow := scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M low omega)
    let aHigh := scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M high omega)
    let flux := fun x ↦ matVecMul (aLow x) (G x)
    volumeAverage (U : Set (Vec d)) (fun x ↦
        vecDot (flux x)
          (matVecMul ((symmPart (aHigh x))⁻¹) (flux x))) ≤
      cutoffRatioSup M low high U omega *
        volumeAverage (U : Set (Vec d)) (fun x ↦
          vecDot (G x) (matVecMul (aLow x) (G x))) := by
  dsimp only
  let aLow := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M low omega)
  let aHigh := scalarCoeffField
    (_root_.SubdiffusiveProcess.Model.aCutoff M high omega)
  let flux := fun x ↦ matVecMul (aLow x) (G x)
  let W := cutoffRatioSup M low high U omega
  have hFlux : MemVectorL2 (U : Set (Vec d)) flux :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hLow hG
  have hInvFlux : MemVectorL2 (U : Set (Vec d))
      (fun x ↦ matVecMul ((symmPart (aHigh x))⁻¹) (flux x)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hHigh hFlux
  have hTargetInt : IntegrableOn (fun x ↦
      vecDot (flux x) (matVecMul ((symmPart (aHigh x))⁻¹) (flux x)))
      (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hFlux hInvFlux
  have hLowFlux : MemVectorL2 (U : Set (Vec d))
      (fun x ↦ matVecMul (aLow x) (G x)) := hFlux
  have hLowInt : IntegrableOn (fun x ↦
      vecDot (G x) (matVecMul (aLow x) (G x)))
      (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hG hLowFlux
  have hpoint : ∀ x ∈ (U : Set (Vec d)),
      vecDot (flux x) (matVecMul ((symmPart (aHigh x))⁻¹) (flux x)) ≤
        W * vecDot (G x) (matVecMul (aLow x) (G x)) := by
    intro x hx
    let cLow := _root_.SubdiffusiveProcess.Model.aCutoff M low omega x
    let cHigh := _root_.SubdiffusiveProcess.Model.aCutoff M high omega x
    have hcLow : 0 < cLow := _root_.SubdiffusiveProcess.Model.aCutoff_pos M low omega x
    have hcHigh : 0 < cHigh := _root_.SubdiffusiveProcess.Model.aCutoff_pos M high omega x
    have hratio := cutoffRatio_le_cutoffRatioSup M low high U omega hx
    have hnorm0 := vecNormSq_nonneg (G x)
    have hinv :
        ((scalarMatrix (d := d) cHigh)⁻¹ : Mat d) =
          cHigh⁻¹ • (1 : Mat d) := by
      rw [nonsing_inv_smul cHigh hcHigh.ne' (by simp)]
      simp
    dsimp only [flux, aLow, aHigh, scalarCoeffField, cLow, cHigh]
    rw [Homogenization.Book.Ch02.symmPart_scalarMatrix, hinv,
      matVecMul_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_left, vecDot_smul_right, vecDot_smul_right]
    have hcoeff : cHigh⁻¹ * cLow ≤ W := by
      simpa only [div_eq_inv_mul] using! hratio
    have hcoeff' : cLow * (cHigh⁻¹ * cLow) ≤ W * cLow :=
      by simpa only [mul_comm, mul_left_comm, mul_assoc] using!
        mul_le_mul_of_nonneg_right hcoeff hcLow.le
    change cLow * (cHigh⁻¹ * (cLow * vecDot (G x) (G x))) ≤
      W * (cLow * vecDot (G x) (G x))
    calc
      cLow * (cHigh⁻¹ * (cLow * vecDot (G x) (G x))) =
          (cLow * (cHigh⁻¹ * cLow)) * vecDot (G x) (G x) := by ring
      _ ≤ (W * cLow) * vecDot (G x) (G x) :=
        mul_le_mul_of_nonneg_right hcoeff' hnorm0
      _ = W * (cLow * vecDot (G x) (G x)) := by ring
  unfold volumeAverage
  calc
    (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)),
          vecDot (flux x)
            (matVecMul ((symmPart (aHigh x))⁻¹) (flux x)) ∂volume ≤
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)),
          W * vecDot (G x) (matVecMul (aLow x) (G x)) ∂volume := by
            apply mul_le_mul_of_nonneg_left
            · apply integral_mono_ae hTargetInt (hLowInt.const_mul W)
              filter_upwards [ae_restrict_mem U.measurableSet] with x hx
              exact hpoint x hx
            · positivity
    _ = W * ((volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)),
          vecDot (G x) (matVecMul (aLow x) (G x)) ∂volume) := by
            rw [MeasureTheory.integral_const_mul]
            ring

/-- The selected constant-mean primal cell energy is the literal random
coarse-matrix quadratic form at the lower cutoff. -/
theorem oneStepSelectedDirichletMean_energy_eq_randomAMatrix
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦
      oneStepDirichletCellMeanField M n h p Q S omega hh
    volumeAverage (openCubeSet R) (fun x ↦
        let X := oneStepSelectedDirichletCell
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
          P hEll
          (oneStepDirichletCellMeanField_memVectorL2_of_descendant
            M n h p Q omega hh) R hR
        vecDot (X.field x)
          (matVecMul
            (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) x)
            (X.field x))) =
      vecDot (oneStepDirichletCellSlope M n h p Q R omega hh)
        (matVecMul (randomAMatrix M n
          (Homogenization.Book.Ch02.cubeDomain R) omega)
          (oneStepDirichletCellSlope M n h p Q R omega hh)) := by
  dsimp only
  let a := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let X := oneStepSelectedDirichletCell a
    (fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh)
    hEll
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh) R hR
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    simpa [volume_openCubeSet_toReal] using! cubeVolume_pos R
  obtain ⟨recovery, sigma0, compat, hA, hSInv, hS, hK, hSigma, _hcanonical⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet R) (hEll R hR) hvol
  have hdetInv : IsUnit
      (sigmaStarInvCoarse (openCubeSet R) a).det :=
    (Matrix.isUnit_iff_isUnit_det
      (sigmaStarInvCoarse (openCubeSet R) a)).mp
      (sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        recovery (isOpenBoundedConvexDomain_openCubeSet R) (hEll R hR)
          hvol compat).isUnit
  have hdet : IsUnit (sigmaStarCoarse (openCubeSet R) a).det := by
    unfold sigmaStarCoarse
    exact Matrix.isUnit_nonsing_inv_det
      (A := sigmaStarInvCoarse (openCubeSet R) a) hdetInv
  have henergy := X.energy_eq_vecDot_sigmaCoarse
    (fun x ↦ scalarMatrix_isSymm _)
    (hEll R hR) hA hS hK hSigma hdet
  let U := Homogenization.Book.Ch02.cubeDomain R
  let coeff := (aCutoffCoeffOnData M n omega U).toCoeffOn
  have htheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
    U coeff (aCutoffCoeffOnData M n omega U).isSymmetric
  have hmatrix : randomAMatrix M n U omega =
      sigmaCoarse (openCubeSet R) a := by
    exact htheory.derived_matrices.1
  rw [hmatrix]
  have hgrad (x : Vec d) :
      (X.isAffineDirichletSolution (hEll R hR)).toAHarmonicFunction.toH1.grad x =
        X.field x := by
    rfl
  have haSymm (x : Vec d) : symmPart (a x) = a x := by
    simp only [a, scalarCoeffField,
      Homogenization.Book.Ch02.symmPart_scalarMatrix]
  calc
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.field x) (matVecMul (a x) (X.field x))) =
        volumeAverage (openCubeSet R)
          (scalarVariationEnergyIntegrand a
            (X.isAffineDirichletSolution (hEll R hR)).toAHarmonicFunction) := by
              congr 1
              funext x
              simp only [scalarVariationEnergyIntegrand, hgrad, haSymm]
    _ = vecDot (oneStepDirichletCellSlope M n h p Q R omega hh)
        (matVecMul (sigmaCoarse (openCubeSet R) a)
          (oneStepDirichletCellSlope M n h p Q R omega hh)) := by
            simpa only [X, a, oneStepDirichletCellMeanField,
              oneStepDirichletCellSlope, oneStepCellMeanVec] using! henergy

/-- The high-cutoff energy of the selected lower-cutoff principal cell is
bounded by the forward cutoff-ratio weight times its random coarse-matrix
readout. -/
theorem oneStepSelectedDirichletMean_highEnergy_le
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦
      oneStepDirichletCellMeanField M n h p Q S omega hh
    let X := oneStepSelectedDirichletCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
      P hLow
      (oneStepDirichletCellMeanField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.field x)
          (matVecMul
            (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)
            (X.field x))) ≤
      oneStepUpperSourceCellWeight M n h R omega *
        vecDot (oneStepDirichletCellSlope M n h p Q R omega hh)
          (matVecMul (randomAMatrix M n
            (Homogenization.Book.Ch02.cubeDomain R) omega)
            (oneStepDirichletCellSlope M n h p Q R omega hh)) := by
  dsimp only
  let aLow := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let X := oneStepSelectedDirichletCell aLow
    (fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh)
    hLow
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh) R hR
  have hX : MemVectorL2 (openCubeSet R) X.field :=
    (oneStepDirichletCellMeanField_memVectorL2_of_descendant
      M n h p Q omega hh R hR).add
      X.correction.toH1Function.grad_memVectorL2
  have hratio := volumeAverage_cutoff_energy_le_ratioSup_mul
    M (n + h) n (Homogenization.Book.Ch02.cubeDomain R) omega X.field hX
      (hHigh R hR) (hLow R hR)
  have hreadout := oneStepSelectedDirichletMean_energy_eq_randomAMatrix
    M n h p Q R omega hh hLow hR
  simpa only [X, aLow, oneStepUpperSourceCellWeight] using!
    hratio.trans_eq (congrArg
      (fun z ↦ cutoffRatioSup M (n + h) n
        (Homogenization.Book.Ch02.cubeDomain R) omega * z) hreadout)

/-- The selected constant-mean dual cell energy is the literal inverse-star
random coarse-matrix quadratic form at the lower cutoff. -/
theorem oneStepSelectedNeumannMean_energy_eq_randomAStarMatrix_inv
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦
      oneStepNeumannCellMeanField M n h q Q S omega hh
    volumeAverage (openCubeSet R) (fun x ↦
        let X := oneStepSelectedNeumannCell
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
          P hEll
          (oneStepNeumannCellMeanField_memVectorL2_of_descendant
            M n h q Q omega hh) R hR
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) x)).lowerRight)
            (X.flux x))) =
      vecDot (oneStepNeumannCellSlope M n h q Q R omega hh)
        (matVecMul ((randomAStarMatrix M n
          (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹)
          (oneStepNeumannCellSlope M n h q Q R omega hh)) := by
  dsimp only
  let a := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let X := oneStepSelectedNeumannCell a
    (fun S ↦ oneStepNeumannCellMeanField M n h q Q S omega hh)
    hEll
    (oneStepNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh) R hR
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    simpa [volume_openCubeSet_toReal] using! cubeVolume_pos R
  obtain ⟨recovery, _sigma0, compat, _hA, _hSInv, hS, _hK, _hSigma,
      _hcanonical⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet R) (hEll R hR) hvol
  have henergy := X.energy_eq_vecDot_sigmaStarInvCoarse
    (fun x ↦ scalarMatrix_isSymm _)
    (hEll R hR) hS
  rw [randomAStarMatrix_inv_eq_sigmaStarInvCoarse M n omega R]
  have hgrad (x : Vec d) :
      (X.isConstantFluxNeumannSolution (hEll R hR)).toAHarmonicFunction.toH1.grad x =
        X.potential.toH1Function.grad x := by
    rfl
  have haSymm (x : Vec d) : symmPart (a x) = a x := by
    simp only [a, scalarCoeffField,
      Homogenization.Book.Ch02.symmPart_scalarMatrix]
  have hfluxEnergy (x : Vec d) :
      vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (X.flux x)) =
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul (a x) (X.potential.toH1Function.grad x)) := by
    have hdet : IsUnit (a x).det :=
      isUnit_det_of_isEllipticMatrix
        (isEllipticMatrix_scalarMatrix
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x))
    unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
    dsimp only
    rw [haSymm, matVecMul_mul, Matrix.nonsing_inv_mul (a x) hdet,
      matVecMul_one]
    exact vecDot_comm _ _
  calc
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (X.flux x))) =
        volumeAverage (openCubeSet R)
          (scalarVariationEnergyIntegrand a
            (X.isConstantFluxNeumannSolution (hEll R hR)).toAHarmonicFunction) := by
              congr 1
              funext x
              rw [hfluxEnergy x]
              simp only [scalarVariationEnergyIntegrand, hgrad, haSymm]
    _ = vecDot (oneStepNeumannCellSlope M n h q Q R omega hh)
        (matVecMul (sigmaStarInvCoarse (openCubeSet R) a)
          (oneStepNeumannCellSlope M n h q Q R omega hh)) := by
            simpa only [X, a, oneStepNeumannCellMeanField,
              oneStepNeumannCellSlope, oneStepCellMeanVec] using! henergy

/-- Gradient-energy form of the dual constant-cell readout. -/
theorem oneStepSelectedNeumannMean_gradientEnergy_eq_randomAStarMatrix_inv
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lam Lam : ℝ}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦ oneStepNeumannCellMeanField M n h q Q S omega hh
    let X := oneStepSelectedNeumannCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
      P hEll
      (oneStepNeumannCellMeanField_memVectorL2_of_descendant
        M n h q Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul
            (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) x)
            (X.potential.toH1Function.grad x))) =
      vecDot (oneStepNeumannCellSlope M n h q Q R omega hh)
        (matVecMul ((randomAStarMatrix M n
          (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹)
          (oneStepNeumannCellSlope M n h q Q R omega hh)) := by
  dsimp only
  let a := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let X := oneStepSelectedNeumannCell a
    (fun S ↦ oneStepNeumannCellMeanField M n h q Q S omega hh)
    hEll
    (oneStepNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh) R hR
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    simpa [volume_openCubeSet_toReal] using! cubeVolume_pos R
  obtain ⟨recovery, _sigma0, compat, _hA, _hSInv, hS, _hK, _hSigma,
      _hcanonical⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet R) (hEll R hR) hvol
  have henergy := X.energy_eq_vecDot_sigmaStarInvCoarse
    (fun x ↦ scalarMatrix_isSymm _) (hEll R hR) hS
  rw [randomAStarMatrix_inv_eq_sigmaStarInvCoarse M n omega R]
  calc
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x)
          (matVecMul (a x) (X.potential.toH1Function.grad x))) =
        volumeAverage (openCubeSet R)
          (scalarVariationEnergyIntegrand a
            (X.isConstantFluxNeumannSolution (hEll R hR)
              ).toAHarmonicFunction) := by
      congr 1
      funext x
      simp only [scalarVariationEnergyIntegrand,
        IsConstantFluxNeumannSolution.toAHarmonicFunction_grad]
      rw [show symmPart (a x) = a x by
        simp only [a, scalarCoeffField,
          Homogenization.Book.Ch02.symmPart_scalarMatrix]]
    _ = _ := by
      simpa only [X, a, oneStepNeumannCellMeanField,
        oneStepNeumannCellSlope, oneStepCellMeanVec] using! henergy

/-- The inverse higher-cutoff energy of the selected lower-cutoff dual
principal cell is bounded by the reciprocal cutoff-ratio weight times its
inverse-star coarse readout. -/
theorem oneStepSelectedNeumannMean_highInverseEnergy_le
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    {lamLow LamLow lamHigh LamHigh : ℝ}
    (hLow : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamLow LamLow (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)))
    (hHigh : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lamHigh LamHigh (openCubeSet S)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)))
    (hR : R ∈ descendantsAtDepth Q j) :
    let P := fun S ↦ oneStepNeumannCellMeanField M n h q Q S omega hh
    let X := oneStepSelectedNeumannCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
      P hLow
      (oneStepNeumannCellMeanField_memVectorL2_of_descendant
        M n h q Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff
              (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)).lowerRight)
            (X.flux x))) ≤
      oneStepLowerSourceCellWeight M n h R omega *
        vecDot (oneStepNeumannCellSlope M n h q Q R omega hh)
          (matVecMul ((randomAStarMatrix M n
            (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹)
            (oneStepNeumannCellSlope M n h q Q R omega hh)) := by
  dsimp only
  let aLow := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
  let X := oneStepSelectedNeumannCell aLow
    (fun S ↦ oneStepNeumannCellMeanField M n h q Q S omega hh)
    hLow
    (oneStepNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh) R hR
  have hratio := volumeAverage_cutoff_flux_inverseEnergy_le_ratioSup_mul
    M n (n + h) (Homogenization.Book.Ch02.cubeDomain R) omega
      X.potential.toH1Function.grad
      X.potential.toH1Function.grad_memVectorL2 (hLow R hR) (hHigh R hR)
  have hreadout :=
    oneStepSelectedNeumannMean_gradientEnergy_eq_randomAStarMatrix_inv
      M n h q Q R omega hh hLow hR
  simpa only [X, aLow, blockMatrixOfCoeff,
    oneStepLowerSourceCellWeight] using!
    hratio.trans_eq (congrArg
      (fun z ↦ cutoffRatioSup M n (n + h)
        (Homogenization.Book.Ch02.cubeDomain R) omega * z) hreadout)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
