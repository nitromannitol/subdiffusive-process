module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.SecondMomentBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeMomentNonpos
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeModulus
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.WeakHessianMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.MeasurabilityProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ScalarEnergyIdentity

@[expose] public section

/-!
# A translated local envelope for the glued dual cell energy

The cutoff depth is fixed in this module while the parent cube grows.  The
local logarithmic envelope is therefore evaluated at the fixed source-cell
scale after translating the sample to the source cell.  Stationarity makes
its fourth moment independent of the cell and of the parent scale.
-/

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

private theorem isEllipticMatrix_scalarMatrix_of_bounds
    {lam Lam s : ℝ} (hlam : 0 < lam) (hs1 : lam ≤ s) (hs2 : s ≤ Lam) :
    IsEllipticMatrix lam Lam (scalarMatrix (d := d) s) := by
  have hs : 0 < s := hlam.trans_le hs1
  refine ⟨hlam, hs1.trans hs2, fun xi ↦ ?_, fun xi ↦ ?_⟩
  · rw [matVecMul_scalarMatrix, vecDot_smul_right]
    exact mul_le_mul_of_nonneg_right hs1 (vecNormSq_nonneg _)
  · have hInv : ((scalarMatrix (d := d) s)⁻¹ : Mat d) =
        s⁻¹ • (1 : Mat d) := by
      rw [scalarMatrix, nonsing_inv_smul s (ne_of_gt hs) (by simp)]
      simp
    rw [hInv, matVecMul_scalarMatrix, vecDot_smul_right]
    refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg _)
    exact (inv_le_inv₀ (hs.trans_le hs2) hs).2 hs2

/-- The sum of two selected Neumann cell minimizers is a minimizer for the
sum of their data. -/
noncomputable def OneStepNeumannCellMinimizer.add
    {R : TriadicCube d} {a : CoeffField d} {F G : Vec d → Vec d}
    {lam Lam : ℝ}
    (X : OneStepNeumannCellMinimizer R a F)
    (Y : OneStepNeumannCellMinimizer R a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hF : MemVectorL2 (openCubeSet R) F)
    (hG : MemVectorL2 (openCubeSet R) G) :
    OneStepNeumannCellMinimizer R a (F + G) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  refine {
  potential :=
    (X.potential.toH1Function + Y.potential.toH1Function).toMeanZero
  weakSolution := by
    intro phi
    simp only [H1Function.toMeanZero_grad, H1Function.add_grad, Pi.add_apply,
      matVecMul_add, vecDot_add_left]
    rw [integral_add
      (integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
          X.potential.toH1Function.grad_memVectorL2)
        phi.toH1Function.grad_memVectorL2)
      (integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
          Y.potential.toH1Function.grad_memVectorL2)
        phi.toH1Function.grad_memVectorL2),
      integral_add
        (integrableOn_vecDot_of_memVectorL2 hF
          phi.toH1Function.grad_memVectorL2)
        (integrableOn_vecDot_of_memVectorL2 hG
          phi.toH1Function.grad_memVectorL2)]
    rw [X.weakSolution phi, Y.weakSolution phi]
  }

@[simp] theorem OneStepNeumannCellMinimizer.add_flux
    {R : TriadicCube d} {a : CoeffField d} {F G : Vec d → Vec d}
    {lam Lam : ℝ}
    (X : OneStepNeumannCellMinimizer R a F)
    (Y : OneStepNeumannCellMinimizer R a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (hF : MemVectorL2 (openCubeSet R) F)
    (hG : MemVectorL2 (openCubeSet R) G) (x : Vec d) :
    (X.add Y hEll hF hG).flux x = X.flux x + Y.flux x := by
  simp [OneStepNeumannCellMinimizer.add,
    OneStepNeumannCellMinimizer.flux, matVecMul_add]

/-- A Neumann cell minimizer costs no more than its datum in a scalar inverse
metric bounded by a constant `W`. -/
theorem OneStepNeumannCellMinimizer.half_inverse_energy_le_envelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    {R : TriadicCube d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) G)
    {lam Lam W : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)))
    (hG : MemVectorL2 (openCubeSet R) G) (hW : 0 < W)
    (hlow : ∀ x ∈ openCubeSet R,
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x)⁻¹ ≤ W)
    (hhigh : ∀ x ∈ openCubeSet R,
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x ≤ W) :
    (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x ↦
      vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
          ).lowerRight) (X.flux x))) ≤
      W * cubeAverage R (fun x ↦ vecNormSq (G x)) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  let a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let u := X.potential
  have hWInv : 0 < W⁻¹ := inv_pos.mpr hW
  have haLower : ∀ x ∈ openCubeSet R, W⁻¹ ≤ a x := by
    intro x hx
    have haPos := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
    have := (inv_le_inv₀ hW (inv_pos.mpr haPos)).2 (hlow x hx)
    simpa [a] using this
  have hEllW : IsEllipticFieldOn W⁻¹ W (openCubeSet R)
      (scalarCoeffField a) := by
    refine ⟨hEll.1, ?_⟩
    intro x hx
    exact isEllipticMatrix_scalarMatrix_of_bounds hWInv
      (haLower x hx) (hhigh x hx)
  have hGsq : IntegrableOn (fun x ↦ vecNormSq (G x)) (openCubeSet R) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hG hG
  have hUsq : IntegrableOn (fun x ↦ vecNormSq (u.toH1Function.grad x))
      (openCubeSet R) := integrableOn_vecNormSq_meanZeroGrad u
  have hpair : IntegrableOn (fun x ↦
      vecDot (G x) (u.toH1Function.grad x)) (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hG
      u.toH1Function.grad_memVectorL2
  have hYoung :
      2 * ∫ x in openCubeSet R, vecDot (G x) (u.toH1Function.grad x) ∂volume ≤
        W * ∫ x in openCubeSet R, vecNormSq (G x) ∂volume +
          W⁻¹ * ∫ x in openCubeSet R,
            vecNormSq (u.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hGsq.const_mul W) (hUsq.const_mul W⁻¹)]
    exact integral_mono (hpair.const_mul 2)
      ((hGsq.const_mul W).add (hUsq.const_mul W⁻¹)) fun x ↦
        two_vecDot_le_of_pos hW (G x) (u.toH1Function.grad x)
  have hCoercive :
      W⁻¹ * ∫ x in openCubeSet R,
          vecNormSq (u.toH1Function.grad x) ∂volume ≤
        ∫ x in openCubeSet R,
          vecDot (G x) (u.toH1Function.grad x) ∂volume :=
    X.weakSolution.energy_le_rhs_pairing_of_isEllipticFieldOn hEllW
  have hPairBound :
      ∫ x in openCubeSet R, vecDot (G x) (u.toH1Function.grad x) ∂volume ≤
        W * ∫ x in openCubeSet R, vecNormSq (G x) ∂volume := by
    linarith
  have hEnergyEq : volumeAverage (openCubeSet R) (fun x ↦
      vecDot (X.flux x)
        (matVecMul ((blockMatrixOfCoeff
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
          ).lowerRight) (X.flux x))) =
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot (G x) (u.toH1Function.grad x)) := by
    unfold volumeAverage
    congr 1
    calc
      (∫ x in openCubeSet R, vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff
            (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
            ).lowerRight) (X.flux x)) ∂volume) =
          ∫ x in openCubeSet R, vecDot (u.toH1Function.grad x)
            (matVecMul (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)
              (u.toH1Function.grad x)) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact vecDot_flux_lowerRight_flux_eq_gradientPairing M L omega X X x
      _ = _ := X.energy_identity
  rw [hEnergyEq, ← oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
  unfold volumeAverage
  have hvol : 0 ≤ ((volume (openCubeSet R)).toReal)⁻¹ := by positivity
  calc
    (1 / 2 : ℝ) *
        (((volume (openCubeSet R)).toReal)⁻¹ *
          ∫ x in openCubeSet R, vecDot (G x) (u.toH1Function.grad x) ∂volume) ≤
      ((volume (openCubeSet R)).toReal)⁻¹ *
        ∫ x in openCubeSet R, vecDot (G x) (u.toH1Function.grad x) ∂volume := by
          have hpair0 : 0 ≤ ∫ x in openCubeSet R,
              vecDot (G x) (u.toH1Function.grad x) ∂volume := by
            exact (mul_nonneg hWInv.le (integral_nonneg fun _ ↦ vecNormSq_nonneg _)
              ).trans hCoercive
          nlinarith [mul_nonneg hvol hpair0]
    _ ≤ ((volume (openCubeSet R)).toReal)⁻¹ *
        (W * ∫ x in openCubeSet R, vecNormSq (G x) ∂volume) :=
      mul_le_mul_of_nonneg_left hPairBound hvol
    _ = W * (((volume (openCubeSet R)).toReal)⁻¹ *
        ∫ x in openCubeSet R, vecNormSq (G x) ∂volume) := by ring

/-! ## The translated cutoff envelope on one source cell -/

theorem aCutoff_inv_le_exp_translatedCubeLogEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x)⁻¹ ≤
      Real.exp (aCutoffCubeLogEnvelope M L R.scale
        (translatePotentialSequence (triadicCubeShift R) omega)) := by
  have hy : x - triadicCubeShift R ∈
      openCubeSet (originCube d R.scale) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R,
      mem_translateSet_iff_sub_mem] at hx
    exact hx
  have hlow := exp_neg_aCutoffCubeLogEnvelope_le_aCutoff M L R.scale
    (translatePotentialSequence (triadicCubeShift R) omega) hy
  rw [aCutoff_translatePotentialSequence] at hlow
  have hpoint : (x - triadicCubeShift R) + triadicCubeShift R = x := by abel
  rw [hpoint] at hlow
  have haPos := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  have hinv := (inv_le_inv₀ haPos (Real.exp_pos _)).2 hlow
  rw [Real.exp_neg, inv_inv] at hinv
  exact hinv

theorem aCutoff_le_exp_translatedCubeLogEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d) (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet R) :
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x ≤
      Real.exp (aCutoffCubeLogEnvelope M L R.scale
        (translatePotentialSequence (triadicCubeShift R) omega)) := by
  have hy : x - triadicCubeShift R ∈
      openCubeSet (originCube d R.scale) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R,
      mem_translateSet_iff_sub_mem] at hx
    exact hx
  have hhigh := aCutoff_le_exp_aCutoffCubeLogEnvelope M L R.scale
    (translatePotentialSequence (triadicCubeShift R) omega) hy
  rw [aCutoff_translatePotentialSequence] at hhigh
  have hpoint : (x - triadicCubeShift R) + triadicCubeShift R = x := by abel
  simpa only [hpoint] using hhigh

/-! ## Contraction of the selected glued cell flux -/

theorem dualGluedCellHalfEnergyAt_le_translatedEnvelope_mul_fluxAverage
    [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ) (q : Vec d)
    (hh : 0 < h) (hK : oneStepLocalizationScale n M.delta ≤ K)
    (R : TriadicCube d) (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : Sample d) :
    dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega ≤
      Real.exp (aCutoffCubeLogEnvelope M (n + h)
        (oneStepLocalizationScale n M.delta : ℤ)
        (translatePotentialSequence (triadicCubeShift R) omega)) *
        cubeAverage R (fun x ↦ vecNormSq
          (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) := by
  classical
  let j := K - oneStepLocalizationScale n M.delta
  let Q : TriadicCube d := originCube d (K : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let a : CoeffField d :=
    scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
  let hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn
        (dualParentEllipticityData M (n + h) omega Q).1
        (dualParentEllipticityData M (n + h) omega Q).2
        (openCubeSet S) a :=
    dualParentEllipticityData_descendants M (n + h) omega Q j
  let P : TriadicCube d → Vec d → Vec d := fun S ↦
    oneStepPaperNeumannCellMeanField M n h q Q S omega hh
  let F : TriadicCube d → Vec d → Vec d := fun S ↦
    oneStepPaperNeumannCellFluctuationField M n h q Q S omega hh
  have hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S) :=
    oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh
  have hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S) :=
    oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
      M n h q Q omega hh
  have hRD : R ∈ D := by
    simpa only [D, Q, j, oneStepSourceCells] using hR
  let XP := oneStepSelectedNeumannCell a P hEll hP R hRD
  let XF := oneStepSelectedNeumannCell a F hEll hF R hRD
  let X := XP.add XF (hEll R hRD) (hP R hRD) (hF R hRD)
  let W := Real.exp (aCutoffCubeLogEnvelope M (n + h)
    (oneStepLocalizationScale n M.delta : ℤ)
    (translatePotentialSequence (triadicCubeShift R) omega))
  have hRscale : R.scale = (oneStepLocalizationScale n M.delta : ℤ) :=
    oneStepSourceCells_scale_eq hK hR
  have hcontract := X.half_inverse_energy_le_envelope M (n + h) omega
    (hEll R hRD) ((hP R hRD).add (hF R hRD)) (Real.exp_pos _)
    (fun x hx ↦ by
      simpa only [W, hRscale] using
        aCutoff_inv_le_exp_translatedCubeLogEnvelope M (n + h) R omega hx)
    (fun x hx ↦ by
      simpa only [W, hRscale] using
        aCutoff_le_exp_translatedCubeLogEnvelope M (n + h) R omega hx)
  have hbackground : ∀ x,
      P R x + F R x =
        oneStepPaperNeumannFlux M n h q Q omega hh x := by
    intro x
    exact oneStepPaperNeumannCellMean_add_fluctuation
      M n h q Q R omega hh x
  have hflux : ∀ x ∈ openCubeSet R,
      oneStepSelectedRetainedGluedNeumannTwoFlux Q j D a P F
          (oneStepPaperNeumannFlux M n h q Q omega hh) hEll hP hF x =
        X.flux x := by
    intro x hx
    rw [oneStepSelectedRetainedGluedNeumannTwoFlux_eq_of_mem
      a P F (oneStepPaperNeumannFlux M n h q Q omega hh)
      (fun _S hS ↦ hS) hEll hP hF hRD hx
      (hbackground x).symm]
    exact (OneStepNeumannCellMinimizer.add_flux XP XF
      (hEll R hRD) (hP R hRD) (hF R hRD) x).symm
  rw [show dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega =
      (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (X.flux x))) by
    unfold dualGluedCellHalfEnergyAt paperGluedCellHalfEnergy
    rw [volumeAverage_const_mul]
    congr 1
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    have hmem : ∀ᵐ x ∂volume.restrict (openCubeSet R),
        x ∈ openCubeSet R := ae_restrict_mem (measurableSet_openCubeSet R)
    filter_upwards [hmem] with x hx
    rw [hflux x hx]]
  simpa only [W, a, Q, P, F, Pi.add_apply,
    oneStepPaperNeumannCellMean_add_fluctuation] using hcontract

/-! ## Stationary fourth moment of the translated envelope -/

def oneStepDualCellCutoffEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) (omega : Sample d) : ℝ :=
  Real.exp (aCutoffCubeLogEnvelope M (n + h)
    (oneStepLocalizationScale n M.delta : ℤ)
    (translatePotentialSequence (triadicCubeShift R) omega))

theorem measurable_oneStepDualCellCutoffEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) :
    Measurable (oneStepDualCellCutoffEnvelope M n h R) := by
  exact ((measurable_aCutoffCubeLogEnvelope M (n + h)
    (oneStepLocalizationScale n M.delta : ℤ)).exp).comp
      (measurable_translatePotentialSequence (triadicCubeShift R))

theorem memLp_four_oneStepDualCellCutoffEnvelope [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) :
    MemLp (oneStepDualCellCutoffEnvelope M n h R) 4 M.P.toMeasure := by
  have hmem := (memLp_exp_aCutoffCubeLogEnvelope M (n + h)
    (oneStepLocalizationScale n M.delta : ℤ) (by norm_num : (1 : ℝ) ≤ 4)
    ).comp_measurePreserving
      (measurePreserving_translatePotentialSequence M (triadicCubeShift R))
  simpa [oneStepDualCellCutoffEnvelope, Function.comp_def] using! hmem

theorem integral_oneStepDualCellCutoffEnvelope_four_eq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) :
    ∫ omega, oneStepDualCellCutoffEnvelope M n h R omega ^ (4 : ℕ)
        ∂M.P.toMeasure =
      ∫ omega, Real.exp (aCutoffCubeLogEnvelope M (n + h)
        (oneStepLocalizationScale n M.delta : ℤ) omega) ^ (4 : ℕ)
        ∂M.P.toMeasure := by
  let f : Sample d → ℝ := fun omega ↦
    Real.exp (aCutoffCubeLogEnvelope M (n + h)
      (oneStepLocalizationScale n M.delta : ℤ) omega) ^ (4 : ℕ)
  have hf : AEStronglyMeasurable f M.P.toMeasure :=
    (((measurable_aCutoffCubeLogEnvelope M (n + h)
      (oneStepLocalizationScale n M.delta : ℤ)).exp).pow_const 4
      ).aestronglyMeasurable
  simpa only [oneStepDualCellCutoffEnvelope, f, Function.comp_apply] using
    Homogenization.integral_comp_eq_of_map_eq
      (measurable_translatePotentialSequence (triadicCubeShift R))
      (potentialSequenceLaw_stationary M (triadicCubeShift R)) f hf

/-! ## Measurability of the selected cell energy

The cell minimizer itself was introduced by choice.  Its energy is nevertheless
canonical: it is the supremum of the concave Neumann functional over a fixed
countable dense family in the mean-zero `H¹` graph space.  The next lemmas make
that representation explicit. -/

private theorem measurable_cutoff_fixed_meanZero_gradient_energy
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (z : H1CoerciveHilbertSpace (U := openCubeSet R)) :
    Measurable fun omega : Sample d =>
      ∫ x in openCubeSet R,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq ((H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad x) ∂volume := by
  let u : H1MeanZeroFunction (openCubeSet R) :=
    H1CoerciveHilbert.toH1MeanZeroFunction (U := openCubeSet R) z
  let g : Vec d → Vec d :=
    u.toH1Function.grad_memVectorL2.aestronglyMeasurable.mk
      u.toH1Function.grad
  have hg : Measurable g :=
    u.toH1Function.grad_memVectorL2.aestronglyMeasurable.measurable_mk
  have hsq : Measurable fun x => vecNormSq (g x) := by
    simp only [vecNormSq]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hg).mul ((measurable_pi_apply i).comp hg)
  have hjoint : Measurable fun y : Sample d × Vec d =>
      _root_.SubdiffusiveProcess.Model.aCutoff M L y.1 y.2 * vecNormSq (g y.2) :=
    (measurable_cutoff_uncurry M L).mul (hsq.comp measurable_snd)
  have hint : StronglyMeasurable fun omega : Sample d =>
      ∫ x, _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (g x)
        ∂volumeMeasureOn (openCubeSet R) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  have heq : (fun omega : Sample d =>
      ∫ x in openCubeSet R,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.toH1Function.grad x) ∂volume) =
      fun omega =>
        ∫ x, _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (g x)
          ∂volumeMeasureOn (openCubeSet R) := by
    funext omega
    apply integral_congr_ae
    filter_upwards [u.toH1Function.grad_memVectorL2.aestronglyMeasurable.ae_eq_mk]
      with x hx
    rw [hx]
  change Measurable fun omega : Sample d =>
    ∫ x in openCubeSet R,
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
        vecNormSq (u.toH1Function.grad x) ∂volume
  rw [heq]
  exact hint.measurable

private def oneStepNeumannDenseFunctional
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (G : Sample d → HilbertVectorL2 (openCubeSet R))
    (omega : Sample d)
    (z : H1CoerciveHilbertSpace (U := openCubeSet R)) : ℝ :=
  2 * inner ℝ (G omega) (H1CoerciveHilbert.gradient (U := openCubeSet R) z) -
    ∫ x in openCubeSet R,
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
        vecNormSq ((H1CoerciveHilbert.toH1MeanZeroFunction
          (U := openCubeSet R) z).toH1Function.grad x) ∂volume

private theorem measurable_oneStepNeumannDenseFunctional
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (G : Sample d → HilbertVectorL2 (openCubeSet R))
    (hG : Measurable G)
    (z : H1CoerciveHilbertSpace (U := openCubeSet R)) :
    Measurable fun omega => oneStepNeumannDenseFunctional M L R G omega z := by
  have hpair : Measurable fun omega =>
      inner ℝ (G omega) (H1CoerciveHilbert.gradient (U := openCubeSet R) z) :=
    (continuous_id.inner continuous_const).measurable.comp hG
  exact (measurable_const.mul hpair).sub
    (measurable_cutoff_fixed_meanZero_gradient_energy M L R z)

private theorem continuous_oneStepNeumannDenseFunctional
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d)
    (omega : Sample d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (G : HilbertVectorL2 (openCubeSet R)) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))) :
    Continuous fun z : H1CoerciveHilbertSpace (U := openCubeSet R) =>
      oneStepNeumannDenseFunctional M L R (fun _ => G) omega z := by
  let B := H1CoerciveHilbert.coeffGradientBilin (U := openCubeSet R) hEll
  have henergy : ∀ z : H1CoerciveHilbertSpace (U := openCubeSet R),
      (∫ x in openCubeSet R,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq ((H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad x) ∂volume) = B z z := by
    intro z
    rw [H1CoerciveHilbert.coeffGradientBilin_apply_eq_integral]
    apply integral_congr_ae
    filter_upwards with x
    rw [vecDot_comm,
      Section6HolderInterior.vecDot_matVecMul_scalarCoeffField]
  have hB : Continuous fun z : H1CoerciveHilbertSpace (U := openCubeSet R) =>
      B z z := by
    fun_prop
  have hpair : Continuous fun z : H1CoerciveHilbertSpace (U := openCubeSet R) =>
      inner ℝ G (H1CoerciveHilbert.gradient (U := openCubeSet R) z) := by
    fun_prop
  simpa only [oneStepNeumannDenseFunctional, henergy] using!
    (continuous_const.mul hpair).sub hB

private theorem oneStepNeumannDenseFunctional_le_solutionEnergy
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d)
    (omega : Sample d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (g : Vec d → Vec d)
    (G : HilbertVectorL2 (openCubeSet R))
    (hpair : ∀ z : H1CoerciveHilbertSpace (U := openCubeSet R),
      inner ℝ G (H1CoerciveHilbert.gradient (U := openCubeSet R) z) =
        ∫ x in openCubeSet R, vecDot (g x)
          ((H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad x) ∂volume)
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) g)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)))
    (z : H1CoerciveHilbertSpace (U := openCubeSet R)) :
    oneStepNeumannDenseFunctional M L R (fun _ => G) omega z ≤
      ∫ x in openCubeSet R,
        vecDot (X.potential.toH1Function.grad x) (X.flux x) ∂volume := by
  let u := X.potential
  let v := H1CoerciveHilbert.toH1MeanZeroFunction (U := openCubeSet R) z
  let a := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  have hcrossInt : IntegrableOn (fun x =>
      vecDot (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x))
        (v.toH1Function.grad x)) (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll
        u.toH1Function.grad_memVectorL2)
      v.toH1Function.grad_memVectorL2
  have hvInt : IntegrableOn (fun x =>
      vecDot (v.toH1Function.grad x)
        (matVecMul (scalarCoeffField a x) (v.toH1Function.grad x)))
      (openCubeSet R) :=
    integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn_meanZero hEll v
  have huInt : IntegrableOn (fun x =>
      vecDot (u.toH1Function.grad x)
        (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x)))
      (openCubeSet R) :=
    integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn_meanZero hEll u
  have hpoint : ∀ x ∈ openCubeSet R,
      2 * vecDot (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x))
          (v.toH1Function.grad x) -
        vecDot (v.toH1Function.grad x)
          (matVecMul (scalarCoeffField a x) (v.toH1Function.grad x)) ≤
        vecDot (u.toH1Function.grad x)
          (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x)) := by
    intro x hx
    have ha0 : 0 ≤ a x := (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
    have hc := two_vecDot_le_of_pos (d := d) one_pos
      (u.toH1Function.grad x) (v.toH1Function.grad x)
    rw [Section6HolderInterior.vecDot_matVecMul_scalarCoeffField,
      Section6HolderInterior.vecDot_matVecMul_scalarCoeffField]
    have hcross : vecDot (matVecMul (scalarCoeffField a x)
        (u.toH1Function.grad x)) (v.toH1Function.grad x) =
        a x * vecDot (u.toH1Function.grad x) (v.toH1Function.grad x) := by
      simp only [scalarCoeffField, matVecMul_scalarMatrix, vecDot_smul_left]
    rw [hcross]
    nlinarith [mul_nonneg ha0
      (sub_nonneg.mpr (by simpa only [one_mul, inv_one] using hc))]
  have hIntegralLe :
      ∫ x in openCubeSet R,
          (2 * vecDot (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x))
              (v.toH1Function.grad x) -
            vecDot (v.toH1Function.grad x)
              (matVecMul (scalarCoeffField a x) (v.toH1Function.grad x))) ∂volume ≤
        ∫ x in openCubeSet R,
          vecDot (u.toH1Function.grad x)
            (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x)) ∂volume := by
    apply integral_mono_ae ((hcrossInt.const_mul 2).sub hvInt) huInt
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hpoint x hx
  have hweak := X.weakSolution v
  have hscalarEq :
      (∫ x in openCubeSet R,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq ((H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad x) ∂volume) =
      ∫ x in openCubeSet R,
        vecDot (v.toH1Function.grad x)
          (matVecMul (scalarCoeffField a x) (v.toH1Function.grad x)) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Section6HolderInterior.vecDot_matVecMul_scalarCoeffField]
  have htarget : oneStepNeumannDenseFunctional M L R (fun _ => G) omega z =
      ∫ x in openCubeSet R,
          (2 * vecDot (matVecMul (scalarCoeffField a x) (u.toH1Function.grad x))
              (v.toH1Function.grad x) -
            vecDot (v.toH1Function.grad x)
              (matVecMul (scalarCoeffField a x) (v.toH1Function.grad x))) ∂volume := by
    rw [oneStepNeumannDenseFunctional, hpair z]
    rw [← hweak]
    rw [hscalarEq]
    rw [← integral_const_mul, ← integral_sub (hcrossInt.const_mul 2) hvInt]
  rw [htarget]
  calc
    _ ≤ _ := hIntegralLe
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rfl

private noncomputable def oneStepH1DenseSeq (R : TriadicCube d) :
    ℕ → H1CoerciveHilbertSpace (U := openCubeSet R) := by
  letI : MeasureTheory.IsSeparable
      (volumeMeasureOn (openCubeSet R)) := inferInstance
  letI : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  letI : SecondCountableTopology (ScalarL2 (openCubeSet R)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (HilbertVectorL2 (openCubeSet R)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology
      (H1CoerciveHilbertSpace (U := openCubeSet R)) := inferInstance
  exact TopologicalSpace.denseSeq
    (H1CoerciveHilbertSpace (U := openCubeSet R))

private theorem denseRange_oneStepH1DenseSeq (R : TriadicCube d) :
    DenseRange (oneStepH1DenseSeq R) := by
  let : MeasureTheory.IsSeparable
      (volumeMeasureOn (openCubeSet R)) := inferInstance
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  let : SecondCountableTopology (ScalarL2 (openCubeSet R)) :=
    MeasureTheory.Lp.SecondCountableTopology
  let : SecondCountableTopology (HilbertVectorL2 (openCubeSet R)) :=
    MeasureTheory.Lp.SecondCountableTopology
  let : SecondCountableTopology
      (H1CoerciveHilbertSpace (U := openCubeSet R)) := inferInstance
  exact TopologicalSpace.denseRange_denseSeq
    (H1CoerciveHilbertSpace (U := openCubeSet R))

private theorem solutionEnergy_eq_iSup_oneStepNeumannDenseFunctional
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (R : TriadicCube d)
    (omega : Sample d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (g : Vec d → Vec d)
    (G : HilbertVectorL2 (openCubeSet R))
    (hpair : ∀ z : H1CoerciveHilbertSpace (U := openCubeSet R),
      inner ℝ G (H1CoerciveHilbert.gradient (U := openCubeSet R) z) =
        ∫ x in openCubeSet R, vecDot (g x)
          ((H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad x) ∂volume)
    (X : OneStepNeumannCellMinimizer R
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) g)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))) :
    (∫ x in openCubeSet R,
        vecDot (X.potential.toH1Function.grad x) (X.flux x) ∂volume) =
      ⨆ j : ℕ, oneStepNeumannDenseFunctional M L R (fun _ => G) omega
        (oneStepH1DenseSeq R j) := by
  classical
  let H := H1CoerciveHilbertSpace (U := openCubeSet R)
  let xi : ℕ → H := oneStepH1DenseSeq R
  let E : ℝ := ∫ x in openCubeSet R,
    vecDot (X.potential.toH1Function.grad x) (X.flux x) ∂volume
  let Phi : H → ℝ := fun z =>
    oneStepNeumannDenseFunctional M L R (fun _ => G) omega z
  have hle : ∀ z, Phi z ≤ E := by
    intro z
    exact oneStepNeumannDenseFunctional_le_solutionEnergy
      M L R omega g G hpair X hEll z
  have hbdd : BddAbove (Set.range fun j => Phi (xi j)) :=
    ⟨E, fun y hy => by obtain ⟨j, rfl⟩ := hy; exact hle (xi j)⟩
  have hupper : (⨆ j, Phi (xi j)) ≤ E := ciSup_le fun j => hle (xi j)
  let zu : H := H1MeanZeroFunction.toH1CoerciveHilbertSpace
    (U := openCubeSet R) X.potential
  let vu : H1MeanZeroFunction (openCubeSet R) :=
    H1CoerciveHilbert.toH1MeanZeroFunction (U := openCubeSet R) zu
  have hgradClass : vu.gradToHilbertVectorL2 =
      X.potential.gradToHilbertVectorL2 := by
    simp only [vu, zu,
      H1CoerciveHilbert.toH1MeanZeroFunction_gradToHilbertVectorL2,
      H1MeanZeroFunction.H1CoerciveHilbert_gradient_toH1CoerciveHilbertSpace]
  have hgradAE : vu.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      X.potential.toH1Function.grad := by
    filter_upwards [vu.toH1Function.coeFn_gradToHilbertVectorL2,
      X.potential.toH1Function.coeFn_gradToHilbertVectorL2] with x hv hu
    have hClass : vu.toH1Function.gradToHilbertVectorL2 =
        X.potential.toH1Function.gradToHilbertVectorL2 := hgradClass
    have hAt := congrArg
      (fun F : HilbertVectorL2 (openCubeSet R) => F x) hClass
    have hHilbert : hilbertifyVecField vu.toH1Function.grad x =
        hilbertifyVecField X.potential.toH1Function.grad x := by
      rw [← hv, ← hu]
      exact hAt
    simpa only [hilbertifyVecField, HilbertVec.toVec_ofVec] using
      congrArg HilbertVec.toVec hHilbert
  have hcrossEq :
      (∫ x in openCubeSet R, vecDot (g x) (vu.toH1Function.grad x) ∂volume) =
      ∫ x in openCubeSet R,
        vecDot (g x) (X.potential.toH1Function.grad x) ∂volume :=
    by
      apply integral_congr_ae
      filter_upwards [hgradAE] with x hx
      rw [hx]
  have hcoeffEq :
      (∫ x in openCubeSet R,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (vu.toH1Function.grad x) ∂volume) =
      ∫ x in openCubeSet R,
        vecDot (X.potential.toH1Function.grad x) (X.flux x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hgradAE] with x hx
    rw [hx]
    exact (Section6HolderInterior.vecDot_matVecMul_scalarCoeffField
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x
      (X.potential.toH1Function.grad x)).symm
  have hPhiZu : Phi zu = E := by
    change oneStepNeumannDenseFunctional M L R (fun _ => G) omega zu = E
    rw [oneStepNeumannDenseFunctional, hpair zu]
    change 2 * (∫ x in openCubeSet R,
        vecDot (g x) (vu.toH1Function.grad x) ∂volume) -
      (∫ x in openCubeSet R,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (vu.toH1Function.grad x) ∂volume) = E
    rw [hcrossEq, hcoeffEq, ← X.energy_identity]
    ring
  have hcont : Continuous Phi := by
    exact continuous_oneStepNeumannDenseFunctional M L R omega G hEll
  have hclosure : zu ∈ closure (Set.range xi) := by
    exact denseRange_oneStepH1DenseSeq R zu
  obtain ⟨s, hsrange, hsto⟩ := mem_closure_iff_seq_limit.mp hclosure
  choose index hindex using hsrange
  have hxiTendsto : Tendsto (fun j => xi (index j)) atTop (𝓝 zu) := by
    have heq : (fun j => xi (index j)) = s := funext hindex
    rw [heq]
    exact hsto
  have hPhiTendsto : Tendsto (fun j => Phi (xi (index j))) atTop (𝓝 E) := by
    simpa only [hPhiZu] using! hcont.continuousAt.tendsto.comp hxiTendsto
  have hlower : E ≤ ⨆ j, Phi (xi j) := by
    apply le_of_tendsto hPhiTendsto
    filter_upwards with j
    exact le_ciSup hbdd (index j)
  exact le_antisymm hlower hupper

private theorem dualGluedCellHalfEnergyAt_eq_scaled_iSup_of_pairing
    [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ) (q : Vec d)
    (hh : 0 < h) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet R))]
    (G : Sample d → HilbertVectorL2 (openCubeSet R))
    (hpair : ∀ omega,
      ∀ z : H1CoerciveHilbertSpace (U := openCubeSet R),
      inner ℝ (G omega) (H1CoerciveHilbert.gradient (U := openCubeSet R) z) =
        ∫ x in openCubeSet R,
          vecDot (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)
            ((H1CoerciveHilbert.toH1MeanZeroFunction
              (U := openCubeSet R) z).toH1Function.grad x) ∂volume)
    (omega : Sample d) :
    dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega =
      (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
        (⨆ r : ℕ, oneStepNeumannDenseFunctional M (n + h) R G omega
          (oneStepH1DenseSeq R r)) := by
  classical
  let Q : TriadicCube d := originCube d (K : ℤ)
  let j := K - oneStepLocalizationScale n M.delta
  have hRD : R ∈ descendantsAtDepth Q j := by
    simpa only [Q, j, oneStepSourceCells] using hR
  let g : Vec d → Vec d :=
    oneStepPaperNeumannFlux M n h q Q omega hh
  let a : CoeffField d :=
    scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega)
  let hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn
        (dualParentEllipticityData M (n + h) omega Q).1
        (dualParentEllipticityData M (n + h) omega Q).2
        (openCubeSet S) a :=
    dualParentEllipticityData_descendants M (n + h) omega Q j
  let P : TriadicCube d → Vec d → Vec d := fun S =>
    oneStepPaperNeumannCellMeanField M n h q Q S omega hh
  let F : TriadicCube d → Vec d → Vec d := fun S =>
    oneStepPaperNeumannCellFluctuationField M n h q Q S omega hh
  have hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S) :=
    oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
      M n h q Q omega hh
  have hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S) :=
    oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
      M n h q Q omega hh
  let XP := oneStepSelectedNeumannCell a P hEll hP R hRD
  let XF := oneStepSelectedNeumannCell a F hEll hF R hRD
  let X := XP.add XF (hEll R hRD) (hP R hRD) (hF R hRD)
  have hbackground : ∀ x, P R x + F R x = g x := by
    intro x
    exact oneStepPaperNeumannCellMean_add_fluctuation
      M n h q Q R omega hh x
  let Xg : OneStepNeumannCellMinimizer R a g := {
    potential := X.potential
    weakSolution := by
      intro phi
      calc
        ∫ x in openCubeSet R,
            vecDot (matVecMul (a x) (X.potential.toH1Function.grad x))
              (phi.toH1Function.grad x) ∂volume =
            ∫ x in openCubeSet R,
              vecDot ((P R + F R) x) (phi.toH1Function.grad x) ∂volume :=
          X.weakSolution phi
        _ = ∫ x in openCubeSet R,
              vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Pi.add_apply, hbackground x]
  }
  have hflux : ∀ x ∈ openCubeSet R,
      oneStepSelectedRetainedGluedNeumannTwoFlux Q j
          (descendantsAtDepth Q j) a P F g hEll hP hF x = Xg.flux x := by
    intro x hx
    rw [oneStepSelectedRetainedGluedNeumannTwoFlux_eq_of_mem
      a P F g (fun _S hS => hS) hEll hP hF hRD hx (hbackground x).symm]
    change _ = X.flux x
    exact (OneStepNeumannCellMinimizer.add_flux XP XF
      (hEll R hRD) (hP R hRD) (hF R hRD) x).symm
  have henergyEq :
      dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega =
        (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
          (∫ x in openCubeSet R,
            vecDot (Xg.potential.toH1Function.grad x) (Xg.flux x) ∂volume) := by
    rw [show dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega =
        (1 / 2 : ℝ) * volumeAverage (openCubeSet R) (fun x =>
          vecDot (Xg.flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (Xg.flux x))) by
      unfold dualGluedCellHalfEnergyAt paperGluedCellHalfEnergy
      rw [volumeAverage_const_mul]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      rw [hflux x hx]]
    unfold volumeAverage
    have hintEq :
        (∫ x in openCubeSet R,
          vecDot (Xg.flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight) (Xg.flux x))
            ∂volume) =
          ∫ x in openCubeSet R,
            vecDot (Xg.potential.toH1Function.grad x) (Xg.flux x) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact vecDot_flux_lowerRight_flux_eq_gradientPairing
        M (n + h) omega Xg Xg x
    rw [hintEq]
    ring
  have hsolution := solutionEnergy_eq_iSup_oneStepNeumannDenseFunctional
    M (n + h) R omega g (G omega) (hpair omega) Xg (hEll R hRD)
  calc
    dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega =
        (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
          (∫ x in openCubeSet R,
            vecDot (Xg.potential.toH1Function.grad x) (Xg.flux x) ∂volume) := henergyEq
    _ = (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
        (⨆ r : ℕ, oneStepNeumannDenseFunctional M (n + h) R
          (fun _ => G omega) omega (oneStepH1DenseSeq R r)) :=
      congrArg (fun t : ℝ =>
        (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ * t) hsolution
    _ = (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
        (⨆ r : ℕ, oneStepNeumannDenseFunctional M (n + h) R G omega
          (oneStepH1DenseSeq R r)) := rfl

/-- Although the glued cell minimizers were introduced by classical choice,
their scalar energy is measurable.  The proof identifies that energy with a
countable supremum over the fixed dense family `oneStepH1DenseSeq`. -/
theorem measurable_dualGluedCellHalfEnergyAt
    [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ) (q : Vec d)
    (hh : 0 < h)
    (R : TriadicCube d) (hR : R ∈ oneStepSourceCells d K n M.delta) :
    Measurable (dualGluedCellHalfEnergyAt (K := K) M n h q hh R) := by
  classical
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  let Q : TriadicCube d := originCube d (K : ℤ)
  let j := K - oneStepLocalizationScale n M.delta
  have hRD : R ∈ descendantsAtDepth Q j := by
    simpa only [Q, j, oneStepSourceCells] using hR
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRD
  let g : Sample d → Vec d → Vec d := fun omega =>
    oneStepPaperNeumannFlux M n h q Q omega hh
  have hg : ∀ omega, MemVectorL2 (openCubeSet R) (g omega) := by
    intro omega
    exact (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh).mono_measure
      (Measure.restrict_mono_set volume hRQ)
  let G : Sample d → HilbertVectorL2 (openCubeSet R) := fun omega =>
    toHilbertVectorL2OfVecField (hg omega)
  have hG_eq : G = fun omega => hilbertVectorL2RestrictCLM hRQ
      (oneStepPaperNeumannFluxL2 M n h q Q omega hh) := by
    funext omega
    rw [oneStepPaperNeumannFluxL2_eq_toHilbertVectorL2OfVecField]
    apply Lp.ext
    filter_upwards
        [coeFn_toHilbertVectorL2OfVecField (hg omega),
          hilbertVectorL2RestrictCLM_coeFn hRQ
            (toHilbertVectorL2OfVecField
              (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh)),
          (coeFn_toHilbertVectorL2OfVecField
            (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh)).filter_mono
              (ae_mono (Measure.restrict_mono_set volume hRQ))]
      with x hlocal hrestrict hparent
    rw [hlocal, hrestrict, hparent]
  have hGmeas : Measurable G := by
    rw [hG_eq]
    apply Measurable.hilbertVectorL2_restrict hRQ
    exact (measurable_oneStepPaperNeumannFluxL2_potentialShellIndexSigma_Ioi
      M n h q Q hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hpair : ∀ omega,
      ∀ z : H1CoerciveHilbertSpace (U := openCubeSet R),
      inner ℝ (G omega) (H1CoerciveHilbert.gradient (U := openCubeSet R) z) =
        ∫ x in openCubeSet R, vecDot (g omega x)
          ((H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad x) ∂volume := by
    intro omega z
    change inner ℝ (toHilbertVectorL2OfVecField (hg omega))
      (H1CoerciveHilbert.gradient (U := openCubeSet R) z) = _
    rw [← H1CoerciveHilbert.toH1MeanZeroFunction_gradToHilbertVectorL2]
    simpa only [H1MeanZeroFunction.gradToHilbertVectorL2,
      H1Function.gradToHilbertVectorL2] using
        inner_toHilbertVectorL2OfVecField_eq_integral (hg omega)
          (H1CoerciveHilbert.toH1MeanZeroFunction
            (U := openCubeSet R) z).toH1Function.grad_memVectorL2
  have hrep : ∀ omega,
      dualGluedCellHalfEnergyAt (K := K) M n h q hh R omega =
        (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
          (⨆ r : ℕ, oneStepNeumannDenseFunctional M (n + h) R G omega
            (oneStepH1DenseSeq R r)) :=
    dualGluedCellHalfEnergyAt_eq_scaled_iSup_of_pairing
      M n h K q hh R hR G hpair
  have hsup : Measurable fun omega =>
      ⨆ r : ℕ, oneStepNeumannDenseFunctional M (n + h) R G omega
        (oneStepH1DenseSeq R r) := by
    apply Measurable.iSup
    intro r
    exact measurable_oneStepNeumannDenseFunctional M (n + h) R G hGmeas
      (oneStepH1DenseSeq R r)
  have hscaled : Measurable fun omega =>
      (1 / 2 : ℝ) * (volume (openCubeSet R)).toReal⁻¹ *
        (⨆ r : ℕ, oneStepNeumannDenseFunctional M (n + h) R G omega
          (oneStepH1DenseSeq R r)) := measurable_const.mul hsup
  convert hscaled using 1
  funext omega
  exact hrep omega

/-- **The translated glued-cell envelope.**  The constant is allowed to
depend on the fixed model and cutoff depths, but is uniform in the parent
scale and in the translated source cell. -/
theorem exists_dualGluedCellPathwiseEnvelope (d : ℕ) [NeZero d] :
    DualGluedCellPathwiseEnvelope d := by
  intro M n h
  let CW : ℝ := ∫ omega,
    Real.exp (aCutoffCubeLogEnvelope M (n + h)
      (oneStepLocalizationScale n M.delta : ℤ) omega) ^ (4 : ℕ)
      ∂M.P.toMeasure
  have hCW : 0 ≤ CW := by
    exact integral_nonneg fun _ => pow_nonneg (Real.exp_pos _).le _
  refine ⟨CW, hCW, ?_⟩
  intro K q hq hh hblock hsource hK
  let W : TriadicCube d → Sample d → ℝ := fun R =>
    oneStepDualCellCutoffEnvelope M n h R
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · intro R hR omega
    exact (Real.exp_pos _).le
  · intro R hR
    exact memLp_four_oneStepDualCellCutoffEnvelope M n h R
  · intro R hR
    rw [show (∫ omega, W R omega ^ (4 : ℕ) ∂M.P.toMeasure) = CW by
      exact integral_oneStepDualCellCutoffEnvelope_four_eq M n h R]
  · intro R hR
    exact (measurable_dualGluedCellHalfEnergyAt M n h K q hh R hR
      ).aestronglyMeasurable
  · intro R hR omega
    exact dualGluedCellHalfEnergyAt_le_translatedEnvelope_mul_fluxAverage
      M n h K q hh hK R hR omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
