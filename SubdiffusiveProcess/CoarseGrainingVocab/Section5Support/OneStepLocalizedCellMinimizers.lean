module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellEnergy
public import Homogenization.PDE.NeumannRHS
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import Homogenization.CoarseGraining.Symmetric.VariationalProblems

@[expose] public section

/-!
# Local variable-coefficient cell minimizers for the one-step argument

This module supplies the actual cell fields used in Steps 2.  The construction mirrors
`Algsuperdiff/.../ApproximateRecurrence/LocalizationSelectionExistence.lean`,
but uses CoarseGraining's established Dirichlet and Neumann Lax--Milgram
operators directly.

For a vector field `F` on a triadic cell and a uniformly elliptic coefficient
`a`, the primal selection is the zero-trace solution with datum `-a F`; hence
`F + grad phi` is coefficient-solenoidal.  The dual selection is the mean-zero
Neumann solution with datum `G`; its flux `a grad eta` differs from `G` by a
solenoidal field with zero normal trace.  These are exactly the manuscript's
`chi_z, phi_z, psi_z, eta_z` carriers.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A selected zero-trace minimizer for the affine Dirichlet problem with
field-valued slope `F`. -/
structure OneStepDirichletCellMinimizer {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (F : Vec d → Vec d) where
  correction : H10Function (openCubeSet Q)
  weakSolution : IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q)
    correction (fun x => -matVecMul (a x) (F x))

/-- A selected mean-zero Neumann minimizer for a prescribed flux field `G`.
The physical flux is `a grad potential`; its difference from `G` has zero
normal trace. -/
structure OneStepNeumannCellMinimizer {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (G : Vec d → Vec d) where
  potential : H1MeanZeroFunction (openCubeSet Q)
  weakSolution : IsMeanZeroNeumannRhsWeakSolution a (openCubeSet Q)
    potential G

/-- The corrected primal field `F + grad phi`. -/
def OneStepDirichletCellMinimizer.field {d : ℕ} {Q : TriadicCube d}
    {a : CoeffField d} {F : Vec d → Vec d}
    (X : OneStepDirichletCellMinimizer Q a F) : Vec d → Vec d :=
  fun x => F x + X.correction.toH1Function.grad x

/-- The selected dual flux `a grad eta`. -/
def OneStepNeumannCellMinimizer.flux {d : ℕ} {Q : TriadicCube d}
    {a : CoeffField d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer Q a G) : Vec d → Vec d :=
  fun x => matVecMul (a x) (X.potential.toH1Function.grad x)

/-- The zero-normal-trace correction to the prescribed dual field. -/
def OneStepNeumannCellMinimizer.residual {d : ℕ} {Q : TriadicCube d}
    {a : CoeffField d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer Q a G) : Vec d → Vec d :=
  fun x => X.flux x - G x

/-- A Dirichlet cell minimizer depends only on the almost-everywhere class
of its prescribed slope. -/
def OneStepDirichletCellMinimizer.congrDatum {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {F G : Vec d → Vec d}
    (X : OneStepDirichletCellMinimizer Q a F)
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    OneStepDirichletCellMinimizer Q a G where
  correction := X.correction
  weakSolution := by
    intro phi
    calc
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (X.correction.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (-matVecMul (a x) (F x))
            (phi.toH1Function.grad x) ∂volume := X.weakSolution phi
      _ = ∫ x in openCubeSet Q,
          vecDot (-matVecMul (a x) (G x))
            (phi.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hFG] with x hx
        rw [hx]

/-- A Neumann cell minimizer likewise depends only on the almost-everywhere
class of its prescribed flux datum. -/
def OneStepNeumannCellMinimizer.congrDatum {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {F G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer Q a F)
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    OneStepNeumannCellMinimizer Q a G where
  potential := X.potential
  weakSolution := by
    intro phi
    calc
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (X.potential.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (F x) (phi.toH1Function.grad x) ∂volume :=
            X.weakSolution phi
      _ = ∫ x in openCubeSet Q,
          vecDot (G x) (phi.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hFG] with x hx
        rw [hx]

/-- Uniqueness of the cell Dirichlet problem identifies the corrected fields
of any two minimizer selections. -/
theorem OneStepDirichletCellMinimizer.field_ae_eq
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {F : Vec d → Vec d} {lam Lam : ℝ}
    (X Y : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    X.field =ᵐ[volumeMeasureOn (openCubeSet Q)] Y.field := by
  have hgrad :=
    IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (openCubeSet_nonempty_internal Q) X.weakSolution Y.weakSolution hEll
  have hX := X.correction.toH1Function.coeFn_gradToVectorL2
  have hY := Y.correction.toH1Function.coeFn_gradToVectorL2
  rw [hgrad] at hX
  filter_upwards [hX, hY] with x hx hy
  unfold OneStepDirichletCellMinimizer.field
  rw [← hx, ← hy]

/-- Neumann uniqueness identifies the selected physical fluxes. -/
theorem OneStepNeumannCellMinimizer.flux_ae_eq
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    {F : Vec d → Vec d} {lam Lam : ℝ}
    (X Y : OneStepNeumannCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    X.flux =ᵐ[volumeMeasureOn (openCubeSet Q)] Y.flux := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hgrad :=
    IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (openCubeSet_nonempty_internal Q) X.weakSolution Y.weakSolution hEll
  change X.potential.toH1Function.gradToVectorL2 =
    Y.potential.toH1Function.gradToVectorL2 at hgrad
  have hX := X.potential.toH1Function.coeFn_gradToVectorL2
  have hY := Y.potential.toH1Function.coeFn_gradToVectorL2
  rw [hgrad] at hX
  filter_upwards [hX, hY] with x hx hy
  unfold OneStepNeumannCellMinimizer.flux
  rw [← hx, ← hy]

/-- Existence of the variable-coefficient zero-trace cell minimizer. -/
theorem exists_oneStepDirichletCellMinimizer {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : Vec d → Vec d) (hF : MemVectorL2 (openCubeSet Q) F) :
    Nonempty (OneStepDirichletCellMinimizer Q a F) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  have haF : MemVectorL2 (openCubeSet Q)
      (fun x => -matVecMul (a x) (F x)) :=
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll hF).neg
  obtain ⟨phi, hphi⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      haF hRealize (Book.Ch02.openCubeSet_nonempty Q) hEll
  exact ⟨⟨phi, hphi⟩⟩

/-- Existence of the variable-coefficient mean-zero Neumann cell minimizer. -/
theorem exists_oneStepNeumannCellMinimizer {d : ℕ}
    (Q : TriadicCube d) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G) :
    Nonempty (OneStepNeumannCellMinimizer Q a G) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hC : H1CoerciveEstimate (openCubeSet Q) :=
    h1CoerciveEstimate_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  obtain ⟨eta, heta⟩ :=
    exists_isMeanZeroNeumannRhsWeakSolution_of_h1CoerciveEstimate
      hG hC (Book.Ch02.openCubeSet_nonempty Q) hEll
  exact ⟨⟨eta, heta⟩⟩

/-- Canonical choice of the primal cell minimizer.  All downstream facts use
`oneStepDirichletCellMinimizer_weakSolution`, so no property depends on the
choice of Sobolev representative. -/
noncomputable def oneStepDirichletCellMinimizer {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : Vec d → Vec d) (hF : MemVectorL2 (openCubeSet Q) F) :
    OneStepDirichletCellMinimizer Q a F :=
  Classical.choice (exists_oneStepDirichletCellMinimizer Q hEll F hF)

theorem oneStepDirichletCellMinimizer_weakSolution {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : Vec d → Vec d) (hF : MemVectorL2 (openCubeSet Q) F) :
    IsZeroTraceDirichletRhsWeakSolution a (openCubeSet Q)
      (oneStepDirichletCellMinimizer Q hEll F hF).correction
      (fun x => -matVecMul (a x) (F x)) :=
  (oneStepDirichletCellMinimizer Q hEll F hF).weakSolution

/-- Canonical choice of the dual cell minimizer. -/
noncomputable def oneStepNeumannCellMinimizer {d : ℕ}
    (Q : TriadicCube d) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G) :
    OneStepNeumannCellMinimizer Q a G :=
  Classical.choice (exists_oneStepNeumannCellMinimizer Q hEll G hG)

theorem oneStepNeumannCellMinimizer_weakSolution {d : ℕ}
    (Q : TriadicCube d) {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G) :
    IsMeanZeroNeumannRhsWeakSolution a (openCubeSet Q)
      (oneStepNeumannCellMinimizer Q hEll G hG).potential G :=
  (oneStepNeumannCellMinimizer Q hEll G hG).weakSolution

/-- The selected primal field is weakly coefficient-solenoidal. -/
theorem OneStepDirichletCellMinimizer.weakDivergenceFree {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} (X : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    ∀ psi : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (a x) (X.field x))
            (psi.toH1Function.grad x) ∂volume = 0 := by
  exact oneStep_correctedField_weakDivergenceFree hEll hF X.weakSolution

/-- The selected primal minimizer satisfies the exact energy identity used in
the oscillatory-cell estimate. -/
theorem OneStepDirichletCellMinimizer.energy_identity {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {F : Vec d → Vec d} (X : OneStepDirichletCellMinimizer Q a F)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    ∫ x in openCubeSet Q,
        vecDot (X.field x) (matVecMul (a x) (X.field x)) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (F x) (matVecMul (a x) (X.field x)) ∂volume := by
  exact oneStep_oscillatoryCell_energy_identity hEll hF X.weakSolution

/-- The dual correction has zero normal trace on its cell. -/
theorem OneStepNeumannCellMinimizer.residual_zeroNormalTrace {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) X.residual := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact X.weakSolution.residual_zeroNormalTrace hEll hG

/-- The selected dual flux belongs to vector `L²`. -/
theorem OneStepNeumannCellMinimizer.flux_memVectorL2 {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    MemVectorL2 (openCubeSet Q) X.flux := by
  exact memVectorL2_matVecMul_of_isEllipticFieldOn hEll
    X.potential.toH1Function.grad_memVectorL2

/-- The dual cell energy is paired exactly with the prescribed flux field. -/
theorem OneStepNeumannCellMinimizer.energy_identity {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    {G : Vec d → Vec d} (X : OneStepNeumannCellMinimizer Q a G) :
    ∫ x in openCubeSet Q,
        vecDot (X.potential.toH1Function.grad x)
          (X.flux x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (G x) (X.potential.toH1Function.grad x) ∂volume := by
  exact X.weakSolution.energy_identity

/-! ## Identification with the public symmetric variational carriers -/

/-- Add the affine boundary datum to a selected constant-slope Dirichlet
correction. -/
def OneStepDirichletCellMinimizer.affineFunction {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {p : Vec d}
    (X : OneStepDirichletCellMinimizer Q a (fun _ => p)) :
    H1Function (openCubeSet Q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p +
      X.correction.toH1Function

/-- A selected constant-slope cell minimizer is exactly an affine Dirichlet
solution in CoarseGraining's public symmetric variational interface. -/
theorem OneStepDirichletCellMinimizer.isAffineDirichletSolution {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ} {p : Vec d}
    (X : OneStepDirichletCellMinimizer Q a (fun _ => p))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    IsAffineDirichletSolution a (openCubeSet Q) p X.affineFunction := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  constructor
  · constructor
    · exact X.affineFunction.isPotentialOn
    · intro psi
      simpa [OneStepDirichletCellMinimizer.affineFunction,
        H1Function.affineOnIsSobolevRegularDomain_grad] using!
        X.weakDivergenceFree hEll (MeasureTheory.memLp_const p) psi
  · have hgrad : (fun x => X.affineFunction.grad x - p) =
        X.correction.toH1Function.grad := by
      funext x
      simp [OneStepDirichletCellMinimizer.affineFunction]
    simpa [hgrad] using X.correction.isPotentialZeroTraceOn

/-- A selected constant-datum Neumann minimizer is exactly the public
constant-flux Neumann solution. -/
theorem OneStepNeumannCellMinimizer.isConstantFluxNeumannSolution {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ} {q : Vec d}
    (X : OneStepNeumannCellMinimizer Q a (fun _ => q))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    IsConstantFluxNeumannSolution a (openCubeSet Q) q X.potential := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  constructor
  · constructor
    · exact X.potential.toH1Function.isPotentialOn
    · intro phi
      calc
        ∫ x in openCubeSet Q,
            vecDot (X.flux x) (phi.toH1Function.grad x) ∂volume =
            ∫ x in openCubeSet Q,
              vecDot q (phi.toH1Function.grad x) ∂volume := by
                simpa using! X.weakSolution phi.toH1Function.toMeanZero
        _ = 0 := integral_vecDot_const_zeroTraceGrad_eq_zero phi q
  · exact X.residual_zeroNormalTrace hEll (MeasureTheory.memLp_const q)

/-- Read the selected constant-slope Dirichlet cell energy as the public
coarse Dirichlet matrix quadratic form. -/
theorem OneStepDirichletCellMinimizer.energy_eq_vecDot_sigmaCoarse {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ} {p : Vec d}
    (X : OneStepDirichletCellMinimizer Q a (fun _ => p))
    (ha : IsSymmetricCoeffField a)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hA : IsCoarseBlockMatrix (openCubeSet Q) a
      (deterministicCoarseBlockMatrix (openCubeSet Q) a))
    {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse (openCubeSet Q) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet Q) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet Q) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    volumeAverage (openCubeSet Q)
        (scalarVariationEnergyIntegrand a
          (X.isAffineDirichletSolution hEll).toAHarmonicFunction) =
      vecDot p (matVecMul (sigmaCoarse (openCubeSet Q) a) p) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact (X.isAffineDirichletSolution hEll
    ).energy_eq_vecDot_sigmaCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn
      ha hEll hA hS hK hSigma hdet

/-- Read the selected constant-flux Neumann cell energy as the public starred
coarse matrix quadratic form. -/
theorem OneStepNeumannCellMinimizer.energy_eq_vecDot_sigmaStarInvCoarse {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ} {q : Vec d}
    (X : OneStepNeumannCellMinimizer Q a (fun _ => q))
    (ha : IsSymmetricCoeffField a)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse (openCubeSet Q) a sigmaStar) :
    volumeAverage (openCubeSet Q)
        (scalarVariationEnergyIntegrand a
          (X.isConstantFluxNeumannSolution hEll).toAHarmonicFunction) =
      vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact (X.isConstantFluxNeumannSolution hEll
    ).energy_eq_vecDot_sigmaStarInvCoarse_of_isSymmetricCoeffField_of_isEllipticFieldOn
      ha hEll hS

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
