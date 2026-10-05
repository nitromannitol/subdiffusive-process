module
public import SubdiffusiveProcessAudit.ProcessConvergence.SolutionBasic
public import SubdiffusiveProcess.MainTheorems
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
-- Use Mathlib's canonical instances when elaborating the challenge telescope.
attribute [-instance] Homogenization.instMeasurableSpaceVec
  MarkovProcess.ContinuousPath.instMeasurableSpace
  MarkovProcess.ContinuousPath.instBorelSpace
@[expose] public section
noncomputable section
namespace SubdiffusiveProcessAudit.ProcessConvergence
open MeasureTheory
namespace Conversion
variable {d : ℕ} {U : Set (Fin d → ℝ)}
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess.Model

/-! The isolated potential-field operations agree with the library's. -/
theorem translate_eq (z : Homogenization.Vec d) (g : PotentialField d) :
    PotentialField.translate z g =
      _root_.SubdiffusiveProcess.Model.PotentialField.translate z g := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    rfl
  · ext x v
    rfl
theorem triadicScale_eq (k : ℕ) (g : PotentialField d) :
    PotentialField.triadicScale k g =
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    simp [PotentialField.triadicScale, PotentialField.pullback,
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScaleAmbient,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialMap,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialCLM]
  · ext x v
    simp [PotentialField.triadicScale, PotentialField.pullback, PotentialField.precomp,
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScaleAmbient,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialMap,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialCLM,
      _root_.SubdiffusiveProcess.Model.PotentialField.derivScaleMap,
      _root_.SubdiffusiveProcess.Model.PotentialField.derivScaleCLM]
    rfl
theorem rotate_eq (R : Homogenization.Mat d) (hR : Homogenization.IsSignedPermutationMatrix R)
    (g : PotentialField d) :
    PotentialField.rotate R hR g =
      _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR g := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    simp [PotentialField.rotate, PotentialField.pullback,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotate,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotateAmbient,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotateDomainMap]
    rfl
  · ext x v
    simp [PotentialField.rotate, PotentialField.pullback, PotentialField.precomp,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotate,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotateAmbient,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotateDomainMap,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotateDerivativeContinuousMap,
      _root_.SubdiffusiveProcess.Model.PotentialField.rotateDerivativeMap]
    rfl
theorem negate_eq (g : PotentialField d) :
    PotentialField.negate g =
      _root_.SubdiffusiveProcess.Model.PotentialField.negate g := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    simp [PotentialField.negate,
      _root_.SubdiffusiveProcess.Model.PotentialField.negate,
      _root_.SubdiffusiveProcess.Model.PotentialField.scale,
      _root_.SubdiffusiveProcess.Model.PotentialField.scaleAmbient,
      _root_.SubdiffusiveProcess.Model.PotentialField.valueScaleMap]
  · ext x v
    simp [PotentialField.negate,
      _root_.SubdiffusiveProcess.Model.PotentialField.negate,
      _root_.SubdiffusiveProcess.Model.PotentialField.scale,
      _root_.SubdiffusiveProcess.Model.PotentialField.scaleAmbient,
      _root_.SubdiffusiveProcess.Model.PotentialField.derivScaleMap,
      _root_.SubdiffusiveProcess.Model.PotentialField.derivScaleCLM]
theorem iSup_eq_sSup_insert {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ⨆ i, f i = sSup (insert 0 (Set.range f)) := by
  by_cases hb : BddAbove (Set.range f)
  · by_cases hne : Nonempty ι
    · rw [csSup_insert hb (Set.range_nonempty f)]
      exact (sup_eq_right.mpr (Real.iSup_nonneg hf)).symm
    · have : IsEmpty ι := not_nonempty_iff.mp hne
      rw [Set.range_eq_empty, Real.iSup_of_isEmpty]
      simp
  · have hb' : ¬ BddAbove (insert (0 : ℝ) (Set.range f)) :=
      fun h => hb (h.mono (Set.subset_insert _ _))
    rw [Real.sSup_of_not_bddAbove hb', Real.iSup_of_not_bddAbove hb]
theorem unitCubeValueNorm_eq (g : PotentialField d) :
    PotentialField.unitCubeValueNorm g =
      _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm g := by
  unfold PotentialField.unitCubeValueNorm
    _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm
  rw [iSup_eq_sSup_insert _ fun x => abs_nonneg _]
  congr 1
  ext y
  constructor
  · rintro (rfl | ⟨x, rfl⟩)
    exacts [⟨none, rfl⟩, ⟨some x, rfl⟩]
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl⟩
theorem unitCubeDerivNorm_eq (g : PotentialField d) :
    PotentialField.unitCubeDerivNorm g =
      _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm g := by
  unfold PotentialField.unitCubeDerivNorm
    _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm
  rw [iSup_eq_sSup_insert _ fun x => norm_nonneg _]
  congr 1
  ext y
  constructor
  · rintro (rfl | ⟨x, rfl⟩)
    exacts [⟨none, rfl⟩, ⟨some x, rfl⟩]
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl⟩
theorem unitCubeDerivLipschitzSeminorm_eq (g : PotentialField d) :
    PotentialField.unitCubeDerivLipschitzSeminorm g =
      _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm g := by
  unfold PotentialField.unitCubeDerivLipschitzSeminorm
    _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm
  rw [iSup_eq_sSup_insert _ fun p => div_nonneg dist_nonneg dist_nonneg]
  congr 1
  ext y
  constructor
  · rintro (rfl | ⟨x, rfl⟩)
    exacts [⟨none, rfl⟩, ⟨some x, rfl⟩]
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl⟩
theorem g2Observable_eq (g : PotentialField d) :
    PotentialField.g2Observable g =
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
  unfold PotentialField.g2Observable
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
  rw [unitCubeValueNorm_eq, unitCubeDerivNorm_eq, unitCubeDerivLipschitzSeminorm_eq]
theorem localSigma_eq [NeZero d] (W : Set (Homogenization.Vec d)) :
    PotentialField.localSigma W =
      _root_.SubdiffusiveProcess.Model.PotentialField.localSigma W := by
  have h0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  unfold PotentialField.localSigma
    _root_.SubdiffusiveProcess.Model.PotentialField.localSigma
    _root_.Homogenization.LocalSigmaR
  rw [MeasurableSpace.comap_generateFrom]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨phi, hmeas, hbdd, hcpt, hsupp, t, ht, rfl⟩
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨_root_.Homogenization.entryTestR h0 h0 phi ⁻¹' t,
      ⟨h0, h0, phi, ⟨hmeas, hbdd, hcpt⟩, hsupp, t, ht, rfl⟩, ?_⟩
    ext g
    simp [_root_.Homogenization.entryTestR,
      _root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential,
      _root_.Homogenization.scalarMatrix]
    rfl
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨S, ⟨i, j, phi, ⟨hmeas, hbdd, hcpt⟩, hsupp, t, ht, rfl⟩, rfl⟩
    by_cases hij : i = j
    · subst hij
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨phi, hmeas, hbdd, hcpt, hsupp, t, ht, ?_⟩
      ext g
      simp [_root_.Homogenization.entryTestR,
        _root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential,
        _root_.Homogenization.scalarMatrix]
      rfl
    · have hzero : ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
          _root_.Homogenization.entryTestR i j phi
            (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) = 0 := by
        intro g
        simp [_root_.Homogenization.entryTestR,
          _root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential,
          _root_.Homogenization.scalarMatrix, hij]
      have : (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential ⁻¹'
          (_root_.Homogenization.entryTestR i j phi ⁻¹' t) :
            Set (_root_.SubdiffusiveProcess.Model.PotentialField d)) = {_g | (0 : ℝ) ∈ t} := by
        ext g
        change _root_.Homogenization.entryTestR i j phi
          (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) ∈ t ↔ (0 : ℝ) ∈ t
        rw [hzero g]
      rw [this]
      exact MeasurableSet.const _
def h1To (u : Homogenization.H1Function U) : _root_.Homogenization.H1Function U :=
  ⟨u.toFun, u.grad, u.memL2, u.gradMemL2, u.hasWeakGradient⟩
def h1From (u : _root_.Homogenization.H1Function U) : Homogenization.H1Function U :=
  ⟨u.toFun, u.grad, u.memL2, u.gradMemL2, u.hasWeakGradient⟩
@[simp] theorem h1From_to (u : Homogenization.H1Function U) : h1From (h1To u) = u := by cases u; rfl
@[simp] theorem h1To_from (u : _root_.Homogenization.H1Function U) : h1To (h1From u) = u := by cases u; rfl
def h10To (u : Homogenization.H10Function U) : _root_.Homogenization.H10Function U :=
  ⟨h1To u.toH1Function, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩
def h10From (u : _root_.Homogenization.H10Function U) : Homogenization.H10Function U :=
  ⟨h1From u.toH1Function, u.approx, u.approx_smooth, u.approx_hasCompactSupport,
    u.approx_support_subset, u.tendsto_approx, u.tendsto_approx_grad⟩
@[simp] theorem h10From_to (u : Homogenization.H10Function U) : h10From (h10To u) = u := by cases u; rfl
@[simp] theorem h10To_from (u : _root_.Homogenization.H10Function U) : h10To (h10From u) = u := by cases u; rfl

def toModel (M : GMCModel d) : _root_.SubdiffusiveProcess.Model.GMCModel d :=
  haveI : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  { delta := M.delta
    P := M.P
    shellPrefix := ⟨M.shellPrefix.dimension, M.shellPrefix.delta_pos,
      M.shellPrefix.delta_le_half, M.shellPrefix.independent, fun k => by
        have h := M.shellPrefix.marginal_scaling k
        have hf : (PotentialField.triadicScale k : PotentialField d → PotentialField d) =
            _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k :=
          funext (triadicScale_eq k)
        rw [hf] at h
        exact h⟩
    G1 := ⟨M.G1.integrable, M.G1.mean_zero, fun z => by
        have h := M.G1.stationary z
        have hf : (PotentialField.translate z : PotentialField d → PotentialField d) =
            _root_.SubdiffusiveProcess.Model.PotentialField.translate z :=
          funext (translate_eq z)
        rw [hf] at h
        exact h, by
        intro W V hW hV hWV
        rw [← localSigma_eq W, ← localSigma_eq V]
        exact M.G1.range_dependence W V hW hV hWV⟩
    G2 := ⟨by
      have h := M.G2.regularity_expectation
      have hf : (PotentialField.g2Observable : PotentialField d → ℝ) =
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable :=
        funext g2Observable_eq
      rw [hf] at h
      exact h⟩
    G3 := ⟨fun R hR => by
        have h := M.G3.signed_coordinate_permutations R hR
        have hf : (PotentialField.rotate R hR : PotentialField d → PotentialField d) =
            _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR :=
          funext (rotate_eq R hR)
        rw [hf] at h
        exact h, by
        have h := M.G3.negation
        have hf : (PotentialField.negate : PotentialField d → PotentialField d) =
            _root_.SubdiffusiveProcess.Model.PotentialField.negate :=
          funext negate_eq
        rw [hf] at h
        exact h⟩
    G4 := ⟨M.G4.exponential_integrable, M.G4.tauSq_pos⟩ }

open scoped Pointwise in
/-- The cell energy of the isolated vocabulary is the diagonal entry of the library's coarse matrix. -/
theorem cellEnergy_eq (M : GMCModel d) (L n : ℕ) (omega : PotentialSample d) (i : Fin d) :
    SubdiffusiveProcess.CoarseGrainingVocab.cellEnergy (aCutoff M L omega)
        (Homogenization.originCube d n) i =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix (toModel M) L
        (_root_.Homogenization.Book.Ch02.cubeDomain (_root_.Homogenization.originCube d n))
        omega i i := by
  let U := _root_.Homogenization.Book.Ch02.cubeDomain (_root_.Homogenization.originCube d n)
  have hdata := _root_.SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData (toModel M) L omega U
  have ha0 : ∀ x, 0 ≤ _root_.SubdiffusiveProcess.Model.aCutoff (toModel M) L omega x :=
    fun x => (Real.exp_pos _).le
  have h := _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.vecDot_aMatrix_eq_dirichletInfOn
    hdata ha0 (Pi.single i 1)
  have hdiag : _root_.Homogenization.vecDot (Pi.single i (1 : ℝ))
      (_root_.Homogenization.matVecMul
        (_root_.SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hdata.toCoeffOn) (Pi.single i 1)) =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hdata.toCoeffOn i i := by
    simp [_root_.Homogenization.vecDot, _root_.Homogenization.matVecMul, Pi.single_apply]
  show _ = _root_.SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hdata.toCoeffOn i i
  rw [← hdiag, h, _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletInfOn]
  unfold SubdiffusiveProcess.CoarseGrainingVocab.cellEnergy
  have hset : {E | ∃ w : Homogenization.H10Function
        (Homogenization.openCubeSet (Homogenization.originCube d n)),
      E = SubdiffusiveProcess.CoarseGrainingVocab.volumeAverage
        (Homogenization.openCubeSet (Homogenization.originCube d n))
        (fun x => aCutoff M L omega x *
          Homogenization.vecNormSq (Homogenization.basisVec i + w.grad x))} =
      (MeasureTheory.volume (U : Set (Fin d → ℝ))).toReal⁻¹ •
        _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.dirichletEnergySet
          (_root_.SubdiffusiveProcess.Model.aCutoff (toModel M) L omega)
          (U : Set (Fin d → ℝ)) (Pi.single i 1) := by
    ext E
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨h10To w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨h10From w, rfl⟩
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  rfl

theorem ahom_eq (M : GMCModel d) (L : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M L =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom (toModel M) L := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.ahom _root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom
  apply congrArg sInf
  apply congrArg Set.range
  funext n
  unfold _root_.SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.abar
  congr 1
  rw [Matrix.trace]
  simp only [Matrix.diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.Homogenization.integral_matrix_apply
    (_root_.SubdiffusiveProcess.CoarseGrainingVocab.integrable_randomAMatrix (toModel M) L _) i i]
  congr 1
  funext omega
  exact cellEnergy_eq M L n omega i

open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.MarkovProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess.CoarseGrainingVocab.Resolvent
open scoped ZeroAtInfty
variable {α : Type*} [MeasurableSpace α]
def semigroupTo (P : SubMarkovKernelSemigroup α) : _root_.MarkovProcess.SubMarkovKernelSemigroup α :=
  ⟨P.kernel, P.measurable_kernel, P.kernel_zero, P.kernel_add, P.isSubMarkovKernel⟩
def semigroupFrom (P : _root_.MarkovProcess.SubMarkovKernelSemigroup α) : SubMarkovKernelSemigroup α :=
  ⟨P.kernel, P.measurable_kernel, P.kernel_zero, P.kernel_add, P.isSubMarkovKernel⟩
@[simp] theorem conservative_from (P : _root_.MarkovProcess.SubMarkovKernelSemigroup α) :
    (semigroupFrom P).IsConservative ↔ P.IsConservative := Iff.rfl
@[simp] theorem finiteTime_from (P : _root_.MarkovProcess.SubMarkovKernelSemigroup α)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    SubMarkovKernelSemigroup.finiteTimeKernel (semigroupFrom P) times =
      _root_.MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P times := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [SubMarkovKernelSemigroup.finiteTimeKernel,
        _root_.MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel]
      rw [ih]
      rfl
@[simp] theorem finiteSet_from (P : _root_.MarkovProcess.SubMarkovKernelSemigroup α)
    (I : Finset NNReal) :
    SubMarkovKernelSemigroup.finiteSetKernel (semigroupFrom P) I =
      _root_.MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P I := by
  unfold SubMarkovKernelSemigroup.finiteSetKernel
    _root_.MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
  rw [finiteTime_from]
  rfl
variable {E : Type*} [TopologicalSpace E]
def resolventFrom (D : _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum E) :
    C0ResolventDatum E :=
  ⟨D.solution, D.solution_add, D.solution_smul, D.solution_nonneg,
    D.norm_solution_le, D.solution_sub_solution⟩
@[simp] theorem operator_from
    (D : _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum E)
    (mu : MarkovProcess.Semigroup.PositiveShift) :
    (resolventFrom D).operator mu = D.operator mu := rfl
@[simp] theorem massive_iff (c rho : (Fin d → ℝ) → ℝ) (mu : ℝ)
    (u : Homogenization.H1Function U) (f : (Fin d → ℝ) → ℝ) :
    IsMassiveWeakSolutionOn c rho mu U u f ↔
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
        c rho mu U (h1To u) f := by
  constructor
  · intro h phi; exact h (h10From phi)
  · intro h phi; exact h (h10To phi)
theorem convexDomain_iff (W : Set (Fin d → ℝ)) :
    Homogenization.IsOpenBoundedConvexDomain W ↔ _root_.Homogenization.IsOpenBoundedConvexDomain W := by
  unfold Homogenization.IsOpenBoundedConvexDomain _root_.Homogenization.IsOpenBoundedConvexDomain
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, _root_.Homogenization.Bornology.IsBounded.isBoundedDomain h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, _root_.Homogenization.IsBoundedDomain.isBounded h2, h3⟩
@[simp] theorem weakResolvent_from (c rho : (Fin d → ℝ) → ℝ)
    (D : _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Fin d → ℝ)) :
    IsWeakEllipticResolvent c rho (resolventFrom D) ↔
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent c rho D := by
  constructor
  · intro h mu f W hW
    obtain ⟨u, hu, hmassive⟩ := h mu f W ((convexDomain_iff W).mpr hW)
    exact ⟨h1To u, hu, (massive_iff c rho mu u f).mp hmassive⟩
  · intro h mu f W hW
    obtain ⟨u, hu, hmassive⟩ := h mu f W ((convexDomain_iff W).mp hW)
    exact ⟨h1From u, hu, (massive_iff c rho mu (h1From u) f).mpr (by simpa using hmassive)⟩
@[simp] theorem coefficient_eq (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    cutoffCoefficient M H omega N = _root_.SubdiffusiveProcess.cutoffCoefficient (toModel M) H omega N := by
  unfold cutoffCoefficient _root_.SubdiffusiveProcess.cutoffCoefficient
  rw [ahom_eq]
  rfl
@[simp] theorem speed_eq (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedDensity M H omega N = _root_.SubdiffusiveProcess.cutoffSpeedDensity (toModel M) H omega N := rfl
@[simp] theorem speedMeasure_eq (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedMeasure M H omega N = _root_.SubdiffusiveProcess.cutoffSpeedMeasure (toModel M) H omega N := rfl
@[simp] theorem chaos_eq (M : GMCModel d) (omega : BilateralField d) (N : ℕ) :
    chaosCutoff M N omega = _root_.SubdiffusiveProcess.chaosCutoff (toModel M) N omega := rfl
@[simp] theorem strongMarkov_iff [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : ProbabilityTheory.Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) : HasStrongMarkovRestart K omega ↔
      _root_.SubdiffusiveProcess.HasStrongMarkovRestart K omega := Iff.rfl
@[simp] theorem symmetric_from (P : _root_.MarkovProcess.SubMarkovKernelSemigroup (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d)) : SemigroupSymmetric (semigroupFrom P) mu ↔
      _root_.SubdiffusiveProcess.SemigroupSymmetric P mu := Iff.rfl

@[simp] theorem physicalTime_eq (M : GMCModel d) (N : ℕ) :
    physicalTimeFactor M N = _root_.SubdiffusiveProcess.physicalTimeFactor (toModel M) N := by
  unfold physicalTimeFactor _root_.SubdiffusiveProcess.physicalTimeFactor
  rw [ahom_eq, ahom_eq]
  exact Real.toNNReal_of_nonneg _
@[simp] theorem physicalPath_eq (M : GMCModel d) (N : ℕ) :
    physicalRescaledPath M N = _root_.SubdiffusiveProcess.physicalRescaledPath (toModel M) N := by
  unfold physicalRescaledPath _root_.SubdiffusiveProcess.physicalRescaledPath
  funext path
  congr 2
  ext t
  exact congrArg (fun a : NNReal => ((a * t : NNReal) : ℝ)) (physicalTime_eq M N)
@[simp] theorem finsetEvaluation_eq (I : Finset NNReal) :
    ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I =
      _root_.MarkovProcess.ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I := rfl
@[simp] theorem locally_iff (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d)) :
    MeasuresConvergeLocally muN mu ↔ _root_.SubdiffusiveProcess.MeasuresConvergeLocally muN mu := Iff.rfl
@[simp] theorem commonLaw_eq [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (nu : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) :
    commonScaleLaw d nu = _root_.SubdiffusiveProcess.commonScaleLaw d nu := rfl
@[simp] theorem zeroLaw_eq (M : GMCModel d) :
    zeroPotentialLaw M.P = _root_.SubdiffusiveProcess.Model.zeroPotentialLaw (toModel M).P := rfl


end Conversion
end SubdiffusiveProcessAudit.ProcessConvergence

namespace SubdiffusiveProcessAudit.ProcessConvergence
open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.MarkovProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
/-- **Theorem A** (`t.A`). `δ₀` depends only on `d`; `C`, `η` and the processes are chosen after
the model, in the order: the infrared field `H`, the cutoff semigroups `PN`, the limit semigroup
`P`, the cutoff path laws `KN` and the limit path law `K`. The clauses are, in order: Feller
continuity of `K`;
the cutoff resolvent identification, the finite-dimensional distributions of `KN`, `K` and the
strong Markov property of `K` (almost surely in the environment); then (i) `AnnealedConvergence`,
(ii) and (iv) `SingularReversibleMarginals`, (iii) `AnomalousScaling`. -/
theorem theoremA (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ,
      0 < delta0 ∧
        ∀ (M : SubdiffusiveProcess.Model.GMCModel d),
          0 < M.delta →
            M.delta ≤ delta0 →
              let forget :
                C(SubdiffusiveProcess.Model.PotentialField d,
                  C(SpatialCoordinates d, ℝ)) :=
                ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
              let nu := (SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map forget
              let law := (commonScaleLaw d nu).toMeasure
              ∃ C eta : ℝ,
                0 < eta ∧
                  (d = 2 → eta = SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
                    ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ),
                      Measurable H ∧
                        ∃ PN :
                          ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
                          ∃ _hPN : ∀ N omega, (PN N omega).IsConservative,
                            ∃ P :
                              BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
                              ∃ _hP : ∀ omega, (P omega).IsConservative,
                                ∃ KN :
                                  ℕ →
                                    Kernel (BilateralField d × SpatialCoordinates d)
                                      (DiffusionPath d),
                                  ∃ _hKN : ∀ N, IsMarkovKernel (KN N),
                                    ∃ K :
                                      Kernel (BilateralField d × SpatialCoordinates d)
                                        (DiffusionPath d),
                                      ∃ hK : IsMarkovKernel K,
                                        (∀ omega : BilateralField d,
                                            Continuous
                                              (fun x ↦ jointPathProbabilityMeasure K hK omega x)) ∧
                                          (∀ᵐ omega ∂law,
                                              Tendsto (infraredPartialSum omega) atTop
                                                  (nhds (H omega)) ∧
                                                (∀ N, IsCutoffResolvent M H omega N PN) ∧
                                                  (∀ N I x,
                                                      (KN N).map (ContinuousPath.finsetEvaluation I)
                                                          (omega, x) =
                                                        SubMarkovKernelSemigroup.finiteSetKernel
                                                          (PN N omega) I x) ∧
                                                    (∀ I x,
                                                        K.map (ContinuousPath.finsetEvaluation I)
                                                            (omega, x) =
                                                          SubMarkovKernelSemigroup.finiteSetKernel
                                                            (P omega) I x) ∧
                                                      HasStrongMarkovRestart K omega) ∧
                                            AnnealedConvergence M law KN K ∧
                                              SingularReversibleMarginals M H law P K ∧
                                                AnomalousScaling C eta law K :=
  by
  obtain ⟨delta0, hdelta0, hmain⟩ := _root_.SubdiffusiveProcess.process_convergence d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hpos hsmall
  obtain ⟨C, eta, heta, heta2, H, hH, PN, hPN, P, hP, KN, hKN, K, hK, hrest⟩ :=
    hmain (Conversion.toModel M) hpos hsmall
  refine ⟨C, eta, heta, heta2, H, hH,
    fun N omega => Conversion.semigroupFrom (PN N omega), hPN,
    fun omega => Conversion.semigroupFrom (P omega), hP, KN, hKN, K, hK, ?_⟩
  obtain ⟨hcont, hae, hann, hlim, hexit, hfinal⟩ := hrest
  refine ⟨hcont, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hae] with omega homega
    obtain ⟨hinfra, hD, hKNfinite, hKfinite, hstrong⟩ := homega
    refine ⟨hinfra, ?_, ?_, ?_, hstrong⟩
    · intro N
      obtain ⟨D, hdense, hweak, hrep⟩ := hD N
      refine ⟨Conversion.resolventFrom D, hdense, ?_, hrep⟩
      rw [Conversion.coefficient_eq, Conversion.speed_eq, Conversion.weakResolvent_from]
      exact hweak
    · simpa only [Conversion.finiteSet_from, Conversion.finsetEvaluation_eq] using hKNfinite
    · simpa only [Conversion.finiteSet_from, Conversion.finsetEvaluation_eq] using hKfinite
  · unfold AnnealedConvergence
    simp only [Conversion.physicalPath_eq, Conversion.commonLaw_eq, Conversion.zeroLaw_eq]
    exact hann
  · unfold SingularReversibleMarginals
    simp only [Conversion.chaos_eq, Conversion.speedMeasure_eq, Conversion.locally_iff,
      Conversion.symmetric_from, Conversion.commonLaw_eq, Conversion.zeroLaw_eq]
    exact hlim
  · unfold AnomalousScaling
    simp only [Conversion.commonLaw_eq, Conversion.zeroLaw_eq]
    exact ⟨hexit, hfinal⟩
end SubdiffusiveProcessAudit.ProcessConvergence
