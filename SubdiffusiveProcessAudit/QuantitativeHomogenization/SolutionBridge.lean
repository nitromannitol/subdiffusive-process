module
public import SubdiffusiveProcessAudit.QuantitativeHomogenization.SolutionBasic
public import SubdiffusiveProcess.Paper.t_B
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
@[expose] public section
/-! Explicit transport of the probabilistic, variational and Sobolev vocabulary. -/
noncomputable section
namespace SubdiffusiveProcessAudit.QuantitativeHomogenization
open MeasureTheory
namespace Conversion
variable {d : ℕ} {U : Set (Fin d → ℝ)}
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.SubdiffusiveProcess.Model
theorem localSigma_eq (W : Set (Homogenization.Vec d)) :
    PotentialField.localSigma W = _root_.SubdiffusiveProcess.Model.PotentialField.localSigma W := by
  unfold PotentialField.localSigma _root_.SubdiffusiveProcess.Model.PotentialField.localSigma
    Homogenization.LocalSigmaR _root_.Homogenization.LocalSigmaR
  rw [MeasurableSpace.comap_generateFrom, MeasurableSpace.comap_generateFrom]
  congr 1
  ext s
  constructor
  · rintro ⟨t, ⟨i, j, phi, hphi, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨_root_.Homogenization.entryTestR i j phi ⁻¹' r,
      ⟨i, j, phi, ⟨hphi.measurable, hphi.bounded, hphi.hasCompactSupport⟩, hsupp, r, hr, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨i, j, phi, hphi, hsupp, r, hr, rfl⟩, rfl⟩
    exact ⟨Homogenization.entryTestR i j phi ⁻¹' r,
      ⟨i, j, phi, ⟨hphi.measurable, hphi.bounded, hphi.hasCompactSupport⟩, hsupp, r, hr, rfl⟩, rfl⟩
def toModel (M : GMCModel d) : _root_.SubdiffusiveProcess.Model.GMCModel d where
  delta := M.delta
  P := M.P
  shellPrefix := ⟨M.shellPrefix.dimension, M.shellPrefix.delta_pos,
    M.shellPrefix.delta_le_half, M.shellPrefix.independent, M.shellPrefix.marginal_scaling⟩
  G1 := ⟨M.G1.integrable, M.G1.mean_zero, M.G1.stationary, by
    intro W V hW hV hWV
    rw [← localSigma_eq W, ← localSigma_eq V]
    exact M.G1.range_dependence W V hW hV hWV⟩
  G2 := ⟨M.G2.regularity_expectation⟩
  G3 := ⟨M.G3.signed_coordinate_permutations, M.G3.negation⟩
  G4 := ⟨M.G4.exponential_integrable, M.G4.tauSq_pos⟩
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

def cubeTo (Q : Homogenization.TriadicCube d) : _root_.Homogenization.TriadicCube d := ⟨Q.scale, Q.index⟩

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

theorem rescaled_eq (M : GMCModel d) (L N : ℕ) (omega : PotentialSample d) :
    SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient (toModel M) L N omega := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient
  rw [ahom_eq]
  rfl
def h1Equiv : Homogenization.H1Function U ≃ _root_.Homogenization.H1Function U :=
  ⟨h1To, h1From, h1From_to, h1To_from⟩
theorem forall_h1 (p : _root_.Homogenization.H1Function U → Prop) :
    (∀ u, p u) ↔ ∀ u, p (h1To u) := h1Equiv.symm.forall_congr_left
theorem exists_h1 (p : _root_.Homogenization.H1Function U → Prop) :
    (∃ u, p u) ↔ ∃ u, p (h1To u) := h1Equiv.symm.exists_congr_left

open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.SubdiffusiveProcess.CoarseGrainingVocab
theorem scalar_rhs_iff (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (u : Homogenization.H1Function U) (f : (Fin d → ℝ) → ℝ) :
    IsScalarRhsWeakSolutionOn a U u f ↔
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarRhsWeakSolutionOn a U (h1To u) f := by
  constructor
  · intro h phi; exact h (h10From phi)
  · intro h phi; exact h (h10To phi)
theorem zeroTrace_iff (u h : Homogenization.H1Function U) :
    HasZeroTraceDifferenceOn U u h ↔
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn U (h1To u) (h1To h) := by
  constructor
  · rintro ⟨w, hw, hgrad⟩; exact ⟨h10To w, hw, hgrad⟩
  · rintro ⟨w, hw, hgrad⟩; exact ⟨h10From w, hw, hgrad⟩
theorem dirichlet_iff (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (Q : Homogenization.TriadicCube d) (u h : Homogenization.H1Function (Homogenization.openCubeSet Q))
    (f : (Fin d → ℝ) → ℝ) :
    IsScalarDirichletSolutionOn a Q u h f ↔
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn a (cubeTo Q) (h1To u) (h1To h) f :=
  and_congr (zeroTrace_iff u h) (scalar_rhs_iff a u f)
def h2To {Q : Homogenization.TriadicCube d} (h : H2Datum Q) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum (cubeTo Q) :=
  ⟨h1To h.toH1, ⟨h.weakHessian.hess, h.weakHessian.hess_memL2, h.weakHessian.weak_second⟩⟩
def h2From {Q : Homogenization.TriadicCube d}
    (h : _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum (cubeTo Q)) : H2Datum Q :=
  ⟨h1From h.toH1, ⟨h.weakHessian.hess, h.weakHessian.hess_memL2, h.weakHessian.weak_second⟩⟩
def h2Equiv (Q : Homogenization.TriadicCube d) :
    H2Datum Q ≃ _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum (cubeTo Q) :=
  ⟨h2To, h2From, fun h => by cases h; rfl, fun h => by cases h; rfl⟩
theorem forall_h2 (p : _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum
    (_root_.Homogenization.originCube d 0) → Prop) :
    (∀ h, p h) ↔ ∀ h : H2Datum (Homogenization.originCube d 0), p (h2To h) :=
  (h2Equiv (Homogenization.originCube d 0)).symm.forall_congr_left
def l2To {Q : Homogenization.TriadicCube d} (F : L2VectorField Q) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField (cubeTo Q) := ⟨F.toFun, F.memLpCoord⟩
def l2From {Q : Homogenization.TriadicCube d}
    (F : _root_.SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField (cubeTo Q)) : L2VectorField Q := ⟨F.toFun, F.memLpCoord⟩
def l2Equiv (Q : Homogenization.TriadicCube d) :
    L2VectorField Q ≃ _root_.SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField (cubeTo Q) :=
  ⟨l2To, l2From, fun F => by cases F; rfl, fun F => by cases F; rfl⟩
theorem exists_l2 (p : _root_.SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField
    (_root_.Homogenization.originCube d 0) → Prop) :
    (∃ F, p F) ↔ ∃ F : L2VectorField (Homogenization.originCube d 0), p (l2To F) :=
  (l2Equiv (Homogenization.originCube d 0)).symm.exists_congr_left
theorem h2_norm {Q : Homogenization.TriadicCube d} (h : H2Datum Q) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum.norm (h2To h) = h.norm := rfl
theorem hminus_eq [NeZero d] {Q : Homogenization.TriadicCube d} (F : L2VectorField Q) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (cubeTo Q) (l2To F) =
      ordinaryVectorHMinusOne Q F := rfl
theorem dirichlet_zero_iff (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (u h : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d 0)))
    (f : (Fin d → ℝ) → ℝ) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn a
        (_root_.Homogenization.originCube d 0) (h1To u) (h1To h) f ↔
      IsScalarDirichletSolutionOn a (Homogenization.originCube d 0) u h f :=
  (dirichlet_iff a (Homogenization.originCube d 0) u h f).symm
theorem h2_norm_zero (h : H2Datum (Homogenization.originCube d 0)) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum.norm (h2To h) = h.norm := rfl
theorem hminus_zero_eq [NeZero d] (F : L2VectorField (Homogenization.originCube d 0)) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne
        (_root_.Homogenization.originCube d 0) (l2To F) =
      ordinaryVectorHMinusOne (Homogenization.originCube d 0) F := rfl
theorem l2_zero_eq (f : (Fin d → ℝ) → ℝ) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.l2Size (_root_.Homogenization.originCube d 0) f =
      l2Size (Homogenization.originCube d 0) f := rfl
theorem coefficientMeasurable_iff {Ω : Type*} (A : Ω → (Fin d → ℝ) → ℝ) (X : Ω → ℝ) :
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.CoefficientMeasurable A X ↔ CoefficientMeasurable A X := Iff.rfl
theorem cutoff_eq (M : GMCModel d) (L : ℕ) :
    _root_.SubdiffusiveProcess.Model.aCutoff (toModel M) L = aCutoff M L := rfl
theorem model_delta (M : GMCModel d) : (toModel M).delta = M.delta := rfl
theorem model_P (M : GMCModel d) : (toModel M).P = M.P := rfl
theorem h2_toH1_zero (h : H2Datum (Homogenization.originCube d 0)) :
    (h2To h).toH1 = h1To h.toH1 := rfl
theorem h1_toFun (u : Homogenization.H1Function U) : (h1To u).toFun = u.toFun := rfl
theorem h1_grad (u : Homogenization.H1Function U) : (h1To u).grad = u.grad := rfl
theorem l2_toFun {Q : Homogenization.TriadicCube d} (F : L2VectorField Q) : (l2To F).toFun = F.toFun := rfl
end Conversion
end SubdiffusiveProcessAudit.QuantitativeHomogenization

noncomputable section
namespace SubdiffusiveProcessAudit.QuantitativeHomogenization
open MeasureTheory
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.Homogenization
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
def DirichletConclusion {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) (h : H2Datum Q) (f : Vec d → ℝ) (flux : Vec d → Vec d → Vec d) (P : ℝ≥0∞ → ℝ≥0∞ → Prop) : Prop :=
  (∃ u : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u h.toH1 f) ∧
  (∀ u u' : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u h.toH1 f →
    IsScalarDirichletSolutionOn a Q u' h.toH1 f →
      u.toFun =ᵐ[volume.restrict (openCubeSet Q)] u'.toFun ∧
        u.grad =ᵐ[volume.restrict (openCubeSet Q)] u'.grad) ∧
  (∃ u : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn (fun _ => 1) Q u h.toH1 f) ∧
  (∀ u u' : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn (fun _ => 1) Q u h.toH1 f →
    IsScalarDirichletSolutionOn (fun _ => 1) Q u' h.toH1 f →
      u.toFun =ᵐ[volume.restrict (openCubeSet Q)] u'.toFun ∧
        u.grad =ᵐ[volume.restrict (openCubeSet Q)] u'.grad) ∧
  ∀ u v : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u h.toH1 f →
    IsScalarDirichletSolutionOn (fun _ => 1) Q v h.toH1 f →
      ∃ G F : L2VectorField Q,
        (∀ x, G.toFun x = u.grad x - v.grad x) ∧
        (∀ x, F.toFun x = flux x (u.grad x) - v.grad x) ∧
        P (l2Size Q (fun x => u.toFun x - v.toFun x) +
          ordinaryVectorHMinusOne Q G + ordinaryVectorHMinusOne Q F) h.norm
end SubdiffusiveProcessAudit.QuantitativeHomogenization
namespace QuantitativeHomogenizationRoot
open MeasureTheory _root_.Homogenization
open _root_.SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
def DirichletConclusion {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) (h : H2Datum Q) (f : Vec d → ℝ) (flux : Vec d → Vec d → Vec d) (P : ℝ≥0∞ → ℝ≥0∞ → Prop) : Prop :=
  (∃ u : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u h.toH1 f) ∧
  (∀ u u' : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u h.toH1 f →
    IsScalarDirichletSolutionOn a Q u' h.toH1 f →
      u.toFun =ᵐ[volume.restrict (openCubeSet Q)] u'.toFun ∧
        u.grad =ᵐ[volume.restrict (openCubeSet Q)] u'.grad) ∧
  (∃ u : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn (fun _ => 1) Q u h.toH1 f) ∧
  (∀ u u' : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn (fun _ => 1) Q u h.toH1 f →
    IsScalarDirichletSolutionOn (fun _ => 1) Q u' h.toH1 f →
      u.toFun =ᵐ[volume.restrict (openCubeSet Q)] u'.toFun ∧
        u.grad =ᵐ[volume.restrict (openCubeSet Q)] u'.grad) ∧
  ∀ u v : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u h.toH1 f →
    IsScalarDirichletSolutionOn (fun _ => 1) Q v h.toH1 f →
      ∃ G F : L2VectorField Q,
        (∀ x, G.toFun x = u.grad x - v.grad x) ∧
        (∀ x, F.toFun x = flux x (u.grad x) - v.grad x) ∧
        P (l2Size Q (fun x => u.toFun x - v.toFun x) +
          ordinaryVectorHMinusOne Q G + ordinaryVectorHMinusOne Q F) h.norm
end QuantitativeHomogenizationRoot
namespace SubdiffusiveProcessAudit.QuantitativeHomogenization.Conversion
open MeasureTheory
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.Homogenization
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
theorem transfer_dirichlet {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) (h : H2Datum Q) (f : Vec d → ℝ) (flux : Vec d → Vec d → Vec d) (P : ℝ≥0∞ → ℝ≥0∞ → Prop)
    (H : QuantitativeHomogenizationRoot.DirichletConclusion (cubeTo Q) a (h2To h) f flux P) :
    DirichletConclusion Q a h f flux P := by
  rcases H with ⟨hex, huniq, hhom, hhomuniq, hbound⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hex with ⟨u, hu⟩
    refine ⟨h1From u, ?_⟩
    apply (dirichlet_iff a Q (h1From u) h.toH1 f).mpr
    simpa only [h1To_from] using! hu
  · intro u u' hu hu'
    exact huniq (h1To u) (h1To u') ((dirichlet_iff a Q u h.toH1 f).mp hu)
      ((dirichlet_iff a Q u' h.toH1 f).mp hu')
  · rcases hhom with ⟨u, hu⟩
    refine ⟨h1From u, ?_⟩
    apply (dirichlet_iff (fun _ => 1) Q (h1From u) h.toH1 f).mpr
    simpa only [h1To_from] using! hu
  · intro u u' hu hu'
    exact hhomuniq (h1To u) (h1To u') ((dirichlet_iff (fun _ => 1) Q u h.toH1 f).mp hu)
      ((dirichlet_iff (fun _ => 1) Q u' h.toH1 f).mp hu')
  · intro u v hu hv
    rcases hbound (h1To u) (h1To v) ((dirichlet_iff a Q u h.toH1 f).mp hu)
      ((dirichlet_iff (fun _ => 1) Q v h.toH1 f).mp hv) with ⟨G, F, hG, hF, hP⟩
    refine ⟨l2From G, l2From F, hG, hF, ?_⟩
    have hGnorm := hminus_eq (l2From G)
    have hFnorm := hminus_eq (l2From F)
    simpa only [l2To, l2From, h2_norm, h1To, ← hGnorm, ← hFnorm] using! hP
end SubdiffusiveProcessAudit.QuantitativeHomogenization.Conversion

noncomputable section
namespace SubdiffusiveProcessAudit.QuantitativeHomogenization
open MeasureTheory _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.Homogenization
open scoped ENNReal
theorem transfer_B (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (hB :
(∀ vartheta q : ℝ, vartheta ∈ Set.Ioo (0 : ℝ) 1 → 1 ≤ q →
           ∃ delta0 C : ℝ, 0 < delta0 ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
             (M.delta ≤ delta0 →
             ∃ Z : ℕ → ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
               (∀ L N, L ≤ N →
                 _root_.SubdiffusiveProcess.CoarseGrainingVocab.CoefficientMeasurable
                   (fun omega ↦ _root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
               (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
               (∀ L N, L ≤ N →
                 eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C) ∧
               ∀ᵐ omega ∂M.P.toMeasure, ∀ L N : ℕ, L ≤ N →
                 ∀ (f : _root_.Homogenization.Vec d → ℝ),
                   MemLp f 2 (volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))) →
                 ∀ h : _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum (_root_.Homogenization.originCube d 0),
                   (∃ uLM : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                       (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                       (_root_.Homogenization.originCube d 0) uLM h.toH1 f) ∧
                   (∀ uLM uLM' : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                         (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                         (_root_.Homogenization.originCube d 0) uLM h.toH1 f →
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                         (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                         (_root_.Homogenization.originCube d 0) uLM' h.toH1 f →
                     uLM.toFun =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uLM'.toFun ∧
                       uLM.grad =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uLM'.grad) ∧
                   (∃ uHom : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                       (_root_.Homogenization.originCube d 0) uHom h.toH1 f) ∧
                   (∀ uHom uHom' : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (_root_.Homogenization.originCube d 0) uHom h.toH1 f →
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (_root_.Homogenization.originCube d 0) uHom' h.toH1 f →
                     uHom.toFun =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uHom'.toFun ∧
                       uHom.grad =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uHom'.grad) ∧
                   ∀ (uLM uHom : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))),
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                         (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                         (_root_.Homogenization.originCube d 0) uLM h.toH1 f →
                     _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (_root_.Homogenization.originCube d 0) uHom h.toH1 f →
                     ∃ gradDifference fluxDifference : _root_.SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField (_root_.Homogenization.originCube d 0),
                       (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                       (∀ x, fluxDifference.toFun x =
                         _root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.l2Size (_root_.Homogenization.originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                             _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (_root_.Homogenization.originCube d 0) gradDifference +
                           _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (_root_.Homogenization.originCube d 0) fluxDifference ≤
                         ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                           (_root_.SubdiffusiveProcess.CoarseGrainingVocab.l2Size (_root_.Homogenization.originCube d 0) f + h.norm) ∧
                         (f = 0 →
                         _root_.SubdiffusiveProcess.CoarseGrainingVocab.l2Size (_root_.Homogenization.originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (_root_.Homogenization.originCube d 0) gradDifference +
                             _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (_root_.Homogenization.originCube d 0) fluxDifference ≤
                           ENNReal.ofReal (Z L N omega * C * M.delta) * h.norm))) ∧
    (∃ alphaHom : ℝ, 0 < alphaHom ∧
           ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q → ∀ delta : ℝ,
             ∃ C : ℝ, 0 < C ∧
               ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta = delta →
               ∃ Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
               _root_.SubdiffusiveProcess.CoarseGrainingVocab.CoefficientMeasurable (_root_.SubdiffusiveProcess.Model.aCutoff M L) Y ∧
                 (∀ omega, 1 ≤ Y omega) ∧
                 eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
                 ∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
                   ∀ (f : _root_.Homogenization.Vec d → ℝ),
                     MemLp f 2 (volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))) →
                   ∀ h : _root_.SubdiffusiveProcess.CoarseGrainingVocab.H2Datum (_root_.Homogenization.originCube d 0),
                     (∃ uLM : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                         (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                         (_root_.Homogenization.originCube d 0) uLM h.toH1 f) ∧
                     (∀ uLM uLM' : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                           (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                           (_root_.Homogenization.originCube d 0) uLM h.toH1 f →
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                           (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                           (_root_.Homogenization.originCube d 0) uLM' h.toH1 f →
                       uLM.toFun =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uLM'.toFun ∧
                         uLM.grad =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uLM'.grad) ∧
                     (∃ uHom : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (_root_.Homogenization.originCube d 0) uHom h.toH1 f) ∧
                     (∀ uHom uHom' : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0)),
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (_root_.Homogenization.originCube d 0) uHom h.toH1 f →
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (_root_.Homogenization.originCube d 0) uHom' h.toH1 f →
                       uHom.toFun =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uHom'.toFun ∧
                         uHom.grad =ᵐ[volume.restrict (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))] uHom'.grad) ∧
                     ∀ (uLM uHom : _root_.Homogenization.H1Function (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d 0))),
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn
                           (_root_.SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (_root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega))
                           (_root_.Homogenization.originCube d 0) uLM h.toH1 f →
                       _root_.SubdiffusiveProcess.CoarseGrainingVocab.IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (_root_.Homogenization.originCube d 0) uHom h.toH1 f →
                       ∃ gradDifference fluxDifference : _root_.SubdiffusiveProcess.CoarseGrainingVocab.L2VectorField (_root_.Homogenization.originCube d 0),
                         (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                         (∀ x, fluxDifference.toFun x =
                           _root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                         _root_.SubdiffusiveProcess.CoarseGrainingVocab.l2Size (_root_.Homogenization.originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (_root_.Homogenization.originCube d 0) gradDifference +
                             _root_.SubdiffusiveProcess.CoarseGrainingVocab.ordinaryVectorHMinusOne (_root_.Homogenization.originCube d 0) fluxDifference ≤
                           ENNReal.ofReal
                               (Y omega * (3 : ℝ) ^ (-alphaHom * ((N : ℝ) - (L : ℝ)))) *
                             (_root_.SubdiffusiveProcess.CoarseGrainingVocab.l2Size (_root_.Homogenization.originCube d 0) f + h.norm))) :
(∀ vartheta q : ℝ, vartheta ∈ Set.Ioo (0 : ℝ) 1 → 1 ≤ q →
           ∃ delta0 C : ℝ, 0 < delta0 ∧ ∀ M : SubdiffusiveProcess.Model.GMCModel d,
             (M.delta ≤ delta0 →
             ∃ Z : ℕ → ℕ → SubdiffusiveProcess.Model.PotentialSample d → ℝ,
               (∀ L N, L ≤ N →
                 CoefficientMeasurable
                   (fun omega ↦ rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
               (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
               (∀ L N, L ≤ N →
                 eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C) ∧
               ∀ᵐ omega ∂M.P.toMeasure, ∀ L N : ℕ, L ≤ N →
                 ∀ (f : Homogenization.Vec d → ℝ),
                   MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
                 ∀ h : H2Datum (originCube d 0),
                   (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn
                       (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                       (originCube d 0) uLM h.toH1 f) ∧
                   (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM h.toH1 f →
                     IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM' h.toH1 f →
                     uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.toFun ∧
                       uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.grad) ∧
                   (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                       (originCube d 0) uHom h.toH1 f) ∧
                   (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom h.toH1 f →
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom' h.toH1 f →
                     uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.toFun ∧
                       uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.grad) ∧
                   ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                     IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM h.toH1 f →
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom h.toH1 f →
                     ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                       (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                       (∀ x, fluxDifference.toFun x =
                         rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                       l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                             ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                           ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                         ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                           (l2Size (originCube d 0) f + h.norm) ∧
                         (f = 0 →
                         l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                             ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                           ENNReal.ofReal (Z L N omega * C * M.delta) * h.norm))) ∧
    (∃ alphaHom : ℝ, 0 < alphaHom ∧
           ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q → ∀ delta : ℝ,
             ∃ C : ℝ, 0 < C ∧
               ∀ M : SubdiffusiveProcess.Model.GMCModel d, M.delta = delta →
               ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
               CoefficientMeasurable (SubdiffusiveProcess.Model.aCutoff M L) Y ∧
                 (∀ omega, 1 ≤ Y omega) ∧
                 eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
                 ∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
                   ∀ (f : Homogenization.Vec d → ℝ),
                     MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
                   ∀ h : H2Datum (originCube d 0),
                     (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM h.toH1 f) ∧
                     (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn
                           (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                           (originCube d 0) uLM h.toH1 f →
                       IsScalarDirichletSolutionOn
                           (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                           (originCube d 0) uLM' h.toH1 f →
                       uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.toFun ∧
                         uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.grad) ∧
                     (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom h.toH1 f) ∧
                     (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (originCube d 0) uHom h.toH1 f →
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (originCube d 0) uHom' h.toH1 f →
                       uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.toFun ∧
                         uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.grad) ∧
                     ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                       IsScalarDirichletSolutionOn
                           (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                           (originCube d 0) uLM h.toH1 f →
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (originCube d 0) uHom h.toH1 f →
                       ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                         (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                         (∀ x, fluxDifference.toFun x =
                           rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                         l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                             ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                           ENNReal.ofReal
                               (Y omega * (3 : ℝ) ^ (-alphaHom * ((N : ℝ) - (L : ℝ)))) *
                             (l2Size (originCube d 0) f + h.norm)) := by
  constructor
  · intro vartheta q hvartheta hq
    obtain ⟨delta0, C, hdelta0, hmodels⟩ := hB.1 vartheta q hvartheta hq
    refine ⟨delta0, C, hdelta0, ?_⟩
    intro M hdelta
    obtain ⟨Z, hcoef, hZ, hMoment, hAE⟩ := hmodels (Conversion.toModel M) hdelta
    refine ⟨Z, ?_, hZ, hMoment, ?_⟩
    · intro L N hLN
      have hc := hcoef L N hLN
      have heq : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          _root_.SubdiffusiveProcess.CoarseGrainingVocab.rescaledCutoffCoefficient (Conversion.toModel M) L N omega) =
          (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            rescaledCutoffCoefficient M L N omega) := by
        funext omega
        exact (Conversion.rescaled_eq M L N omega).symm
      rw [heq] at hc
      exact hc
    · filter_upwards [hAE] with omega ho
      intro L N hLN f hf h
      have hp := ho L N hLN f hf (Conversion.h2To h)
      erw [← Conversion.rescaled_eq M L N omega] at hp
      exact Conversion.transfer_dirichlet (originCube d 0)
        (scalarCoeffField (rescaledCutoffCoefficient M L N omega)) h f
        (fun x grad => rescaledCutoffCoefficient M L N omega x • grad)
        (fun T H => T ≤ ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) * (l2Size (originCube d 0) f + H) ∧
          (f = 0 → T ≤ ENNReal.ofReal (Z L N omega * C * M.delta) * H)) hp
  · obtain ⟨alphaHom, halphaHom, hmodels⟩ := hB.2
    refine ⟨alphaHom, halphaHom, ?_⟩
    intro L q hq delta
    obtain ⟨C, hC, hmodels'⟩ := hmodels L q hq delta
    refine ⟨C, hC, ?_⟩
    intro M hdelta
    obtain ⟨Y, hcoef, hY, hMoment, hAE⟩ := hmodels' (Conversion.toModel M) hdelta
    refine ⟨Y, hcoef, hY, hMoment, ?_⟩
    filter_upwards [hAE] with omega ho
    intro N hLN f hf h
    have hp := ho N hLN f hf (Conversion.h2To h)
    erw [← Conversion.rescaled_eq M L N omega] at hp
    exact Conversion.transfer_dirichlet (originCube d 0)
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega)) h f
      (fun x grad => rescaledCutoffCoefficient M L N omega x • grad)
      (fun T H => T ≤ ENNReal.ofReal (Y omega * (3 : ℝ) ^ (-alphaHom * ((N : ℝ) - (L : ℝ)))) *
        (l2Size (originCube d 0) f + H)) hp
end SubdiffusiveProcessAudit.QuantitativeHomogenization
