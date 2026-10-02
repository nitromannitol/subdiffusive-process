import SubdiffusiveProcessAudit.ProcessConvergence.SolutionBasic
import SubdiffusiveProcess.MainTheorems
noncomputable section
namespace SubdiffusiveProcessAudit.ProcessConvergence
open MeasureTheory
namespace Conversion
variable {d : ℕ} {U : Set (Fin d → ℝ)}
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess.Frozen.Assumptions
theorem localSigma_eq (W : Set (Homogenization.Vec d)) :
    PotentialField.localSigma W = _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma W := by
  unfold PotentialField.localSigma _root_.SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma
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
def toModel (M : GMCModel d) : _root_.SubdiffusiveProcess.Frozen.Assumptions.GMCModel d where
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

theorem potential_iff (f : (Fin d → ℝ) → (Fin d → ℝ)) :
    Homogenization.IsPotentialOn U f ↔ _root_.Homogenization.IsPotentialOn U f := by
  constructor
  · rintro ⟨u, hu⟩; exact ⟨h1To u, hu⟩
  · rintro ⟨u, hu⟩; exact ⟨h1From u, hu⟩
theorem solenoidal_iff (f : (Fin d → ℝ) → (Fin d → ℝ)) :
    Homogenization.IsSolenoidalOn U f ↔ _root_.Homogenization.IsSolenoidalOn U f := by
  constructor
  · intro h u; exact h (h10From u)
  · intro h u; exact h (h10To u)
theorem harmonic_iff (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) :
    Homogenization.IsAHarmonicGradient a U f ↔ _root_.Homogenization.IsAHarmonicGradient a U f :=
  and_congr (potential_iff f) (solenoidal_iff _)
def harmonicTo {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (u : Homogenization.AHarmonicFunction a U) : _root_.Homogenization.AHarmonicFunction a U :=
  ⟨h1To u.toH1, (harmonic_iff a u.toH1.grad).mp u.isHarmonic⟩
def harmonicFrom {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (u : _root_.Homogenization.AHarmonicFunction a U) : Homogenization.AHarmonicFunction a U :=
  ⟨h1From u.toH1, (harmonic_iff a u.toH1.grad).mpr u.isHarmonic⟩
def cubeTo (Q : Homogenization.TriadicCube d) : _root_.Homogenization.TriadicCube d := ⟨Q.scale, Q.index⟩
def domainTo (W : Homogenization.Book.Ch02.Domain d) : _root_.Homogenization.Book.Ch02.Domain d :=
  ⟨W.carrier, W.isDomain, W.nonempty⟩
def coeffTo {W : Homogenization.Book.Ch02.Domain d} (a : Homogenization.Book.Ch02.CoeffOn W) :
    _root_.Homogenization.Book.Ch02.CoeffOn (domainTo W) :=
  ⟨a.toCoeffField, a.lam, a.Lam, a.lam_pos, a.lam_le_Lam, a.aeStronglyMeasurable, a.aeElliptic⟩

theorem response_eq (W : Homogenization.Book.Ch02.Domain d)
    (a : Homogenization.Book.Ch02.CoeffOn W) (p q : Fin d → ℝ) :
    Homogenization.Book.Ch02.responseJ W a p q =
      _root_.Homogenization.Book.Ch02.responseJ (domainTo W) (coeffTo a) p q := by
  apply congrArg sSup
  ext m
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨harmonicTo u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨harmonicFrom u, hu⟩

theorem response_field_eq (W : _root_.Homogenization.Book.Ch02.Domain d)
    (a b : _root_.Homogenization.Book.Ch02.CoeffOn W)
    (h : a.toCoeffField = b.toCoeffField) (p q : Fin d → ℝ) :
    _root_.Homogenization.Book.Ch02.responseJ W a p q =
      _root_.Homogenization.Book.Ch02.responseJ W b p q := by
  cases a
  cases b
  cases h
  rfl

theorem coarse_eq_of_response (W : Homogenization.Book.Ch02.Domain d)
    (a : Homogenization.Book.Ch02.CoeffOn W)
    (b : _root_.Homogenization.Book.Ch02.CoeffOn (domainTo W))
    (h : ∀ p q, Homogenization.Book.Ch02.responseJ W a p q =
      _root_.Homogenization.Book.Ch02.responseJ (domainTo W) b p q) :
    Homogenization.Book.Ch02.aCoarse W a =
      _root_.Homogenization.Book.Ch02.aCoarse (domainTo W) b := by
  dsimp only [Homogenization.Book.Ch02.aCoarse, _root_.Homogenization.Book.Ch02.aCoarse,
    Homogenization.Book.Ch02.coarseMatrices, _root_.Homogenization.Book.Ch02.coarseMatrices,
    Homogenization.Book.Ch02.CoarseMatrices.coeff, _root_.Homogenization.Book.Ch02.CoarseMatrices.coeff,
    Homogenization.Book.Ch02.sigmaCoarse, _root_.Homogenization.Book.Ch02.sigmaCoarse,
    Homogenization.Book.Ch02.sigmaEntry, _root_.Homogenization.Book.Ch02.sigmaEntry,
    Homogenization.Book.Ch02.canonicalSigmaCorrectedResponse, _root_.Homogenization.Book.Ch02.canonicalSigmaCorrectedResponse,
    Homogenization.Book.Ch02.kappaCoarse, _root_.Homogenization.Book.Ch02.kappaCoarse,
    Homogenization.Book.Ch02.sigmaStarCoarse, _root_.Homogenization.Book.Ch02.sigmaStarCoarse,
    Homogenization.Book.Ch02.sigmaStarInvCoarse, _root_.Homogenization.Book.Ch02.sigmaStarInvCoarse,
    Homogenization.Book.Ch02.sigmaStarInvEntry, _root_.Homogenization.Book.Ch02.sigmaStarInvEntry,
    Homogenization.Book.Ch02.sigmaStarInvKappaCoarse, _root_.Homogenization.Book.Ch02.sigmaStarInvKappaCoarse,
    Homogenization.Book.Ch02.mixedResponse, _root_.Homogenization.Book.Ch02.mixedResponse]
  unfold Homogenization.Book.Ch02.sigmaCoarse _root_.Homogenization.Book.Ch02.sigmaCoarse
    Homogenization.Book.Ch02.sigmaEntry _root_.Homogenization.Book.Ch02.sigmaEntry
    Homogenization.Book.Ch02.canonicalSigmaCorrectedResponse _root_.Homogenization.Book.Ch02.canonicalSigmaCorrectedResponse
    Homogenization.Book.Ch02.kappaCoarse _root_.Homogenization.Book.Ch02.kappaCoarse
    Homogenization.Book.Ch02.sigmaStarCoarse _root_.Homogenization.Book.Ch02.sigmaStarCoarse
    Homogenization.Book.Ch02.sigmaStarInvCoarse _root_.Homogenization.Book.Ch02.sigmaStarInvCoarse
    Homogenization.Book.Ch02.sigmaStarInvEntry _root_.Homogenization.Book.Ch02.sigmaStarInvEntry
    Homogenization.Book.Ch02.sigmaStarInvKappaCoarse _root_.Homogenization.Book.Ch02.sigmaStarInvKappaCoarse
    Homogenization.Book.Ch02.mixedResponse _root_.Homogenization.Book.Ch02.mixedResponse
  simp only [h]
  rfl

theorem cutoff_coarse_eq (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (W : Homogenization.Book.Ch02.Domain d) :
    SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix M L W omega =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix (toModel M) L (domainTo W) omega := by
  apply coarse_eq_of_response
  intro p q
  rw [response_eq]
  apply response_field_eq
  rfl

theorem ahom_eq (M : GMCModel d) (L : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M L =
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.ahom (toModel M) L := by
  apply congrArg sInf
  apply congrArg Set.range
  funext n
  unfold SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout
  congr 2
  unfold SubdiffusiveProcess.CoarseGrainingVocab.abar _root_.SubdiffusiveProcess.CoarseGrainingVocab.abar
  congr 1
  funext omega
  exact cutoff_coarse_eq M L omega _

open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.MarkovProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
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
@[simp] theorem weakResolvent_from (c rho : (Fin d → ℝ) → ℝ)
    (D : _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Fin d → ℝ)) :
    IsWeakEllipticResolvent c rho (resolventFrom D) ↔
      _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent c rho D := by
  constructor
  · intro h mu f W hW
    obtain ⟨u, hu, hmassive⟩ := h mu f W hW
    exact ⟨h1To u, hu, (massive_iff c rho mu u f).mp hmassive⟩
  · intro h mu f W hW
    obtain ⟨u, hu, hmassive⟩ := h mu f W hW
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
@[simp] theorem brownian_iff (Q : Measure (DiffusionPath d)) :
    Paper.lim_brownian_law Q ↔ _root_.Paper.lim_brownian_law Q := Iff.rfl
@[simp] theorem strongMarkov_iff [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : ProbabilityTheory.Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) : HasStrongMarkovRestart K omega ↔
      _root_.SubdiffusiveProcess.HasStrongMarkovRestart K omega := Iff.rfl
@[simp] theorem exits_iff [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (K : ProbabilityTheory.Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) : HasFiniteMeanExits K omega ↔
      _root_.SubdiffusiveProcess.HasFiniteMeanExits K omega := Iff.rfl
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
    zeroPotentialLaw M.P = _root_.SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw (toModel M).P := rfl

end Conversion
end SubdiffusiveProcessAudit.ProcessConvergence

namespace SubdiffusiveProcessAudit.ProcessConvergence
open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.MarkovProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.SubdiffusiveProcess
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Paper
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
theorem theoremA
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)  :
∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 1 ≤ C ∧ 0 < eta ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hKN : ∀ N, IsMarkovKernel (KN N),
        ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hK : IsMarkovKernel K,
          (∀ omega : BilateralField d,
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) ∧
          (∀ᵐ omega ∂law,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NoAtoms mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          (∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law))) ∧
          -- (ii) the limiting measures `M = lim M_N` and `μ = e^H M`, reversibility's invariance
          (∃ Mlim : BilateralField d → Measure (SpatialCoordinates d), Measurable Mlim ∧
            (∀ᵐ omega ∂law,
              let mu := (Mlim omega).withDensity
                (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))
              MeasuresConvergeLocally (fun N ↦ chaosCutoff M N omega) (Mlim omega) ∧
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure (Mlim omega) ∧ NoAtoms (Mlim omega) ∧
              (Mlim omega).IsOpenPosMeasure ∧ Mlim omega ⟂ₘ volume ∧
              IsLocallyFiniteMeasure mu ∧ NoAtoms mu ∧ mu.IsOpenPosMeasure ∧ mu ⟂ₘ volume ∧
              (∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
                ∫⁻ x, (∫⁻ w, f (w t) ∂(K (omega, x))) ∂mu = ∫⁻ x, f x ∂mu) ∧
              -- (iv) positive-time transition laws: absolutely continuous, non-Gaussian
              ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
                (K (omega, x)).map (fun w : DiffusionPath d ↦ w t) ≪ mu ∧
                ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d ↦ w t))) ∧
            (¬ ∃ m : Measure (SpatialCoordinates d), ∀ᵐ omega ∂law, Mlim omega = m) ∧
            (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
              ∫⁻ omega, Mlim omega A ∂law = volume A) ∧
            ∀ y : SpatialCoordinates d,
              law.map (fun omega ↦ (Mlim omega).map (fun z ↦ z + y)) = law.map Mlim) ∧
          -- (iii) annealed small-cube exits, Brownian singularity, pointwise Hölder bound
          (∀ (x : SpatialCoordinates d) (k : ℕ),
            ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
                (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K (omega, x))) ∂law ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
          ∀ x : SpatialCoordinates d, ∀ᵐ omega ∂law,
            (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega, x) ⟂ₘ Q) ∧
            (∀ (Θ : Type) [MeasurableSpace Θ] (nu' : Measure Θ) [IsProbabilityMeasure nu']
                (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
              K (omega, x) ⟂ₘ nu'.bind kappa) ∧
            ∀ᵐ w ∂(K (omega, x)), ∀ gamma : ℝ, 0 ≤ gamma →
              (fun t : ℝ≥0 ↦ ‖w t - w 0‖) =O[𝓝[>] 0] (fun t : ℝ≥0 ↦ (t : ℝ) ^ gamma) →
              gamma ≤ 1 / (2 + eta) := by
  obtain ⟨delta0, hdelta0, hmain⟩ := _root_.SubdiffusiveProcess.process_convergence d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hpos hsmall
  obtain ⟨C, eta, hC, heta, heta2, hdecay, H, hH, PN, hPN, P, hP, KN, hKN, K, hK, hrest⟩ :=
    hmain (Conversion.toModel M) hpos hsmall
  refine ⟨C, eta, hC, heta, heta2, ?_, H, hH,
    fun N omega => Conversion.semigroupFrom (PN N omega), hPN,
    fun omega => Conversion.semigroupFrom (P omega), hP, KN, hKN, K, hK, ?_⟩
  · simpa only [Conversion.ahom_eq] using hdecay
  · obtain ⟨hcont, hae, hann, hlim, hexit, hfinal⟩ := hrest
    refine ⟨hcont, ?_, ?_, ?_, hexit, ?_⟩
    · filter_upwards [hae] with omega homega
      obtain ⟨hinfra, hD, hKNfinite, hKfinite, hcontomega, hcompact, hfeller, hmu, hstrong, hexits⟩ := homega
      refine ⟨hinfra, ?_, ?_, ?_, hcontomega, hcompact, hfeller, ?_, hstrong, hexits⟩
      · intro N
        obtain ⟨D, hdense, hweak, hrep⟩ := hD N
        refine ⟨Conversion.resolventFrom D, hdense, ?_, hrep⟩
        rw [Conversion.coefficient_eq, Conversion.speed_eq, Conversion.weakResolvent_from]
        exact hweak
      · simpa only [Conversion.finiteSet_from, Conversion.finsetEvaluation_eq] using hKNfinite
      · simpa only [Conversion.finiteSet_from, Conversion.finsetEvaluation_eq] using hKfinite
      · obtain ⟨mu, hconv, hfinite, hno, hopen, hsym⟩ := hmu
        refine ⟨mu, ?_, hfinite, hno, hopen, hsym⟩
        simpa only [Conversion.speedMeasure_eq, Conversion.locally_iff, Conversion.commonLaw_eq, Conversion.zeroLaw_eq] using hconv
    · simp only [Conversion.physicalPath_eq, Conversion.commonLaw_eq, Conversion.zeroLaw_eq]
      exact hann
    · simp only [Conversion.chaos_eq, Conversion.speedMeasure_eq, Conversion.locally_iff, Conversion.commonLaw_eq, Conversion.zeroLaw_eq]
      exact hlim
    · simp only [Conversion.brownian_iff, Conversion.commonLaw_eq, Conversion.zeroLaw_eq]
      exact hfinal
end SubdiffusiveProcessAudit.ProcessConvergence
