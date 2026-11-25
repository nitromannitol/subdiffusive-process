module

public import SubdiffusiveProcess.SDE.FiniteDimensional
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_path_kernel
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

/-!
# The cutoff diffusions solve the stochastic differential equation

The cutoff semigroup `P_N^ω` of `finiteDimensional_cutoff_path_kernel` has the weak elliptic
resolvent of `ρ⁻¹ ∇·(c ∇)` with `c = κ ρ`, `ρ = e^{V}`, `κ = 1 / ā_N` and
`V = ψ_N^ω − (N + 1) τ²`, where `ψ_N^ω` is the cutoff potential. By interior elliptic regularity its
resolvent is a bounded `C²` solution of `μ u − κ (Δu + ∇V·∇u) = h`
(`hasClassicalResolvent_of_weakEllipticResolvent`), which is the generator
`(σ²/2) Δ + b·∇` with `σ = √(2κ)` and `b = κ ∇ψ_N^ω`. Hence, almost surely, for every `N` and every
`x`, the stochastic differential equation `dX = κ ∇ψ_N^ω(X) dt + √(2κ) dW` has a strong solution
started at `x` on every filtered probability space carrying a Brownian motion and satisfying the usual
condition on null sets, and the law of every such solution is the cutoff path law `K_N(ω, x)`
(`cutoff_solution_law`, and with the path kernels of `finiteDimensional_cutoff_path_kernel`,
`finiteDimensional_cutoff_path_kernel_solutionLaw`).

The three facts used from the literature are the cited inputs of `SubdiffusiveProcess.SDE.Inputs`:
strong existence for a locally Lipschitz drift of linear growth, Itô's formula at the exit time of a
ball, and interior elliptic regularity.
-/

@[expose] public section

noncomputable section

namespace SubdiffusiveProcess.SDE

open MeasureTheory ProbabilityTheory Filter Set Real MarkovProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped NNReal ENNReal Topology ContDiff ZeroAtInfty

variable {d : ℕ}

universe u

/-- A smooth compactly supported function as an element of `C₀`. -/
def toC0 (h : Vec d → ℝ) (hh : Continuous h) (hhc : HasCompactSupport h) : C₀(Vec d, ℝ) :=
  compactSupportToC0 (toCompactSupportMap h hh hhc)

theorem toC0_apply (h : Vec d → ℝ) (hh : Continuous h) (hhc : HasCompactSupport h) (x : Vec d) :
    toC0 h hh hhc x = h x := rfl

theorem abs_apply_le_norm (f : C₀(Vec d, ℝ)) (x : Vec d) : |f x| ≤ ‖f‖ := by
  have h := BoundedContinuousFunction.norm_coe_le_norm f.toBCF x
  rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, Real.norm_eq_abs] at h

/-- **The classical resolvent from the weak one.** -/
theorem hasClassicalResolvent_of_weakEllipticResolvent (hI3 : InteriorEllipticRegularity d)
    {V : Vec d → ℝ} (hV : ContDiff ℝ 1 V) (hVl : LocallyLipschitz (fderiv ℝ V)) {κ : ℝ}
    (hκ : 0 < κ) {Q : SubMarkovKernelSemigroup (Vec d)} {D : C0ResolventDatum (Vec d)}
    (hweak : IsWeakEllipticResolvent (fun x => κ * Real.exp (V x)) (fun x => Real.exp (V x)) D)
    (hLap : ∀ (mu : Semigroup.PositiveShift) (f : C₀(Vec d, ℝ)) (x : Vec d),
      D.solution mu f x =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) * kernelIntegral (Q (Real.toNNReal t)) f x) :
    HasClassicalResolvent Q (Real.sqrt (2 * κ))
      (fun x => κ • Homogenization.euclideanGradient V x) := by
  intro n h hh hhc
  let mu : Semigroup.PositiveShift := ⟨(n : ℝ) + 1, Set.mem_Ioi.mpr (by positivity)⟩
  let f : C₀(Vec d, ℝ) := toC0 h hh.continuous hhc
  obtain ⟨hu2, hueq⟩ := hI3 V hV hVl κ ((n : ℝ) + 1) hκ (by positivity) h hh hhc
    (D.solution mu f) (D.solution mu f).continuous fun W hW => hweak mu f W hW
  refine ⟨D.solution mu f, hu2, ⟨‖D.solution mu f‖, abs_apply_le_norm _⟩, fun x => ?_,
    fun x => hLap mu f x⟩
  have hσ : Real.sqrt (2 * κ) ^ 2 / 2 = κ := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hs : ∑ i, (κ • Homogenization.euclideanGradient V x) i * partialDeriv i (D.solution mu f) x =
      κ * ∑ i, partialDeriv i V x * partialDeriv i (D.solution mu f) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show κ * partialDeriv i V x * _ = _
    ring
  rw [← hueq x, spaceGenerator, hσ, hs]
  ring

/-- Time continuity of a Feller semigroup tested against a continuous compactly supported
function. -/
theorem continuous_integral_of_isFeller {Q : SubMarkovKernelSemigroup (Vec d)}
    (hQ : Q.IsFellerKernelSemigroup) (h : Vec d → ℝ) (hh : Continuous h)
    (hhc : HasCompactSupport h) (y : Vec d) :
    Continuous fun t : ℝ≥0 => ∫ z, h z ∂(Q t y) := by
  have horb := hQ.hasContinuousC0Orbits (toC0 h hh hhc)
  have heq : (fun t : ℝ≥0 => ∫ z, h z ∂(Q t y)) =
      fun t => (Q.c0Operator hQ.mapsC0 t (toC0 h hh hhc)) y := by
    funext t
    rfl
  rw [heq]
  have h1 : Continuous fun t : ℝ≥0 =>
      (ZeroAtInftyContinuousMap.toBCF (Q.c0Operator hQ.mapsC0 t (toC0 h hh hhc))) y :=
    (continuous_eval_const (F := BoundedContinuousFunction (Vec d) ℝ) y).comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp horb)
  exact h1

/-- The evaluation of a linear form at the coordinate vectors, scaled by `κ`. -/
def gradientMap (κ : ℝ) : (Vec d →L[ℝ] ℝ) →L[ℝ] Vec d :=
  κ • ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℝ ℝ (Homogenization.basisVec i)

theorem smul_euclideanGradient_eq {V : Vec d → ℝ} {V' : Vec d → (Vec d →L[ℝ] ℝ)}
    (hV : ∀ x, HasFDerivAt V (V' x) x) (κ : ℝ) (x : Vec d) :
    κ • Homogenization.euclideanGradient V x = gradientMap κ (V' x) := by
  funext i
  simp only [Homogenization.euclideanGradient, Homogenization.euclideanCoordDeriv, gradientMap,
    (hV x).fderiv, Pi.smul_apply, smul_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.apply_apply]

/-- A derivative field that is Lipschitz on compact sets is locally Lipschitz. -/
theorem locallyLipschitz_of_lipschitzOnWith_compact {V' : Vec d → (Vec d →L[ℝ] ℝ)}
    (hV' : ∀ K : Set (Vec d), IsCompact K → ∃ C : ℝ≥0, LipschitzOnWith C V' K) :
    LocallyLipschitz V' := by
  intro x
  obtain ⟨C, hC⟩ := hV' (Metric.closedBall x 1) (isCompact_closedBall x 1)
  exact ⟨C, Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, hC⟩

/-- **Regularity of a potential with a compact-set Lipschitz derivative.** -/
theorem potential_regularity {V : Vec d → ℝ} {V' : Vec d → (Vec d →L[ℝ] ℝ)} (hV'c : Continuous V')
    (hV : ∀ x, HasFDerivAt V (V' x) x)
    (hV' : ∀ K : Set (Vec d), IsCompact K → ∃ C : ℝ≥0, LipschitzOnWith C V' K) (c κ : ℝ) :
    ContDiff ℝ 1 (fun x => V x - c) ∧ LocallyLipschitz (fderiv ℝ fun x => V x - c) ∧
      LocallyLipschitz (fun x => κ • Homogenization.euclideanGradient V x) ∧
      (fun x => κ • Homogenization.euclideanGradient (fun y => V y - c) x) =
        fun x => κ • Homogenization.euclideanGradient V x := by
  have hVc : ∀ x, HasFDerivAt (fun y => V y - c) (V' x) x := fun x => (hV x).sub_const c
  have hfd : fderiv ℝ (fun y => V y - c) = V' := funext fun x => (hVc x).fderiv
  have hll := locallyLipschitz_of_lipschitzOnWith_compact hV'
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun x => (hVc x).differentiableAt, by rw [hfd]; exact hV'c⟩,
    by rw [hfd]; exact hll, ?_, ?_⟩
  · have heq : (fun x => κ • Homogenization.euclideanGradient V x) = gradientMap κ ∘ V' :=
      funext fun x => smul_euclideanGradient_eq hV κ x
    rw [heq]
    exact (gradientMap κ).lipschitzWith.locallyLipschitz.comp hll
  · funext x
    rw [smul_euclideanGradient_eq hVc κ x, smul_euclideanGradient_eq hV κ x]

/-- The diffusivity `√(2 / ā_N)` of the cutoff equation. -/
def cutoffDiffusivity (M : SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) : ℝ :=
  Real.sqrt (2 * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹)

/-- The drift `ā_N⁻¹ ∇ψ_N^ω` of the cutoff equation. -/
def cutoffDrift (M : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Vec d → Vec d :=
  fun y => (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
    Homogenization.euclideanGradient (cutoffPotential H omega N) y

/-- In the environment `ω`: for every `N` and `x`, on every filtered probability space with a
Brownian motion `W`, the cutoff equation `dX = ā_N⁻¹ ∇ψ_N^ω(X) dt + √(2 / ā_N) dW` has a strong
solution started at `x` when the filtration contains the null sets, and every strong solution
started at `x` has law `K_N(ω, x)`. -/
def IsCutoffSolutionLaw [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d) : Prop :=
  ∀ (N : ℕ) (x : SpatialCoordinates d) {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → Vec d),
    IsBrownianMotion W ℱ P →
      ((∀ (t : ℝ≥0) (s : Set Ω), P s = 0 → MeasurableSet[ℱ t] s) →
        ∃ X : ℝ≥0 → Ω → Vec d,
          IsStrongSolution (cutoffDiffusivity M N) (cutoffDrift M H omega N) W X ℱ ∧
            ∀ w, X 0 w = x) ∧
      ∀ (X : ℝ≥0 → Ω → Vec d)
        (hX : IsStrongSolution (cutoffDiffusivity M N) (cutoffDrift M H omega N) W X ℱ),
        (∀ w, X 0 w = x) → P.map (solutionPath hX) = KN N (omega, x)

/-- **The cutoff diffusions are the solutions of the stochastic differential equation.** Under the
hypotheses of `finiteDimensional_cutoff_path_kernel`, let `K_N` be Markov kernels into continuous
paths with the finite-dimensional laws of the cutoff semigroups. Almost surely
`IsCutoffSolutionLaw M H K ω`. -/
theorem cutoff_solution_law (hI1 : StrongSolutionExistsUnique.{u} d)
    (hIto : ItoFormulaStopped.{u} d) (hI3 : InteriorEllipticRegularity d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hPNfeller : ∀ N omega, (PN N omega).IsFellerKernelSemigroup)
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ D : C0ResolventDatum (SpatialCoordinates d),
        (∀ mu, DenseRange (D.operator mu)) ∧
        IsWeakEllipticResolvent (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
        ∀ (mu : Semigroup.PositiveShift) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
          D.solution mu f x =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
              kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (hnonexplosion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
        ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
            Homogenization.euclideanGradient (cutoffPotential H omega N) x‖ ≤ K * (1 + ‖x‖))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKNm : ∀ N, IsMarkovKernel (KN N))
    (hKN : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N (I : Finset NNReal) x,
      (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, IsCutoffSolutionLaw.{u} M H KN omega := by
  filter_upwards [SubdiffusiveProcess.Paper.aux_finiteDimensional_cutoff_path_kernel_potential
    hd M H hH, hres, hnonexplosion, hKN] with omega hpot hres' hnon hKN'
  unfold IsCutoffSolutionLaw
  intro N x Ω mΩ P _ ℱ W hW
  obtain ⟨g, hg⟩ := hpot N
  obtain ⟨D, -, hweak, hLap⟩ := hres' N
  obtain ⟨K, -, hK⟩ := hnon N
  have hκ : 0 < (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ :=
    inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  have hψd : ∀ y, HasFDerivAt (cutoffPotential H omega N) (g.1.2 y) y := fun y =>
    (show HasFDerivAt (fun z => g z) (g.1.2 y) y from g.2.1 y).congr_of_eventuallyEq
      (Eventually.of_forall hg)
  obtain ⟨hV1, hVl, hbl, hbeq⟩ := potential_regularity g.1.2.continuous hψd g.2.2
    ((N + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P)
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
  have hdrift : cutoffDrift M H omega N = fun y =>
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
        Homogenization.euclideanGradient
          (fun z => cutoffPotential H omega N z - (N + 1 : ℝ) * SubdiffusiveProcess.Model.tauSq M.P)
          y := by
    rw [hbeq]
    rfl
  have hQ : HasClassicalResolvent (PN N omega) (cutoffDiffusivity M N) (cutoffDrift M H omega N) := by
    rw [hdrift]
    exact hasClassicalResolvent_of_weakEllipticResolvent hI3 hV1 hVl hκ hweak hLap
  have hbc : Continuous (cutoffDrift M H omega N) := hbl.continuous
  have hQc : ∀ h : Vec d → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ y,
      Continuous fun t : ℝ≥0 => ∫ z, h z ∂(PN N omega t y) := fun h hh hhc y =>
    continuous_integral_of_isFeller (hPNfeller N omega) h hh.continuous hhc y
  refine ⟨fun hnull => ?_, fun X hX hX0 => ?_⟩
  · exact (hI1 (cutoffDiffusivity M N) (cutoffDrift M H omega N) hbl ⟨K, hK⟩ P ℱ hnull W hW
      x).1
  · have := hKNm N
    refine map_solutionPath_eq hIto hbc hW hX hQ hQc hX0 (KN N (omega, x)) fun I => ?_
    rw [← Kernel.map_apply _ (measurable_finsetEvaluation' I)]
    exact hKN' N I x

/-- **The path kernels of `finiteDimensional_cutoff_path_kernel` are the laws of the solutions of
the cutoff equation**, from the three cited inputs. -/
theorem finiteDimensional_cutoff_path_kernel_solutionLaw (hI1 : StrongSolutionExistsUnique.{u} d)
    (hIto : ItoFormulaStopped.{u} d) (hI3 : InteriorEllipticRegularity d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hPNcons : ∀ N omega, (PN N omega).IsConservative)
    (hPNfeller : ∀ N omega, (PN N omega).IsFellerKernelSemigroup)
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ D : C0ResolventDatum (SpatialCoordinates d),
        (∀ mu, DenseRange (D.operator mu)) ∧
        IsWeakEllipticResolvent (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
        ∀ (mu : Semigroup.PositiveShift) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
          D.solution mu f x =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
              kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (hnonexplosion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
        ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
            Homogenization.euclideanGradient (cutoffPotential H omega N) x‖ ≤ K * (1 + ‖x‖)) :
    ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
      (∀ N, IsMarkovKernel (KN N)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N (I : Finset NNReal) x,
        (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, IsCutoffSolutionLaw.{u} M H KN omega := by
  obtain ⟨KN, hKNm, hKN⟩ := SubdiffusiveProcess.Paper.finiteDimensional_cutoff_path_kernel hd M H
    hH PN hPNcons hPNfeller hres hnonexplosion
  exact ⟨KN, hKNm, hKN,
    cutoff_solution_law hI1 hIto hI3 hd M H hH PN hPNfeller hres hnonexplosion KN hKNm hKN⟩

end SubdiffusiveProcess.SDE
