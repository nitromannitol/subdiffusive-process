module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Section8.GMCResolventDatum
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRadialGenerator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationFamily
public import MarkovProcess.Examples.Identity
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.layer_regularity_moments

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_resolvent_datum_congr
    {d : ℕ} {c c' rho rho' : SpatialCoordinates d → ℝ}
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
      (SpatialCoordinates d))
    (hc : ∀ x, c x = c' x) (hrho : ∀ x, rho x = rho' x)
    (hD : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      c rho D) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      c' rho' D := by
  intro mu f W hW
  obtain ⟨u, hu, hsol⟩ := hD mu f W hW
  refine ⟨u, hu, ?_⟩
  intro φ
  simpa only [hc, hrho] using hsol φ

noncomputable def aux_resolvent_datum_cube_bounds
    {d : ℕ} {c rho : SpatialCoordinates d → ℝ}
    (hc : Continuous c) (hrho : Continuous rho)
    (hcp : ∀ x, 0 < c x) (hrhop : ∀ x, 0 < rho x) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho := by
  choose p hp hcb using fun n ↦
    SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.exists_cube_bounds hc hcp n
  choose q hq hρb using fun n ↦
    SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.exists_cube_bounds hrho hrhop n
  refine {
    lam := fun n ↦ (p n).1
    Lam := fun n ↦ (p n).2
    rhoMin := fun n ↦ (q n).1
    rhoMax := fun n ↦ (q n).2
    lam_pos := fun n ↦ (hp n)
    rhoMin_pos := fun n ↦ (hq n)
    ell := ?_
    coeff_lower := ?_
    rho_measurable := ?_
    rho_lower := ?_
    rho_bounded := ?_ }
  · intro n
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isOpen.measurableSet
      hc.continuousOn (hp n) (hcb n)
  · intro n x hx
    exact (hcb n x hx).1
  · intro n
    exact hrho.aestronglyMeasurable.restrict
  · intro n x hx
    exact (hρb n x hx).1
  · intro n
    filter_upwards [ae_restrict_mem
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        (n : ℤ)).isOpen.measurableSet] with x hx
    rw [abs_of_pos (hrhop x)]
    exact (hρb n x hx).2

theorem aux_resolvent_datum_scaled_growth
    {d : ℕ} {a : SpatialCoordinates d → ℝ} {r K : ℝ}
    (hr : 0 < r) (ha : ContDiff ℝ 1 a)
    (hgrowth : ∀ x,
      Homogenization.euclideanNorm (Homogenization.euclideanGradient a x) + a x ≤
        K * a x * (1 + ‖x‖)) :
    ∀ x,
      Homogenization.euclideanNorm
          (Homogenization.euclideanGradient (fun y ↦ r * a y) x) + r * a x ≤
        (r * K) * a x * (1 + ‖x‖) := by
  intro x
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.euclideanGradient_const_mul
    (ha.differentiable (by simp))]
  rw [Homogenization.euclideanNorm_smul, abs_of_pos hr]
  calc
    r * Homogenization.euclideanNorm (Homogenization.euclideanGradient a x) + r * a x =
        r * (Homogenization.euclideanNorm (Homogenization.euclideanGradient a x) + a x) := by ring
    _ ≤ r * (K * a x * (1 + ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hgrowth x) hr.le
    _ = (r * K) * a x * (1 + ‖x‖) := by ring

/-- Conservative Feller semigroups for the finite-cutoff generator
`L_N = ahom_N⁻¹ e⁻ʰᴺ ∇·(eʰᴺ ∇)`, conditional on `GMCModel` and the displayed
infrared characterization. The proof constructs the dense-range weak
elliptic resolvent from
`SubdiffusiveProcess.Frozen.Section8.exists_gmc_resolvent_data` and identifies its solution
operator through
`SubdiffusiveProcess.Frozen.Section8.exists_fellerKernelSemigroup_of_resolvent_datum`.

The principal declaration retains explicit carrier-identification,
coefficient-time-scaling and cutoff-by-cutoff nonexplosion hypotheses.
The proof uses the first two to transport the upstream resolvent; it
clears the nonexplosion hypothesis and obtains conservativity from the
constructed semigroup. These conditional interfaces do not assert an
unconditional carrier or time-scaling construction.

Resolvent identification holds almost surely: the infrared field is
specified only up to a null set. Conservativeness and the Feller property
hold for every environment by completing the construction with a default
semigroup off the full-measure analytic event. The small-disorder threshold
is produced before the model. -/
theorem resolvent_datum
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        M.delta ≤ delta0 →
        (hcarrier : ∃ hmeas : MeasurableSet
            (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d),
          ∃ hfull : M.P.toMeasure
              (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d) = 1,
            ∀ N : ℕ, ∃ ι : BilateralField d →
                _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d,
              MeasurePreserving ι (chaosSampleLaw M).toMeasure
                (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas hfull).toMeasure ∧
                ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ x,
                  cutoffSpeedDensity M H omega N x =
                    SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt M (N : WithTop ℕ)
                      (ι omega) x) →
        (htime : ∀ (a : SpatialCoordinates d → ℝ) (c : ℝ)
            (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
              (SpatialCoordinates d)),
          0 < c →
          (∀ mu, DenseRange (D.operator mu)) →
          SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
            a a D →
          ∃ D' : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
              (SpatialCoordinates d),
            (∀ mu, DenseRange (D'.operator mu)) ∧
            SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
              (fun x => c * a x) a D') →
        (hnonexplosion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
            ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
                Homogenization.euclideanGradient
                  (cutoffPotential H omega N) x‖ ≤
              K * (1 + ‖x‖)) →
        ∃ PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
          (∀ N omega, (PN N omega).IsConservative) ∧
          (∀ N omega, (PN N omega).IsFellerKernelSemigroup) ∧
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
              (SpatialCoordinates d),
            (∀ mu, DenseRange (D.operator mu)) ∧
            SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
              (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
            ∀ (mu : Semigroup.PositiveShift)
              (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
              (x : SpatialCoordinates d),
              D.solution mu f x =
                ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                  kernelIntegral (PN N omega (Real.toNNReal t)) f x := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hdatum⟩ :=
    SubdiffusiveProcess.Frozen.Section8.exists_gmc_resolvent_data (d := d)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hH hM hcarrier htime hnonexplosion
  clear hnonexplosion
  obtain ⟨hmeas, hfull, hcarrier⟩ := hcarrier
  let Good : ℕ → BilateralField d → Prop := fun N omega ↦
    ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (SpatialCoordinates d),
      ∃ hDdense : (∀ mu, DenseRange (D.operator mu)),
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
        (D.fellerKernelSemigroup hDdense).IsConservative
  have hGoodN : ∀ N : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Good N omega := by
    intro N
    obtain ⟨ι, hι, hιcoef⟩ := hcarrier N
    obtain ⟨hmeas', hfull', full, hfullMeas, hfullOne, DX, DY, hDX⟩ :=
      hdatum M hM (N : WithTop ℕ)
    have hι' : MeasurePreserving ι (chaosSampleLaw M).toMeasure
        (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas' hfull').toMeasure := by
      simpa using hι
    have hae_full : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ι omega ∈ full :=
      hι'.quasiMeasurePreserving.tendsto_ae
        ((mem_ae_iff_prob_eq_one hfullMeas).2 hfullOne)
    have hgrowth_anch :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ae_reversible_family_linearGrowth M
    have hgrowth_anch' : ∀ᵐ omega ∂
        (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas' hfull').toMeasure,
        ∃ K : ℝ, 0 ≤ K ∧ ∀ b : SpatialCoordinates d → ℝ,
          (b = _root_.SubdiffusiveProcess.Model.aAnchored M omega ∨
            (∃ L : ℕ, b = _root_.SubdiffusiveProcess.Model.aCutoff M L omega.1) ∨
            (∃ L : ℕ, b = SubdiffusiveProcess.CoarseGrainingVocab.anchoredCutoff M L omega.1)) →
          ContDiff ℝ 1 b ∧ (∀ x, 0 < b x) ∧ ∀ x,
            Homogenization.euclideanNorm (Homogenization.euclideanGradient b x) + b x ≤
              K * b x * (1 + ‖x‖) := by
      simpa using hgrowth_anch
    have hae_growth : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∃ K : ℝ, 0 ≤ K ∧ ∀ b : SpatialCoordinates d → ℝ,
          (b = _root_.SubdiffusiveProcess.Model.aAnchored M (ι omega) ∨
            (∃ L : ℕ, b = _root_.SubdiffusiveProcess.Model.aCutoff M L (ι omega).1) ∨
            (∃ L : ℕ, b = SubdiffusiveProcess.CoarseGrainingVocab.anchoredCutoff M L (ι omega).1)) →
          ContDiff ℝ 1 b ∧ (∀ x, 0 < b x) ∧ ∀ x,
            Homogenization.euclideanNorm (Homogenization.euclideanGradient b x) + b x ≤
              K * b x * (1 + ‖x‖) :=
      hι'.quasiMeasurePreserving.tendsto_ae hgrowth_anch'
    have hae_coef : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ x,
        cutoffSpeedDensity M H omega N x =
          _root_.SubdiffusiveProcess.Model.aCutoff M N (ι omega).1 x := by
      filter_upwards [hιcoef] with omega hω
      intro x
      simpa only [SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.coefficientAt_natCast] using hω x
    filter_upwards [hae_full, hae_growth, hae_coef] with omega hωfull hωgrowth hωcoef
    obtain ⟨K, hK, hfamily⟩ := hωgrowth
    obtain ⟨ha, hapos, hlinear⟩ := hfamily
      (_root_.SubdiffusiveProcess.Model.aCutoff M N (ι omega).1)
      (Or.inr (Or.inl ⟨N, rfl⟩))
    obtain ⟨D, hDdense, hDweak⟩ := htime
      (_root_.SubdiffusiveProcess.Model.aCutoff M N (ι omega).1)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ (DX (ι omega))
      (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (hDX (ι omega) hωfull).1 (by
        simpa only [SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.coefficientAt_natCast] using
          (hDX (ι omega) hωfull).2.1)
    have hspeed : ∀ x,
        cutoffSpeedDensity M H omega N x =
          _root_.SubdiffusiveProcess.Model.aCutoff M N (ι omega).1 x := hωcoef
    have hcoeff : ∀ x,
        cutoffCoefficient M H omega N x =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            _root_.SubdiffusiveProcess.Model.aCutoff M N (ι omega).1 x := by
      intro x
      simpa only [cutoffCoefficient, cutoffSpeedDensity] using
        congrArg (fun z ↦ (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * z) (hspeed x)
    have hDtarget := aux_resolvent_datum_congr D
      (fun x ↦ (hcoeff x).symm) (fun x ↦ (hspeed x).symm) hDweak
    have hcons : (D.fellerKernelSemigroup hDdense).IsConservative := by
      let r : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
      let a : SpatialCoordinates d → ℝ :=
        _root_.SubdiffusiveProcess.Model.aCutoff M N (ι omega).1
      have hr : 0 < r := by
        dsimp [r]
        exact inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
      have hac : ContDiff ℝ 1 a := by
        dsimp [a]
        exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.contDiff_one_aCutoff
          M N (ι omega).1
      have hρc : Continuous a := hac.continuous
      have hρp : ∀ x, 0 < a x := by
        intro x
        exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M N (ι omega).1 x
      have hrc : ContDiff ℝ 1 (fun x ↦ r * a x) := by
        simpa only [a, r, smul_eq_mul] using
          (SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.contDiff_one_aCutoff
            M N (ι omega).1).const_smul r
      have hrcp : ∀ x, 0 < r * a x := fun x ↦ mul_pos hr (hρp x)
      have hDscaled :
          SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
            (fun x ↦ r * a x) a D := by
        simpa only [r, a] using hDweak
      have hB := aux_resolvent_datum_cube_bounds hrc.continuous hρc hrcp hρp
      have hg := aux_resolvent_datum_scaled_growth hr hac hlinear
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.isConservative_of_weakResolvent_linearGrowth
        hB hrc hρc D hDdense hDscaled (fun x ↦ (hrcp x).le)
        (mul_nonneg hr.le hK) hg
    exact ⟨D, hDdense, hDtarget, hcons⟩
  have hGood : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, Good N omega :=
    ae_all_iff.2 hGoodN
  classical
  let PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d) :=
    fun N omega ↦ if h : Good N omega then
      (Classical.choose h).fellerKernelSemigroup ((Classical.choose_spec h).1)
    else MarkovProcess.idSemigroup
  refine ⟨PN, ?_, ?_, ?_⟩
  · intro N omega
    by_cases h : Good N omega
    · dsimp [PN]
      rw [dite_eq_left h]
      exact (Classical.choose_spec h).2.2
    · dsimp [PN]
      rw [dite_eq_right h]
      exact MarkovProcess.isConservative_idSemigroup
  · intro N omega
    by_cases h : Good N omega
    · dsimp [PN]
      rw [dite_eq_left h]
      exact (Classical.choose h).isFellerKernelSemigroup_fellerKernelSemigroup
        (Classical.choose_spec h).1
    · dsimp [PN]
      rw [dite_eq_right h]
      exact MarkovProcess.isFellerKernelSemigroup_idSemigroup
  · filter_upwards [hGood] with omega hω
    intro N
    let hN := hω N
    refine ⟨Classical.choose hN, (Classical.choose_spec hN).1,
      (Classical.choose_spec hN).2.1, ?_⟩
    dsimp [PN]
    rw [dite_eq_left hN]
    exact (Classical.choose hN).solution_eq_laplace (Classical.choose_spec hN).1

end SubdiffusiveProcess.Paper
