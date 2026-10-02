import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.WeightedChaosCutoff
import SubdiffusiveProcess.Main.ChaosCutoff
import SubdiffusiveProcess.Main.ConditionalFineFiltration
import SubdiffusiveProcess.Main.MeasuresConvergeLocally
import SubdiffusiveProcess.Main.SemigroupSymmetric
import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
import SubdiffusiveProcess.Main.HasStrongMarkovRestart
import SubdiffusiveProcess.Main.HasFiniteMeanExits
import SubdiffusiveProcess.Main.PathLevyProkhorovDist
import SubdiffusiveProcess.Main.PhysicalRescaledPath
import SubdiffusiveProcess.Main.PhysicalTimeFactor
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.DiffusionPath
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.Sobolev.ResponseSpace
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane2.KilledInverse
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Probability.CubeMassMartingale
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Inputs.MarkovProcesses
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierLimit
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumC0Data
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumDenseRange
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Frozen.Section8.GMCResolventDatum
import SubdiffusiveProcess.Frozen.Vocab.Ahom
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRadialGenerator
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationFamily
import MarkovProcess.Examples.Identity
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import SubdiffusiveProcess.Paper.in_normalization
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.layer_regularity_moments
import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_nonexplosion
import SubdiffusiveProcess.Paper.coefficient_physical_identity
open Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace MarkovProcess
  SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal NNReal BigOperators
open scoped CompactlySupported ZeroAtInfty
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

def aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum
    {d : ℕ} (φ : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d
  | 0 => φ 0
  | n + 1 => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
      (aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum φ n)
      (φ (n + 1))

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum_apply
    {d : ℕ} (φ : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (n : ℕ) (x : SpatialCoordinates d) :
    aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum φ n x =
      ∑ j ∈ Finset.range (n + 1), φ j x := by
  induction n with
  | zero => simp [aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum]
  | succ n ih =>
      rw [aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply, ih]
      simpa only [Nat.add_assoc] using
        (Finset.sum_range_succ (f := fun j => φ j x) (n + 1)).symm

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_native_tendsto
    {d : ℕ} (omega : NativeBilateralPotentialSample d)
    (G : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (hG : ∀ K : Compacts (SpatialCoordinates d),
      Tendsto
        (fun L => compactPotentialC1Norm K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) G)))
        atTop (nhds 0)) :
    Tendsto
      (fun L => infraredPartialSum
        (fun j => layerScaling d j
          ((fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => q.1.1) (omega j))) L)
      atTop
      (nhds ((fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => q.1.1) G)) := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  have hπ : ∀ omega n,
      forget (positiveScaledNativeLayer omega n) = π omega (Int.ofNat (n + 1)) := by
    intro omega n
    ext x
    change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • x) =
      omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • x)
    congr 1
  have hsum : ∀ omega L,
      infraredPartialSum (π omega) L =
        forget (positiveAnchoredInfraredTruncation omega L) := by
    intro omega L
    induction L with
    | zero =>
        simp [infraredPartialSum, positiveAnchoredInfraredTruncation, forget,
          zeroNativePotentialField]
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih, ← hπ omega L]
        ext x
        change (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0) =
          (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0)
        rfl
  have hfield_tendsto :
      Tendsto (fun L => forget (positiveAnchoredInfraredTruncation omega L))
        atTop (nhds (forget G)) := by
    apply (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn).2
    intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hK := hG (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
        (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hK] with L hL
    intro x hx
    have hq : ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget G) x‖ ≤
        compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) G)) := by
      let q := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
        (positiveAnchoredInfraredTruncation omega L)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) G)
      change ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget G) x‖ ≤
        ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) => q z.1,
          q.1.1.continuous.comp continuous_subtype_val⟩ :
            C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)), ℝ))‖ +
          ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) =>
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q z.1,
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q).continuous.comp
              continuous_subtype_val⟩ :
              C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)),
                SpatialCoordinates d →L[ℝ] ℝ))‖
      have heval := ContinuousMap.norm_coe_le_norm
        (⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) => q z.1,
            q.1.1.continuous.comp continuous_subtype_val⟩ :
              C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)), ℝ))
        ⟨x, hx⟩
      rw [show (forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget G) x = q x by
        change (positiveAnchoredInfraredTruncation omega L) x - G x = q x
        dsimp [q]
        ring]
      calc
        ‖q x‖ ≤ ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) => q z.1,
            q.1.1.continuous.comp continuous_subtype_val⟩ :
              C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)), ℝ))‖ := heval
        _ ≤ _ + ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) =>
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q z.1,
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q).continuous.comp
              continuous_subtype_val⟩ :
              C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)),
                SpatialCoordinates d →L[ℝ] ℝ))‖ :=
          le_add_of_nonneg_right (by positivity)
    change dist ((forget G) x)
        ((forget (positiveAnchoredInfraredTruncation omega L)) x) < ε
    rw [dist_eq_norm']
    have hc : 0 ≤ compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) G)) := by
      unfold compactPotentialC1Norm
      positivity
    have hL' : compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) G)) < ε := by
      have hL'' : dist (compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) G))) 0 < ε := hL
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hc] using hL''
    exact hq.trans_lt hL'
  apply hfield_tendsto.congr
  intro L
  exact (hsum omega L).symm

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_exists_mem_centeredCube
    {d : ℕ} (x : SpatialCoordinates d) :
    ∃ n : ℕ, x ∈ cube d (n : ℤ) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * ‖x‖)
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hpow : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hpow]
  constructor <;> nlinarith [neg_le_of_abs_le hxi, le_of_abs_le hxi]

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_local_representative
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {c rho : SpatialCoordinates d → ℝ}
    (B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho)
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    {mu U : ℝ} (f : C_c(SpatialCoordinates d, ℝ)) {u : SpatialCoordinates d → ℝ}
    (huBound : ∀ x, |u x| ≤ U)
    (huLocal : ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
      uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) uLocal f) :
    Continuous (euclideanBallAverageRepresentative u) ∧
      euclideanBallAverageRepresentative u =ᵐ[volume] u := by
  choose uLocal huLocalAE huLocalSolution using huLocal
  let v : ℕ → SpatialCoordinates d → ℝ := fun k ↦
    euclideanBallAverageRepresentative (uLocal k).toFun
  have huLocalBound : ∀ k, ∀ᵐ x ∂(volume.restrict (cube d (k : ℤ))),
      |(uLocal k).toFun x| ≤ U := by
    intro k
    filter_upwards [huLocalAE k] with x hx
    rw [hx]
    exact huBound x
  have hv : ∀ k,
      ContinuousOn (v k) (cube d (k : ℤ)) ∧
        v k =ᵐ[volume.restrict (cube d (k : ℤ))] (uLocal k).toFun := by
    intro k
    exact continuousOn_and_ae_eq_massiveWeakSolutionRepresentative_of_two_le
      hd hc.continuousOn (fun x _hx ↦ hcpos x) f
      (B.rho_measurable k) (B.rho_bounded k) (huLocalBound k)
      (huLocalSolution k)
  have hcanonical : ∀ k, Set.EqOn (euclideanBallAverageRepresentative u)
      (v k) (cube d (k : ℤ)) := by
    intro k x hx
    have hseq : euclideanBallAverageSequence u x =ᶠ[atTop]
        euclideanBallAverageSequence (uLocal k).toFun x :=
      eventuallyEq_euclideanBallAverageSequence_of_ae_eq_on_open
        (isOpen_openCubeSet (originCube d (k : ℤ))) (huLocalAE k).symm hx
    have htendstoLocal : Tendsto
        (euclideanBallAverageSequence (uLocal k).toFun x) atTop (𝓝 (v k x)) :=
      tendsto_euclideanBallAverageSequence_of_localRepresentative
        (isOpen_openCubeSet (originCube d (k : ℤ))) Set.Subset.rfl
        (hv k).2 (hv k).1 hx
    have htendsto : Tendsto (euclideanBallAverageSequence u x) atTop
        (𝓝 (v k x)) :=
      (tendsto_congr' hseq).2 htendstoLocal
    exact htendsto.limUnder_eq
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨k, hx⟩ :=
      aux_finiteDimensional_cutoff_full_coefficient_semigroup_exists_mem_centeredCube x
    exact ((hv k).1.congr fun y hy ↦ hcanonical k hy).continuousAt
      ((isOpen_openCubeSet (originCube d (k : ℤ))).mem_nhds hx)
  · have hk : ∀ k : ℕ, ∀ᵐ x ∂volume,
        x ∈ cube d (k : ℤ) → euclideanBallAverageRepresentative u x = u x := by
      intro k
      have hvAEGlobal : ∀ᵐ x ∂volume,
          x ∈ cube d (k : ℤ) → v k x = (uLocal k).toFun x :=
        (ae_restrict_iff'
          (isOpen_openCubeSet (originCube d (k : ℤ))).measurableSet).1 (hv k).2
      have huAEGlobal : ∀ᵐ x ∂volume,
          x ∈ cube d (k : ℤ) → (uLocal k).toFun x = u x :=
        (ae_restrict_iff'
          (isOpen_openCubeSet (originCube d (k : ℤ))).measurableSet).1
          (huLocalAE k)
      filter_upwards [hvAEGlobal, huAEGlobal] with x hxv hxu
      intro hx
      rw [hcanonical k hx, hxv hx, hxu hx]
    filter_upwards [ae_all_iff.2 hk] with x hx
    obtain ⟨k, hxk⟩ :=
      aux_finiteDimensional_cutoff_full_coefficient_semigroup_exists_mem_centeredCube x
    exact hx k hxk

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_compact_solutions
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {c rho : SpatialCoordinates d → ℝ}
    (B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho)
    (hcC1 : ContDiff ℝ 1 c) (hcpos : ∀ x, 0 < c x)
    (hrhopos : ∀ x, 0 < rho x) {K : ℝ}
    (hK : 0 ≤ K)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
      K * rho x * (1 + ‖x‖)) :
    HasC0MassiveSolutionsOnCompactData c rho := by
  classical
  intro mu hmu f
  have hcdiff : Differentiable ℝ c := hcC1.differentiable le_rfl
  have hrhoNe : ∀ x, rho x ≠ 0 := fun x ↦ (hrhopos x).ne'
  set beta : ℝ := barrierExponent d K mu with hbetadef
  have hbetapos : 0 < beta := barrierExponent_pos d hK hmu
  have hbeta1 : beta ≤ 1 := barrierExponent_le_one d K mu
  have hbetaK : beta * K * (2 * Real.sqrt d + 6) ≤ mu / 2 :=
    barrierExponent_mul_le d hK hmu
  obtain ⟨R0, hR0sub⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : SpatialCoordinates d)).1
      f.hasCompactSupport.isCompact.isBounded
  set R : ℝ := max R0 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRsupp : ∀ x, x ∈ tsupport (f : SpatialCoordinates d → ℝ) → ‖x‖ ≤ R := by
    intro x hx
    have := hR0sub hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set T : ℝ := (d : ℝ) * R ^ 2 with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hTpos : (0 : ℝ) < 1 + T := by linarith
  set nf : ℝ := ‖compactSupportToC0 f‖ with hnfdef
  have hnf0 : 0 ≤ nf := norm_nonneg _
  set A : ℝ := 2 * nf / mu * (1 + T) ^ (beta / 2) + 1 with hAdef
  have hApos : 0 < A := by
    have h1 : 0 ≤ 2 * nf / mu * (1 + T) ^ (beta / 2) := by
      have := Real.rpow_pos_of_pos hTpos (beta / 2)
      positivity
    linarith
  set bb : SpatialCoordinates d → ℝ := radialBarrier A beta with hbbdef
  have hbbpos : ∀ x, 0 < bb x := fun x ↦ radialBarrier_pos hApos beta x
  have hbbsmooth : ContDiff ℝ (⊤ : ℕ∞) bb := contDiff_radialBarrier A beta
  have hdivle : ∀ x, coeffFluxDiv c bb x ≤ mu * rho x / 2 * bb x :=
    fun x ↦ coeffFluxDiv_radialBarrier_le hcdiff (fun y ↦ (hcpos y).le) hK hApos
      hrhopos hgrowth hbetapos hbeta1 hbetaK x
  have hhalf : ∀ x, mu * bb x / 2 ≤ smoothMassiveForcing c rho mu bb x := by
    intro x
    have hquot : coeffFluxDiv c bb x / rho x ≤ mu * bb x / 2 := by
      rw [div_le_iff₀ (hrhopos x)]
      have := hdivle x
      nlinarith [this]
    have : smoothMassiveForcing c rho mu bb x =
        mu * bb x - coeffFluxDiv c bb x / rho x := rfl
    rw [this]
    linarith
  have hsuper : ∀ x, |f x| ≤ smoothMassiveForcing c rho mu bb x := by
    intro x
    refine le_trans ?_ (hhalf x)
    by_cases hx : x ∈ tsupport (f : SpatialCoordinates d → ℝ)
    · have hnorm : |f x| ≤ nf := by
        have hpoint : |f x| ≤ ‖compactSupportToC0 f‖ := by
          simpa only [Real.norm_eq_abs, compactSupportToC0_apply] using
            BoundedContinuousFunction.norm_coe_le_norm
              (ZeroAtInftyContinuousMap.toBCF (compactSupportToC0 f)) x
        exact hpoint
      have hxT : vecNormSq x ≤ T := by
        have h1 : vecNormSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := vecNormSq_le_dim_mul_sq_norm x
        have h2 : ‖x‖ ≤ R := hRsupp x hx
        have h3 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
        have h4 : (d : ℝ) * ‖x‖ ^ 2 ≤ (d : ℝ) * R ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
        linarith
      have hlow := radialBarrier_ge_of_vecNormSq_le hApos hbetapos.le hxT
      have hcancel : (1 + T) ^ (beta / 2) * (1 + T) ^ (-(beta / 2)) = 1 := by
        rw [← Real.rpow_add hTpos]
        simp
      have hAval : A * (1 + T) ^ (-(beta / 2)) =
          2 * nf / mu + (1 + T) ^ (-(beta / 2)) := by
        rw [hAdef, add_mul, one_mul, mul_assoc, hcancel, mul_one]
      have hbig : 2 * nf / mu ≤ bb x := by
        have hposrp : (0 : ℝ) < (1 + T) ^ (-(beta / 2)) :=
          Real.rpow_pos_of_pos hTpos _
        have hbbx : A * (1 + T) ^ (-(beta / 2)) ≤ bb x := by
          rw [hbbdef]
          exact hlow
        rw [hAval] at hbbx
        linarith
      have : nf ≤ mu * bb x / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hbig hmu.le
        have hexp : mu * (2 * nf / mu) = 2 * nf := by field_simp
        rw [hexp] at hmul
        linarith
      linarith
    · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hbb : 0 < mu * bb x / 2 := by
        have := hbbpos x
        positivity
      rw [hzero]
      simpa using hbb.le
  obtain ⟨u, hubd, hbar, hloc⟩ :=
    exists_barrier_bounded_signed_localMassiveWeakSolution_of_compactSupport B hcC1
      hrhoNe hbbsmooth (fun x ↦ (hbbpos x).le) hmu f hsuper
  have hreg :=
    aux_finiteDimensional_cutoff_full_coefficient_semigroup_local_representative
      hd B hcC1.continuous (fun x ↦ hcpos x) f hubd hloc
  set U : SpatialCoordinates d → ℝ := euclideanBallAverageRepresentative u
    with hUdef
  have hUcont : Continuous U := hreg.1
  have hUb : ∀ x, |U x| ≤ 2 * bb x := by
    have hae : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), |U x| ≤ 2 * bb x := by
      filter_upwards [hreg.2, hbar] with x hx hxb
      rw [hx]
      exact hxb
    intro x
    by_contra hcon
    push_neg at hcon
    have hopen : IsOpen {y : SpatialCoordinates d | 2 * bb y < |U y|} :=
      isOpen_lt (continuous_const.mul hbbsmooth.continuous) hUcont.abs
    have hne : ({y : SpatialCoordinates d | 2 * bb y < |U y|}).Nonempty := ⟨x, hcon⟩
    have hpos : 0 < volume {y : SpatialCoordinates d | 2 * bb y < |U y|} :=
      hopen.measure_pos volume hne
    have hzero : volume {y : SpatialCoordinates d | 2 * bb y < |U y|} = 0 := by
      have hnot : ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)),
          ¬ (2 * bb y < |U y|) := by
        filter_upwards [hae] with y hy
        exact not_lt.mpr hy
      simpa using MeasureTheory.ae_iff.mp hnot
    exact absurd hzero hpos.ne'
  have hdecay : Filter.Tendsto U (Filter.cocompact (SpatialCoordinates d)) (nhds 0) := by
    refine squeeze_zero_norm (a := fun x ↦ 2 * bb x) (fun x ↦ ?_) ?_
    · simpa only [Real.norm_eq_abs] using hUb x
    · have := (tendsto_radialBarrier_cocompact (d := d) A hbetapos).const_mul (2 : ℝ)
      simpa [hbbdef] using this
  refine ⟨{ toContinuousMap := ⟨U, hUcont⟩, zero_at_infty' := hdecay }, fun k ↦ ?_⟩
  obtain ⟨v, hv, hvsol⟩ := hloc k
  have huAE : U =ᵐ[volume.restrict (cube d (k : ℤ))] u :=
    hreg.2.filter_mono (ae_mono Measure.restrict_le_self)
  have hvU : v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] U := hv.trans huAE.symm
  refine ⟨H1Function.ofAEEq v U hvU.symm, fun x ↦ rfl, ?_⟩
  exact IsMassiveWeakSolutionOn.congr (u := v) hvU
    (Filter.Eventually.of_forall fun _ ↦ rfl) hvsol

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_exists_c0_solution
    {d : ℕ} [NeZero d] {c rho : SpatialCoordinates d → ℝ}
    (B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho)
    (hsolve : HasC0MassiveSolutionsOnCompactData c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ) :
    ∃ g : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ, ∀ k : ℕ,
      ∃ v : H1Function (cube d (k : ℤ)),
        (∀ x, v.toFun x = g x) ∧
          IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun x ↦ f x) := by
  classical
  choose G hG using fun j : ℕ ↦ hsolve mu hmu (cubeTruncation f j)
  have hGloc : ∀ j : ℕ, ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = G j x) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v
          (fun x ↦ (compactSupportToC0 (cubeTruncation f j)) x) :=
    fun j k ↦ hG j k
  have htrunc_norm : ∀ j : ℕ,
      ‖compactSupportToC0 (cubeTruncation f j)‖ ≤ ‖f‖ := by
    intro j
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x ↦ ?_
    simp only [ZeroAtInftyContinuousMap.toBCF_apply, compactSupportToC0_apply,
      cubeTruncation_apply, Real.norm_eq_abs, abs_mul]
    have h1 : |f x| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF f) x
    have h2 := cubeCutoff_abs_le d j x
    nlinarith [abs_nonneg (f x), abs_nonneg (cubeCutoff d j x)]
  have hGnorm : ∀ j : ℕ, ‖G j‖ ≤ mu⁻¹ * ‖f‖ := by
    intro j
    have h := norm_le_of_localMassiveWeakSolution B hmu (G j)
      (compactSupportToC0 (cubeTruncation f j)) (hGloc j)
    have hmono : mu⁻¹ * ‖compactSupportToC0 (cubeTruncation f j)‖ ≤ mu⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (htrunc_norm j) (inv_nonneg.2 hmu.le)
    exact h.trans hmono
  have hGpoint : ∀ (j : ℕ) (x : SpatialCoordinates d),
      |G j x| ≤ mu⁻¹ * ‖f‖ := by
    intro j x
    have h1 : |G j x| ≤ ‖G j‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF (G j)) x
    exact h1.trans (hGnorm j)
  have hdata : CauchySeq (fun j ↦ compactSupportToC0 (cubeTruncation f j)) :=
    (tendsto_cubeTruncation f).cauchySeq
  have hCauchy : CauchySeq G := by
    refine Metric.cauchySeq_iff.2 fun eps heps ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hdata (mu * eps) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 := hN m hm n hn
    have h2 := norm_sub_le_of_localMassiveWeakSolution B hmu (G m) (G n)
      (compactSupportToC0 (cubeTruncation f m))
      (compactSupportToC0 (cubeTruncation f n)) (hGloc m) (hGloc n)
    rw [dist_eq_norm] at h1 ⊢
    calc ‖G m - G n‖ ≤ mu⁻¹ * ‖compactSupportToC0 (cubeTruncation f m) -
            compactSupportToC0 (cubeTruncation f n)‖ := h2
      _ < mu⁻¹ * (mu * eps) := by
          exact mul_lt_mul_of_pos_left h1 (inv_pos.2 hmu)
      _ = eps := by field_simp
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hgpoint : ∀ x : SpatialCoordinates d,
      Tendsto (fun j ↦ G j x) atTop (nhds (g x)) := by
    intro x
    refine Metric.tendsto_atTop.2 fun eps heps ↦ ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hg eps heps
    refine ⟨N, fun j hj ↦ ?_⟩
    have h := hN j hj
    rw [dist_eq_norm] at h ⊢
    have hpt : ‖G j x - g x‖ ≤ ‖G j - g‖ := by
      simpa only [ZeroAtInftyContinuousMap.toBCF_apply,
        ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply,
        ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF (G j - g)) x
    exact lt_of_le_of_lt hpt h
  refine ⟨g, fun k ↦ ?_⟩
  set Q : Set (SpatialCoordinates d) := cube d (k : ℤ) with hQdef
  have hQ := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hWbig := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d ((k + 1 : ℕ) : ℤ)
  have hQW : cube d (k : ℤ) ⊆ cube d ((k + 1 : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  letI : IsFiniteMeasure (volumeMeasureOn (cube d (k : ℤ))) :=
    hQ.isBoundedDomain.isFiniteMeasure_restrict_volume
  choose V hV1 hV2 using fun n : ℕ ↦ hG (k + 1 + n) (k + 1)
  have hVsol : ∀ n : ℕ, IsMassiveWeakSolutionOn c rho mu
      (cube d ((k + 1 : ℕ) : ℤ)) (V n) (fun x ↦ f x) := by
    intro n
    refine IsMassiveWeakSolutionOn.congr_forcing_on hWbig.isOpen.measurableSet
      (fun x hx ↦ ?_) (hV2 n)
    exact cubeTruncation_eq_of_mem f (by omega) hx
  have hVbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (cube d ((k + 1 : ℕ) : ℤ))),
      |(V n).toFun x| ≤ mu⁻¹ * ‖f‖ := by
    intro n
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [hV1 n x]
    exact hGpoint (k + 1 + n) x
  obtain ⟨Cgrad, hCgrad0, hCgrad⟩ :=
    exists_uniform_cube_gradient_bound B hmu.le k (fun x ↦ f x) (mu⁻¹ * ‖f‖)
  set w : ℕ → H1Function (cube d (k : ℤ)) :=
    fun n ↦ (V n).restrict hQ.isOpen hQW with hw_def
  have hwsol : ∀ n, IsMassiveWeakSolutionOn c rho mu
      (cube d (k : ℤ)) (w n) (fun x ↦ f x) := fun n ↦
    IsMassiveWeakSolutionOn.restrict hQ.isOpen hWbig.isOpen hQW (hVsol n)
  have hwbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      |(w n).toFun x| ≤ mu⁻¹ * ‖f‖ :=
    fun n ↦ (hVbound n).filter_mono (ae_mono (Measure.restrict_mono hQW le_rfl))
  have hwgrad : ∀ n, ‖(w n).gradToHilbertVectorL2‖ ≤ Cgrad := fun n ↦
    hCgrad (V n) hQ.isOpen hQW (memL2On_of_zeroAtInfty hWbig f)
      (hVsol n) (hVbound n)
  have hwpoint : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (g x)) := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hshift : Tendsto (fun n ↦ G (k + 1 + n) x) atTop (nhds (g x)) := by
      simpa only [Function.comp_apply] using
        (hgpoint x).comp (strictMono_id.const_add (k + 1)).tendsto_atTop
    refine hshift.congr fun n ↦ ?_
    simp only [hw_def, H1Function.restrict]
    exact (hV1 n x).symm
  obtain ⟨v, hvae, hvsol⟩ :=
    exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit (B.ell k)
      (B.rho_measurable k) (B.rho_bounded k)
      (memL2On_of_zeroAtInfty hQ f) w hwbound hwpoint hwgrad hwsol
  refine ⟨H1Function.ofAEEq v (fun x ↦ g x) hvae.symm, fun x ↦ rfl, ?_⟩
  exact IsMassiveWeakSolutionOn.congr (u := v) hvae
    (Filter.Eventually.of_forall fun _ ↦ rfl) hvsol

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_c0_solutions
    {d : ℕ} [NeZero d] {c rho : SpatialCoordinates d → ℝ}
    (B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho)
    (hsolve : HasC0MassiveSolutionsOnCompactData c rho) :
    HasC0MassiveSolutions c rho := by
  intro mu f
  exact aux_finiteDimensional_cutoff_full_coefficient_semigroup_exists_c0_solution
    B hsolve mu.2 f

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_cube_bounds
    {d : ℕ} {c rho : SpatialCoordinates d → ℝ}
    (hc : Continuous c) (hcpos : ∀ x, 0 < c x)
    (hrho : Continuous rho) (hrhopos : ∀ x, 0 < rho x) :
    ∃ B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho, True := by
  classical
  have hminc : ∀ n : ℕ, ∃ x ∈ closure (cube d (n : ℤ)),
      IsMinOn c (closure (cube d (n : ℤ))) x := by
    intro n
    apply (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isBoundedDomain.isBounded
      |>.isCompact_closure.exists_isMinOn
    · exact ⟨0, subset_closure (by
        rw [cube, mem_openCubeSet_originCube_iff]
        intro i
        have hp : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
        have hhalf : (0 : ℝ) < (1 / 2) * (3 : ℝ) ^ (n : ℤ) :=
          mul_pos (by norm_num) hp
        constructor
        · simpa using (neg_lt_zero.mpr hhalf)
        · simpa using hhalf)⟩
    · exact hc.continuousOn
  have hmaxc : ∀ n : ℕ, ∃ x ∈ closure (cube d (n : ℤ)),
      IsMaxOn c (closure (cube d (n : ℤ))) x := by
    intro n
    apply (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isBoundedDomain.isBounded
      |>.isCompact_closure.exists_isMaxOn
    · exact ⟨0, subset_closure (by
        rw [cube, mem_openCubeSet_originCube_iff]
        intro i
        have hp : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
        have hhalf : (0 : ℝ) < (1 / 2) * (3 : ℝ) ^ (n : ℤ) :=
          mul_pos (by norm_num) hp
        constructor
        · simpa using (neg_lt_zero.mpr hhalf)
        · simpa using hhalf)⟩
    · exact hc.continuousOn
  have hminrho : ∀ n : ℕ, ∃ x ∈ closure (cube d (n : ℤ)),
      IsMinOn rho (closure (cube d (n : ℤ))) x := by
    intro n
    apply (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isBoundedDomain.isBounded
      |>.isCompact_closure.exists_isMinOn
    · exact ⟨0, subset_closure (by
        rw [cube, mem_openCubeSet_originCube_iff]
        intro i
        have hp : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
        have hhalf : (0 : ℝ) < (1 / 2) * (3 : ℝ) ^ (n : ℤ) :=
          mul_pos (by norm_num) hp
        constructor
        · simpa using (neg_lt_zero.mpr hhalf)
        · simpa using hhalf)⟩
    · exact hrho.continuousOn
  have hmaxrho : ∀ n : ℕ, ∃ x ∈ closure (cube d (n : ℤ)),
      IsMaxOn rho (closure (cube d (n : ℤ))) x := by
    intro n
    apply (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isBoundedDomain.isBounded
      |>.isCompact_closure.exists_isMaxOn
    · exact ⟨0, subset_closure (by
        rw [cube, mem_openCubeSet_originCube_iff]
        intro i
        have hp : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
        have hhalf : (0 : ℝ) < (1 / 2) * (3 : ℝ) ^ (n : ℤ) :=
          mul_pos (by norm_num) hp
        constructor
        · simpa using (neg_lt_zero.mpr hhalf)
        · simpa using hhalf)⟩
    · exact hrho.continuousOn
  choose xmin hxmin hmin using hminc
  choose xmax hxmax hmax using hmaxc
  choose rmin hrmin hrmin' using hminrho
  choose rmax hrmax hrmax' using hmaxrho
  let B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho :=
    { lam := fun n ↦ c (xmin n), Lam := fun n ↦ c (xmax n),
      rhoMin := fun n ↦ rho (rmin n), rhoMax := fun n ↦ rho (rmax n),
      lam_pos := fun n ↦ hcpos (xmin n),
      rhoMin_pos := fun n ↦ hrhopos (rmin n), ell := by
        intro n
        apply Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
          (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
          hc.continuousOn (hcpos (xmin n))
        intro x hx
        exact ⟨hmin n (subset_closure hx), hmax n (subset_closure hx)⟩,
      coeff_lower := by
        intro n x hx
        exact hmin n (subset_closure hx),
      rho_measurable := by
        intro n
        exact hrho.aestronglyMeasurable,
      rho_lower := by
        intro n x hx
        exact hrmin' n (subset_closure hx),
      rho_bounded := by
        intro n
        filter_upwards [ae_restrict_mem
          (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet]
          with x hx
        rw [abs_of_pos (hrhopos x)]
        exact hrmax' n (subset_closure hx) }
  exact ⟨B, trivial⟩

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_exp_growth
    {d : ℕ} [NeZero d] (q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (a z K : ℝ) (ha : 0 < a) (hK : 0 ≤ K)
    (hbound : ∀ x : SpatialCoordinates d,
      ‖a • euclideanGradient (fun y => q y) x‖ ≤ K * (1 + ‖x‖)) :
    ∀ x, euclideanNorm (euclideanGradient
      (fun y => a * Real.exp (q y - z)) x) + a * Real.exp (q x - z) ≤
      ((d : ℝ) * K + a) * Real.exp (q x - z) * (1 + ‖x‖) := by
  have hgradq : ∀ x : SpatialCoordinates d,
      euclideanGradient (fun y => q y) x = shellGradient q x := by
    intro x
    funext i
    have hq : HasFDerivAt (fun y : SpatialCoordinates d =>
        (q : SpatialCoordinates d → ℝ) y) (PotentialField.deriv q x) x :=
      q.hasFDerivAt x
    show euclideanCoordDeriv i (fun y : SpatialCoordinates d => q y) x = _
    rw [euclideanCoordDeriv, hq.fderiv]
    rfl
  have hgrad : ∀ x : SpatialCoordinates d,
      euclideanGradient (fun y => a * Real.exp (q y - z)) x =
        a • (Real.exp (q x - z) • shellGradient q x) := by
    intro x
    have harg : HasFDerivAt (fun y : SpatialCoordinates d => q y - z)
        (PotentialField.deriv q x) x := by
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
        (q.hasFDerivAt x).sub (hasFDerivAt_const (x := x) (c := z))
    have hexdiff : Differentiable ℝ
        (fun y : SpatialCoordinates d => Real.exp (q y - z)) := by
      intro y
      have hargy : HasFDerivAt (fun y : SpatialCoordinates d => q y - z)
          (PotentialField.deriv q y) y := by
        simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
          (q.hasFDerivAt y).sub (hasFDerivAt_const (x := y) (c := z))
      exact ((Real.hasDerivAt_exp (q y - z)).comp_hasFDerivAt y hargy).differentiableAt
    have hexp : HasFDerivAt (fun y : SpatialCoordinates d => Real.exp (q y - z))
        (Real.exp (q x - z) • PotentialField.deriv q x) x := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_exp (q x - z)).comp_hasFDerivAt x harg
    have hexpgrad : euclideanGradient (fun y : SpatialCoordinates d =>
        Real.exp (q y - z)) x = Real.exp (q x - z) • shellGradient q x := by
      funext i
      show euclideanCoordDeriv i
        (fun y : SpatialCoordinates d => Real.exp (q y - z)) x = _
      rw [euclideanCoordDeriv, hexp.fderiv]
      rfl
    rw [euclideanGradient_const_mul hexdiff a x, hexpgrad]
  intro x
  have hr : 0 < Real.exp (q x - z) := Real.exp_pos _
  have hb_e : euclideanNorm (a • euclideanGradient (fun y => q y) x) ≤
      (d : ℝ) * (K * (1 + ‖x‖)) := by
    exact (euclideanNorm_le_dimension_mul_norm _).trans
      (mul_le_mul_of_nonneg_left (hbound x) (Nat.cast_nonneg d))
  rw [hgrad x]
  calc
    euclideanNorm (a • (Real.exp (q x - z) • shellGradient q x)) +
        a * Real.exp (q x - z) =
      Real.exp (q x - z) *
        (euclideanNorm (a • euclideanGradient (fun y => q y) x) + a) := by
          rw [hgradq x]
          simp only [euclideanNorm_smul, abs_of_pos ha, abs_of_pos hr]
          ring
    _ ≤ Real.exp (q x - z) * ((d : ℝ) * (K * (1 + ‖x‖)) + a) :=
      mul_le_mul_of_nonneg_left (add_le_add hb_e (le_refl a)) hr.le
    _ ≤ Real.exp (q x - z) * (((d : ℝ) * K + a) * (1 + ‖x‖)) := by
      gcongr
      nlinarith [norm_nonneg x, hK, ha]
    _ = ((d : ℝ) * K + a) * Real.exp (q x - z) * (1 + ‖x‖) := by ring

theorem aux_finiteDimensional_cutoff_full_coefficient_semigroup_native_datum
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (beta : BilateralField d) (N : ℕ)
    (q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (hq : cutoffPotential H beta N = fun x ↦ q x)
    (hnon : ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
          Homogenization.euclideanGradient (cutoffPotential H beta N) x‖ ≤
        K * (1 + ‖x‖)) :
    ∃ P : SubMarkovKernelSemigroup (SpatialCoordinates d),
      P.IsConservative ∧ P.IsFellerKernelSemigroup ∧
      ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (SpatialCoordinates d),
        (∀ mu, DenseRange (D.operator mu)) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (cutoffCoefficient M H beta N) (cutoffSpeedDensity M H beta N) D ∧
        ∀ (mu : Semigroup.PositiveShift)
          (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
          D.solution mu f x =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
              kernelIntegral (P (Real.toNNReal t)) f x := by
  obtain ⟨K, hK, hnon'⟩ := hnon
  let a : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
  let z : ℝ := (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  let c : SpatialCoordinates d → ℝ := fun x ↦ a * Real.exp (q x - z)
  let rho : SpatialCoordinates d → ℝ := fun x ↦ Real.exp (q x - z)
  have ha : 0 < a := inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  have hcpos : ∀ x, 0 < c x := fun x ↦ mul_pos ha (Real.exp_pos _)
  have hrhopos : ∀ x, 0 < rho x := fun x ↦ Real.exp_pos _
  have hqC1 : ContDiff ℝ 1 (fun x : SpatialCoordinates d ↦ q x) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one q
  have hcC1 : ContDiff ℝ 1 c := by
    dsimp [c]
    exact contDiff_const.mul ((hqC1.sub contDiff_const).exp)
  have hrhoC : Continuous rho := by
    dsimp [rho]
    exact ((hqC1.sub contDiff_const).exp).continuous
  have hcutc : cutoffCoefficient M H beta N = c := by
    funext x
    unfold cutoffCoefficient
    rw [hq]
  have hcutrho : cutoffSpeedDensity M H beta N = rho := by
    funext x
    unfold cutoffSpeedDensity
    rw [hq]
  have hbound : ∀ x : SpatialCoordinates d,
      ‖a • euclideanGradient (fun y => q y) x‖ ≤ K * (1 + ‖x‖) := by
    intro x
    have hx := hnon' x
    simpa only [a, hq] using hx
  have hgrowth_c : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤
      ((d : ℝ) * K + a) * rho x * (1 + ‖x‖) := by
    intro x
    have h := aux_finiteDimensional_cutoff_full_coefficient_semigroup_exp_growth
      q a z K ha hK hbound x
    simpa only [c, rho] using h
  obtain ⟨B, _⟩ :=
    aux_finiteDimensional_cutoff_full_coefficient_semigroup_cube_bounds
      hcC1.continuous hcpos hrhoC hrhopos
  have hcompact :=
    aux_finiteDimensional_cutoff_full_coefficient_semigroup_compact_solutions
      hd B hcC1 hcpos hrhopos (by positivity) hgrowth_c
  let R : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveC0Resolvent c rho :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveC0Resolvent.ofHasC0MassiveSolutions
      (aux_finiteDimensional_cutoff_full_coefficient_semigroup_c0_solutions B hcompact)
  have hdense0 :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.hasDenseMassiveResolventRange_of_contDiff
      B hcC1 hrhoC
  have hstrong :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange
      B hdense0
  obtain ⟨D, hDdense, hDweak⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_c0ResolventDatum_of_massiveC0Resolvent
      B R (hstrong R)
  have hK' : 0 ≤ (d : ℝ) * K + a := by positivity
  have hcons :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.isConservative_of_weakResolvent_linearGrowth
      B hcC1 hrhoC D hDdense hDweak (fun x ↦ (hcpos x).le) hK' hgrowth_c
  obtain ⟨P, hPcons, hPfeller, hLap⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_conservative_fellerKernelSemigroup_of_c0ResolventDatum
      D hDdense hcons
  refine ⟨P, hPcons, hPfeller, D, hDdense, ?_, ?_⟩
  · simpa only [hcutc, hcutrho] using hDweak
  · exact hLap


theorem finiteDimensional_cutoff_full_coefficient_semigroup
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        M.delta ≤ delta0 →
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
  obtain ⟨delta0, hdelta0, hright⟩ :=
    finiteDimensional_cutoff_nonexplosion hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M H hH hdelta hnon
  classical
  letI : NeZero d := ⟨by omega⟩
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
  obtain ⟨C, hC, hinfrared⟩ := lem_infrared hd
  obtain ⟨G, hGmeas, hGobs, hGgood, hGrest⟩ := hinfrared M μ rfl
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  have hπmeas : Measurable π := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hmp : MeasurePreserving π μ (chaosSampleLaw M).toMeasure := by
    refine ⟨hπmeas, ?_⟩
    simpa only [π, μ, chaosSampleLaw, chaosRootFieldLaw, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hnative : ∀ᵐ omega ∂μ,
      Tendsto (fun L => infraredPartialSum (π omega) L) atTop
        (nhds (forget (G omega))) := by
    filter_upwards [hGgood] with omega homega
    simpa only [π, forget] using
      (aux_finiteDimensional_cutoff_full_coefficient_semigroup_native_tendsto
        omega (G omega) homega.2.1)
  have hHpull : ∀ᵐ omega ∂μ,
      Tendsto (fun L => infraredPartialSum (π omega) L) atTop
        (nhds (H (π omega))) := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hH.2] with omega homega
    simpa only [Function.comp_apply] using homega
  have hnativeEq : ∀ᵐ omega ∂μ, H (π omega) = forget (G omega) := by
    filter_upwards [hnative, hHpull] with omega hnative' hH'
    exact tendsto_nhds_unique hH' hnative'
  have hforget_inj : Function.Injective forget := by
    intro g g' hgg'
    apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
    intro x
    exact congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x) hgg'
  have hforgetEmb : MeasurableEmbedding forget :=
    Measurable.measurableEmbedding forget.continuous.measurable hforget_inj
  have hregSet : MeasurableSet {beta : BilateralField d |
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, H beta = forget g} := by
    have heq : {beta : BilateralField d |
        ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, H beta = forget g} =
        H ⁻¹' Set.range forget := by
      ext beta
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, hg.symm⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, hg.symm⟩
    rw [heq]
    exact hforgetEmb.measurableSet_range.preimage hH.1
  have hreg : ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, H beta = forget g := by
    rw [← hmp.map_eq]
    apply (ae_map_iff hπmeas.aemeasurable hregSet).2
    filter_upwards [hnativeEq] with omega hEq
    exact ⟨G omega, hEq⟩
  have hcoord : ∀ j : ℤ, ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, beta j = forget g := by
    intro j
    have hcoordSet : MeasurableSet {beta : BilateralField d |
        ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, beta j = forget g} := by
      have heq : {beta : BilateralField d |
          ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, beta j = forget g} =
          (fun beta => beta j) ⁻¹' Set.range forget := by
        ext beta
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
        constructor
        · rintro ⟨g, hg⟩
          exact ⟨g, hg.symm⟩
        · rintro ⟨g, hg⟩
          exact ⟨g, hg.symm⟩
      rw [heq]
      exact hforgetEmb.measurableSet_range.preimage (measurable_pi_apply j)
    rw [← hmp.map_eq]
    apply (ae_map_iff hπmeas.aemeasurable hcoordSet).2
    exact Filter.Eventually.of_forall fun omega ↦ by
      refine ⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale
          ((3 : ℝ) ^ (-j)) (omega j), ?_⟩
      ext x
      rfl
  have hcoordAll : ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure,
      ∀ j : ℤ, ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        beta j = forget g :=
    ae_all_iff.2 hcoord
  let Good : ℕ → BilateralField d → Prop := fun N beta ↦
    ∃ P : SubMarkovKernelSemigroup (SpatialCoordinates d),
      P.IsConservative ∧ P.IsFellerKernelSemigroup ∧
      ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
        (SpatialCoordinates d),
        (∀ mu, DenseRange (D.operator mu)) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (cutoffCoefficient M H beta N) (cutoffSpeedDensity M H beta N) D ∧
        ∀ (mu : Semigroup.PositiveShift)
          (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
          (x : SpatialCoordinates d),
          D.solution mu f x =
            ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
              kernelIntegral (P (Real.toNNReal t)) f x
  let PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d) :=
    fun N beta => if h : Good N beta then Classical.choose h else idSemigroup
  have hPNcons : ∀ N beta, (PN N beta).IsConservative := by
    intro N beta
    by_cases h : Good N beta
    · simpa only [PN, dif_pos h] using (Classical.choose_spec h).1
    · simpa only [PN, dif_neg h] using isConservative_idSemigroup
  have hPNfeller : ∀ N beta, (PN N beta).IsFellerKernelSemigroup := by
    intro N beta
    by_cases h : Good N beta
    · simpa only [PN, dif_pos h] using (Classical.choose_spec h).2.1
    · simpa only [PN, dif_neg h] using isFellerKernelSemigroup_idSemigroup
  refine ⟨PN, hPNcons, hPNfeller, ?_⟩
  filter_upwards [hreg, hcoordAll, hnon] with beta hbeta hcoords hnb
  intro N
  obtain ⟨g, hg⟩ := hbeta
  let φ : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun j ↦
    Classical.choose (hcoords (-(Int.ofNat j)))
  have hφ : ∀ j : ℕ, beta (-(Int.ofNat j)) = forget (φ j) := by
    intro j
    exact Classical.choose_spec (hcoords (-(Int.ofNat j)))
  let q : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add g
      (aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum φ N)
  have hq : cutoffPotential H beta N = fun x ↦ q x := by
    funext x
    unfold cutoffPotential
    have hgx : H beta x = forget g x := congrArg
      (fun F : C(SpatialCoordinates d, ℝ) => F x) hg
    calc
      H beta x + ∑ j ∈ Finset.range (N + 1), beta (-(Int.ofNat j)) x =
          forget g x + ∑ j ∈ Finset.range (N + 1), forget (φ j) x := by
            rw [hgx]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            exact congrArg (fun F : C(SpatialCoordinates d, ℝ) => F x) (hφ j)
      _ = q x := by
        simp [forget, q, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply,
          aux_finiteDimensional_cutoff_full_coefficient_semigroup_potentialSum_apply]
  obtain ⟨P, hPcons, hPfeller, D, hDdense, hDweak, hLap⟩ :=
    aux_finiteDimensional_cutoff_full_coefficient_semigroup_native_datum
      hd M H beta N q hq (hnb N)
  have hGood : Good N beta := by
    exact ⟨P, hPcons, hPfeller, D, hDdense, hDweak, hLap⟩
  obtain ⟨hPcons', hPfeller', D', hDdense', hDweak', hLap'⟩ :=
    Classical.choose_spec hGood
  refine ⟨D', hDdense', hDweak', ?_⟩
  simpa only [PN, dif_pos hGood] using hLap'
end Paper
