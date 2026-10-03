module

public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_measurable_semigroup
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.resolvent_datum
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff_nonexplosion
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationResolventSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKSemigroupIdentification
public import MarkovProcess.Parameterized.ContinuousProcessProperties
public import MarkovProcess.Trajectory.FellerFiniteMarginals

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_finiteDimensional_cutoff_path_kernel_potential
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        ∀ x, cutoffPotential H omega N x = g x := by
  classical
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
  let F : NativeBilateralPotentialSample d →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
    fun omega k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (omega (k : ℤ))
  have hFmeas : Measurable F := by
    apply measurable_pi_lambda _
    intro k
    exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).comp
      (measurable_pi_apply (k : ℤ))
  have hFmap : Measure.map F μ = M.P.toMeasure := by
    let μ0 : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
    let S : Set ℤ := {j | 0 ≤ j}
    let e : ℕ ≃ {j : ℤ // j ∈ S} :=
      { toFun := fun k => ⟨(k : ℤ), by simp [S]⟩
        invFun := fun j => j.1.toNat
        left_inv := by intro k; simp
        right_inv := by
          intro j
          apply Subtype.ext
          simp [S, Int.toNat_of_nonneg j.2] }
    let R : (ℤ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) →
        ({j : ℤ // j ∈ S} → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      S.restrict
    let E : ({j : ℤ // j ∈ S} → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) →
        (ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      fun x k => x (e k)
    let T : (ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) →
        (ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      fun x k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (x k)
    have hR : Measurable R := by
      exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
    have hE : Measurable E := by
      exact measurable_pi_lambda fun k => measurable_pi_apply (e k)
    have hT : Measurable T := by
      exact measurable_pi_lambda fun k =>
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).comp
          (measurable_pi_apply k)
    have hrestrict :
        Measure.map R μ = Measure.infinitePi
          (fun _ : {j : ℤ // j ∈ S} => μ0) := by
      simpa only [R, μ, μ0] using!
        (Measure.infinitePi_map_restrict' (μ := fun _ : ℤ => μ0) (I := S))
    have hreindex :
        Measure.map E (Measure.infinitePi
          (fun _ : {j : ℤ // j ∈ S} => μ0)) =
          Measure.infinitePi (fun _ : ℕ => μ0) := by
      have h := Measure.infinitePi_map_piCongrLeft
        (μ := fun _ : ℕ => μ0) e.symm
      simpa only [E, e] using! h
    have hscale :
        Measure.map T (Measure.infinitePi (fun _ : ℕ => μ0)) =
          Measure.infinitePi (fun k : ℕ =>
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure.map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)) := by
      rw [Measure.infinitePi_map_pi
        (μ := fun _ : ℕ => μ0)
        (f := fun k : ℕ =>
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)]
    have hprod : M.P.toMeasure = Measure.infinitePi
        (fun k : ℕ =>
          (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure) := by
      have hi :=
        (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
          (P := M.P.toMeasure)
          (X := fun k (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) => omega k)
          (fun k => measurable_pi_apply k)).mp M.shellPrefix.independent
      simpa only [Measure.map_id'] using! hi
    have hcomp : F = T ∘ E ∘ R := by
      funext omega k
      rfl
    calc
      Measure.map F μ = Measure.map (T ∘ E ∘ R) μ := by rw [hcomp]
      _ = Measure.map T (Measure.map E (Measure.map R μ)) := by
        calc
          Measure.map (T ∘ E ∘ R) μ =
              Measure.map T (Measure.map (E ∘ R) μ) :=
            (Measure.map_map hT (hE.comp hR)).symm
          _ = Measure.map T (Measure.map E (Measure.map R μ)) := by
            rw [Measure.map_map hE hR]
      _ = M.P.toMeasure := by
        rw [hrestrict, hreindex, hscale]
        calc
          Measure.infinitePi (fun k : ℕ =>
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure.map
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)) =
              Measure.infinitePi (fun k : ℕ =>
                (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure) := by
            congr 1
            funext k
            have hm := congrArg
              (fun Q : ProbabilityMeasure
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) => Q.toMeasure)
              (M.shellPrefix.marginal_scaling k)
            calc
              Measure.map
                  (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
                  (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure =
                  ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
                    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)).toMeasure := rfl
              _ = (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := hm.symm
          _ = M.P.toMeasure := hprod.symm
  obtain ⟨C0, hC0, hlem⟩ := lem_infrared hd
  obtain ⟨Hn, hHnmeas, hHnObs, hHnAE, hHnLp, hHnExp⟩ := hlem M μ rfl
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
  have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using!
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hπinj : Function.Injective π := by
    have hforgetinj : Function.Injective forget := by
      intro g h hgh
      apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
      intro x
      exact congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x) hgh
    intro omega omega' heq
    funext j
    have hscaleinj : Function.Injective (layerScaling d j) := by
      intro f g hfg
      ext x
      have hx := congrArg (fun q : C(SpatialCoordinates d, ℝ) =>
        q ((3 : ℝ) ^ j • x)) hfg
      change f ((3 : ℝ) ^ (-j) • ((3 : ℝ) ^ j • x)) =
        g ((3 : ℝ) ^ (-j) • ((3 : ℝ) ^ j • x)) at hx
      have hp : (3 : ℝ) ^ (-j) * (3 : ℝ) ^ j = 1 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        simp
      have hp' : ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ j = 1 :=
        inv_mul_cancel₀ (by positivity)
      simpa [smul_smul, hp, hp'] using! hx
    apply hforgetinj
    apply hscaleinj
    exact congrFun heq j
  have hπemb : MeasurableEmbedding π := hπmeas.measurableEmbedding hπinj
  have hHβ : ∀ᵐ omega ∂μ,
      Tendsto (fun L => infraredPartialSum (π omega) L) atTop
        (nhds (H (π omega))) := by
    have h0 := hH.2
    rw [← hπmeasure] at h0
    exact ae_of_ae_map hπmeas.aemeasurable h0
  have hsum : ∀ omega L,
      infraredPartialSum (π omega) L =
        forget (positiveAnchoredInfraredTruncation omega L) := by
    intro omega L
    have hπpos : ∀ n,
        forget (positiveScaledNativeLayer omega n) =
          π omega (Int.ofNat (n + 1)) := by
      intro n
      ext x
      change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • x) =
        omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • x)
      congr 1
    induction L with
    | zero =>
        simp [infraredPartialSum, positiveAnchoredInfraredTruncation, forget,
          zeroNativePotentialField]
        rfl
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih, ← hπpos L]
        ext x
        change (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0) =
          (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0)
        rfl
  have hnative_eq : ∀ᵐ omega ∂μ, ∀ x,
      H (π omega) x = (forget (Hn omega)) x := by
    filter_upwards [hHβ, hHnAE] with omega hbeta hnative
    intro x
    have hbeta_x :=
      ((continuous_eval_const x).tendsto (H (π omega))).comp hbeta
    have hbeta_x' : Tendsto
        (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x)
        atTop (nhds (H (π omega) x)) := by
      change Tendsto (fun L => (infraredPartialSum (π omega) L) x) atTop
        (nhds (H (π omega) x)) at hbeta_x
      rw [show (fun L => (infraredPartialSum (π omega) L) x) =
          (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x) by
        funext L
        exact congrArg (fun q : C(SpatialCoordinates d, ℝ) => q x)
          (hsum omega L)] at hbeta_x
      exact hbeta_x
    have hpt : Tendsto
        (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x)
        atTop (nhds ((forget (Hn omega)) x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun L => norm_nonneg _)
      · intro L
        let q := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (Hn omega))
        change ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
            (forget (Hn omega)) x‖ ≤ compactPotentialC1Norm
              (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) q
        rw [show (forget (positiveAnchoredInfraredTruncation omega L)) x -
            (forget (Hn omega)) x = q x by
              change (positiveAnchoredInfraredTruncation omega L) x - (Hn omega) x = q x
              dsimp [q]
              ring]
        unfold compactPotentialC1Norm
        exact (ContinuousMap.norm_coe_le_norm
          (⟨fun z : (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) =>
              q z.1, q.1.1.continuous.comp continuous_subtype_val⟩ :
            C((⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)), ℝ))
          ⟨x, Set.mem_singleton x⟩).trans
          (le_add_of_nonneg_right (by positivity))
      · simpa only [sub_zero] using!
          hnative.2.1 (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d))
    exact tendsto_nhds_unique hbeta_x' hpt
  have hnative_final : ∀ᵐ omega ∂μ, ∀ N : ℕ,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        ∀ x, cutoffPotential H (π omega) N x = g x := by
    filter_upwards [hnative_eq] with omega hEq
    intro N
    let negField : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun j =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3 : ℝ) ^ j)
        (omega (-(Int.ofNat j)))
    let G : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun N =>
      Nat.rec
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add (Hn omega) (negField 0))
        (fun n g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add g (negField (n + 1))) N
    refine ⟨G N, ?_⟩
    have hnegfun : ∀ j : ℕ,
        (fun x => (π omega) (-(Int.ofNat j)) x) = fun x => negField j x := by
      intro j
      funext x
      simp only [π, negField, layerScaling,
        ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
        neg_neg, Int.ofNat_eq_natCast, zpow_natCast]
      rfl
    have hfun : (fun y => H (π omega) y) = fun y => (Hn omega) y := by
      funext y
      exact hEq y
    have hcut : ∀ N,
        cutoffPotential H (π omega) N = fun x => G N x := by
      intro N
      induction N with
      | zero =>
          funext x
          calc
            cutoffPotential H (π omega) 0 x = H (π omega) x + (π omega) 0 x := by
              simp [cutoffPotential]
            _ = (Hn omega) x + (negField 0) x := by
              rw [congrFun hfun x]
              have h0 := congrFun (hnegfun 0) x
              exact congrArg (fun z => (Hn omega) x + z)
                (by simpa only [Int.ofNat_zero, neg_zero] using! h0)
            _ = G 0 x := by rfl
      | succ N ih =>
          funext x
          have hstep : cutoffPotential H (π omega) (N + 1) x =
              cutoffPotential H (π omega) N x +
                (π omega) (-(Int.ofNat (N + 1))) x := by
            change H (π omega) x +
                (∑ j ∈ Finset.range ((N + 1) + 1), (π omega) (-(Int.ofNat j)) x) =
              (H (π omega) x +
                (∑ j ∈ Finset.range (N + 1), (π omega) (-(Int.ofNat j)) x)) +
                (π omega) (-(Int.ofNat (N + 1))) x
            rw [Finset.sum_range_succ]
            ring
          calc
            cutoffPotential H (π omega) (N + 1) x =
                cutoffPotential H (π omega) N x +
                  (π omega) (-(Int.ofNat (N + 1))) x := hstep
            _ = (G N) x + (π omega) (-(Int.ofNat (N + 1))) x := by
              rw [congrFun ih x]
            _ = (G (N + 1)) x := by
              rw [show G (N + 1) =
                SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add (G N) (negField (N + 1)) by rfl]
              have hn := congrFun (hnegfun (N + 1)) x
              simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply] using!
                congrArg (fun z => (G N) x + z) hn
    exact congrFun (hcut N)
  rw [← hπmeasure]
  exact hπemb.ae_map_iff.mpr hnative_final

theorem aux_finiteDimensional_cutoff_path_kernel_support
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
      (SpatialCoordinates d))
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (hg : ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      ∀ x, cutoffPotential H omega N x = g x)
    (hgrowth : ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
          Homogenization.euclideanGradient (cutoffPotential H omega N) x‖ ≤
        K * (1 + ‖x‖)) :
    Kernel.IsSupportedOnContinuousPaths
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory
        (D.fellerKernelSemigroup hdense) hcons
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding) := by
  obtain ⟨g, hgc⟩ := hg
  obtain ⟨K, hK, hgrowth⟩ := hgrowth
  let a : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
  let c : SpatialCoordinates d → ℝ := cutoffCoefficient M H omega N
  let rho : SpatialCoordinates d → ℝ := cutoffSpeedDensity M H omega N
  have ha : 0 < a := by
    dsimp [a]
    exact SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hpot : cutoffPotential H omega N = fun x => g x := by
    funext x
    exact hgc x
  have hcform : c = fun x => a⁻¹ * Real.exp (g x -
      (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    funext x
    simp only [c, a, cutoffCoefficient]
    rw [hpot]
  have hc : ContDiff ℝ 1 c := by
    rw [hcform]
    exact contDiff_const.mul
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one g).sub contDiff_const).exp
  have hrho : Continuous rho := by
    unfold rho cutoffSpeedDensity
    rw [hpot]
    fun_prop
  have hcpos : ∀ x, 0 < c x := by
    intro x
    dsimp [c]
    exact mul_pos (inv_pos.mpr ha) (Real.exp_pos _)
  have hrhopos : ∀ x, 0 < rho x := by
    intro x
    dsimp [rho, cutoffSpeedDensity]
    rw [show cutoffPotential H omega N x = g x from hgc x]
    exact Real.exp_pos _
  have hB : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho :=
    aux_resolvent_datum_cube_bounds hc.continuous hrho hcpos hrhopos
  have hbound : ∀ x,
      Homogenization.euclideanNorm
          (Homogenization.euclideanGradient (fun y => g y) x) ≤
        (d : ℝ) * a * K * (1 + ‖x‖) := by
    intro x
    have hx := hgrowth x
    rw [hpot] at hx
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.euclideanGradient_potentialField] at hx
    change ‖a⁻¹ • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x‖ ≤
      K * (1 + ‖x‖) at hx
    have hxeu : Homogenization.euclideanNorm
          (a⁻¹ • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤
        (d : ℝ) * (K * (1 + ‖x‖)) := by
      exact (Homogenization.euclideanNorm_le_dimension_mul_norm _).trans
        (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg d))
    calc
      Homogenization.euclideanNorm
          (Homogenization.euclideanGradient (fun y => g y) x) =
          a * Homogenization.euclideanNorm
            (a⁻¹ • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) := by
              rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.euclideanGradient_potentialField]
              calc
                Homogenization.euclideanNorm
                    (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) =
                    Homogenization.euclideanNorm
                      (a • (a⁻¹ • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x)) := by
                        rw [smul_smul]
                        rw [mul_inv_cancel₀ ha.ne', one_smul]
                _ = a * Homogenization.euclideanNorm
                    (a⁻¹ • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) := by
                      rw [Homogenization.euclideanNorm_smul, abs_of_pos ha]
      _ ≤ a * ((d : ℝ) * (K * (1 + ‖x‖))) :=
        mul_le_mul_of_nonneg_left hxeu ha.le
      _ = (d : ℝ) * a * K * (1 + ‖x‖) := by ring
  have hgrowth' : ∀ x,
      Homogenization.euclideanNorm
          (Homogenization.euclideanGradient c x) + c x ≤
        ((d : ℝ) * K + a⁻¹) * rho x * (1 + ‖x‖) := by
    intro x
    have hgrad : Homogenization.euclideanGradient c x =
        (a⁻¹ * Real.exp (-(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) •
          (Real.exp (g x) • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) := by
      rw [hcform]
      calc
        Homogenization.euclideanGradient
            (fun y => a⁻¹ * Real.exp (g y -
              (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) x =
            a⁻¹ • Homogenization.euclideanGradient
              (fun y => Real.exp (g y -
                (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) x :=
          SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.euclideanGradient_const_mul
            (((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one g).sub
              contDiff_const).exp.differentiable (by norm_num)) _ _
        _ = (a⁻¹ * Real.exp (-(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) •
              Real.exp (g x) • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x := by
          have hexp :
              (fun y => Real.exp (g y -
                (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
              (fun y => Real.exp (-(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                Real.exp (g y)) := by
            funext y
            calc
              Real.exp (g y - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
                  Real.exp (g y) /
                    Real.exp ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
                Real.exp_sub _ _
              _ = Real.exp (-(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                    Real.exp (g y) := by
                have hC : -(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
                    -((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by ring
                rw [hC, Real.exp_neg]
                ring
          calc
            a⁻¹ • Homogenization.euclideanGradient
                (fun y => Real.exp (g y -
                  (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) x =
                a⁻¹ • (Real.exp (-(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) •
                  Homogenization.euclideanGradient (fun y => Real.exp (g y)) x) := by
                    rw [hexp,
                      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.euclideanGradient_const_mul
                        ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one g).exp.differentiable (by norm_num))]
            _ = (a⁻¹ * Real.exp (-(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) •
                  Real.exp (g x) • SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x := by
                    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.euclideanGradient_exp_potentialField]
                    rw [smul_smul]
    have hnorm : Homogenization.euclideanNorm
          (Homogenization.euclideanGradient c x) =
        c x * Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) := by
      rw [hgrad, Homogenization.euclideanNorm_smul,
        abs_of_pos (mul_pos (inv_pos.mpr ha) (Real.exp_pos _)),
        Homogenization.euclideanNorm_smul, abs_of_pos (Real.exp_pos _)]
      rw [hcform]
      dsimp
      have hC : -(N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
          -((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by ring
      rw [hC, Real.exp_neg, Real.exp_sub]
      field_simp
    rw [hnorm]
    have hcrho : c x = a⁻¹ * rho x := by
      simp only [c, rho, a, cutoffCoefficient, cutoffSpeedDensity]
    have hgrad' := hbound x
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.euclideanGradient_potentialField] at hgrad'
    rw [hcrho]
    have hcx : 0 ≤ rho x := (hrhopos x).le
    have hbn : 0 ≤ 1 + ‖x‖ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgrad'
      (mul_nonneg (inv_pos.mpr ha).le hcx)
    calc
      a⁻¹ * rho x * Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) + a⁻¹ * rho x
          ≤ a⁻¹ * rho x * ((d : ℝ) * a * K * (1 + ‖x‖)) + a⁻¹ * rho x := by
            exact add_le_add hmul (le_refl _)
      _ = rho x * ((d : ℝ) * K * (1 + ‖x‖) + a⁻¹) := by
            field_simp
      _ ≤ rho x * (((d : ℝ) * K + a⁻¹) * (1 + ‖x‖)) := by
            apply mul_le_mul_of_nonneg_left _ hcx
            have hi := mul_le_mul_of_nonneg_left
              (show (1 : ℝ) ≤ 1 + ‖x‖ by linarith [norm_nonneg x]) (inv_pos.mpr ha).le
            nlinarith
      _ = ((d : ℝ) * K + a⁻¹) * rho x * (1 + ‖x‖) := by ring
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.supportedOnContinuousPaths_of_weakResolvent_linearGrowth
    hB hc hrho D hdense hD (fun x => (hcpos x).le) hcons
      (add_nonneg (mul_nonneg (Nat.cast_nonneg d) hK) (inv_pos.mpr ha).le) hgrowth'

theorem aux_finiteDimensional_cutoff_path_kernel_resolvent
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsFellerKernelSemigroup)
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
      (SpatialCoordinates d))
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hLap : ∀ (mu : Semigroup.PositiveShift)
      (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
      (x : SpatialCoordinates d),
      D.solution mu f x =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (P (Real.toNNReal t)) f x) :
    P = D.fellerKernelSemigroup hdense := by
  let hD : (D.fellerKernelSemigroup hdense).IsFellerKernelSemigroup :=
    D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  let μ : Semigroup.PositiveShift := ⟨1, by norm_num⟩
  have hres : hP.c0Semigroup.resolvent μ = hD.c0Semigroup.resolvent μ := by
    apply ContinuousLinearMap.ext
    intro f
    ext x
    calc
      hP.c0Semigroup.resolvent μ f x =
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) *
            kernelIntegral (P (Real.toNNReal t)) f x :=
        hP.resolvent_apply_apply μ f x
      _ = D.solution μ f x := (hLap μ f x).symm
      _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) *
            kernelIntegral ((D.fellerKernelSemigroup hdense) (Real.toNNReal t)) f x :=
        D.solution_eq_laplace hdense μ f x
      _ = hD.c0Semigroup.resolvent μ f x :=
        (hD.resolvent_apply_apply μ f x).symm
  have hsem : hP.c0Semigroup = hD.c0Semigroup :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKSemigroupIdentification.sccs_ext_of_resolvent_eq
      hP.c0Semigroup hD.c0Semigroup μ hres
  refine SubMarkovKernelSemigroup.ext fun t => ?_
  refine Kernel.ext fun x => ?_
  haveI : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure ((D.fellerKernelSemigroup hdense) t x) :=
    ⟨lt_of_le_of_lt
      ((D.fellerKernelSemigroup hdense).measure_univ_le_one t x) ENNReal.one_lt_top⟩
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  let g : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hgf : ∀ y, g y = f y := fun y =>
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f y
  have hleft : ∫ y, f y ∂P t x = ∫ y, g y ∂P t x := by
    simp only [hgf]
  have hright :
      ∫ y, f y ∂(D.fellerKernelSemigroup hdense) t x =
        ∫ y, g y ∂(D.fellerKernelSemigroup hdense) t x := by
    simp only [hgf]
  rw [hleft, hright]
  have hop := congrArg
    (fun S : Semigroup.StronglyContinuousContractionSemigroup
      (ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ) => S t g x) hsem
  simpa only [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.c0Semigroup_apply_apply, kernelIntegral]
    using! hop

theorem aux_finiteDimensional_cutoff_path_kernel_prefix_bound
    (I : Finset DenseTime) :
    ∃ n, SubMarkovKernelSemigroup.denseTimePhysicalSet I ⊆
      SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro t ht
      simp only [SubMarkovKernelSemigroup.denseTimePhysicalSet,
        Finset.map_empty, Finset.notMem_empty] at ht
  | @insert a I ha ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max n (DenseTime.enumeration.symm a + 1), ?_⟩
      intro t ht
      rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ht
      obtain ⟨r, hr, rfl⟩ := ht
      rw [SubMarkovKernelSemigroup.denseTimePhysicalPrefix, Finset.mem_map]
      refine ⟨r, ?_, rfl⟩
      rw [CountableEnumeration.mem_prefix_iff]
      rw [Finset.mem_insert] at hr
      rcases hr with rfl | hr
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
      · have hmem : DenseTime.castOrderEmbedding r ∈
            SubMarkovKernelSemigroup.denseTimePhysicalSet I := by
          rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
          exact ⟨r, hr, rfl⟩
        have hprefix := hn hmem
        rw [SubMarkovKernelSemigroup.denseTimePhysicalPrefix, Finset.mem_map] at hprefix
        obtain ⟨r', hr', heq⟩ := hprefix
        have hrr' : r = r' := DenseTime.castOrderEmbedding.injective heq.symm
        subst r'
        rw [CountableEnumeration.mem_prefix_iff] at hr'
        exact Nat.lt_of_lt_of_le hr' (le_max_left _ _)

theorem aux_finiteDimensional_cutoff_path_kernel_finiteDense
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (default : DiffusionPath d)
    (hsupport : Kernel.IsSupportedOnContinuousPaths
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory P hP
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding))
    (I : Finset DenseTime) :
    (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
        (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalSet I) ↦ path t) =
      SubMarkovKernelSemigroup.finiteSetKernel P
        (SubMarkovKernelSemigroup.denseTimePhysicalSet I) := by
  classical
  obtain ⟨n, hsubset⟩ :=
    aux_finiteDimensional_cutoff_path_kernel_prefix_bound I
  let equiv : Fin n ≃
      SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n :=
    Equiv.ofBijective
      (fun i ↦ ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration i), by
        rw [SubMarkovKernelSemigroup.denseTimePhysicalPrefix, Finset.mem_map]
        exact ⟨DenseTime.enumeration i, by
          rw [CountableEnumeration.mem_prefix_iff, DenseTime.enumeration.symm_apply_apply]
          exact i.isLt, rfl⟩⟩)
      ⟨by
        intro i j hij
        apply Fin.ext
        apply DenseTime.enumeration.injective
        apply DenseTime.castOrderEmbedding.injective
        exact congrArg Subtype.val hij,
       by
        intro t
        have ht := t.property
        change t.val ∈ (CountableEnumeration.prefix DenseTime.enumeration n).map
          DenseTime.castOrderEmbedding.toEmbedding at ht
        rw [Finset.mem_map] at ht
        obtain ⟨r, hr, hrt⟩ := ht
        let i : Fin n := ⟨DenseTime.enumeration.symm r, by
          rw [CountableEnumeration.mem_prefix_iff] at hr
          exact hr⟩
        refine ⟨i, Subtype.ext ?_⟩
        change DenseTime.castOrderEmbedding (DenseTime.enumeration i) = t
        rw [show DenseTime.enumeration i = r by
          exact DenseTime.enumeration.apply_symm_apply r]
        exact hrt⟩
  let prefixPath : (Fin n → SpatialCoordinates d) →
      SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n → SpatialCoordinates d :=
    fun path t ↦ path (equiv.symm t)
  have hleft :
      prefixPath ∘
          (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
            ContinuousPath.denseRestriction) =
        (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalPrefix
          DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t) := by
    funext path t
    change path (DenseTime.castOrderEmbedding
      (DenseTime.enumeration (equiv.symm t))) = path t
    exact congrArg path (congrArg Subtype.val (equiv.apply_symm_apply t))
  have hright :
      prefixPath ∘ SubMarkovKernelSemigroup.denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n = id := by
    funext path t
    change path (equiv (equiv.symm t)) = path t
    rw [equiv.apply_symm_apply]
  have hprefixPath_meas : Measurable prefixPath :=
    measurable_pi_iff.mpr fun t =>
      measurable_pi_apply (X := fun _ => SpatialCoordinates d) (equiv.symm t)
  have hrestrictPrefix_meas : Measurable
      (Finset.restrict₂ (π := fun _ ↦ SpatialCoordinates d) hsubset ∘ prefixPath) :=
    (Finset.measurable_restrict₂ (X := fun _ ↦ SpatialCoordinates d) hsubset).comp
      hprefixPath_meas
  have htraj_meas : Measurable
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix
          DenseTime.enumeration n ∘ ContinuousPath.denseRestriction) :=
    (SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix
      (α := SpatialCoordinates d) DenseTime.enumeration n).comp
      ContinuousPath.measurable_denseRestriction
  have hreindex_meas : Measurable
      (SubMarkovKernelSemigroup.denseTimePrefixReindex DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n) :=
    SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex
      (α := SpatialCoordinates d) DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n
  let kappa := SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory P hP
    DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          ContinuousPath.denseRestriction = kappa := by
    exact Kernel.IsSupportedOnContinuousPaths.map_denseRestriction kappa hsupport default
  have hpref :
      (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
            ContinuousPath.denseRestriction) =
        SubMarkovKernelSemigroup.denseTimePrefixKernel P DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n := by
    rw [Kernel.map_comp_right]
    · rw [hback]
      exact SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_prefix P hP
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding n
    · exact ContinuousPath.measurable_denseRestriction
    · exact SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix
        (α := SpatialCoordinates d) DenseTime.enumeration n
  have hfun :
      (fun path : DiffusionPath d ↦
        fun t : SubMarkovKernelSemigroup.denseTimePhysicalSet I ↦ path t) =
      Finset.restrict₂ (π := fun _ ↦ SpatialCoordinates d) hsubset ∘
        (fun path : DiffusionPath d ↦
          fun t : SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n ↦ path t) := by
    rfl
  have hphysical :
      (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n) ↦ path t) =
        SubMarkovKernelSemigroup.finiteSetKernel P
          (SubMarkovKernelSemigroup.denseTimePhysicalPrefix DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding n) := by
    rw [← hleft, Kernel.map_comp_right]
    · rw [hpref, SubMarkovKernelSemigroup.denseTimePrefixKernel_eq_map,
        ← Kernel.map_comp_right]
      · rw [hright, Kernel.map_id]
      · exact SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex
          (α := SpatialCoordinates d) DenseTime.enumeration
          DenseTime.castOrderEmbedding.toEmbedding n
      · exact hprefixPath_meas
    · exact htraj_meas
    · exact hprefixPath_meas
  rw [hfun, Kernel.map_comp_right]
  · rw [hphysical]
    exact (hP.finiteSetKernel_map_restrict₂ P hsubset).symm
  · apply measurable_pi_iff.mpr
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) (t : NNReal)
  · exact Finset.measurable_restrict₂ (X := fun _ ↦ SpatialCoordinates d) hsubset

theorem aux_finiteDimensional_cutoff_path_kernel_fdd
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup)
    (default : DiffusionPath d)
    (hsupport : Kernel.IsSupportedOnContinuousPaths
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory P hP
        DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding))
    (I : Finset NNReal) :
    (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
        (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I := by
  classical
  obtain ⟨q, hq⟩ := exists_denseTime_finset_seq_tendsto I
  let K := SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default
  have hmarkovK : IsMarkovKernel K := by infer_instance
  have hmarkovFinite : IsMarkovKernel (SubMarkovKernelSemigroup.finiteSetKernel P I) :=
    hP.isMarkovKernel_finiteSetKernel P I
  apply Kernel.map_finiteEvaluation_eq_of_integral_tendsto
    K hmarkovK
      (fun k ↦ SubMarkovKernelSemigroup.finiteDenseApproximationKernel P (q k))
      (SubMarkovKernelSemigroup.finiteSetKernel P I) hmarkovFinite
      (fun t : I ↦ (t : NNReal))
      (fun k t ↦ DenseTime.castOrderEmbedding (q k t)) hq
  · intro k
    let evalPhysical : DiffusionPath d →
        SubMarkovKernelSemigroup.finiteDenseApproximationPhysicalSet (q k) →
          SpatialCoordinates d := fun path t ↦ path t
    have hevalPhysical : Measurable evalPhysical := by
      rw [measurable_pi_iff]
      intro t
      exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) t
    have hcomp :
        SubMarkovKernelSemigroup.finiteDenseApproximationReindex (γ := SpatialCoordinates d)
            (q k) ∘ evalPhysical =
          ContinuousPath.finiteEvaluation
            (fun t : I ↦ DenseTime.castOrderEmbedding (q k t)) := by
      rfl
    rw [← hcomp, Kernel.map_comp_right]
    · have hrational := aux_finiteDimensional_cutoff_path_kernel_finiteDense
        P hP default hsupport
        (SubMarkovKernelSemigroup.finiteDenseApproximationIndexSet (q k))
      change (SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default).map
          evalPhysical =
        SubMarkovKernelSemigroup.finiteSetKernel P
          (SubMarkovKernelSemigroup.finiteDenseApproximationPhysicalSet (q k)) at hrational
      rw [hrational]
      rfl
    · exact hevalPhysical
    · exact SubMarkovKernelSemigroup.measurable_finiteDenseApproximationReindex (q k)
  · intro x f
    exact hF.tendsto_integral_compactlySupported_finiteDenseApproximationKernel
      hP q hq f x

theorem aux_finiteDimensional_cutoff_path_kernel_trajectory_congr
    {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
    [Nonempty alpha]
    (P Q : SubMarkovKernelSemigroup alpha) (hPQ : P = Q)
    (hP : P.IsConservative) (hQ : Q.IsConservative)
    (default : ContinuousPath alpha) :
    SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory P hP default =
      SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory Q hQ default := by
  subst Q
  rfl



theorem finiteDimensional_cutoff_path_kernel
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d →
      SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hPNcons : ∀ N omega, (PN N omega).IsConservative)
    (hPNfeller : ∀ N omega, (PN N omega).IsFellerKernelSemigroup)
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
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
              kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (hnonexplosion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
        ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
            Homogenization.euclideanGradient
              (cutoffPotential H omega N) x‖ ≤
          K * (1 + ‖x‖)) :
    ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
        (DiffusionPath d),
      (∀ N, IsMarkovKernel (KN N)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ N (I : Finset NNReal) x,
          (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
            SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x := by
  classical
  obtain ⟨P, hPcons, hPfeller, hPae⟩ :=
    finiteDimensional_cutoff_measurable_semigroup hd M H hH PN hPNcons hPNfeller
      hres hnonexplosion
  have hPcons' : ∀ N, (P N).IsConservative := by
    intro N omega
    exact hPcons N omega
  let KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d)
      (DiffusionPath d) := fun N =>
    ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
      (P N) (hPcons' N)
  refine ⟨KN, ?_, ?_⟩
  · intro N
    dsimp [KN]
    infer_instance
  · have hpotAE := aux_finiteDimensional_cutoff_path_kernel_potential hd M H hH
    filter_upwards [hres, hnonexplosion, hpotAE, hPae] with omega hresω hnonω hpotω hPω
    intro N I x
    obtain ⟨D, hdense, hD, hLap⟩ := hresω N
    obtain ⟨g, hg⟩ := hpotω N
    obtain ⟨K, hK, hgrowth⟩ := hnonω N
    have hEq : PN N omega = D.fellerKernelSemigroup hdense :=
      aux_finiteDimensional_cutoff_path_kernel_resolvent
        (PN N omega) (hPNfeller N omega) D hdense hLap
    have hDcons : (D.fellerKernelSemigroup hdense).IsConservative := by
      rw [← hEq]
      exact hPNcons N omega
    have hsupport := aux_finiteDimensional_cutoff_path_kernel_support
      M H omega N D hdense hD hDcons ⟨g, hg⟩ ⟨K, hK, hgrowth⟩
    let default : DiffusionPath d :=
      ContinuousMap.const NNReal (Classical.arbitrary (SpatialCoordinates d))
    have hfdd := aux_finiteDimensional_cutoff_path_kernel_fdd
      (D.fellerKernelSemigroup hdense) hDcons
      (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
      default hsupport I
    have hPfibre : (P N).toSubMarkovKernelSemigroup omega =
        D.fellerKernelSemigroup hdense :=
      (hPω N).trans hEq
    change
      ((ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        (P N) (hPcons' N)).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    rw [ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply]
    rw [SubMarkovKernelSemigroup.IsConservative.continuousProcess]
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    have hpath :
        SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory
            ((P N).toSubMarkovKernelSemigroup omega) (hPcons N omega) default =
          SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory
            (D.fellerKernelSemigroup hdense) hDcons default := by
      exact aux_finiteDimensional_cutoff_path_kernel_trajectory_congr
        _ _ hPfibre (hPcons N omega) hDcons default
    rw [hpath]
    have hfddx := congrArg
      (fun K : Kernel (SpatialCoordinates d) (I → SpatialCoordinates d) => K x) hfdd
    simpa [default, hEq] using! hfddx

end Paper
