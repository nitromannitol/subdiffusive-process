module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_cell_moment_uniform
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_unit_chart_compact
public import SubdiffusiveProcess.Paper.chart_coords_measurable
public import SubdiffusiveProcess.Probability.SeriesMoment

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace Paper

/-- Model-uniform `L^p` moment bound (any target `p ≥ 1`, not just `L^1` compactness) on
`LambdaSq` and `lambdaSq⁻¹` of the origin unit chart `F K` at weight `t`, for every cutoff depth
`K`. Same gap/threshold construction as `lem_prefix_limit_g9_unit_chart_compact` (choose an
internal exponent `q` large enough that `d / q < t`, so the geometric weight beats both the
cell-count growth and the moment-growth rate `A * delta^2`), but assembled from the model-uniform
per-cell bank `lem_prefix_limit_g9_cell_moment_uniform` via `eLpNorm_tsum_sup'_le`, and
additionally choosing `q ≥ p` so the internal `L^q` bound downgrades (via the probability-space
Jensen inequality) to the target `L^p` bound. -/
theorem lem_prefix_limit_g9_unit_chart_moment {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I) (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (t p : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) (hp : 1 ≤ p) :
    ∃ delta0 KLam Klaminv : ℝ, 0 < delta0 ∧ 0 < KLam ∧ 0 < Klaminv ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
        fun K omega => I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      ∀ K : ℕ,
        MemLp (fun omega => Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) t
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega => Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) t
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal KLam ∧
        MemLp (fun omega =>
            (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) t
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun omega =>
            (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) t
              (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Klaminv := by
  set q : ℝ := max p (max 2 ((d : ℝ) / t + 1)) with hqdef
  have hqp : p ≤ q := le_max_left _ _
  have hq2 : (2 : ℝ) ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hq1lt : 1 < q := lt_of_lt_of_le (by norm_num) hq2
  have hqgap : (d : ℝ) / q < t := by
    have hqt : (d : ℝ) / t < q := by
      have h1 : (d : ℝ) / t + 1 ≤ q := (le_max_right _ _).trans (le_max_right _ _)
      linarith
    apply (div_lt_iff₀ hqpos).2
    have hqmul : (d : ℝ) < q * t := (div_lt_iff₀ ht.1).1 hqt
    nlinarith
  obtain ⟨deltaMoment, A, hdeltaMoment, hA, Cfn, hCfnpos, hCfnmono, hmoment⟩ :=
    lem_prefix_limit_g9_cell_moment_uniform hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp q hq1lt.le
  set gap : ℝ := (2 * t - (d : ℝ) / q) * Real.log 3 with hgapdef
  have hgap : 0 < gap := mul_pos (by linarith [ht.1, hqgap]) (Real.log_pos (by norm_num))
  set delta0 : ℝ := min deltaMoment (Real.sqrt (gap / (A + 1))) with hdelta0def
  have hdelta0pos : 0 < delta0 := by rw [hdelta0def]; positivity
  have hCfn0pos : 0 < Cfn delta0 := hCfnpos delta0
  set D' : ℕ → Finset (Homogenization.TriadicCube d) :=
    aux_lem_prefix_limit_g9_unit_chart_compact_D (d := d) with hD'def
  have hD'nonempty : ∀ n, (D' n).Nonempty := aux_lem_prefix_limit_g9_unit_chart_compact_D_nonempty
  have hD'card : ∀ n, ((D' n).card : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) :=
    aux_lem_prefix_limit_g9_unit_chart_compact_D_card
  have hAgapOf : ∀ delta : ℝ, 0 ≤ delta → delta ≤ Real.sqrt (gap / (A + 1)) →
      A * delta ^ 2 < gap := by
    intro delta hdelta0 hdeltale
    have hA1 : 0 < A + 1 := by linarith
    have hsqrtsq : Real.sqrt (gap / (A + 1)) ^ 2 = gap / (A + 1) :=
      Real.sq_sqrt (by positivity)
    have hle2 : delta ^ 2 ≤ gap / (A + 1) := by nlinarith [Real.sqrt_nonneg (gap / (A + 1))]
    calc A * delta ^ 2 ≤ A * (gap / (A + 1)) := mul_le_mul_of_nonneg_left hle2 hA
      _ < gap := by
          rw [show A * (gap / (A + 1)) = (A * gap) / (A + 1) by ring, div_lt_iff₀ hA1]
          nlinarith
  have hAgap0 : A * delta0 ^ 2 < gap :=
    hAgapOf delta0 hdelta0pos.le (min_le_right _ _)
  have hsummable0 : Summable (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) * (Cfn delta0 * Real.exp (A * delta0 ^ 2 * (n : ℝ)))) :=
    aux_lem_prefix_limit_g9_unit_chart_compact_weight_card_exp D' hD'card t q (Cfn delta0) A
      delta0 ht.1 hqpos hCfn0pos.le hA hAgap0
  have hCn0nonneg : ∀ n : ℕ, 0 ≤ Cfn delta0 * Real.exp (A * delta0 ^ 2 * (n : ℝ)) :=
    fun n => (mul_nonneg hCfn0pos.le (Real.exp_pos _).le)
  set KLam0 : ℝ := ∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) * max (Cfn delta0 * Real.exp (A * delta0 ^ 2 * (n : ℝ))) 0
    with hKLam0def
  have hKLam0eq : KLam0 = ∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) * (Cfn delta0 * Real.exp (A * delta0 ^ 2 * (n : ℝ))) := by
    rw [hKLam0def]
    refine tsum_congr (fun n => ?_)
    rw [max_eq_left (hCn0nonneg n)]
  have hKLam0pos : 0 < KLam0 := by
    rw [hKLam0eq]
    have h0 : 0 < Homogenization.Book.Ch02.geometricWeight t 2 0 *
        ((D' 0).card : ℝ) ^ (1 / q) * (Cfn delta0 * Real.exp (A * delta0 ^ 2 * (0 : ℝ))) := by
      have hw0 : 0 < Homogenization.Book.Ch02.geometricWeight t 2 0 := by
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_pos 0 (mul_pos ht.1 (by norm_num))
      have hcard0 : (0:ℝ) < ((D' 0).card : ℝ) ^ (1 / q) := by
        have := (hD'nonempty 0).card_pos
        positivity
      positivity
    calc (0:ℝ) < Homogenization.Book.Ch02.geometricWeight t 2 0 *
          ((D' 0).card : ℝ) ^ (1 / q) * (Cfn delta0 * Real.exp (A * delta0 ^ 2 * (0 : ℝ))) := h0
      _ ≤ _ := hsummable0.sum_le_tsum {0}
          (fun n _ => by
            have : 0 ≤ Homogenization.Book.Ch02.geometricWeight t 2 n := by
              rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
              exact Homogenization.geometricWeight_nonneg n (mul_nonneg ht.1.le (by norm_num))
            positivity) |>.trans_eq' (by simp)
  refine ⟨delta0, KLam0, KLam0, hdelta0pos, hKLam0pos, hKLam0pos, ?_⟩
  intro M hM Rm hRm Sreg _It H hH
  dsimp only
  intro K
  have hMdeltapos : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hMdelta0 : M.delta ≤ delta0 := hM
  have hMmoment : M.delta ≤ deltaMoment := hM.trans (min_le_left _ _)
  have hMsqrt : M.delta ≤ Real.sqrt (gap / (A + 1)) := hM.trans (min_le_right _ _)
  have hAgapM : A * M.delta ^ 2 < gap := hAgapOf M.delta hMdeltapos hMsqrt
  have hCfnMpos : 0 < Cfn M.delta := hCfnpos M.delta
  have hsummableM : Summable (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) * (Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ)))) :=
    aux_lem_prefix_limit_g9_unit_chart_compact_weight_card_exp D' hD'card t q (Cfn M.delta) A
      M.delta ht.1 hqpos hCfnMpos.le hA hAgapM
  have hsummableM' : Summable (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) * max (Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ))) 0) := by
    refine hsummableM.congr (fun n => ?_)
    rw [max_eq_left (mul_nonneg hCfnMpos.le (Real.exp_pos _).le)]
  have hterm_le : ∀ n : ℕ, Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ)) ≤
      Cfn delta0 * Real.exp (A * delta0 ^ 2 * (n : ℝ)) := by
    intro n
    have h1 : Cfn M.delta ≤ Cfn delta0 := hCfnmono M.delta delta0 hMdeltapos hMdelta0
    have h2 : A * M.delta ^ 2 * (n : ℝ) ≤ A * delta0 ^ 2 * (n : ℝ) := by
      have hsqle : M.delta ^ 2 ≤ delta0 ^ 2 := by nlinarith [hMdelta0, hMdeltapos]
      have hh : A * M.delta ^ 2 ≤ A * delta0 ^ 2 := mul_le_mul_of_nonneg_left hsqle hA
      exact mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n)
    exact mul_le_mul h1 (Real.exp_le_exp.2 h2) (Real.exp_pos _).le (hCfnpos delta0).le
  have htsum_le : (∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) * (Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ)))) ≤
      KLam0 := by
    rw [hKLam0eq]
    refine hsummableM.tsum_le_tsum (fun n => ?_) hsummable0
    have hwc : 0 ≤ Homogenization.Book.Ch02.geometricWeight t 2 n *
        ((D' n).card : ℝ) ^ (1 / q) := by
      have hw : 0 ≤ Homogenization.Book.Ch02.geometricWeight t 2 n := by
        rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
        exact Homogenization.geometricWeight_nonneg n (mul_nonneg ht.1.le (by norm_num))
      positivity
    exact mul_le_mul_of_nonneg_left (hterm_le n) hwc
  set F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    fun K omega => I.chart 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
    with hFdef
  set μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hμdef
  obtain ⟨hmomentCell, hmomentRoot⟩ := hmoment M hMmoment Rm hRm Sreg _It H hH
  dsimp only at hmomentCell hmomentRoot
  have hDroot : ∀ n (R : Homogenization.TriadicCube d), R ∈ D' n →
      R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(n : ℤ)) := by
    intro n R hR
    simpa [hD'def, aux_lem_prefix_limit_g9_unit_chart_compact_D, Homogenization.originCube]
      using hR
  have hVmSigmaStarInv : ∀ n (R : Homogenization.TriadicCube d), R ∈ D' n →
      AEStronglyMeasurable (fun omega =>
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega)) μ := by
    intro n R hR
    have hRsub : Homogenization.openCubeSet R ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      aux_lem_prefix_limit_g9_unit_chart_compact_D_subset n R hR
    refine Measurable.aestronglyMeasurable ?_
    unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
    apply aux_measlam_matrixNorm
    intro i j
    simpa [hFdef] using
      aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hH.1 K
        (0 : SpatialCoordinates d) 1 one_pos R hRsub i j
  have hVmB : ∀ n (R : Homogenization.TriadicCube d), R ∈ D' n →
      AEStronglyMeasurable (fun omega =>
        Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega)) μ := by
    intro n R hR
    have hRsub : Homogenization.openCubeSet R ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      aux_lem_prefix_limit_g9_unit_chart_compact_D_subset n R hR
    refine Measurable.aestronglyMeasurable ?_
    unfold Homogenization.Book.Ch02.coarseBMatrixNorm
    apply aux_measlam_matrixNorm
    intro i j
    simpa [hFdef] using
      aux_core_bCoarse_measurable_R_gen hd I M H hH.1 K
        (0 : SpatialCoordinates d) 1 one_pos R hRsub i j
  have hSigmaStarInv := eLpNorm_tsum_sup'_le μ D' hD'nonempty
    (fun n R omega => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega))
    (fun n R omega => by
      unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
        Homogenization.Book.Ch02.matrixNorm
      exact norm_nonneg _)
    (fun n R hR => hVmSigmaStarInv n R hR)
    (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n)
    (fun n => Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ))) q hq1lt
    (fun n => by
      show 0 ≤ Homogenization.Book.Ch02.geometricWeight t 2 n
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
      exact Homogenization.geometricWeight_nonneg n (mul_nonneg ht.1.le (by norm_num)))
    (fun n R hR => (hmomentCell n R (hDroot n R hR) K).1)
    hsummableM'
  have hB := eLpNorm_tsum_sup'_le μ D' hD'nonempty
    (fun n R omega => Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega))
    (fun n R omega => by
      unfold Homogenization.Book.Ch02.coarseBMatrixNorm Homogenization.Book.Ch02.matrixNorm
      exact norm_nonneg _)
    (fun n R hR => hVmB n R hR)
    (fun n => Homogenization.Book.Ch02.geometricWeight t 2 n)
    (fun n => Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ))) q hq1lt
    (fun n => by
      show 0 ≤ Homogenization.Book.Ch02.geometricWeight t 2 n
      rw [Homogenization.Book.Ch02.geometricWeight_eq_old]
      exact Homogenization.geometricWeight_nonneg n (mul_nonneg ht.1.le (by norm_num)))
    (fun n R hR => (hmomentCell n R (hDroot n R hR) K).2.1)
    hsummableM'
  have hboundval : ENNReal.ofReal (∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
      ((D' n).card : ℝ) ^ (1 / q) *
      max (Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ))) 0) ≤ ENNReal.ofReal KLam0 := by
    apply ENNReal.ofReal_le_ofReal
    have heq : (∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
        ((D' n).card : ℝ) ^ (1 / q) *
        max (Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ))) 0) =
        ∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
          ((D' n).card : ℝ) ^ (1 / q) *
          (Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ))) := by
      refine tsum_congr (fun n => ?_)
      rw [max_eq_left (by
        have := hCn0nonneg n
        have h1 : 0 ≤ Cfn M.delta * Real.exp (A * M.delta ^ 2 * (n : ℝ)) :=
          mul_nonneg hCfnMpos.le (Real.exp_pos _).le
        exact h1)]
    rw [heq]
    exact htsum_le
  have hLamEqK : (fun omega => Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) t
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega)) =
      (fun omega => ∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
        (D' n).sup' (hD'nonempty n)
          (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega))) := by
    funext omega
    simpa [hD'def] using
      aux_lem_prefix_limit_g9_unit_chart_compact_Lam_eq t (F K omega)
  have hlamInvEqK : (fun omega =>
      (Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) t
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) (F K omega))⁻¹) =
      (fun omega => ∑' n, Homogenization.Book.Ch02.geometricWeight t 2 n *
        (D' n).sup' (hD'nonempty n)
          (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega))) := by
    funext omega
    simpa [hD'def] using
      aux_lem_prefix_limit_g9_unit_chart_compact_lam_inv_eq t (F K omega)
  obtain ⟨hmB, hcB⟩ := hB
  obtain ⟨hmS, hcS⟩ := hSigmaStarInv
  have hcB' : eLpNorm (fun omega => Homogenization.Book.Ch02.LambdaSq
      (Homogenization.originCube d 0) t (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      (F K omega)) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal KLam0 := by
    rw [hLamEqK]; exact hcB.trans hboundval
  have hcS' : eLpNorm (fun omega => (Homogenization.Book.Ch02.lambdaSq
      (Homogenization.originCube d 0) t (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      (F K omega))⁻¹) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal KLam0 := by
    rw [hlamInvEqK]; exact hcS.trans hboundval
  have hmB' : MemLp (fun omega => Homogenization.Book.Ch02.LambdaSq
      (Homogenization.originCube d 0) t (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      (F K omega)) (ENNReal.ofReal q) μ := by rw [hLamEqK]; exact hmB
  have hmS' : MemLp (fun omega => (Homogenization.Book.Ch02.lambdaSq
      (Homogenization.originCube d 0) t (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      (F K omega))⁻¹) (ENNReal.ofReal q) μ := by rw [hlamInvEqK]; exact hmS
  have hqpENN : (ENNReal.ofReal p) ≤ (ENNReal.ofReal q) := ENNReal.ofReal_le_ofReal hqp
  refine ⟨(hmB'.mono_exponent hqpENN),
    (eLpNorm_le_eLpNorm_of_exponent_le hqpENN).trans hcB',
    (hmS'.mono_exponent hqpENN),
    (eLpNorm_le_eLpNorm_of_exponent_le hqpENN).trans hcS'⟩

end Paper
