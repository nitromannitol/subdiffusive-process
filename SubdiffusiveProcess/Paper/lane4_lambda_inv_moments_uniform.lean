module

public import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments

@[expose] public section




open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open Homogenization Homogenization.Book.Ch02

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Explicit (non-existential) combine step: same construction as
`aux_lane4_lambda_inv_cell_moment_assemble`'s inner witness, but exposes
`Cq := 1 + Cplus + Cminus` directly in the conclusion instead of behind `∃ Cq`, so a downstream
caller can see that `Cq` is a fixed monotone-in-`delta` function of `Cplus`, `Cminus` alone. -/
theorem aux_lane4_lambda_inv_moments_uniform_combine {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) (q a b c delta Cplus Cminus : ℝ) (hq : 1 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hdelta : 0 ≤ delta) (hplus : 0 ≤ Cplus) (hminus : 0 ≤ Cminus)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hAbove : ∀ N n : ℕ, n ≤ N →
      AEStronglyMeasurable (Y N n) μ ∧
        eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (Cplus * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
            Real.exp (a * (q + q ^ 2) * delta ^ 2 * (n : ℝ))))
    (hBelow : ∀ N n : ℕ, N < n →
      AEStronglyMeasurable (Y N n) μ ∧
        eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (Cminus * Real.exp ((b * delta + c * delta ^ 2) * (N : ℝ)))) :
    ∀ N n : ℕ,
      AEStronglyMeasurable (Y N n) μ ∧
        eLpNorm (Y N n) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal ((1 + Cplus + Cminus) * (if n ≤ N then
            (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
              Real.exp ((1 + a + b + c) * (q + q ^ 2) * delta ^ 2 * (n : ℝ))
          else Real.exp (((1 + a + b + c) * delta + (1 + a + b + c) * delta ^ 2) * (N : ℝ)))) := by
  intro N n
  have hq2 : 0 ≤ q + q ^ 2 := by nlinarith
  by_cases hn : n ≤ N
  · obtain ⟨hMeas, hNorm⟩ := hAbove N n hn
    refine ⟨hMeas, hNorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [if_pos hn]
    have h3 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) := Real.rpow_nonneg (by norm_num) _
    have hexp : Real.exp (a * (q + q ^ 2) * delta ^ 2 * (n : ℝ)) ≤
        Real.exp ((1 + a + b + c) * (q + q ^ 2) * delta ^ 2 * (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hq2) (sq_nonneg delta)) (Nat.cast_nonneg n))
    calc Cplus * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) * Real.exp (a * (q + q ^ 2) * delta ^ 2 * (n : ℝ))
        ≤ (1 + Cplus + Cminus) * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
            Real.exp ((1 + a + b + c) * (q + q ^ 2) * delta ^ 2 * (n : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) h3) hexp (Real.exp_pos _).le
            (by positivity)
      _ = _ := by ring
  · obtain ⟨hMeas, hNorm⟩ := hBelow N n (by omega)
    refine ⟨hMeas, hNorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [if_neg hn]
    have hexp : Real.exp ((b * delta + c * delta ^ 2) * (N : ℝ)) ≤
        Real.exp (((1 + a + b + c) * delta + (1 + a + b + c) * delta ^ 2) * (N : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) hdelta)
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg delta))) (Nat.cast_nonneg N))
    exact mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- Same construction as `aux_lane4_lambda_inv_cell_moment_rooted`, but with `ℓ` supplied
externally (it never depended on `M`) and the final `Cq` exposed explicitly as
`1 + Cplus + Cminus` via `aux_lane4_lambda_inv_moments_uniform_combine`, instead of behind `∃ Cq`. -/
theorem aux_lane4_lambda_inv_moments_uniform_rooted {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (q q' : ℝ) (hq : 1 ≤ q) (hqq' : q ≤ q') (hdq' : (d : ℝ) / q' ≤ 1 / 2)
    (Cenv CH : Compacts (SpatialCoordinates d) → ℝ)
    (henvM : aux_lane4_lambda_inv_cell_moment_EnvMomentProp M H Cenv)
    (family : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ) (hresp : aux_lane4_lambda_inv_cell_moment_RespProp M family J)
    (CJ B R : ℝ) (hCJ : 0 ≤ CJ) (hR : 0 ≤ R)
    (hpieceM : ∀ K : Compacts (SpatialCoordinates d),
      aux_lane4_lambda_inv_cell_moment_PieceMomentProp M H K J CJ q
        (Real.log 4 / (2 * q) + 4 * (2 * q) * CH K * M.delta ^ 2 + B * M.delta ^ 2) B)
    (hBR : B ≤ R)
    (hCRR : 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 ≤ R)
    (hBδ : B * M.delta ^ 2 ≤ Real.log (3 / 2))
    (hCRδ : (2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
      M.delta ^ 2 ≤ Real.log (Real.sqrt 3))
    (hδq : M.delta ≤ 1 / q)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (ℓ : ℕ) (hℓ : (1 / 3 : ℝ) ^ ℓ ≤ r) :
    let K := aux_lane4_lambda_inv_cell_moment_rootK z
    let P0 := Real.log 4 / (2 * q) + 4 * (2 * q) * CH K * M.delta ^ 2 + B * M.delta ^ 2
    let CR := 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2
    let E0 := Real.log 4 / q' + 4 * q' * Cenv K * M.delta ^ 2
    let Cplus := aux_lane4_lambda_inv_cell_moment_Cplus d M.delta r CJ P0 B CR E0 ℓ
    let Cminus := Real.exp (Real.log 4 * M.delta + 4 * Cenv K * M.delta +
      ((d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
        M.delta + 2 * Real.log 2 * M.delta ^ 2))
    ∀ N n : ℕ,
      AEStronglyMeasurable (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((1 + Cplus + Cminus) * (if n ≤ N then
          (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
            Real.exp ((1 + R + (d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) +
              2 * Real.log 2) * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))
        else Real.exp (((1 + R + (d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) +
              2 * Real.log 2) * M.delta +
            (1 + R + (d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) +
              2 * Real.log 2) * M.delta ^ 2) * (N : ℝ)))) := by
  intro K P0 CR E0 Cplus Cminus
  have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hCplus0 : 0 ≤ Cplus := by
    show 0 ≤ aux_lane4_lambda_inv_cell_moment_Cplus d M.delta r CJ P0 B CR E0 ℓ
    unfold aux_lane4_lambda_inv_cell_moment_Cplus; positivity
  have hcell : ∀ N n : ℕ, n ≤ N → ∀ Q ∈ descendantsAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)),
      eLpNorm (fun om => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q
        (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cplus * Real.exp (R * M.delta ^ 2 * n)) := by
    intro N n hnN Q hQ
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (aux_lem_extension_cell_moment_aesm_coarseS_chart hd E M H hH.1 N z r hr z r hr Set.Subset.rfl Q (aux_lane4_lambda_inv_cell_moment_desc_facts n Q hQ).1)]
    exact aux_lane4_lambda_inv_cell_moment_cell_moment hd E M H q q' hq hqq' hdq' Cenv henvM z r hr hr1
      family J hresp CJ P0 B R hCJ (hpieceM K) hBR hCRR hBδ hCRδ ℓ hℓ N n hnN Q hQ
  have hmeas : ∀ N n : ℕ, AEStronglyMeasurable (fun om =>
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
      (chaosSampleLaw M).toMeasure := by
    intro N n
    have h := aux_lem_extension_cell_moment_aesm_maxS_chart hd E M H hH.1 N z r hr z r hr
      Set.Subset.rfl n
    simpa [Homogenization.originCube] using h
  exact aux_lane4_lambda_inv_moments_uniform_combine (chaosSampleLaw M).toMeasure d q R
    (d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) (2 * Real.log 2)
    M.delta Cplus Cminus hq hR (by positivity) (by positivity) hδ0 hCplus0 (Real.exp_pos _).le
    (fun N n om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ))
      (E.chart z r hr (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r))
    (fun N n hnN => ⟨hmeas N n, aux_lane4_lambda_inv_cell_moment_branch_above hd E M H hH.1 q hq
      z r hr Cplus R hCplus0 hR hcell N n hnN⟩)
    (fun N n _ => ⟨hmeas N n, by
      rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hmeas N n)]
      exact aux_lane4_lambda_inv_cell_moment_below hd E M H Cenv henvM q hq hδq
        z r hr hr1 N n⟩)



theorem aux_lane4_lambda_inv_moments_uniform_cell_unconditional :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (q : ℝ), 1 ≤ q →
  ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∃ Cq_fn : ℝ → ℝ, (∀ δ, 0 ≤ δ → 0 < Cq_fn δ) ∧
      (∀ δ1 δ2, 0 ≤ δ1 → δ1 ≤ δ2 → Cq_fn δ1 ≤ Cq_fn δ2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        M.delta ≤ deltaq →
        ∀ N n : ℕ,
          let Y : BilateralField d → ℝ := fun om =>
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0) (-(n : ℤ))
              (E.chart z r hr
                (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r)
          AEStronglyMeasurable Y (chaosSampleLaw M).toMeasure ∧
          eLpNorm Y (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cq_fn M.delta * (if n ≤ N then
                (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                  Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))
              else Real.exp ((Cd * M.delta + Cd * M.delta ^ 2) * (N : ℝ)))) := by
  intro d hd _ _ E q hq
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hq0 : 0 < q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hlogs3 : 0 < Real.log (Real.sqrt 3) :=
    Real.log_pos (by rw [Real.lt_sqrt (by norm_num)]; norm_num)
  obtain ⟨δresp, CJ, hδresp, hCJ, hresp⟩ :=
    aux_lem_extension_cell_moment_matched_response hd E q hq
  obtain ⟨CH, hCH0, hpieceM⟩ := aux_lane4_lambda_inv_cell_moment_pieceG_moment hd
  obtain ⟨Cenv, hCenv0, henvM⟩ := aux_lane4_lambda_inv_cell_moment_envMax_moment hd
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ, q' = max q (2 * d) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = aux_lem_extension_cell_moment_aboveRate d (2 * q) := ⟨_, rfl⟩
  obtain ⟨CR, hCR⟩ : ∃ CR : ℝ,
      CR = 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 :=
    ⟨_, rfl⟩
  have hBpos : 0 < B := by
    rw [hB]; exact aux_lem_extension_cell_moment_aboveRate_pos d (2 * q) (by positivity)
  have hq'q : q ≤ q' := by rw [hq']; exact le_max_left _ _
  have hq'0 : 0 < q' := by linarith
  have hCRpos : 0 < CR := by rw [hCR]; positivity
  have hdq' : (d : ℝ) / q' ≤ 1 / 2 := by
    rw [div_le_iff₀ hq'0]
    have : 2 * (d : ℝ) ≤ q' := by rw [hq']; exact le_max_right _ _
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max B CR := ⟨_, rfl⟩
  have hBR : B ≤ R := by rw [hR]; exact le_max_left _ _
  have hCRR : CR ≤ R := by rw [hR]; exact le_max_right _ _
  have hR0 : 0 ≤ R := hBpos.le.trans hBR
  refine ⟨min δresp (min (1 / q) (min (Real.sqrt (Real.log (3 / 2) / B))
    (Real.sqrt (Real.log (Real.sqrt 3) / CR)))),
    1 + R + ((d : ℝ) * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) +
      2 * Real.log 2,
    lt_min hδresp (lt_min (by positivity) (lt_min (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_pos.mpr (by positivity)))), by positivity, ?_⟩
  intro z r hr hr1
  obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 3 : ℝ) < 1)
  set K := aux_lane4_lambda_inv_cell_moment_rootK z with hK
  set Cplus_fn : ℝ → ℝ := fun δ =>
    aux_lane4_lambda_inv_cell_moment_Cplus d δ r CJ
      (Real.log 4 / (2 * q) + 4 * (2 * q) * CH K * δ ^ 2 + B * δ ^ 2) B CR
      (Real.log 4 / q' + 4 * q' * Cenv K * δ ^ 2) ℓ with hCplus_fn
  set Cminus_fn : ℝ → ℝ := fun δ => Real.exp (Real.log 4 * δ + 4 * Cenv K * δ +
    ((d * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) *
      δ + 2 * Real.log 2 * δ ^ 2)) with hCminus_fn
  have hCplus_mono : ∀ δ1 δ2 : ℝ, 0 ≤ δ1 → δ1 ≤ δ2 → Cplus_fn δ1 ≤ Cplus_fn δ2 := by
    intro δ1 δ2 hδ1 hδ12
    have hsq : δ1 ^ 2 ≤ δ2 ^ 2 := pow_le_pow_left₀ hδ1 hδ12 2
    have hCHK := hCH0 K
    have hCenvK := hCenv0 K
    have hell : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    have hCRsqL : CR * δ1 ^ 2 * (ℓ : ℝ) ≤ CR * δ2 ^ 2 * (ℓ : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCRpos.le) hell
    have hBsqL : B * δ1 ^ 2 * (ℓ : ℝ) ≤ B * δ2 ^ 2 * (ℓ : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hBpos.le) hell
    have hCenvsq : 4 * q' * Cenv K * δ1 ^ 2 ≤ 4 * q' * Cenv K * δ2 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have hCHsq : 4 * (2 * q) * CH K * δ1 ^ 2 ≤ 4 * (2 * q) * CH K * δ2 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    simp only [hCplus_fn]
    unfold aux_lane4_lambda_inv_cell_moment_Cplus
    gcongr
  have hCminus_mono : ∀ δ1 δ2 : ℝ, 0 ≤ δ1 → δ1 ≤ δ2 → Cminus_fn δ1 ≤ Cminus_fn δ2 := by
    intro δ1 δ2 hδ1 hδ12
    have hsq : δ1 ^ 2 ≤ δ2 ^ 2 := pow_le_pow_left₀ hδ1 hδ12 2
    simp only [hCminus_fn]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log 4 * δ1 ≤ Real.log 4 * δ2 :=
      mul_le_mul_of_nonneg_left hδ12 (Real.log_nonneg (by norm_num))
    have h2 : 4 * Cenv K * δ1 ≤ 4 * Cenv K * δ2 :=
      mul_le_mul_of_nonneg_left hδ12 (mul_nonneg (by norm_num) (hCenv0 K))
    have h3 : ((d : ℝ) * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) * δ1 ≤
        ((d : ℝ) * Real.log 3 + (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2) * δ2 :=
      mul_le_mul_of_nonneg_left hδ12 (by positivity)
    have h4 : 2 * Real.log 2 * δ1 ^ 2 ≤ 2 * Real.log 2 * δ2 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  refine ⟨fun δ => 1 + Cplus_fn δ + Cminus_fn δ, ?_, ?_, ?_⟩
  · intro δ hδ
    have : 0 ≤ Cplus_fn δ := by
      simp only [hCplus_fn]; unfold aux_lane4_lambda_inv_cell_moment_Cplus; positivity
    have : 0 ≤ Cminus_fn δ := by simp only [hCminus_fn]; positivity
    linarith
  · intro δ1 δ2 hδ1 hδ12
    have := hCplus_mono δ1 δ2 hδ1 hδ12
    have := hCminus_mono δ1 δ2 hδ1 hδ12
    linarith
  · intro M H hH hδ
    have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
    have hδresp' : M.delta ≤ δresp := hδ.trans (min_le_left _ _)
    have hδq : M.delta ≤ 1 / q := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδB : M.delta ≤ Real.sqrt (Real.log (3 / 2) / B) :=
      hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hδC : M.delta ≤ Real.sqrt (Real.log (Real.sqrt 3) / CR) :=
      hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hBδ : B * M.delta ^ 2 ≤ Real.log (3 / 2) := by
      have h := pow_le_pow_left₀ hδ0 hδB 2
      rw [Real.sq_sqrt (by positivity), le_div_iff₀ hBpos] at h
      linarith
    have hCRδ : CR * M.delta ^ 2 ≤ Real.log (Real.sqrt 3) := by
      have h := pow_le_pow_left₀ hδ0 hδC 2
      rw [Real.sq_sqrt (by positivity), le_div_iff₀ hCRpos] at h
      linarith
    have hrespM := hresp M hδresp'
    rcases hrespM with ⟨family, J, hfamily, hJgreat, hJmeas, hJnorm⟩
    have hJ0 : ∀ N om, 0 ≤ J N om := by
      intro N om
      obtain ⟨e, _, he⟩ := (hJgreat N om).1
      rw [he]
      exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
    have hCRβ : CR = 2 * Real.log 2 + q' * (aux_lem_extension_cell_moment_nativeFluctuationConst d) ^ 2 := hCR
    intro N n
    have hstep := aux_lane4_lambda_inv_moments_uniform_rooted hd E M H hH q q' hq hq'q hdq' Cenv CH (henvM M H hH)
      family J ⟨hfamily, hJgreat, hJ0⟩ CJ B R hCJ.le hR0
      (fun K' N' L w => hB ▸ hpieceM M H hH K' N' J CJ q hCJ.le hq hJmeas hJnorm L w)
      hBR (hCRβ ▸ hCRR) (hB ▸ hBδ) (hCRβ ▸ hCRδ) hδq z r hr hr1 ℓ hℓ.le N n
    simp only [hCplus_fn, hCminus_fn, hK, hCR]
    simpa using hstep

/-- Same construction as `lane4_lambda_inv_moments`, but with the final `Cbound` exposed as an
EXPLICIT real function `Cbound_fn` of `delta`, chosen BEFORE `∀ M` (only `z,r,p` fix it), monotone
increasing on `[0, delta0 p]`, instead of behind `∀ M, ... → ∃ Cbound`. This is what actually
makes the bound model-uniform: `Cbound_fn (deltaS)` for any fixed `deltaS ≤ delta0 p` bounds
EVERY model with `M.delta ≤ deltaS`, since they all share the same `Cbound_fn`. -/
theorem aux_lane4_lambda_inv_moments_uniform_explicit_unconditional :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ p : ℝ, 1 ≤ p →
    ∃ Cbound_fn : ℝ → ℝ,
      (∀ δ, 0 ≤ δ → δ ≤ delta0 p → 0 < Cbound_fn δ) ∧
      (∀ δ1 δ2, 0 ≤ δ1 → δ1 ≤ δ2 → δ2 ≤ delta0 p → Cbound_fn δ1 ≤ Cbound_fn δ2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        M.delta ≤ delta0 p →
        ∀ N : ℕ, MemLp (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound_fn M.delta) := by
  intro d hd _ _ E s hs
  obtain ⟨hs0, hs14⟩ := hs
  have hs1 : s ≤ 1 := by linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set Qf : ℝ → ℝ := fun p => max (2 * p) (2 * (d : ℝ) / s) with hQf_def
  have hQfge1 : ∀ p : ℝ, 1 ≤ Qf p := by
    intro p
    have h16 : (16 : ℝ) < 2 * (d : ℝ) / s := by
      rw [lt_div_iff₀ hs0]; nlinarith
    have h2 : (16 : ℝ) ≤ Qf p := h16.le.trans (le_max_right _ _)
    linarith
  have hQfpos : ∀ p : ℝ, 0 < Qf p := fun p => lt_of_lt_of_le one_pos (hQfge1 p)
  have hDQp : ∀ p : ℝ, 2 * (d : ℝ) ≤ s * Qf p := by
    intro p
    have h1 : 2 * (d : ℝ) / s ≤ Qf p := le_max_right _ _
    rw [div_le_iff₀ hs0] at h1
    linarith
  have hcell := fun p => aux_lane4_lambda_inv_moments_uniform_cell_unconditional d hd E (Qf p) (hQfge1 p)
  choose deltaQ CdF hdeltaQpos hCdFpos hmain using hcell
  set delta0A : ℝ → ℝ := fun p =>
    Real.sqrt (s * Real.log 3 / (4 * (CdF p * (Qf p + (Qf p) ^ 2)) + 4)) with hdelta0A_def
  set delta0B : ℝ → ℝ := fun p => min 1 (s * Real.log 3 / (2 * (CdF p) + 1)) with hdelta0B_def
  set delta0 : ℝ → ℝ := fun p => min (deltaQ p) (min (delta0A p) (delta0B p)) with hdelta0_def
  have hdelta0A_pos : ∀ p : ℝ, 0 < delta0A p := by
    intro p
    rw [hdelta0A_def]
    apply Real.sqrt_pos.mpr
    apply div_pos (mul_pos hs0 hlog3pos)
    have hQ2 : 0 < Qf p + (Qf p) ^ 2 := by nlinarith [hQfpos p]
    nlinarith [hCdFpos p]
  have hdelta0B_pos : ∀ p : ℝ, 0 < delta0B p := by
    intro p
    rw [hdelta0B_def]
    apply lt_min one_pos
    apply div_pos (mul_pos hs0 hlog3pos)
    linarith [hCdFpos p]
  have hdelta0_pos : ∀ p : ℝ, 0 < delta0 p := by
    intro p
    rw [hdelta0_def]
    exact lt_min (hdeltaQpos p) (lt_min (hdelta0A_pos p) (hdelta0B_pos p))
  refine ⟨delta0, fun p _ => hdelta0_pos p, ?_⟩
  intro z r hr hrle1 p hp1
  obtain ⟨Cq_fn, hCq_fnPos, hCq_fnMono, hCbound_main⟩ := hmain p z r hr hrle1
  have hcondAgen : ∀ δ : ℝ, 0 ≤ δ → δ ≤ delta0 p →
      CdF p * (Qf p + (Qf p) ^ 2) * δ ^ 2 ≤ (s / 4) * Real.log 3 := by
    intro δ hδnn hδ
    have hδ_A : δ ≤ delta0A p := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hdl2_le : δ ^ 2 ≤ s * Real.log 3 / (4 * (CdF p * (Qf p + (Qf p) ^ 2)) + 4) := by
      have hstep : δ ^ 2 ≤ (delta0A p) ^ 2 := pow_le_pow_left₀ hδnn hδ_A 2
      have hQ2nn : (0 : ℝ) ≤ Qf p + (Qf p) ^ 2 := by nlinarith [hQfpos p]
      have hden_nn : (0 : ℝ) ≤ s * Real.log 3 / (4 * (CdF p * (Qf p + (Qf p) ^ 2)) + 4) := by
        apply div_nonneg (mul_nonneg hs0.le hlog3pos.le)
        nlinarith [hCdFpos p, hQ2nn]
      rw [hdelta0A_def, Real.sq_sqrt hden_nn] at hstep
      exact hstep
    have := aux_lane4_lambda_inv_moments_condA_helper (CdF p * (Qf p + (Qf p) ^ 2))
      (s * Real.log 3) (δ ^ 2) (by nlinarith [hCdFpos p, hQfpos p])
      (by positivity) (sq_nonneg _) hdl2_le
    linarith [this]
  have hcondBgen : ∀ δ : ℝ, 0 ≤ δ → δ ≤ delta0 p →
      CdF p * δ * (1 + δ) ≤ s * Real.log 3 := by
    intro δ hδnn hδ
    have hδ_B : δ ≤ delta0B p := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hδ_le1 : δ ≤ 1 := hδ_B.trans (min_le_left _ _)
    have hδ_leZ : δ ≤ s * Real.log 3 / (2 * (CdF p) + 1) := hδ_B.trans (min_le_right _ _)
    exact aux_lane4_lambda_inv_moments_condB_helper (CdF p) (s * Real.log 3) δ
      (hCdFpos p).le (by positivity) hδ_le1 hδnn hδ_leZ
  have hDpos : ∀ δ : ℝ, 0 ≤ δ → δ ≤ delta0 p →
      0 < 1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ ^ 2) := by
    intro δ hδnn hδ
    have hA := hcondAgen δ hδnn hδ
    have : -(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ ^ 2 < 0 := by nlinarith
    have := Real.exp_lt_one_iff.mpr this
    linarith
  have hDanti : ∀ δ1 δ2 : ℝ, 0 ≤ δ1 → δ1 ≤ δ2 → δ2 ≤ delta0 p →
      1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ2 ^ 2) ≤
      1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ1 ^ 2) := by
    intro δ1 δ2 hδ1 hδ12 hδ2
    have hsq : δ1 ^ 2 ≤ δ2 ^ 2 := pow_le_pow_left₀ hδ1 hδ12 2
    have hexp : Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ1 ^ 2) ≤
        Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ2 ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq (by nlinarith [hCdFpos p, hQfpos p] :
        (0 : ℝ) ≤ CdF p * (Qf p + (Qf p) ^ 2))]
    linarith
  set Cbound_fn : ℝ → ℝ := fun δ => (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ /
      (1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ ^ 2)) +
    (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s)) with hCbound_fn_def
  have h3s : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    have : (3 : ℝ) ^ (-s) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  refine ⟨Cbound_fn, ?_, ?_, ?_⟩
  · intro δ hδnn hδ
    have hD := hDpos δ hδnn hδ
    have hCq := hCq_fnPos δ hδnn
    rw [hCbound_fn_def]
    have ht1 : 0 < (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ /
        (1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ ^ 2)) :=
      div_pos (mul_pos h3s hCq) hD
    have ht2 : 0 ≤ (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s)) := by
      positivity
    linarith
  · intro δ1 δ2 hδ1 hδ12 hδ2
    have hδ1le : δ1 ≤ delta0 p := hδ12.trans hδ2
    set D1 : ℝ := 1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ1 ^ 2)
      with hD1_def
    set D2 : ℝ := 1 - Real.exp (-(s / 2) * Real.log 3 + CdF p * (Qf p + (Qf p) ^ 2) * δ2 ^ 2)
      with hD2_def
    have hD1 : 0 < D1 := hDpos δ1 hδ1 hδ1le
    have hD2 : 0 < D2 := hDpos δ2 (hδ1.trans hδ12) hδ2
    have hDa : D2 ≤ D1 := hDanti δ1 δ2 hδ1 hδ12 hδ2
    have hCqm := hCq_fnMono δ1 δ2 hδ1 hδ12
    have hCq1 := hCq_fnPos δ1 hδ1
    have hCq2 := hCq_fnPos δ2 (hδ1.trans hδ12)
    rw [hCbound_fn_def]
    show (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ1 / D1 +
        (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ1 * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s)) ≤
      (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 / D2 +
        (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s))
    have hnum : (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ1 ≤ (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 :=
      mul_le_mul_of_nonneg_left hCqm h3s.le
    have hfrac : (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ1 / D1 ≤ (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 / D2 := by
      have step1 : (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ1 / D1 ≤ (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 / D1 :=
        div_le_div_of_nonneg_right hnum hD1.le
      have step2 : (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 / D1 ≤ (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 / D2 :=
        div_le_div_of_nonneg_left (by positivity) hD2 hDa
      linarith
    have hterm2 : (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ1 * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s)) ≤
        (1 - (3 : ℝ) ^ (-s)) * Cq_fn δ2 * (3 : ℝ) ^ (-s) / (1 - (3 : ℝ) ^ (-s)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum (by positivity)) h3s.le
    linarith
  · intro M H hInfrared hMdelta
    have hMdelta0 : M.delta ≤ deltaQ p := hMdelta.trans (min_le_left _ _)
    have hMdelta_nn : 0 ≤ M.delta := (M.shellPrefix.delta_pos).le
    have hCqpos := hCq_fnPos M.delta hMdelta_nn
    have hcellbound := hCbound_main M H hInfrared hMdelta0
    set Cq : ℝ := Cq_fn M.delta with hCqDef
    have hcondA : CdF p * (Qf p + (Qf p) ^ 2) * M.delta ^ 2 ≤ (s / 4) * Real.log 3 :=
      hcondAgen M.delta hMdelta_nn hMdelta
    have hcondB : CdF p * M.delta * (1 + M.delta) ≤ s * Real.log 3 :=
      hcondBgen M.delta hMdelta_nn hMdelta
    have hQpge : ENNReal.ofReal p ≤ ENNReal.ofReal (Qf p) :=
      ENNReal.ofReal_le_ofReal ((le_max_left (2 * p) (2 * (d : ℝ) / s)).trans' (by linarith))
    intro N
    set YN : ℕ → BilateralField d → ℝ := fun n om =>
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) with hYN_def
    have hYNnn : ∀ n om, 0 ≤ YN n om := fun n om => aux_lane4_lambda_inv_moments_Y_nonneg _ _
    have hYmeasN : ∀ n : ℕ, AEStronglyMeasurable (YN n) (chaosSampleLaw M).toMeasure :=
      fun n => (hcellbound N n).1
    have hYboundN : ∀ n : ℕ, eLpNorm (YN n) (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cq * (if n ≤ N then (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / (Qf p)) *
              Real.exp (CdF p * (Qf p + (Qf p) ^ 2) * M.delta ^ 2 * (n : ℝ))
             else Real.exp ((CdF p * M.delta + CdF p * M.delta ^ 2) * (N : ℝ)))) :=
      fun n => (hcellbound N n).2
    obtain ⟨hMemLpQ, hBoundQ, hSummableAE⟩ :=
      aux_lane4_lambda_inv_moments_series_bound (chaosSampleLaw M).toMeasure s (d : ℝ) (Qf p)
        (CdF p) Cq M.delta N hs0 (Nat.cast_nonneg d) (hDQp p) (hQfge1 p) (hCdFpos p) hCqpos
        hMdelta_nn hcondA hcondB YN hYNnn hYmeasN hYboundN
    have hae_dom : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹ ≤
          ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * YN n om := by
      filter_upwards [hSummableAE] with om hom_summable
      obtain ⟨Ssum0, hSsum0nn, hsqrt_summable, hSsum0eq, hlam_inv_eq⟩ :=
        aux_lane4_lambda_inv_moments_lam_inv_eq E z r hr (cutoffPositiveCoefficient M H om N z hr)
          s hs0 hs1
      have hYnn' : ∀ n : ℕ, 0 ≤ YN n om := fun n => hYNnn n om
      have hcs := aux_lane4_lambda_inv_moments_cs hs0 0 (fun n => YN n om) hYnn'
        (by simpa using hsqrt_summable) (by simpa using hom_summable)
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.add_zero] at hcs
      rw [hlam_inv_eq, hSsum0eq]
      exact hcs
    have hsqrt_summable_all : ∀ om : BilateralField d, Summable (fun n : ℕ =>
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (YN n om) (1 / 2)) := by
      intro om
      obtain ⟨_, _, hs', _, _⟩ := aux_lane4_lambda_inv_moments_lam_inv_eq E z r hr
        (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1
      exact hs'
    have hSsum_meas : AEStronglyMeasurable (fun om => ∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n * Real.rpow (YN n om) (1 / 2))
        (chaosSampleLaw M).toMeasure :=
      aux_lane4_lambda_inv_moments_Ssum_meas (chaosSampleLaw M).toMeasure s YN hYmeasN
        hsqrt_summable_all
    have hlam_inv_meas : AEStronglyMeasurable (fun om : BilateralField d =>
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (chaosSampleLaw M).toMeasure := by
      have heq : (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹) =
          (fun om => (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow (YN n om) (1 / 2)) ^ 2) := by
        funext om
        obtain ⟨Ssum0, _, _, hSsum0eq, hlam_inv_eq⟩ := aux_lane4_lambda_inv_moments_lam_inv_eq E z r hr
          (cutoffPositiveCoefficient M H om N z hr) s hs0 hs1
        rw [hlam_inv_eq, hSsum0eq]
      rw [heq]
      exact (continuous_pow 2).comp_aestronglyMeasurable hSsum_meas
    have hlam_nn : ∀ om : BilateralField d, 0 ≤
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹ := fun om =>
      le_of_lt (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _))
    have heLpNorm_le : eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure ≤
        eLpNorm (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n * YN n om)
          (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure := by
      apply eLpNorm_mono_ae_real hlam_inv_meas
      filter_upwards [hae_dom] with om hom
      rwa [Real.norm_of_nonneg (hlam_nn om)]
    have heLpNorm_final : eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal (Qf p)) (chaosSampleLaw M).toMeasure :=
      eLpNorm_le_eLpNorm_of_exponent_le hQpge
    have hfinal_bound : eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound_fn M.delta) := by
      rw [hCbound_fn_def]
      exact heLpNorm_final.trans (heLpNorm_le.trans hBoundQ)
    exact ⟨hfinal_bound.trans_lt ENNReal.ofReal_lt_top, hfinal_bound⟩

/-- Compatibility wrapper retaining the former auxiliary telescope. -/
theorem aux_lane4_lambda_inv_moments_uniform_cell :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (q : ℝ), 1 ≤ q →
  ∃ deltaq Cd : ℝ, 0 < deltaq ∧ 0 < Cd ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∃ Cq_fn : ℝ → ℝ, (∀ δ, 0 ≤ δ → 0 < Cq_fn δ) ∧
      (∀ δ1 δ2, 0 ≤ δ1 → δ1 ≤ δ2 → Cq_fn δ1 ≤ Cq_fn δ2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        M.delta ≤ deltaq →
        ∀ N n : ℕ,
          let Y : BilateralField d → ℝ := fun om =>
            Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
              (Homogenization.originCube d 0) (-(n : ℤ))
              (E.chart z r hr
                (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H om N z hr) z r)
          AEStronglyMeasurable Y (chaosSampleLaw M).toMeasure ∧
          eLpNorm Y (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cq_fn M.delta * (if n ≤ N then
                (3 : ℝ) ^ ((d : ℝ) * (n : ℝ) / q) *
                  Real.exp (Cd * (q + q ^ 2) * M.delta ^ 2 * (n : ℝ))
              else Real.exp ((Cd * M.delta + Cd * M.delta ^ 2) * (N : ℝ)))) := by
  intro d hd _ _ E q hq
  obtain ⟨deltaq, Cd, hdq, hCd, h⟩ := aux_lane4_lambda_inv_moments_uniform_cell_unconditional d hd E q hq
  refine ⟨deltaq, Cd, hdq, hCd, ?_⟩
  intro z r hr hr1
  obtain ⟨Cq, hpos, hmono, hbound⟩ := h z r hr hr1
  exact ⟨Cq, hpos, hmono, fun M _Rm H => hbound M H⟩


/-- Compatibility wrapper retaining the former auxiliary telescope. -/
theorem aux_lane4_lambda_inv_moments_uniform_explicit :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ p : ℝ, 1 ≤ p →
    ∃ Cbound_fn : ℝ → ℝ,
      (∀ δ, 0 ≤ δ → δ ≤ delta0 p → 0 < Cbound_fn δ) ∧
      (∀ δ1 δ2, 0 ≤ δ1 → δ1 ≤ δ2 → δ2 ≤ delta0 p → Cbound_fn δ1 ≤ Cbound_fn δ2) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        M.delta ≤ delta0 p →
        ∀ N : ℕ, MemLp (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om : BilateralField d =>
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound_fn M.delta) := by
  intro d hd _ _ E s hs
  obtain ⟨delta0, hpos, h⟩ := aux_lane4_lambda_inv_moments_uniform_explicit_unconditional d hd E s hs
  refine ⟨delta0, hpos, ?_⟩
  intro z r hr hr1 p hp
  obtain ⟨C, hC, hmono, hbound⟩ := h z r hr hr1 p hp
  exact ⟨C, hC, hmono, fun M _Rm H => hbound M H⟩

/-- Uniform inverse ellipticity moments do not require the unused response record. -/
theorem aux_lane4_lambda_inv_moments_uniform_unconditional :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
  ∀ p : ℝ, 1 ≤ p →
  ∃ deltaS : ℝ, 0 < deltaS ∧ ∃ KS : ℝ, 0 < KS ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ deltaS →
      ∀ N : ℕ, MemLp (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal KS := by
  intro d hd _ _ E s hs z r hr hr1 p hp1
  obtain ⟨delta0, hdelta0pos, hmain⟩ := aux_lane4_lambda_inv_moments_uniform_explicit_unconditional d hd E s hs
  obtain ⟨Cbound_fn, hCbound_pos, hCbound_mono, hCbound_main⟩ := hmain z r hr hr1 p hp1
  have hdp := hdelta0pos p hp1
  refine ⟨delta0 p, hdp, Cbound_fn (delta0 p), hCbound_pos (delta0 p) hdp.le (le_refl _), ?_⟩
  intro M H hInfrared hMdelta N
  have hMdelta_nn : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  obtain ⟨hmem, hle⟩ := hCbound_main M H hInfrared hMdelta N
  refine ⟨hmem, hle.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact hCbound_mono M.delta (delta0 p) hMdelta_nn hMdelta (le_refl _)

/-- The actual model-uniform hoist: nitro-7b's shortcut, realized. `KS := Cbound_fn (delta0 p)`
is chosen ONCE (independent of `M`), and monotonicity transports every model's own bound up to
it. This is a genuine `∃ deltaS, ∃ KS, ∀ M, M.delta ≤ deltaS → ...` statement (`KS` chosen before
`∀ M`), unlike `lane4_lambda_inv_moments` itself. -/
theorem lane4_lambda_inv_moments_uniform :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
  ∀ p : ℝ, 1 ≤ p →
  ∃ deltaS : ℝ, 0 < deltaS ∧ ∃ KS : ℝ, 0 < KS ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
      M.delta ≤ deltaS →
      ∀ N : ℕ, MemLp (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om : BilateralField d =>
          (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r s 1)⁻¹)
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal KS := by
  intro d hd _ _ E s hs z r hr hr1 p hp1
  obtain ⟨delta0, hdelta0pos, hmain⟩ := aux_lane4_lambda_inv_moments_uniform_explicit d hd E s hs
  obtain ⟨Cbound_fn, hCbound_pos, hCbound_mono, hCbound_main⟩ := hmain z r hr hr1 p hp1
  have hdp := hdelta0pos p hp1
  refine ⟨delta0 p, hdp, Cbound_fn (delta0 p), hCbound_pos (delta0 p) hdp.le (le_refl _), ?_⟩
  intro M Rm H hInfrared hMdelta N
  have hMdelta_nn : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  obtain ⟨hmem, hle⟩ := hCbound_main M Rm H hInfrared hMdelta N
  refine ⟨hmem, hle.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact hCbound_mono M.delta (delta0 p) hMdelta_nn hMdelta (le_refl _)

end Paper

