import Mathlib
import SubdiffusiveProcess.Paper.calib3_HT
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.prop_growth_trunc_energy_assembly
import SubdiffusiveProcess.Paper.aux_macro_moment_bank

/-! Stage 3 (calibration): coefficient envelope and log-Lipschitz majorant, with moments, of the top-block-removed model
`HT_j = -∑_{i<j} ω(-i)` on a unit cube, from the same statement for the infrared-free coefficient
(`aux_prop_growth_trunc_energy_assembly_root_extremes` at `L0 = 0`): `A^{HT_j}_N = c_j · A^0_N / A^0_{j-1}`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- `A^{HT_j}_N = c_j · A^0_N / A^0_{j-1}` with `c_j = (ahom_{j-1} e^{jτ²})⁻¹` (`j ≥ 1`), pointwise. -/
theorem aux_calib3_envelope_ratio {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j N : ℕ) (hj : 0 < j)
    (om : BilateralField d) (x : SpatialCoordinates d) :
    cutoffCoefficient M (calib3_HT d j) om N x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1) * Real.exp ((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹ *
        (cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om N x /
          cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om (j - 1) x) := by
  have hj1 : j - 1 + 1 = j := by omega
  unfold cutoffCoefficient cutoffPotential calib3_HT
  simp only [infraredPartialSum, Finset.sum_range_zero, ContinuousMap.zero_apply,
    ContinuousMap.neg_apply, ContinuousMap.coe_sum, Finset.sum_apply, zero_add]
  rw [hj1]
  have hp : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    have h1 : 1 ≤ j := hj
    rw [Nat.cast_sub h1, Nat.cast_one]
    ring
  rw [hp]
  have hA : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ≠ 0 := ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  have hB : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1)) ≠ 0 := ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (j - 1))
  rw [show Real.exp (-∑ c ∈ Finset.range j, (om (-Int.ofNat c)) x +
          ∑ c ∈ Finset.range (N + 1), (om (-Int.ofNat c)) x - (↑N + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        = Real.exp (∑ c ∈ Finset.range (N + 1), (om (-Int.ofNat c)) x - (↑N + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          Real.exp (-(∑ c ∈ Finset.range j, (om (-Int.ofNat c)) x - (j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
          Real.exp (-((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) from by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring]
  rw [mul_inv, div_eq_mul_inv, mul_inv, inv_inv, ← Real.exp_neg, ← Real.exp_neg]
  field_simp [hA, hB] <;> ring

theorem aux_calib3_envelope_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    0 < cutoffCoefficient M H om N x := by
  unfold cutoffCoefficient
  exact mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- Pointwise envelope arithmetic for a quotient. -/
theorem aux_calib3_envelope_arith (c a1 a2 M1 M2 Cj : ℝ) (hc : 0 < c) (hM1 : 0 < M1) (hM2 : 0 < M2)
    (h1 : M1⁻¹ ≤ a1 ∧ a1 ≤ M1) (h2 : M2⁻¹ ≤ a2 ∧ a2 ≤ M2) (hCj : c ≤ Cj ∧ c⁻¹ ≤ Cj) :
    (Cj * (M1 * M2))⁻¹ ≤ c * (a1 / a2) ∧ c * (a1 / a2) ≤ Cj * (M1 * M2) := by
  have hM1inv : 0 < M1⁻¹ := inv_pos.2 hM1
  have hM2inv : 0 < M2⁻¹ := inv_pos.2 hM2
  have ha1 : 0 < a1 := lt_of_lt_of_le hM1inv h1.1
  have ha2 : 0 < a2 := lt_of_lt_of_le hM2inv h2.1
  have hCj0 : 0 < Cj := lt_of_lt_of_le hc hCj.1
  have hCjinv : Cj⁻¹ ≤ c := (inv_le_comm₀ hc hCj0).1 hCj.2
  have hinv2 : a2⁻¹ ≤ M2 := by
    have := (inv_le_inv₀ ha2 hM2inv).2 h2.1
    simpa using this
  have hinv2' : M2⁻¹ ≤ a2⁻¹ := (inv_le_inv₀ hM2 ha2).2 h2.2
  have hdiv_upper : a1 / a2 ≤ M1 * M2 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul h1.2 hinv2 (le_of_lt (inv_pos.2 ha2)) (le_of_lt hM1)
  have hdiv_lower : (M1 * M2)⁻¹ ≤ a1 / a2 := by
    rw [div_eq_mul_inv, mul_inv]
    exact mul_le_mul h1.1 hinv2' (le_of_lt hM2inv) (le_of_lt ha1)
  have ha_div_nonneg : 0 ≤ a1 / a2 := (div_pos ha1 ha2).le
  constructor
  · rw [mul_inv]
    exact mul_le_mul hCjinv hdiv_lower (le_of_lt (inv_pos.2 (mul_pos hM1 hM2))) (le_of_lt hc)
  · exact mul_le_mul hCj.1 hdiv_upper ha_div_nonneg (le_of_lt hCj0)

/-- Log-Lipschitz arithmetic for a quotient. -/
theorem aux_calib3_envelope_loglip (c a1 a2 b1 b2 : ℝ) (hc : 0 < c) (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 < b1)
    (hb2 : 0 < b2) :
    |Real.log (c * (a1 / a2)) - Real.log (c * (b1 / b2))| ≤ |Real.log a1 - Real.log b1| + |Real.log a2 - Real.log b2| := by
  have h1 : Real.log (c * (a1 / a2)) = Real.log c + (Real.log a1 - Real.log a2) := by
    rw [Real.log_mul hc.ne' (ne_of_gt (div_pos ha1 ha2))]
    rw [Real.log_div ha1.ne' ha2.ne']
  have h2 : Real.log (c * (b1 / b2)) = Real.log c + (Real.log b1 - Real.log b2) := by
    rw [Real.log_mul hc.ne' (ne_of_gt (div_pos hb1 hb2))]
    rw [Real.log_div hb1.ne' hb2.ne']
  rw [h1, h2]
  convert abs_sub (Real.log a1 - Real.log b1) (Real.log a2 - Real.log b2) using 2 <;> ring

/-- Moments of `Cj · X · Y`. -/
theorem aux_calib3_envelope_moment_prod {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (q : ℝ) (hq : 1 ≤ q)
    (X Y : Ω → ℝ) (Cj bX bY : ℝ) (hCj : 0 ≤ Cj) (hX : MemLp X (ENNReal.ofReal (2 * q)) μ)
    (hY : MemLp Y (ENNReal.ofReal (2 * q)) μ) (hXb : eLpNorm X (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal bX)
    (hYb : eLpNorm Y (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal bY) :
    MemLp (fun om => Cj * (X om * Y om)) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun om => Cj * (X om * Y om)) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (Cj * (bX * bY)) := by
  have hXY := aux_aux_macro_moment_bank_product_moment μ q X Y hX.1 hY.1
  have hXY_mem : MemLp (fun om => X om * Y om) (ENNReal.ofReal q) μ :=
    ⟨hX.1.mul hY.1, lt_of_le_of_lt hXY (ENNReal.mul_lt_top hX.2 hY.2)⟩
  have hmem : MemLp (fun om => Cj * (X om * Y om)) (ENNReal.ofReal q) μ := hXY_mem.const_mul Cj
  refine ⟨hmem, ?_⟩
  have hEq : (fun om => Cj * (X om * Y om)) = Cj • (fun om => X om * Y om) := by funext om; rfl
  have hb : eLpNorm (fun om => Cj * (X om * Y om)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal Cj * (ENNReal.ofReal bX * ENNReal.ofReal bY) := by
    calc eLpNorm (fun om => Cj * (X om * Y om)) (ENNReal.ofReal q) μ
        = eLpNorm (Cj • (fun om => X om * Y om)) (ENNReal.ofReal q) μ := by rw [hEq]
      _ ≤ ‖Cj‖ₑ * eLpNorm (fun om => X om * Y om) (ENNReal.ofReal q) μ := eLpNorm_const_smul_le
      _ = ENNReal.ofReal Cj * eLpNorm (fun om => X om * Y om) (ENNReal.ofReal q) μ := by
          rw [Real.enorm_of_nonneg hCj]
      _ ≤ ENNReal.ofReal Cj * (ENNReal.ofReal bX * ENNReal.ofReal bY) :=
          mul_le_mul' le_rfl (le_trans hXY (mul_le_mul' hXb hYb))
  have hfinal : ENNReal.ofReal Cj * (ENNReal.ofReal bX * ENNReal.ofReal bY) ≤
      ENNReal.ofReal (Cj * (bX * bY)) := by
    by_cases hbX : 0 ≤ bX
    · have h1 : ENNReal.ofReal (Cj * (bX * bY)) = ENNReal.ofReal Cj * ENNReal.ofReal (bX * bY) :=
        ENNReal.ofReal_mul hCj
      have h2 : ENNReal.ofReal (bX * bY) = ENNReal.ofReal bX * ENNReal.ofReal bY :=
        ENNReal.ofReal_mul hbX
      rw [h1, h2]
    · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hbX), zero_mul, mul_zero]
      exact zero_le _
  exact le_trans hb hfinal

/-- Moments of `X + κ Y` (`κ ≥ 0`) at order `q`, from order `2q`. -/
theorem aux_calib3_envelope_moment_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℝ) (hq : 1 ≤ q)
    (X Y : Ω → ℝ) (κ bX bY : ℝ) (hκ : 0 ≤ κ) (hbX : 0 ≤ bX) (hbY : 0 ≤ bY)
    (hX : MemLp X (ENNReal.ofReal (2 * q)) μ)
    (hY : MemLp Y (ENNReal.ofReal (2 * q)) μ) (hXb : eLpNorm X (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal bX)
    (hYb : eLpNorm Y (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal bY) :
    MemLp (fun om => X om + κ * Y om) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun om => X om + κ * Y om) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (bX + κ * bY) := by
  have hle : ENNReal.ofReal q ≤ ENNReal.ofReal (2 * q) := ENNReal.ofReal_le_ofReal (by linarith)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  have hXq : MemLp X (ENNReal.ofReal q) μ := hX.mono_exponent hle
  have hYq : MemLp Y (ENNReal.ofReal q) μ := hY.mono_exponent hle
  have hKY : MemLp (fun om => κ * Y om) (ENNReal.ofReal q) μ := hYq.const_mul κ
  refine ⟨hXq.add hKY, ?_⟩
  have h1 : eLpNorm (fun om => X om + κ * Y om) (ENNReal.ofReal q) μ ≤
      eLpNorm X (ENNReal.ofReal q) μ + eLpNorm (fun om => κ * Y om) (ENNReal.ofReal q) μ :=
    eLpNorm_add_le hXq.1 hKY.1 hp1
  have h2 : eLpNorm (fun om => κ * Y om) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal κ * eLpNorm Y (ENNReal.ofReal q) μ := by
    have h := eLpNorm_const_smul_le (c := κ) (p := ENNReal.ofReal q) (μ := μ) (f := Y)
    rw [Real.enorm_of_nonneg hκ] at h
    exact h
  have h3 : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal bX :=
    (eLpNorm_le_eLpNorm_of_exponent_le hle hX.1).trans hXb
  have h4 : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal bY :=
    (eLpNorm_le_eLpNorm_of_exponent_le hle hY.1).trans hYb
  calc eLpNorm (fun om => X om + κ * Y om) (ENNReal.ofReal q) μ
      ≤ eLpNorm X (ENNReal.ofReal q) μ + eLpNorm (fun om => κ * Y om) (ENNReal.ofReal q) μ := h1
    _ ≤ ENNReal.ofReal bX + ENNReal.ofReal κ * ENNReal.ofReal bY :=
        add_le_add h3 ((h2.trans (mul_le_mul_left' h4 _)))
    _ = ENNReal.ofReal (bX + κ * bY) := by
        rw [← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_add hbX (mul_nonneg hκ hbY)]

/-- **Envelope and log-Lipschitz majorant of the top-block-removed coefficient** on a unit cube, with moments: the statement of
`aux_prop_growth_trunc_energy_assembly_root_extremes` (unit cube, cutoff level `N`) for the potential `HT_j`, `j ≥ 1`. -/
theorem calib3_envelope (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cp Cd cd : ℝ, 0 < Cp ∧ 0 < Cd ∧ 0 < cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ cd / (2 * q) →
        ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
        ∃ (D Mx : ℕ → BilateralField d → ℝ) (CD CE : ℝ), 0 ≤ CD ∧ 0 ≤ CE ∧
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 < Mx N om ∧
            (∀ x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M (calib3_HT d j) om N x ∧
                cutoffCoefficient M (calib3_HT d j) om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M (calib3_HT d j) om N x) -
                  Real.log (cutoffCoefficient M (calib3_HT d j) om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) ∧
          (∀ N, eLpNorm (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N))) := by
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hroot⟩ :=
    aux_prop_growth_trunc_energy_assembly_root_extremes d hd (2 * q) (by linarith)
  refine ⟨Cp, Cd, cd / 2, hCp, hCd, by positivity, ?_⟩
  intro M hδ j hj z
  have hδ' : M.delta ≤ cd / (2 * (2 * q)) := by
    have e : cd / 2 / (2 * q) = cd / (2 * (2 * q)) := by ring
    rw [← e]; exact hδ
  obtain ⟨D0, Mx0, CD0, CE0, hCD0, hCE0, h0, hae, hmem, hDm, hMm⟩ :=
    hroot M 0 hδ' z 1 one_pos le_rfl
  have hδ0 : 0 < M.delta := M.shellPrefix.delta_pos
  -- deterministic constants
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1) *
      Real.exp ((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact inv_pos.2 (mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (j - 1)) (Real.exp_pos _))
  obtain ⟨Cj, hCjdef⟩ : ∃ Cj : ℝ, Cj = max c c⁻¹ := ⟨_, rfl⟩
  have hCj : c ≤ Cj ∧ c⁻¹ ≤ Cj := ⟨hCjdef ▸ le_max_left _ _, hCjdef ▸ le_max_right _ _⟩
  have hCj0 : 0 < Cj := lt_of_lt_of_le hc0 hCj.1
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (3 : ℝ) ^ j := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  obtain ⟨rate, hrate⟩ : ∃ rate : ℝ, rate = Cd * M.delta + Cp * M.delta ^ 2 := ⟨_, rfl⟩
  refine ⟨fun N om => D0 N om + κ * D0 (j - 1) om, fun N om => Cj * (Mx0 N om * Mx0 (j - 1) om),
    CD0 + κ * (CD0 * Real.sqrt (1 + ((j - 1 : ℕ) : ℝ))),
    Cj * (CE0 * (CE0 * Real.exp (rate * ((j - 1 : ℕ) : ℝ)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro N om
    exact ⟨add_nonneg (h0 N om).1 (mul_nonneg hκ0 (h0 (j - 1) om).1),
      mul_nonneg hCj0.le (mul_nonneg (h0 N om).2 (h0 (j - 1) om).2)⟩
  · filter_upwards [hae] with om h N
    obtain ⟨hpN, hbN, hlN⟩ := h N
    obtain ⟨hpJ, hbJ, hlJ⟩ := h (j - 1)
    refine ⟨mul_pos hCj0 (mul_pos hpN hpJ), ?_, ?_⟩
    · intro x hx
      rw [aux_calib3_envelope_ratio M j N hj om x, ← hcdef]
      exact aux_calib3_envelope_arith c _ _ (Mx0 N om) (Mx0 (j - 1) om) Cj hc0 hpN hpJ (hbN x hx) (hbJ x hx) hCj
    · intro x y hx hy
      rw [aux_calib3_envelope_ratio M j N hj om x, aux_calib3_envelope_ratio M j N hj om y, ← hcdef]
      have h1 := aux_calib3_envelope_loglip c
        (cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om N x)
        (cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om (j - 1) x)
        (cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om N y)
        (cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om (j - 1) y) hc0
        (aux_calib3_envelope_pos M _ om N x) (aux_calib3_envelope_pos M _ om (j - 1) x)
        (aux_calib3_envelope_pos M _ om N y) (aux_calib3_envelope_pos M _ om (j - 1) y)
      have h2 := add_le_add (hlN x y hx hy) (hlJ x y hx hy)
      have hk : (3 : ℝ) ^ (j - 1) ≤ κ * (3 : ℝ) ^ N := by
        rw [hκdef]
        calc (3 : ℝ) ^ (j - 1) ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)
          _ = (3 : ℝ) ^ j * 1 := (mul_one _).symm
          _ ≤ (3 : ℝ) ^ j * (3 : ℝ) ^ N := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) (by positivity)
      have hDJ := (h0 (j - 1) om).1
      have hdist := dist_nonneg (x := x) (y := y)
      have h3 : D0 (j - 1) om * (3 : ℝ) ^ (j - 1) * dist x y ≤ D0 (j - 1) om * (κ * (3 : ℝ) ^ N) * dist x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hDJ) hdist
      have e : (D0 N om + κ * D0 (j - 1) om) * (3 : ℝ) ^ N * dist x y =
          D0 N om * (3 : ℝ) ^ N * dist x y + D0 (j - 1) om * (κ * (3 : ℝ) ^ N) * dist x y := by ring
      show _ ≤ (D0 N om + κ * D0 (j - 1) om) * (3 : ℝ) ^ N * dist x y
      rw [e]
      linarith
  · intro N
    refine ⟨(aux_calib3_envelope_moment_sum (chaosSampleLaw M).toMeasure q hq (D0 N) (D0 (j - 1)) κ _ _ hκ0
        (by positivity) (by positivity) (hmem N).1 (hmem (j - 1)).1 (hDm N) (hDm (j - 1))).1,
      (aux_calib3_envelope_moment_prod (chaosSampleLaw M).toMeasure q hq (Mx0 N) (Mx0 (j - 1)) Cj _ _ hCj0.le
        (hmem N).2 (hmem (j - 1)).2 (hMm N) (hMm (j - 1))).1⟩
  · intro N
    refine (aux_calib3_envelope_moment_sum (chaosSampleLaw M).toMeasure q hq (D0 N) (D0 (j - 1)) κ _ _ hκ0
        (by positivity) (by positivity) (hmem N).1 (hmem (j - 1)).1 (hDm N) (hDm (j - 1))).2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : (1 : ℝ) ≤ Real.sqrt (1 + (N : ℝ)) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + (N : ℝ) by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      rwa [Real.sqrt_one] at h
    have ht : 0 ≤ κ * (CD0 * Real.sqrt (1 + ((j - 1 : ℕ) : ℝ))) := by positivity
    have := le_mul_of_one_le_right ht hs
    nlinarith
  · intro N
    refine (aux_calib3_envelope_moment_prod (chaosSampleLaw M).toMeasure q hq (Mx0 N) (Mx0 (j - 1)) Cj _ _ hCj0.le
        (hmem N).2 (hmem (j - 1)).2 (hMm N) (hMm (j - 1))).2.trans (le_of_eq ?_)
    congr 1
    rw [← hrate]
    ring

end Paper
