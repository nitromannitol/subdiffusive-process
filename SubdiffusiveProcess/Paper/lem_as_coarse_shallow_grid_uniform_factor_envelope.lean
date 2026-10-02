import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_bank_product
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_ahom_ratio
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_envelope
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_point_moments
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_oscillation_moments
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_center_carrier
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_moment_rate
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_bank
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_product
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope_exponential

open MeasureTheory SubdiffusiveProcess Homogenization
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Forward algebra of the uniform factor: a ratio in `[1,E]` and its inverse
are both at most `E`. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_le
    (r E a b : ℝ) (hr : 1 ≤ r) (hrE : r ≤ E) (ha : 0 < a) (hb : 0 ≤ b) :
    b * (r * a + (r * a)⁻¹) ≤ b * (E * (a + a⁻¹)) := by
  have hrinv : r⁻¹ ≤ E := (inv_le_one_of_one_le₀ hr).trans (hr.trans hrE)
  have hainv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have hsum : r * a + r⁻¹ * a⁻¹ ≤ E * a + E * a⁻¹ :=
    add_le_add (mul_le_mul_of_nonneg_right hrE ha.le)
      (mul_le_mul_of_nonneg_right hrinv hainv)
  rw [mul_inv, mul_add E]
  exact mul_le_mul_of_nonneg_left hsum hb

/-- Reverse algebra of the uniform factor: the ratio-free factor costs at most
one more `E^2` than any ratio in `[1,E]`. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_ge
    (r E a b : ℝ) (hr : 1 ≤ r) (hrE : r ≤ E) (ha : 0 < a) (hb : 0 ≤ b) :
    b * (E * (a + a⁻¹)) ≤ E ^ 2 * (b * (r * a + (r * a)⁻¹)) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hE1 : 1 ≤ E := hr.trans hrE
  have hE0 : 0 ≤ E := zero_le_one.trans hE1
  have hainv : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  have h1 : E ≤ E ^ 2 * r := by
    have hEr : 1 ≤ E * r := one_le_mul_of_one_le_of_one_le hE1 hr
    calc
      E = E * 1 := (mul_one E).symm
      _ ≤ E * (E * r) := mul_le_mul_of_nonneg_left hEr hE0
      _ = E ^ 2 * r := by ring
  have h2 : E ≤ E ^ 2 * r⁻¹ := by
    have hEr : 1 ≤ E / r := (one_le_div₀ hr0).mpr hrE
    calc
      E = E * 1 := (mul_one E).symm
      _ ≤ E * (E / r) := mul_le_mul_of_nonneg_left hEr hE0
      _ = E ^ 2 * r⁻¹ := by rw [div_eq_mul_inv]; ring
  have hsum : E * (a + a⁻¹) ≤ E ^ 2 * (r * a + (r * a)⁻¹) := by
    rw [mul_inv]
    calc
      E * (a + a⁻¹) = E * a + E * a⁻¹ := mul_add E a a⁻¹
      _ ≤ E ^ 2 * r * a + E ^ 2 * r⁻¹ * a⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right h1 ha.le)
            (mul_le_mul_of_nonneg_right h2 hainv)
      _ = E ^ 2 * (r * a + r⁻¹ * a⁻¹) := by ring
  calc
    b * (E * (a + a⁻¹)) ≤ b * (E ^ 2 * (r * a + (r * a)⁻¹)) :=
      mul_le_mul_of_nonneg_left hsum hb
    _ = E ^ 2 * (b * (r * a + (r * a)⁻¹)) := by ring

/-- Small disorder absorbs the deterministic `exp(4 τ² k)` loss into half of a
requested exponential growth rate. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_absorb
    (t delta eta : ℝ) (k : ℕ)
    (ht : t ≤ Real.log 2 / 2 * delta ^ 2) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hdeltaeta : delta ≤ eta / 4) :
    Real.exp (4 * t * (k : ℝ)) ≤ (3 : ℝ) ^ (eta / 2 * (k : ℝ)) := by
  have hsq : delta ^ 2 ≤ eta / 4 := by
    calc
      delta ^ 2 = delta * delta := sq delta
      _ ≤ 1 * (eta / 4) := mul_le_mul hdelta1 hdeltaeta hdelta.le zero_le_one
      _ = eta / 4 := one_mul _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog23 : Real.log 2 ≤ Real.log 3 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have heta : 0 ≤ eta := by linarith
  have h4t : 4 * t ≤ Real.log 3 * (eta / 2) := by
    have hB : 2 * Real.log 2 * delta ^ 2 ≤ 2 * Real.log 2 * (eta / 4) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have hC : Real.log 2 * (eta / 2) ≤ Real.log 3 * (eta / 2) :=
      mul_le_mul_of_nonneg_right hlog23 (by linarith)
    linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  calc
    4 * t * (k : ℝ) ≤ Real.log 3 * (eta / 2) * k := mul_le_mul_of_nonneg_right h4t hk
    _ = Real.log 3 * (eta / 2 * k) := by ring

/-- A nonnegative function below a constant multiple of a moment-controlled
function inherits the scaled moment bound. No measurability is needed. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_eLpNorm_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ≥0∞)
    (f g : Ω → ℝ) (c B : ℝ) (hc : 0 ≤ c) (hf : ∀ ω, 0 ≤ f ω)
    (hfg : ∀ ω, f ω ≤ c * g ω) (hg : eLpNorm g p P ≤ ENNReal.ofReal B) :
    eLpNorm f p P ≤ ENNReal.ofReal (c * B) := by
  have hmono : eLpNorm f p P ≤ eLpNorm (c • g) p P := by
    apply eLpNorm_mono_real
    intro ω
    rw [Real.norm_of_nonneg (hf ω)]
    exact hfg ω
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc] at hmono
  calc
    eLpNorm f p P ≤ ENNReal.ofReal c * eLpNorm g p P := hmono
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal B := mul_le_mul_right hg _
    _ = ENNReal.ofReal (c * B) := (ENNReal.ofReal_mul hc).symm

/-- **Uniform-cutoff domination.** For every cutoff `N ≥ k`, the actual
shallow-cell factor is bounded by the `N`-independent factor `D k`, and `D k`
exceeds it by at most `exp(4 τ² k)`. Only the annealed `ahom` ordering is used. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_dominates
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) :
    let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
    let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun N k ω x =>
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (G k ω x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
    let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
      fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
        ∃ x' ∈ Metric.closedBall y (3 * R k),
          v = |G k ω x - G k ω x'|}
    let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω y => sSup (oscSet k ω y)
    let D : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k ω y => Real.exp (osc k ω y) *
        (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
          (Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
            Real.exp (-(G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))))
    ∀ (N k : ℕ), k ≤ N → ∀ (ω : BilateralField d) (y : SpatialCoordinates d),
      0 ≤ Real.exp (osc k ω y) * (s N k ω y + (s N k ω y)⁻¹) ∧
      Real.exp (osc k ω y) * (s N k ω y + (s N k ω y)⁻¹) ≤ D k ω y ∧
      D k ω y ≤ Real.exp (4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
        (Real.exp (osc k ω y) * (s N k ω y + (s N k ω y)⁻¹)) := by
  intro G s R oscSet osc D N k hkN ω y
  obtain ⟨hr1, hrE, -⟩ := lem_as_coarse_shallow_grid_ahom_ratio d M Rm N k hkN
  have ha0 : 0 < Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
    Real.exp_pos _
  have hb0 : 0 ≤ Real.exp (osc k ω y) := (Real.exp_pos _).le
  have hs : s N k ω y =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := rfl
  have hD : D k ω y = Real.exp (osc k ω y) *
      (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
        (Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          (Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹)) := by
    rw [← Real.exp_neg]
  have hE2 : Real.exp (4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) =
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hr0 : 1 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := hr1
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    have hsa : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
      mul_pos (lt_of_lt_of_le one_pos hr0) ha0
    exact mul_nonneg hb0 (add_pos hsa (inv_pos.mpr hsa)).le
  · rw [hs, hD]
    exact aux_lem_as_coarse_shallow_grid_uniform_factor_le _ _ _ _ hr0 hrE ha0 hb0
  · rw [hs, hD, hE2]
    exact aux_lem_as_coarse_shallow_grid_uniform_factor_ge _ _ _ _ hr0 hrE ha0 hb0

/-- **Uniform-cutoff factor moments.** The `N`-independent factor `D k` at every
actual descendant center of `originCube d 0` is measurable and has the requested
exponential moment growth. The constants and disorder threshold are chosen
before the model. The proof compares `D k` with the actual factor at `N = k`. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_moment_rate
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k ω x - G k ω x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet k ω y)
        let D : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => Real.exp (osc k ω y) *
            (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
              (Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
                Real.exp (-(G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))))
        ∀ (k : ℕ) (Q : TriadicCube d),
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          AEStronglyMeasurable (fun ω => D k ω (cubeCenter Q))
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun ω => D k ω (cubeCenter Q))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨B0, delta1, hB0, hd1, hd11, hF⟩ :=
    lem_as_coarse_shallow_grid_actual_factor_moment_rate d hd q (eta / 2) hq
      (by positivity)
  obtain ⟨Cmom, Crate, -, -, h_point_moments⟩ :=
    lem_as_coarse_shallow_grid_centered_point_moments d hd q hq
  obtain ⟨Cosc, -, h_osc_moments⟩ :=
    lem_as_coarse_shallow_grid_centered_oscillation_moments d hd q hq
  have hd0 : 0 < min delta1 (eta / 4) := lt_min hd1 (by positivity)
  have hd01 : min delta1 (eta / 4) ≤ 1 := (min_le_left _ _).trans hd11
  refine ⟨B0, min delta1 (eta / 4), hB0, hd0, hd01, ?_⟩
  intro M Rm H hH hMd G R oscSet osc D k Q hQ
  have hMd1 : M.delta ≤ delta1 := hMd.trans (min_le_left _ _)
  have hMd2 : M.delta ≤ eta / 4 := hMd.trans (min_le_right _ _)
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have h_center : cubeCenter Q ∈ {x : SpatialCoordinates d | ∀ i, |x i| ≤ (1 / 2 : ℝ)} :=
    lem_as_coarse_shallow_grid_center_carrier hQ
  have hdom := aux_lem_as_coarse_shallow_grid_uniform_factor_dominates d M Rm H
  -- measurability, through the `N = k` point factor and its inverse
  have h_point := h_point_moments (min delta1 (eta / 4)) hd0 hd01 M Rm H hH hMd
    (2 * q) ⟨by linarith, le_rfl⟩ k k le_rfl (cubeCenter Q) h_center
  have h_osc := h_osc_moments (min delta1 (eta / 4)) hd0 hd01 M H hH hMd k
    (cubeCenter Q) h_center
  have hr0 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (k - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M k :=
    div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
  have hmeas_s := h_point.2.2.1.aestronglyMeasurable
  have hmeas_sinv := h_point.2.2.2.aestronglyMeasurable
  have hmeas_osc := h_osc.1.aestronglyMeasurable
  have hDeq : (fun ω => D k ω (cubeCenter Q)) = fun ω =>
      Real.exp (osc k ω (cubeCenter Q)) *
        (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M (k - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M k)⁻¹ *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (k - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M k *
              Real.exp (G k ω (cubeCenter Q) -
                (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) +
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (k - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M k *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (k - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M k *
              Real.exp (G k ω (cubeCenter Q) -
                (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))⁻¹)) := by
    funext ω
    change Real.exp (osc k ω (cubeCenter Q)) *
        (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
          (Real.exp (G k ω (cubeCenter Q) - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
            Real.exp (-(G k ω (cubeCenter Q) -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))) = _
    rw [inv_mul_cancel_left₀ hr0.ne', mul_inv, mul_inv_cancel_left₀ hr0.ne',
      Real.exp_neg]
  have hmeas : AEStronglyMeasurable (fun ω => D k ω (cubeCenter Q))
      (chaosSampleLaw M).toMeasure := by
    rw [hDeq]
    exact hmeas_osc.mul (((hmeas_s.const_mul _).add
      (hmeas_sinv.const_mul _)).const_mul _)
  refine ⟨hmeas, ?_⟩
  -- moment, by comparison with the actual factor at `N = k`
  have hXk := hF M Rm H hH hMd1 k k le_rfl Q hQ
  have hc0 : 0 ≤ Real.exp (4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) :=
    (Real.exp_pos _).le
  have hbound := aux_lem_as_coarse_shallow_grid_uniform_factor_eLpNorm_le
    (chaosSampleLaw M).toMeasure (ENNReal.ofReal q)
    (fun ω => D k ω (cubeCenter Q)) _ _ _ hc0
    (fun ω => ((hdom k k le_rfl ω (cubeCenter Q)).1).trans
      ((hdom k k le_rfl ω (cubeCenter Q)).2.1))
    (fun ω => (hdom k k le_rfl ω (cubeCenter Q)).2.2) hXk
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have habsorb := aux_lem_as_coarse_shallow_grid_uniform_factor_absorb
    (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) M.delta eta k
    (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M) hdelta (hMd1.trans hd11) hMd2
  have hY0 : 0 ≤ (3 : ℝ) ^ (eta / 2 * (k : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsplit : (3 : ℝ) ^ (eta * (k : ℝ)) =
      (3 : ℝ) ^ (eta / 2 * (k : ℝ)) * (3 : ℝ) ^ (eta / 2 * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsplit]
  calc
    Real.exp (4 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
        (B0 * (3 : ℝ) ^ (eta / 2 * (k : ℝ))) ≤
      (3 : ℝ) ^ (eta / 2 * (k : ℝ)) * (B0 * (3 : ℝ) ^ (eta / 2 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right habsorb (mul_nonneg hB0.le hY0)
    _ = B0 * ((3 : ℝ) ^ (eta / 2 * (k : ℝ)) * (3 : ℝ) ^ (eta / 2 * (k : ℝ))) := by
        ring

/-- The uniform factor times one plus a shifted unit-bank coordinate: the
measurable, `N`-independent test variable of one retained cell. -/
theorem aux_lem_as_coarse_shallow_grid_uniform_factor_bank_product
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k ω x - G k ω x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet k ω y)
        let D : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => Real.exp (osc k ω y) *
            (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
              (Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
                Real.exp (-(G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))))
        ∀ (k : ℕ) (Q : TriadicCube d),
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          ∀ Z : BilateralField d → ℝ,
            AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure →
            eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal C →
            AEStronglyMeasurable (fun ω => D k ω (cubeCenter Q) *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
              (chaosSampleLaw M).toMeasure ∧
            eLpNorm (fun ω => D k ω (cubeCenter Q) *
              (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
              (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hD⟩ :=
    aux_lem_as_coarse_shallow_grid_uniform_factor_moment_rate d hd (2 * q) eta
      (by linarith) heta
  refine ⟨B0, delta0, hB0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd G R oscSet osc D k Q hQ Z hZ hZbound
  have hDk := hD M Rm H hH hMd k Q hQ
  have hshiftmeas : AEStronglyMeasurable
      (fun ω => Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))
      (chaosSampleLaw M).toMeasure := by
    change AEStronglyMeasurable
      (Z ∘ aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q)) _
    exact hZ.comp_measurePreserving
      (lem_as_coarse_shallow_grid_scale_shift M k (cubeCenter Q))
  have hshiftbound := lem_as_coarse_shallow_grid_shifted_bank M k (cubeCenter Q)
    Z (ENNReal.ofReal (2 * q)) (ENNReal.ofReal C) hZ hZbound
  have hprod := lem_as_coarse_shallow_grid_factor_product
    (chaosSampleLaw M).toMeasure q hq hDk.1 hshiftmeas
    (ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ)))) (ENNReal.ofReal C)
    hDk.2 hshiftbound
  refine ⟨hDk.1.mul (aestronglyMeasurable_const.add hshiftmeas), ?_⟩
  have hpow : 0 ≤ (3 : ℝ) ^ (eta * (k : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    eLpNorm (fun ω => D k ω (cubeCenter Q) *
        (1 + Z (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)))
        (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) * (1 + ENNReal.ofReal C) := hprod
    _ = ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hC,
        ← ENNReal.ofReal_mul (mul_nonneg hB0.le hpow)]
      congr 1
      ring

/-- **Almost-sure uniform-cutoff envelope.** For any finite bank of unit-scale
variables with a common `L^{2q}` bound, one random constant controls every
actual shallow-cell factor times one plus its shifted bank coordinate,
simultaneously for all cutoffs `N ≥ k`, all depths `k`, all descendants of
`originCube d 0` and all bank indices. The disorder threshold depends only on
`d, q, eta`. -/
theorem lem_as_coarse_shallow_grid_uniform_factor_envelope
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (ι : Type*) [Fintype ι]
    (q eta rho : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) (hetarho : eta < rho)
    (hrate : (d : ℝ) < q * (rho - eta)) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (C : ℝ), 0 ≤ C →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => H ω x + ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k ω x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k ω x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k ω x - G k ω x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet k ω y)
        ∀ Z : ι → BilateralField d → ℝ,
          (∀ b, AEStronglyMeasurable (Z b) (chaosSampleLaw M).toMeasure) →
          (∀ b, eLpNorm (Z b) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal C) →
          ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 1 ≤ K ∧
            ∀ (N k : ℕ), k ≤ N → ∀ Q : TriadicCube d,
              Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) → ∀ b : ι,
              |Real.exp (osc k ω (cubeCenter Q)) *
                  (s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹) *
                (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))| ≤
                K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  obtain ⟨B0, delta0, hB0, hd0, hd01, hprod⟩ :=
    aux_lem_as_coarse_shallow_grid_uniform_factor_bank_product d hd q eta hq heta
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro C hC M Rm H hH hMd G s R oscSet osc Z hZ hZbound
  have hdom := aux_lem_as_coarse_shallow_grid_uniform_factor_dominates d M Rm H
  have hP := hprod C hC M Rm H hH hMd
  let D : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun k ω y => Real.exp (osc k ω y) *
      (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (k : ℝ)) *
        (Real.exp (G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          Real.exp (-(G k ω y - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))))
  let Gset : ℕ → Finset (TriadicCube d × ι) := fun k =>
    descendantsAtScale (originCube d 0) (-(k : ℤ)) ×ˢ (Finset.univ : Finset ι)
  let X : ℕ → TriadicCube d × ι → BilateralField d → ℝ := fun k i ω =>
    D k ω (cubeCenter i.1) *
      (1 + Z i.2 (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter i.1) ω))
  have hcard : ∀ k : ℕ,
      ((Gset k).card : ℝ) ≤ (Fintype.card ι : ℝ) * (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
    intro k
    have hdepth :
        (descendantsAtScale (originCube d 0) (-(k : ℤ))).card = (3 ^ d) ^ k := by
      rw [descendantsAtScale_eq_descendantsAtDepth (originCube d 0)
        (by simp [originCube])]
      convert descendantsAtDepth_card (originCube d 0) k using 1; simp [originCube]
    have hpow : (((3 ^ d) ^ k : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
      calc
        (((3 ^ d) ^ k : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ k := by norm_cast
        _ = ((3 : ℝ) ^ (d : ℝ)) ^ (k : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        _ = (3 : ℝ) ^ ((d : ℝ) * (k : ℝ)) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hG : (Gset k).card = (3 ^ d) ^ k * Fintype.card ι := by
      simp only [Gset, Finset.card_product, hdepth, Finset.card_univ]
    rw [hG, Nat.cast_mul, hpow, mul_comm]
  have hX : ∀ k i, i ∈ Gset k →
      AEStronglyMeasurable (X k i) (chaosSampleLaw M).toMeasure := by
    intro k i hi
    exact (hP k i.1 (Finset.mem_product.mp hi).1 (Z i.2) (hZ i.2) (hZbound i.2)).1
  have hLp : ∀ k i, i ∈ Gset k →
      eLpNorm (X k i) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B0 * (1 + C) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
    intro k i hi
    exact (hP k i.1 (Finset.mem_product.mp hi).1 (Z i.2) (hZ i.2) (hZbound i.2)).2
  have henv := lem_as_coarse_shallow_grid_envelope_exponential
    (chaosSampleLaw M).toMeasure Gset X (d : ℝ) q (B0 * (1 + C))
    (Fintype.card ι : ℝ) eta rho (by linarith) (mul_nonneg hB0.le (by linarith))
    (Nat.cast_nonneg _) hetarho hrate hcard hX hLp
  filter_upwards [henv] with ω hω
  obtain ⟨K, hK1, hK⟩ := hω
  refine ⟨K, hK1, ?_⟩
  intro N k hkN Q hQ b
  have hmem : (Q, b) ∈ Gset k := Finset.mem_product.mpr ⟨hQ, Finset.mem_univ b⟩
  have hXb : |X k (Q, b) ω| ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := hK k (Q, b) hmem
  obtain ⟨hX0, hXD, -⟩ := hdom N k hkN ω (cubeCenter Q)
  have hD0 : 0 ≤ D k ω (cubeCenter Q) := hX0.trans hXD
  calc
    |Real.exp (osc k ω (cubeCenter Q)) *
          (s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹) *
        (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))| =
      Real.exp (osc k ω (cubeCenter Q)) *
          (s N k ω (cubeCenter Q) + (s N k ω (cubeCenter Q))⁻¹) *
        |1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)| := by
      rw [abs_mul, abs_of_nonneg hX0]
    _ ≤ D k ω (cubeCenter Q) *
        |1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω)| :=
      mul_le_mul_of_nonneg_right hXD (abs_nonneg _)
    _ = |X k (Q, b) ω| := by
      change _ = |D k ω (cubeCenter Q) *
        (1 + Z b (aux_lem_as_coarse_shallow_grid_scaleShift k (cubeCenter Q) ω))|
      rw [abs_mul, abs_of_nonneg hD0]
    _ ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := hXb

end Paper




