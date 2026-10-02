import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_es
import SubdiffusiveProcess.Paper.lem_15

/-! Moment bounds of the two fibre envelopes of the fine-layer step: from the layer-norm moments of `S` and
a moment of the growth constant `K`, the `L^p` norms of the deletion envelope `env₁` and of the
Efron--Stein envelope `env₂` are bounded by explicit expressions, each carrying the endpoint gap
linearly.  Hölder with two factors of exponent `2p` and `√K ≤ 1 + K`; no other property of `K` is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

theorem aux_prop_conc_fine_layer_env_env1_le (Cex gap Astrip cA s K : ℝ) (hCex : 0 ≤ Cex) (hgap : 0 ≤ gap)
    (hAs : 0 ≤ Astrip) (hcA : 0 ≤ cA) (hs : 0 ≤ s) (hK : 0 ≤ K) :
    aux_prop_conc_fine_fibre_es_env1 Cex gap Astrip cA s K ≤
      (Cex * gap * (Astrip + cA * Real.sqrt Astrip)) * ((s * Real.exp (Cex * s)) * (1 + K)) := by
  unfold aux_prop_conc_fine_fibre_es_env1
  have hsq : Real.sqrt K ≤ 1 + K :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg K]⟩
  have hin : K * Astrip + cA * Real.sqrt K * Real.sqrt Astrip ≤ (Astrip + cA * Real.sqrt Astrip) * (1 + K) := by
    have h1 : K * Astrip ≤ Astrip * (1 + K) := by nlinarith
    have h2 : cA * Real.sqrt K * Real.sqrt Astrip ≤ cA * Real.sqrt Astrip * (1 + K) := by
      have := mul_le_mul_of_nonneg_left hsq (mul_nonneg hcA (Real.sqrt_nonneg Astrip))
      nlinarith
    nlinarith
  have hpos : 0 ≤ Cex * s * Real.exp (Cex * s) * gap := by positivity
  calc Cex * s * Real.exp (Cex * s) * gap * (K * Astrip + cA * Real.sqrt K * Real.sqrt Astrip)
      ≤ Cex * s * Real.exp (Cex * s) * gap * ((Astrip + cA * Real.sqrt Astrip) * (1 + K)) :=
        mul_le_mul_of_nonneg_left hin hpos
    _ = _ := by ring

theorem aux_prop_conc_fine_layer_env_env2_le (Cex gap Acore Astrip Ma Me s K : ℝ) (hCex : 0 ≤ Cex)
    (hgap : 0 ≤ gap) (hAc : 0 ≤ Acore) (hAs : 0 ≤ Astrip) (hMa : 0 ≤ Ma) (hMe : 0 ≤ Me) (hs : 0 ≤ s)
    (hK : 0 ≤ K) :
    aux_prop_conc_fine_fibre_es_env2 Cex gap Acore Astrip Ma Me s K ≤
      (Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 * gap *
          Real.sqrt (Acore + Astrip)) *
        ((Real.sqrt Ma * (s * Real.exp (3 / 2 * Cex * s)) + Real.sqrt Me * Real.exp (3 / 2 * Cex * s)) *
          (1 + K)) := by
  unfold aux_prop_conc_fine_fibre_es_env2
  have hsqK : Real.sqrt K ≤ 1 + K := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg K]⟩
  have hexp : Real.sqrt (Real.exp (Cex * s)) = Real.exp (Cex * s / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    congr 1; ring
  have h1 : Real.sqrt (Cex * Real.exp (Cex * s) * ((Acore + Astrip) * K)) =
      Real.sqrt Cex * Real.exp (Cex * s / 2) * Real.sqrt (Acore + Astrip) * Real.sqrt K := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), hexp]
    ring
  have h2 : Real.sqrt (2 * (s ^ 2 * Ma + Me)) ≤ Real.sqrt 2 * (s * Real.sqrt Ma + Real.sqrt Me) := by
    rw [Real.sqrt_mul (by norm_num)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have := Real.sq_sqrt hMa
    have := Real.sq_sqrt hMe
    nlinarith [Real.sqrt_nonneg Ma, Real.sqrt_nonneg Me, mul_nonneg hs (mul_nonneg (Real.sqrt_nonneg Ma) (Real.sqrt_nonneg Me))]
  have h3 : Real.exp (Cex * s) * Real.exp (Cex * s / 2) = Real.exp (3 / 2 * Cex * s) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1]
  have hE : 0 < Real.exp (Cex * s) := Real.exp_pos _
  have hE2 : 0 < Real.exp (Cex * s / 2) := Real.exp_pos _
  set c := Real.sqrt (2 * (Cex + Cex)) with hc
  set a := Real.sqrt Cex with ha
  set A := Real.sqrt (Acore + Astrip) with hA
  have hpos : 0 ≤ c * gap * (Cex * Real.exp (Cex * s)) := by positivity
  calc c * gap * (Cex * Real.exp (Cex * s) * Real.sqrt (2 * (s ^ 2 * Ma + Me)) *
        (a * Real.exp (Cex * s / 2) * A * Real.sqrt K))
      ≤ c * gap * (Cex * Real.exp (Cex * s) * (Real.sqrt 2 * (s * Real.sqrt Ma + Real.sqrt Me)) *
        (a * Real.exp (Cex * s / 2) * A * (1 + K))) := by
        gcongr
    _ = _ := by
        have : Real.exp (Cex * s) * Real.exp (Cex * s / 2) = Real.exp (3 / 2 * Cex * s) := h3
        calc c * gap * (Cex * Real.exp (Cex * s) * (Real.sqrt 2 * (s * Real.sqrt Ma + Real.sqrt Me)) *
              (a * Real.exp (Cex * s / 2) * A * (1 + K)))
            = (c * Cex * a * Real.sqrt 2 * gap * A) * ((Real.exp (Cex * s) * Real.exp (Cex * s / 2)) *
                (s * Real.sqrt Ma + Real.sqrt Me) * (1 + K)) := by ring
          _ = _ := by rw [this]; ring

/-- **Moments of the fibre envelopes.** -/
theorem prop_conc_fine_layer_env {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (S K : Y → ℝ) (hS : AEStronglyMeasurable S μ) (hK : AEStronglyMeasurable K μ)
    (hS0 : ∀ y, 0 ≤ S y) (hK0 : ∀ᵐ y ∂μ, 0 ≤ K y) (pe : ℝ) (hpe : 1 ≤ pe)
    (Cex gap Astrip Acore Ma Me cA B L1 L0 : ℝ) (hCex : 0 ≤ Cex) (hgap : 0 ≤ gap)
    (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore) (hMa : 0 ≤ Ma) (hMe : 0 ≤ Me) (hcA : 0 ≤ cA) (hB : 0 ≤ B)
    (hL1 : 0 ≤ L1) (hL0 : 0 ≤ L0)
    (hKB : eLpNorm K (ENNReal.ofReal (2 * pe)) μ ≤ ENNReal.ofReal B)
    (hS1 : eLpNorm (fun y => S y * Real.exp (Cex * S y)) (ENNReal.ofReal (2 * pe)) μ ≤
      ENNReal.ofReal L1)
    (hS15 : eLpNorm (fun y => S y * Real.exp (3 / 2 * Cex * S y)) (ENNReal.ofReal (2 * pe)) μ ≤
      ENNReal.ofReal L1)
    (hE15 : eLpNorm (fun y => Real.exp (3 / 2 * Cex * S y)) (ENNReal.ofReal (2 * pe)) μ ≤
      ENNReal.ofReal L0) :
    eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env1 Cex gap Astrip cA (S y) (K y))
        (ENNReal.ofReal pe) μ ≤
      ENNReal.ofReal (Cex * gap * (Astrip + cA * Real.sqrt Astrip) * (L1 * (1 + B))) ∧
    eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env2 Cex gap Acore Astrip Ma Me (S y) (K y))
        (ENNReal.ofReal pe) μ ≤
      ENNReal.ofReal ((Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 * gap *
          Real.sqrt (Acore + Astrip)) * ((Real.sqrt Ma * L1 + Real.sqrt Me * L0) * (1 + B))) := by
  have hp0 : 0 < pe := by linarith
  have h2p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * pe) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hone : AEStronglyMeasurable (fun _ : Y => (1 : ℝ)) μ := aestronglyMeasurable_const
  have hK1 : AEStronglyMeasurable (fun y => 1 + K y) μ := hone.add hK
  have hK1B : eLpNorm (fun y => 1 + K y) (ENNReal.ofReal (2 * pe)) μ ≤ ENNReal.ofReal (1 + B) := by
    refine (eLpNorm_add_le hone hK h2p).trans ?_
    have h1 : eLpNorm (fun _ : Y => (1 : ℝ)) (ENNReal.ofReal (2 * pe)) μ ≤ 1 := by
      rw [eLpNorm_const _ (by simpa using (by linarith : 0 < 2 * pe)) (IsProbabilityMeasure.ne_zero μ)]
      simp
    rw [ENNReal.ofReal_add zero_le_one hB, ENNReal.ofReal_one]
    exact add_le_add h1 hKB
  have hE1 : AEStronglyMeasurable (fun y => S y * Real.exp (Cex * S y)) μ :=
    hS.mul (Real.continuous_exp.comp_aestronglyMeasurable (hS.const_mul Cex))
  have hE15m : AEStronglyMeasurable (fun y => Real.exp (3 / 2 * Cex * S y)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable (hS.const_mul _)
  have hS15m : AEStronglyMeasurable (fun y => S y * Real.exp (3 / 2 * Cex * S y)) μ := hS.mul hE15m
  refine ⟨?_, ?_⟩
  · -- deletion envelope
    have hpt : ∀ᵐ y ∂μ, ‖aux_prop_conc_fine_fibre_es_env1 Cex gap Astrip cA (S y) (K y)‖ ≤
        ‖(Cex * gap * (Astrip + cA * Real.sqrt Astrip)) *
          ((S y * Real.exp (Cex * S y)) * (1 + K y))‖ := by
      filter_upwards [hK0] with y hy
      have hle := aux_prop_conc_fine_layer_env_env1_le Cex gap Astrip cA (S y) (K y) hCex hgap hAs hcA
        (hS0 y) hy
      have hn : 0 ≤ aux_prop_conc_fine_fibre_es_env1 Cex gap Astrip cA (S y) (K y) := by
        unfold aux_prop_conc_fine_fibre_es_env1
        have := hS0 y
        positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn,
        abs_of_nonneg (by have := hS0 y; positivity)]
      exact hle
    refine (eLpNorm_mono_ae hpt).trans ?_
    have hsm : (fun y => (Cex * gap * (Astrip + cA * Real.sqrt Astrip)) *
        ((S y * Real.exp (Cex * S y)) * (1 + K y))) =
        (Cex * gap * (Astrip + cA * Real.sqrt Astrip)) •
          (fun y => (S y * Real.exp (Cex * S y)) * (1 + K y)) := by
      funext y; simp [smul_eq_mul]
    rw [hsm, eLpNorm_const_smul]
    have hH := aux_lem_15_u_holder hE1 hK1 hp0
    calc ‖Cex * gap * (Astrip + cA * Real.sqrt Astrip)‖ₑ *
          eLpNorm (fun y => (S y * Real.exp (Cex * S y)) * (1 + K y)) (ENNReal.ofReal pe) μ
        ≤ ‖Cex * gap * (Astrip + cA * Real.sqrt Astrip)‖ₑ *
          (ENNReal.ofReal L1 * ENNReal.ofReal (1 + B)) := by
          gcongr
          exact hH.trans (mul_le_mul' hS1 hK1B)
      _ = _ := by
          rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul hL1,
            ← ENNReal.ofReal_mul (by positivity)]
  · -- Efron--Stein envelope
    set c₀ : ℝ := Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 * gap *
      Real.sqrt (Acore + Astrip) with hc₀
    have hc₀0 : 0 ≤ c₀ := by positivity
    have hpt : ∀ᵐ y ∂μ, ‖aux_prop_conc_fine_fibre_es_env2 Cex gap Acore Astrip Ma Me (S y) (K y)‖ ≤
        ‖c₀ * ((Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y)) +
          Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) * (1 + K y))‖ := by
      filter_upwards [hK0] with y hy
      have hle := aux_prop_conc_fine_layer_env_env2_le Cex gap Acore Astrip Ma Me (S y) (K y) hCex hgap
        hAc hAs hMa hMe (hS0 y) hy
      have hn : 0 ≤ aux_prop_conc_fine_fibre_es_env2 Cex gap Acore Astrip Ma Me (S y) (K y) := by
        unfold aux_prop_conc_fine_fibre_es_env2
        have := hS0 y
        positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn,
        abs_of_nonneg (by have := hS0 y; positivity)]
      exact hle
    refine (eLpNorm_mono_ae hpt).trans ?_
    have hsm : (fun y => c₀ * ((Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y)) +
          Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) * (1 + K y))) =
        c₀ • (fun y => (Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y)) +
          Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) * (1 + K y)) := by
      funext y; simp [smul_eq_mul]
    rw [hsm, eLpNorm_const_smul]
    have hX : AEStronglyMeasurable (fun y => Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y)) +
        Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) μ :=
      (hS15m.const_mul _).add (hE15m.const_mul _)
    have hXb : eLpNorm (fun y => Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y)) +
        Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) (ENNReal.ofReal (2 * pe)) μ ≤
        ENNReal.ofReal (Real.sqrt Ma * L1 + Real.sqrt Me * L0) := by
      refine (eLpNorm_add_le (hS15m.const_mul _) (hE15m.const_mul _) h2p).trans ?_
      have e1 : (fun y => Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y))) =
          (Real.sqrt Ma) • (fun y => S y * Real.exp (3 / 2 * Cex * S y)) := by
        funext y; simp [smul_eq_mul]
      have e2 : (fun y => Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) =
          (Real.sqrt Me) • (fun y => Real.exp (3 / 2 * Cex * S y)) := by
        funext y; simp [smul_eq_mul]
      rw [e1, e2, eLpNorm_const_smul, eLpNorm_const_smul,
        Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
      calc ENNReal.ofReal (Real.sqrt Ma) *
            eLpNorm (fun y => S y * Real.exp (3 / 2 * Cex * S y)) (ENNReal.ofReal (2 * pe)) μ +
          ENNReal.ofReal (Real.sqrt Me) *
            eLpNorm (fun y => Real.exp (3 / 2 * Cex * S y)) (ENNReal.ofReal (2 * pe)) μ
          ≤ ENNReal.ofReal (Real.sqrt Ma) * ENNReal.ofReal L1 +
            ENNReal.ofReal (Real.sqrt Me) * ENNReal.ofReal L0 := by gcongr
        _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hH := aux_lem_15_u_holder hX hK1 hp0
    calc ‖c₀‖ₑ * eLpNorm (fun y => (Real.sqrt Ma * (S y * Real.exp (3 / 2 * Cex * S y)) +
            Real.sqrt Me * Real.exp (3 / 2 * Cex * S y)) * (1 + K y)) (ENNReal.ofReal pe) μ
        ≤ ‖c₀‖ₑ * (ENNReal.ofReal (Real.sqrt Ma * L1 + Real.sqrt Me * L0) *
          ENNReal.ofReal (1 + B)) := by
          gcongr
          exact hH.trans (mul_le_mul' hXb hK1B)
      _ = _ := by
          rw [Real.enorm_eq_ofReal hc₀0, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hc₀0]

/-- The crude envelope of two independent layer samples: `CL gap (a + c) e^{CL (a + c)}` is at most
`2 CL gap ‖S e^{CL S}‖_{2p} ‖e^{CL S}‖_{2p}` in `L^p(ν ⊗ ν)`. -/
theorem aux_prop_conc_fine_layer_env_crude_norm {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (S : X → ℝ) (hS : Measurable S) (CL gap pe L1 L0 : ℝ)
    (hCL : 0 ≤ CL) (hgap : 0 ≤ gap) (hpe : 1 ≤ pe) (hL1 : 0 ≤ L1) (hL0 : 0 ≤ L0)
    (h1 : eLpNorm (fun x => S x * Real.exp (CL * S x)) (ENNReal.ofReal (2 * pe)) ν ≤ ENNReal.ofReal L1)
    (h0 : eLpNorm (fun x => Real.exp (CL * S x)) (ENNReal.ofReal (2 * pe)) ν ≤ ENNReal.ofReal L0) :
    eLpNorm (fun q : X × X => (CL * (S q.2 + S q.1) * Real.exp (CL * (S q.2 + S q.1))) * gap)
        (ENNReal.ofReal pe) (ν.prod ν) ≤
      ENNReal.ofReal (2 * (CL * gap) * (L1 * L0)) := by
  have hp0 : 0 < pe := by linarith
  have h2p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * pe) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hE : Measurable (fun x => Real.exp (CL * S x)) := Real.measurable_exp.comp (hS.const_mul CL)
  have hSE : Measurable (fun x => S x * Real.exp (CL * S x)) := hS.mul hE
  have hfst : MeasurePreserving (Prod.fst : X × X → X) (ν.prod ν) ν := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : X × X → X) (ν.prod ν) ν := measurePreserving_snd
  set F1 : X × X → ℝ := fun q => (S q.2 * Real.exp (CL * S q.2)) * Real.exp (CL * S q.1) with hF1
  set F2 : X × X → ℝ := fun q => (S q.1 * Real.exp (CL * S q.1)) * Real.exp (CL * S q.2) with hF2
  have hF1m : Measurable F1 := (hSE.comp measurable_snd).mul (hE.comp measurable_fst)
  have hF2m : Measurable F2 := (hSE.comp measurable_fst).mul (hE.comp measurable_snd)
  have hid : (fun q : X × X => (CL * (S q.2 + S q.1) * Real.exp (CL * (S q.2 + S q.1))) * gap) =
      (CL * gap) • (fun q => F1 q + F2 q) := by
    funext q
    simp only [hF1, hF2, Pi.smul_apply, smul_eq_mul]
    rw [mul_add, Real.exp_add]
    ring
  rw [hid, eLpNorm_const_smul]
  have hb1 : eLpNorm F1 (ENNReal.ofReal pe) (ν.prod ν) ≤ ENNReal.ofReal L1 * ENNReal.ofReal L0 := by
    have hH := aux_lem_15_u_holder (μ := ν.prod ν) (hSE.comp measurable_snd).aestronglyMeasurable
      (hE.comp measurable_fst).aestronglyMeasurable hp0
    have e1 : eLpNorm (fun q : X × X => S q.2 * Real.exp (CL * S q.2)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) =
        eLpNorm (fun x => S x * Real.exp (CL * S x)) (ENNReal.ofReal (2 * pe)) ν :=
      eLpNorm_comp_measurePreserving (g := fun x => S x * Real.exp (CL * S x)) hSE.aestronglyMeasurable hsnd
    have e2 : eLpNorm (fun q : X × X => Real.exp (CL * S q.1)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) =
        eLpNorm (fun x => Real.exp (CL * S x)) (ENNReal.ofReal (2 * pe)) ν :=
      eLpNorm_comp_measurePreserving (g := fun x => Real.exp (CL * S x)) hE.aestronglyMeasurable hfst
    refine hH.trans ?_
    show eLpNorm (fun q : X × X => S q.2 * Real.exp (CL * S q.2)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) *
      eLpNorm (fun q : X × X => Real.exp (CL * S q.1)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) ≤ _
    rw [e1, e2]
    exact mul_le_mul' h1 h0
  have hb2 : eLpNorm F2 (ENNReal.ofReal pe) (ν.prod ν) ≤ ENNReal.ofReal L1 * ENNReal.ofReal L0 := by
    have hH := aux_lem_15_u_holder (μ := ν.prod ν) (hSE.comp measurable_fst).aestronglyMeasurable
      (hE.comp measurable_snd).aestronglyMeasurable hp0
    have e1 : eLpNorm (fun q : X × X => S q.1 * Real.exp (CL * S q.1)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) =
        eLpNorm (fun x => S x * Real.exp (CL * S x)) (ENNReal.ofReal (2 * pe)) ν :=
      eLpNorm_comp_measurePreserving (g := fun x => S x * Real.exp (CL * S x)) hSE.aestronglyMeasurable hfst
    have e2 : eLpNorm (fun q : X × X => Real.exp (CL * S q.2)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) =
        eLpNorm (fun x => Real.exp (CL * S x)) (ENNReal.ofReal (2 * pe)) ν :=
      eLpNorm_comp_measurePreserving (g := fun x => Real.exp (CL * S x)) hE.aestronglyMeasurable hsnd
    refine hH.trans ?_
    show eLpNorm (fun q : X × X => S q.1 * Real.exp (CL * S q.1)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) *
      eLpNorm (fun q : X × X => Real.exp (CL * S q.2)) (ENNReal.ofReal (2 * pe)) (ν.prod ν) ≤ _
    rw [e1, e2]
    exact mul_le_mul' h1 h0
  calc ‖CL * gap‖ₑ * eLpNorm (fun q => F1 q + F2 q) (ENNReal.ofReal pe) (ν.prod ν)
      ≤ ‖CL * gap‖ₑ * (eLpNorm F1 (ENNReal.ofReal pe) (ν.prod ν) +
          eLpNorm F2 (ENNReal.ofReal pe) (ν.prod ν)) := by
        gcongr
        exact eLpNorm_add_le hF1m.aestronglyMeasurable hF2m.aestronglyMeasurable
          (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hpe)
    _ ≤ ‖CL * gap‖ₑ * (ENNReal.ofReal L1 * ENNReal.ofReal L0 + ENNReal.ofReal L1 * ENNReal.ofReal L0) := by
        gcongr
    _ = ENNReal.ofReal (2 * (CL * gap) * (L1 * L0)) := by
        rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul hL1,
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end
end Paper
