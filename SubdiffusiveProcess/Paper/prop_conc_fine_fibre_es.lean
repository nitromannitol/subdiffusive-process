module

public import SubdiffusiveProcess.Paper.prop_conc_fine_fibre_det
public import SubdiffusiveProcess.Paper.prop_conc_fine_es_layer
public import SubdiffusiveProcess.Lane3.Elementary
public import SubdiffusiveProcess.Lane3.Interfaces

@[expose] public section

/-! The `L^p` resampling estimate along one fibre of the fine-layer step: for a fixed pair `X` and reference
`x0`, the difference `f(y) - f(y')` of the relative response of two independent layer samples is split into
the deletion errors and the fluctuations of the pieces response (the four-term identity), the latter
bounded by the Efron--Stein inequality for the pieces with the retained endpoint gap `M - m` in every
term. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

section numerics

theorem aux_prop_conc_fine_fibre_es_mass_square_sum {n : ℕ} (gap mx Cnu Czeta : ℝ) (hgap : 0 ≤ gap)
    (nu zeta : Fin n → ℝ) (hnu : ∀ i, 0 ≤ nu i) (hzeta : ∀ i, 0 ≤ zeta i)
    (hmax : ∀ i, nu i ≤ mx) (hnu_total : ∑ i, nu i ≤ Cnu)
    (hzeta_total : ∑ i, zeta i ≤ Czeta * gap ^ 2) (hmx : 0 ≤ mx) :
    ∑ i, (gap * nu i + Real.sqrt (nu i * zeta i)) ^ 2 ≤ 2 * gap ^ 2 * mx * (Cnu + Czeta) := by
  refine (Lane3.efron_stein_square_sum_le gap mx hgap nu zeta hnu hzeta hmax).trans ?_
  calc 2 * gap ^ 2 * mx * (∑ i, nu i) + 2 * mx * (∑ i, zeta i) ≤
        2 * gap ^ 2 * mx * Cnu + 2 * mx * (Czeta * gap ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hnu_total (by positivity))
        (mul_le_mul_of_nonneg_left hzeta_total (by positivity))
    _ = 2 * gap ^ 2 * mx * (Cnu + Czeta) := by ring

/-- The square root of the total variance proxy keeps one full gap factor. -/
theorem aux_prop_conc_fine_fibre_es_sqrt_var {n : ℕ} (gap mx Cnu Czeta H : ℝ) (hgap : 0 ≤ gap)
    (hmx : 0 ≤ mx) (hCnu : 0 ≤ Cnu) (hCzeta : 0 ≤ Czeta) (hH : 0 ≤ H)
    (nu zeta variance : Fin n → ℝ) (hnu : ∀ i, 0 ≤ nu i) (hzeta : ∀ i, 0 ≤ zeta i)
    (hmax : ∀ i, nu i ≤ mx) (hnu_total : ∑ i, nu i ≤ Cnu)
    (hzeta_total : ∑ i, zeta i ≤ Czeta * gap ^ 2)
    (hvariance : ∀ i, variance i ≤ H ^ 2 * (gap * nu i + Real.sqrt (nu i * zeta i)) ^ 2) :
    Real.sqrt (∑ i, variance i) ≤ (Real.sqrt (2 * (Cnu + Czeta)) * gap) * (H * Real.sqrt mx) := by
  have h1 : ∑ i, variance i ≤ H ^ 2 * (2 * gap ^ 2 * mx * (Cnu + Czeta)) :=
    calc ∑ i, variance i ≤ ∑ i, H ^ 2 * (gap * nu i + Real.sqrt (nu i * zeta i)) ^ 2 :=
          Finset.sum_le_sum fun i _ => hvariance i
      _ = H ^ 2 * ∑ i, (gap * nu i + Real.sqrt (nu i * zeta i)) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ H ^ 2 * (2 * gap ^ 2 * mx * (Cnu + Czeta)) :=
          mul_le_mul_of_nonneg_left (aux_prop_conc_fine_fibre_es_mass_square_sum gap mx Cnu Czeta hgap
            nu zeta hnu hzeta hmax hnu_total hzeta_total hmx) (sq_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  refine h1.trans_eq ?_
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hmx]
  ring

/-- The conditional variance of one piece: the squared increment is bounded by the layer-norm envelope of
the resampled sample, whose second moments are `Ma`, `Me`. -/
theorem aux_prop_conc_fine_fibre_es_var_int {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (S : X → ℝ) (a Cex Ma Me D : ℝ) (hMa0 : 0 ≤ Ma)
    (hMe0 : 0 ≤ Me)
    (hIa : Integrable (fun y => Real.exp (2 * Cex * S y)) μ)
    (hIe : Integrable (fun y => S y ^ 2 * Real.exp (2 * Cex * S y)) μ)
    (hMa : ∫ y, Real.exp (2 * Cex * S y) ∂μ ≤ Ma)
    (hMe : ∫ y, S y ^ 2 * Real.exp (2 * Cex * S y) ∂μ ≤ Me)
    (V : X → ℝ) (hV0 : ∀ y, 0 ≤ V y)
    (hV : ∀ y, V y ≤ (Cex * (a + S y) * Real.exp (Cex * (a + S y))) ^ 2 * D ^ 2) :
    ∫ y, V y ∂μ ≤ (Cex * Real.exp (Cex * a) * Real.sqrt (2 * (a ^ 2 * Ma + Me))) ^ 2 * D ^ 2 := by
  set c : ℝ := 2 * Cex ^ 2 * Real.exp (2 * Cex * a) * D ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set g : X → ℝ := fun y => c * (a ^ 2 * Real.exp (2 * Cex * S y) + S y ^ 2 * Real.exp (2 * Cex * S y))
    with hg
  have hgi : Integrable g μ := ((hIa.const_mul (a ^ 2)).add hIe).const_mul c
  have hVg : ∀ y, V y ≤ g y := by
    intro y
    refine (hV y).trans ?_
    have h1 : (Cex * (a + S y) * Real.exp (Cex * (a + S y))) ^ 2 =
        Cex ^ 2 * (a + S y) ^ 2 * (Real.exp (2 * Cex * a) * Real.exp (2 * Cex * S y)) := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      push_cast; ring
    have h2 : (a + S y) ^ 2 ≤ 2 * (a ^ 2 + S y ^ 2) := by nlinarith [sq_nonneg (a - S y)]
    have h3 : 0 ≤ Cex ^ 2 * (Real.exp (2 * Cex * a) * Real.exp (2 * Cex * S y)) * D ^ 2 := by positivity
    calc (Cex * (a + S y) * Real.exp (Cex * (a + S y))) ^ 2 * D ^ 2
        = (a + S y) ^ 2 * (Cex ^ 2 * (Real.exp (2 * Cex * a) * Real.exp (2 * Cex * S y)) * D ^ 2) := by
          rw [h1]; ring
      _ ≤ (2 * (a ^ 2 + S y ^ 2)) * (Cex ^ 2 * (Real.exp (2 * Cex * a) * Real.exp (2 * Cex * S y)) * D ^ 2) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = g y := by simp only [hg, hc]; ring
  have h4 : ∫ y, V y ∂μ ≤ ∫ y, g y ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hV0) hgi (Filter.Eventually.of_forall hVg)
  refine h4.trans ?_
  have h5 : ∫ y, g y ∂μ = c * (a ^ 2 * ∫ y, Real.exp (2 * Cex * S y) ∂μ +
      ∫ y, S y ^ 2 * Real.exp (2 * Cex * S y) ∂μ) := by
    simp only [hg]
    rw [integral_const_mul, integral_add (hIa.const_mul (a ^ 2)) hIe, integral_const_mul]
  rw [h5]
  have h6 : (Cex * Real.exp (Cex * a) * Real.sqrt (2 * (a ^ 2 * Ma + Me))) ^ 2 * D ^ 2 =
      c * (a ^ 2 * Ma + Me) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    simp only [hc]
    push_cast
    ring_nf
  rw [h6]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a]) hc0

/-- The four-term identity on the product of two independent copies. -/
theorem aux_prop_conc_fine_fibre_es_fourterm {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f Ψ' : X → ℝ) (Ebar : ℝ) (hf : Measurable f) (hΨ : Measurable Ψ')
    (pe : ℝ) (hpe : 1 ≤ pe) :
    eLpNorm (fun yy : X × X => f yy.1 - f yy.2) (ENNReal.ofReal pe) (μ.prod μ) ≤
      2 * eLpNorm (fun y => f y - Ψ' y) (ENNReal.ofReal pe) μ +
        2 * eLpNorm (fun y => Ψ' y - Ebar) (ENNReal.ofReal pe) μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pe := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hpe
  set F1 : X → ℝ := fun y => f y - Ψ' y with hF1
  set F2 : X → ℝ := fun y => Ψ' y - Ebar with hF2
  have hF1m : Measurable F1 := hf.sub hΨ
  have hF2m : Measurable F2 := hΨ.sub measurable_const
  have hae : (fun yy : X × X => f yy.1 - f yy.2) =
      fun yy => ((F1 ∘ Prod.fst) yy + (F2 ∘ Prod.fst) yy) - ((F2 ∘ Prod.snd) yy + (F1 ∘ Prod.snd) yy) := by
    funext yy
    simp only [Function.comp_apply, hF1, hF2]
    ring
  rw [hae]
  have hfst : MeasurePreserving (Prod.fst : X × X → X) (μ.prod μ) μ := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : X × X → X) (μ.prod μ) μ := measurePreserving_snd
  have hA : AEStronglyMeasurable (fun yy : X × X => (F1 ∘ Prod.fst) yy + (F2 ∘ Prod.fst) yy) (μ.prod μ) :=
    ((hF1m.comp measurable_fst).add (hF2m.comp measurable_fst)).aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun yy : X × X => (F2 ∘ Prod.snd) yy + (F1 ∘ Prod.snd) yy) (μ.prod μ) :=
    ((hF2m.comp measurable_snd).add (hF1m.comp measurable_snd)).aestronglyMeasurable
  have e1 : eLpNorm (F1 ∘ Prod.fst) (ENNReal.ofReal pe) (μ.prod μ) = eLpNorm F1 (ENNReal.ofReal pe) μ :=
    eLpNorm_comp_measurePreserving hF1m.aestronglyMeasurable hfst
  have e2 : eLpNorm (F2 ∘ Prod.fst) (ENNReal.ofReal pe) (μ.prod μ) = eLpNorm F2 (ENNReal.ofReal pe) μ :=
    eLpNorm_comp_measurePreserving hF2m.aestronglyMeasurable hfst
  have e3 : eLpNorm (F2 ∘ Prod.snd) (ENNReal.ofReal pe) (μ.prod μ) = eLpNorm F2 (ENNReal.ofReal pe) μ :=
    eLpNorm_comp_measurePreserving hF2m.aestronglyMeasurable hsnd
  have e4 : eLpNorm (F1 ∘ Prod.snd) (ENNReal.ofReal pe) (μ.prod μ) = eLpNorm F1 (ENNReal.ofReal pe) μ :=
    eLpNorm_comp_measurePreserving hF1m.aestronglyMeasurable hsnd
  calc eLpNorm (fun yy : X × X => ((F1 ∘ Prod.fst) yy + (F2 ∘ Prod.fst) yy) -
          ((F2 ∘ Prod.snd) yy + (F1 ∘ Prod.snd) yy)) (ENNReal.ofReal pe) (μ.prod μ)
      ≤ eLpNorm (fun yy : X × X => (F1 ∘ Prod.fst) yy + (F2 ∘ Prod.fst) yy) (ENNReal.ofReal pe) (μ.prod μ) +
        eLpNorm (fun yy : X × X => (F2 ∘ Prod.snd) yy + (F1 ∘ Prod.snd) yy) (ENNReal.ofReal pe) (μ.prod μ) :=
        eLpNorm_sub_le hp1
    _ ≤ (eLpNorm (F1 ∘ Prod.fst) (ENNReal.ofReal pe) (μ.prod μ) +
          eLpNorm (F2 ∘ Prod.fst) (ENNReal.ofReal pe) (μ.prod μ)) +
        (eLpNorm (F2 ∘ Prod.snd) (ENNReal.ofReal pe) (μ.prod μ) +
          eLpNorm (F1 ∘ Prod.snd) (ENNReal.ofReal pe) (μ.prod μ)) := by
        gcongr
        · exact eLpNorm_add_le hp1
        · exact eLpNorm_add_le hp1
    _ = 2 * eLpNorm F1 (ENNReal.ofReal pe) μ + 2 * eLpNorm F2 (ENNReal.ofReal pe) μ := by
        rw [e1, e2, e3, e4]; ring

end numerics

section main
variable {d : ℕ}

/-- Envelope of the deletion error of one layer sample. -/
def aux_prop_conc_fine_fibre_es_env1 (Cex gap Astrip cA s K : ℝ) : ℝ :=
  Cex * s * Real.exp (Cex * s) * gap * (K * Astrip + cA * Real.sqrt K * Real.sqrt Astrip)

/-- Envelope of the Efron--Stein fluctuation of the pieces response of one layer sample. -/
def aux_prop_conc_fine_fibre_es_env2 (Cex gap Acore Astrip Ma Me s K : ℝ) : ℝ :=
  Real.sqrt (2 * (Cex + Cex)) * gap *
    (Cex * Real.exp (Cex * s) * Real.sqrt (2 * (s ^ 2 * Ma + Me)) *
      Real.sqrt (Cex * Real.exp (Cex * s) * ((Acore + Astrip) * K)))

/-- **The `L^p` estimate along a fibre.**  For a pair `X`, a reference `x0`, and a layer law `μ` whose grid pieces
are independent, if `f` is the relative response `θ_X(y - x0)` of the layer samples `y` (a.e.) and the masked
pairs of `X` have the growth constant `Kfun y`, then `‖f(y) - f(y')‖_{L^p(μ⊗μ)} ≤ 2‖env₁‖ + 2 C_p ‖env₂‖` with
envelopes depending on `y` only through the layer norm `S y` and the growth constant `Kfun y`. -/
theorem prop_conc_fine_fibre_es (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ Cex : ℝ, 0 < Cex ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (x0 : C(SpatialCoordinates d, ℝ)) (ell w : ℝ) {n : ℕ} (idx : Fin n → (Fin d → ℤ)),
        aux_prop_conc_fine_grid_Grid z r hr ell w idx →
      ∀ (t Astrip Acore : ℝ), 0 ≤ Astrip → 0 ≤ Acore →
        aux_prop_conc_fine_geometry_CellBound z r hr t ell w Astrip Acore →
      ∀ (μ : Measure C(SpatialCoordinates d, ℝ)) [IsProbabilityMeasure μ],
        μ.map (aux_prop_conc_fine_fibre_det_T ell w idx) =
          Measure.pi (fun k => μ.map (fun y => aux_lem_15_u_localize 0 ell w (idx k) y)) →
      ∀ (f : C(SpatialCoordinates d, ℝ) → ℝ), Measurable f →
        (∀ᵐ y ∂μ, f y = aux_prop_conc_pair_data_theta X c p (fun x => y x - x0 x)) →
      ∀ (Kfun : C(SpatialCoordinates d, ℝ) → ℝ), (∀ᵐ y ∂μ, 0 ≤ Kfun y) →
        (∀ᵐ y ∂μ, ∀ (hw : Measurable (aux_prop_conc_fine_fibre_det_wY z r hr x0 y)) (Kw : ℝ)
          (hKw : ∀ x, |aux_prop_conc_fine_fibre_det_wY z r hr x0 y x| ≤ Kw),
          aux_prop_conc_pair_data_growth
            (aux_prop_conc_pair_mask_pair X (aux_prop_conc_fine_fibre_det_wY z r hr x0 y) hw Kw hKw)
            (aux_prop_conc_pair_data_slopes d) t (Kfun y)) →
      ∀ (pe Cp : ℝ), 2 ≤ pe →
        aux_lem_15_u_ESProp (fun k => μ.map (fun y => aux_lem_15_u_localize 0 ell w (idx k) y)) pe Cp →
      ∀ (Ma Me : ℝ), 0 ≤ Ma → 0 ≤ Me →
        Integrable (fun y => Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S z r y)) μ →
        Integrable (fun y => aux_prop_conc_fine_fibre_det_S z r y ^ 2 *
          Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S z r y)) μ →
        (∫ y, Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S z r y) ∂μ ≤ Ma) →
        (∫ y, aux_prop_conc_fine_fibre_det_S z r y ^ 2 *
          Real.exp (2 * Cex * aux_prop_conc_fine_fibre_det_S z r y) ∂μ ≤ Me) →
        eLpNorm (fun yy : C(SpatialCoordinates d, ℝ) × C(SpatialCoordinates d, ℝ) => f yy.1 - f yy.2)
            (ENNReal.ofReal pe) (μ.prod μ) ≤
          2 * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env1 Cex (M - m) Astrip
              (Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
                ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)))
              (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y)) (ENNReal.ofReal pe) μ +
          2 * ENNReal.ofReal Cp * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env2 Cex (M - m) Acore
              Astrip Ma Me (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y)) (ENNReal.ofReal pe) μ := by
  obtain ⟨Cex, hCex, hdet⟩ := prop_conc_fine_fibre_det C0 hC0 d
  obtain ⟨CB, hCB, hpsi⟩ := prop_conc_fine_psi C0 hC0 d
  refine ⟨Cex, hCex, ?_⟩
  intro _ _ Q z r hr m M X c hc p hp x0 ell w n idx hg t Astrip Acore hAs hAc hcb μ _ hπ f hf hfX
    Kfun hK0 hgrowth pe Cp hpe hES Ma Me hMa0 hMe0 hIa hIe hMa hMe
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  set Ψ := aux_prop_conc_fine_psi_Psi X c p x0 ell w idx with hΨdef
  obtain ⟨hΨc, hΨb⟩ := hpsi X c hc p hp x0 ell w idx hg
  have hΨm : Measurable Ψ := hΨc.measurable
  set T := aux_prop_conc_fine_fibre_det_T ell w idx with hTdef
  have hTm : Measurable T :=
    measurable_pi_lambda fun k => (aux_lem_15_u_localize_continuous 0 ell w (idx k)).measurable
  set muk : Fin n → Measure C(SpatialCoordinates d, ℝ) :=
    fun k => μ.map (fun y => aux_lem_15_u_localize 0 ell w (idx k) y) with hmuk
  haveI hprobk : ∀ k, IsProbabilityMeasure (muk k) := fun k => by
    dsimp only [muk]
    infer_instance
  have hmem : MemLp Ψ (ENNReal.ofReal pe) (Measure.pi muk) :=
    MemLp.of_bound hΨm.aestronglyMeasurable (CB * (M - m))
      (Filter.Eventually.of_forall fun T => by
        rw [Real.norm_eq_abs]; exact hΨb T)
  have hes := prop_conc_fine_es_layer μ muk T hTm hπ Ψ hΨm pe Cp hES hmem
  set Ebar : ℝ := ∫ v, Ψ v ∂(Measure.pi muk) with hEbar
  have hΨT : Measurable (fun y => Ψ (T y)) := hΨm.comp hTm
  have hfour := aux_prop_conc_fine_fibre_es_fourterm μ f (fun y => Ψ (T y)) Ebar hf hΨT pe (by linarith)
  refine hfour.trans ?_
  have hcA : 0 ≤ Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
      ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) := Real.sqrt_nonneg _
  have hpen : ENNReal.ofReal pe ≠ 0 := by
    have : 0 < pe := by linarith
    simpa using this
  -- the good set
  have hgood : ∀ᵐ y ∂μ, 0 ≤ Kfun y ∧ f y = aux_prop_conc_pair_data_theta X c p (fun x => y x - x0 x) ∧
      (∀ (hw : Measurable (aux_prop_conc_fine_fibre_det_wY z r hr x0 y)) (Kw : ℝ)
          (hKw : ∀ x, |aux_prop_conc_fine_fibre_det_wY z r hr x0 y x| ≤ Kw),
          aux_prop_conc_pair_data_growth
            (aux_prop_conc_pair_mask_pair X (aux_prop_conc_fine_fibre_det_wY z r hr x0 y) hw Kw hKw)
            (aux_prop_conc_pair_data_slopes d) t (Kfun y)) := by
    filter_upwards [hK0, hfX, hgrowth] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hvarbound : ∀ᵐ y ∂μ, Real.sqrt (∑ i : Fin n, ∫ z', (Ψ (T y) - Ψ (Function.update (T y) i z')) ^ 2 ∂(muk i)) ≤
      aux_prop_conc_fine_fibre_es_env2 Cex (M - m) Acore Astrip Ma Me
        (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y) := by
    filter_upwards [hgood] with y ⟨hK, hfy, hgr⟩
    obtain ⟨-, nu, zeta, mx, hmx0, hnu0, hze0, hnumx, hsnu, hsze, hmxle, hvary⟩ :=
      hdet X c hc p hp x0 ell w idx hg t Astrip Acore hAs hAc hcb y (Kfun y) hK hgr
    set Sy : ℝ := aux_prop_conc_fine_fibre_det_S z r y with hSy
    have hSy0 : 0 ≤ Sy := aux_prop_conc_fine_fibre_det_S_nonneg z r y
    set H : ℝ := Cex * Real.exp (Cex * Sy) * Real.sqrt (2 * (Sy ^ 2 * Ma + Me)) with hH
    have hH0 : 0 ≤ H := by positivity
    have hvi : ∀ i, ∫ z', (Ψ (T y) - Ψ (Function.update (T y) i z')) ^ 2 ∂(muk i) ≤
        H ^ 2 * ((M - m) * nu i + Real.sqrt (nu i * zeta i)) ^ 2 := by
      intro i
      have hmapint : ∫ z', (Ψ (T y) - Ψ (Function.update (T y) i z')) ^ 2 ∂(muk i) =
          ∫ y', (Ψ (T y) - Ψ (Function.update (T y) i (T y' i))) ^ 2 ∂μ := by
        simp only [hmuk]
        refine integral_map (aux_lem_15_u_localize_continuous 0 ell w (idx i)).measurable.aemeasurable ?_
        exact (((hΨm.comp (measurable_update (T y) : Measurable (Function.update (T y) i))).const_sub (Ψ (T y))).pow_const 2).aestronglyMeasurable
      rw [hmapint]
      refine aux_prop_conc_fine_fibre_es_var_int μ (fun y' => aux_prop_conc_fine_fibre_det_S z r y') Sy Cex Ma Me
        ((M - m) * nu i + Real.sqrt (nu i * zeta i)) hMa0 hMe0 hIa hIe hMa hMe _ (fun _ => sq_nonneg _) ?_
      intro y'
      have h1 := hvary y' i
      have h2 : (Ψ (T y) - Ψ (Function.update (T y) i (T y' i))) ^ 2 =
          |Ψ (Function.update (T y) i (T y' i)) - Ψ (T y)| ^ 2 := by
        rw [sq_abs, ← neg_sub, neg_sq]
      rw [h2, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hsq := aux_prop_conc_fine_fibre_es_sqrt_var (M - m) mx Cex Cex H hgap hmx0 hCex.le hCex.le hH0 nu zeta
      (fun i => ∫ z', (Ψ (T y) - Ψ (Function.update (T y) i z')) ^ 2 ∂(muk i)) hnu0 hze0 hnumx hsnu hsze hvi
    refine hsq.trans ?_
    unfold aux_prop_conc_fine_fibre_es_env2
    have hsqrt : Real.sqrt mx ≤ Real.sqrt (Cex * Real.exp (Cex * Sy) * ((Acore + Astrip) * Kfun y)) :=
      Real.sqrt_le_sqrt hmxle
    have hfac : 0 ≤ Real.sqrt (2 * (Cex + Cex)) * (M - m) := by positivity
    calc (Real.sqrt (2 * (Cex + Cex)) * (M - m)) * (H * Real.sqrt mx) ≤
        (Real.sqrt (2 * (Cex + Cex)) * (M - m)) *
          (H * Real.sqrt (Cex * Real.exp (Cex * Sy) * ((Acore + Astrip) * Kfun y))) := by
          gcongr
      _ = _ := by simp only [hH]
  have hA : eLpNorm (fun y => f y - Ψ (T y)) (ENNReal.ofReal pe) μ ≤
      eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env1 Cex (M - m) Astrip
        (Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
          ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)))
        (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y)) (ENNReal.ofReal pe) μ := by
    refine eLpNorm_mono_ae (hf.sub hΨT).aestronglyMeasurable ?_
    filter_upwards [hgood] with y ⟨hK, hfy, hgr⟩
    obtain ⟨h1, -⟩ := hdet X c hc p hp x0 ell w idx hg t Astrip Acore hAs hAc hcb y (Kfun y) hK hgr
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hnn : 0 ≤ aux_prop_conc_fine_fibre_es_env1 Cex (M - m) Astrip
        (Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
          ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)))
        (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y) := by
      unfold aux_prop_conc_fine_fibre_es_env1
      have := aux_prop_conc_fine_fibre_det_S_nonneg z r y
      positivity
    rw [abs_of_nonneg hnn]
    show |f y - Ψ (T y)| ≤ _
    rw [hfy]
    exact h1
  have hVin (i : Fin n) : Measurable (fun q : (Fin n → C(SpatialCoordinates d, ℝ)) × C(SpatialCoordinates d, ℝ) =>
      (Ψ q.1 - Ψ (Function.update q.1 i q.2)) ^ 2) := by
    have h1 : Measurable (fun q : (Fin n → C(SpatialCoordinates d, ℝ)) × C(SpatialCoordinates d, ℝ) => Ψ q.1) := hΨm.comp measurable_fst
    have h2 : Measurable (fun q : (Fin n → C(SpatialCoordinates d, ℝ)) × C(SpatialCoordinates d, ℝ) => Ψ (Function.update q.1 i q.2)) := hΨm.comp (measurable_update'.comp (measurable_fst.prodMk measurable_snd))
    exact (h1.sub h2).pow_const 2
  have hVm : Measurable (fun v : Fin n → C(SpatialCoordinates d, ℝ) =>
      Real.sqrt (∑ i : Fin n, ∫ z', (Ψ v - Ψ (Function.update v i z')) ^ 2 ∂(muk i))) := by
    refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
    exact ((hVin i).stronglyMeasurable.integral_prod_right' (ν := muk i)).measurable
  have hVT : AEStronglyMeasurable (fun y => Real.sqrt (∑ i : Fin n, ∫ z',
      (Ψ (T y) - Ψ (Function.update (T y) i z')) ^ 2 ∂(muk i))) μ :=
    (hVm.comp hTm).aestronglyMeasurable
  have hB : 2 * eLpNorm (fun y => Ψ (T y) - Ebar) (ENNReal.ofReal pe) μ ≤
      2 * ENNReal.ofReal Cp * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env2 Cex (M - m) Acore
        Astrip Ma Me (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y)) (ENNReal.ofReal pe) μ := by
    calc 2 * eLpNorm (fun y => Ψ (T y) - Ebar) (ENNReal.ofReal pe) μ ≤
        2 * (ENNReal.ofReal Cp * eLpNorm (fun y => Real.sqrt (∑ i : Fin n, ∫ z', (Ψ (T y) -
          Ψ (Function.update (T y) i z')) ^ 2 ∂(muk i))) (ENNReal.ofReal pe) μ) := by
          gcongr
      _ ≤ 2 * (ENNReal.ofReal Cp * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env2 Cex (M - m) Acore
            Astrip Ma Me (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y)) (ENNReal.ofReal pe) μ) := by
          gcongr
          refine eLpNorm_mono_ae hVT ?_
          filter_upwards [hvarbound] with y hy
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact hy.trans (le_abs_self _)
      _ = 2 * ENNReal.ofReal Cp * eLpNorm (fun y => aux_prop_conc_fine_fibre_es_env2 Cex (M - m) Acore
            Astrip Ma Me (aux_prop_conc_fine_fibre_det_S z r y) (Kfun y)) (ENNReal.ofReal pe) μ := by
          ring
  exact add_le_add (by gcongr) hB

end main

end
end Paper
