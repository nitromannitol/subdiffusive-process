import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeanOneFubini
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerSigma
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The exchange -/

section Swap

variable (M : GMCModel d) (S : Finset ℕ)
variable {G : PotentialSample d → ℝ} {φ : Vec d → ℝ} {U : Set (Vec d)}

/-- The weighted layer product is integrable on a bounded set. -/
theorem integrableOn_layerCoefficient_mul (omega : PotentialSample d)
    (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (hφint : IntegrableOn φ U volume) :
    IntegrableOn (fun x => layerCoefficient M S omega x * φ x) U volume := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous_of_isBounded
    (continuous_layerCoefficient M S omega) hUb
  refine hφint.bdd_mul (c := C)
    (continuous_layerCoefficient M S omega).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  exact hC x hx

/-- The sample weight times a layer product is integrable at each point. -/
theorem integrable_mul_layerCoefficient_apply (hG : Measurable G)
    (hG0 : ∀ omega, 0 ≤ G omega) (hG1 : ∀ omega, G omega ≤ 1) (x : Vec d) :
    Integrable (fun omega => G omega * layerCoefficient M S omega x) M.P.toMeasure := by
  have hbase : Integrable (fun omega => layerCoefficient M S omega x) M.P.toMeasure :=
    integrable_of_integral_eq_one (integral_layerCoefficient_apply M S x)
  refine hbase.mono'
    ((hG.mul (measurable_layerCoefficient_apply M S x)).aestronglyMeasurable) ?_
  filter_upwards with omega
  have hpos : 0 < layerCoefficient M S omega x := layerCoefficient_pos M S omega x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG0 omega) hpos.le)]
  nlinarith [hG1 omega, hG0 omega, hpos.le]

theorem integral_mul_layerCoefficient_apply_le_one (hG : Measurable G)
    (hG0 : ∀ omega, 0 ≤ G omega) (hG1 : ∀ omega, G omega ≤ 1) (x : Vec d) :
    ∫ omega, G omega * layerCoefficient M S omega x ∂M.P.toMeasure ≤ 1 := by
  have hbase : Integrable (fun omega => layerCoefficient M S omega x) M.P.toMeasure :=
    integrable_of_integral_eq_one (integral_layerCoefficient_apply M S x)
  have hmono := integral_mono
    (integrable_mul_layerCoefficient_apply M S hG hG0 hG1 x) hbase
    (fun omega => by
      have hpos : 0 < layerCoefficient M S omega x := layerCoefficient_pos M S omega x
      nlinarith [hG1 omega, hG0 omega, hpos.le])
  rw [integral_layerCoefficient_apply M S x] at hmono
  exact hmono

theorem integral_mul_layerCoefficient_apply_nonneg (hG0 : ∀ omega, 0 ≤ G omega)
    (x : Vec d) :
    0 ≤ ∫ omega, G omega * layerCoefficient M S omega x ∂M.P.toMeasure :=
  integral_nonneg fun omega =>
    mul_nonneg (hG0 omega) (layerCoefficient_pos M S omega x).le

theorem measurable_integral_mul_layerCoefficient (hG : Measurable G)
    (hG0 : ∀ omega, 0 ≤ G omega) (hG1 : ∀ omega, G omega ≤ 1) :
    Measurable fun x : Vec d =>
      ∫ omega, G omega * layerCoefficient M S omega x ∂M.P.toMeasure := by
  have hlint : Measurable fun x : Vec d =>
      ∫⁻ omega, ENNReal.ofReal (G omega * layerCoefficient M S omega x)
        ∂M.P.toMeasure := by
    refine Measurable.lintegral_prod_left ?_
    exact ENNReal.measurable_ofReal.comp
      ((hG.comp measurable_fst).mul (measurable_layerCoefficient_uncurry M S))
  have hfun : (fun x : Vec d =>
      ∫ omega, G omega * layerCoefficient M S omega x ∂M.P.toMeasure) =
      fun x => (∫⁻ omega, ENNReal.ofReal (G omega * layerCoefficient M S omega x)
        ∂M.P.toMeasure).toReal := by
    funext x
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_mul_layerCoefficient_apply M S hG hG0 hG1 x)
      (Filter.Eventually.of_forall fun omega =>
        mul_nonneg (hG0 omega) (layerCoefficient_pos M S omega x).le),
      ENNReal.toReal_ofReal
        (integral_mul_layerCoefficient_apply_nonneg M S hG0 x)]
  rw [hfun]
  exact hlint.ennreal_toReal

/-- **The exchange.**  The expectation of a weighted spatial integral of a layer
product is the spatial integral of the pointwise expectations. -/
theorem integral_mul_setIntegral_layerCoefficient (hG : Measurable G)
    (hG0 : ∀ omega, 0 ≤ G omega) (hG1 : ∀ omega, G omega ≤ 1)
    (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (hφint : IntegrableOn φ U volume) :
    (∫ omega, G omega * (∫ x in U, layerCoefficient M S omega x * φ x)
        ∂M.P.toMeasure =
      ∫ x in U, (∫ omega, G omega * layerCoefficient M S omega x ∂M.P.toMeasure) *
        φ x) ∧
      Integrable (fun omega : PotentialSample d =>
        G omega * ∫ x in U, layerCoefficient M S omega x * φ x) M.P.toMeasure := by
  classical
  set a : PotentialSample d → Vec d → ℝ := fun omega => layerCoefficient M S omega
    with hadef
  have ha0 : ∀ omega x, 0 ≤ a omega x := fun omega x =>
    (layerCoefficient_pos M S omega x).le
  set ψ : Vec d → ℝ := fun x =>
    ∫ omega, G omega * a omega x ∂M.P.toMeasure with hψdef
  have hψ0 : ∀ x, 0 ≤ ψ x := integral_mul_layerCoefficient_apply_nonneg M S hG0
  have hψ1 : ∀ x, ψ x ≤ 1 := integral_mul_layerCoefficient_apply_le_one M S hG hG0 hG1
  have hψmeas : Measurable ψ :=
    measurable_integral_mul_layerCoefficient M S hG hG0 hG1
  have hprodint : ∀ omega, IntegrableOn (fun x => a omega x * φ x) U volume :=
    fun omega => integrableOn_layerCoefficient_mul M S omega hU hUb hφint
  -- the pointwise `lintegral` identity in the sample
  have hinner : ∀ x : Vec d,
      ∫⁻ omega, ENNReal.ofReal (G omega * a omega x * φ x) ∂M.P.toMeasure =
        ENNReal.ofReal (ψ x * φ x) := by
    intro x
    have hsplit : ∀ omega : PotentialSample d,
        ENNReal.ofReal (G omega * a omega x * φ x) =
          ENNReal.ofReal (G omega * a omega x) * ENNReal.ofReal (φ x) := fun omega =>
      ENNReal.ofReal_mul (mul_nonneg (hG0 omega) (ha0 omega x))
    simp only [hsplit]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal
        (integrable_mul_layerCoefficient_apply M S hG hG0 hG1 x)
        (Filter.Eventually.of_forall fun omega =>
          mul_nonneg (hG0 omega) (ha0 omega x)),
      ← ENNReal.ofReal_mul (hψ0 x)]
  -- the `lintegral` identity in the sample, for fixed sample
  have houter : ∀ omega : PotentialSample d,
      ENNReal.ofReal (G omega * ∫ x in U, a omega x * φ x) =
        ∫⁻ x in U, ENNReal.ofReal (G omega * a omega x * φ x) := by
    intro omega
    rw [ENNReal.ofReal_mul (hG0 omega),
      ofReal_integral_eq_lintegral_ofReal (hprodint omega)
        (Filter.Eventually.of_forall fun x => mul_nonneg (ha0 omega x) (hφ0 x)),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (hG0 omega), mul_assoc]
  have hjoint : Measurable fun z : PotentialSample d × Vec d =>
      ENNReal.ofReal (G z.1 * a z.1 z.2 * φ z.2) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (((hG.comp measurable_fst).mul
      (measurable_layerCoefficient_uncurry M S)).mul (hφ.comp measurable_snd))
  have hswap : ∫⁻ omega, (∫⁻ x in U,
        ENNReal.ofReal (G omega * a omega x * φ x)) ∂M.P.toMeasure =
      ∫⁻ x in U, (∫⁻ omega,
        ENNReal.ofReal (G omega * a omega x * φ x) ∂M.P.toMeasure) :=
    lintegral_lintegral_swap hjoint.aemeasurable
  -- the total mass is finite
  have hfin : ∫⁻ x in U, ENNReal.ofReal (ψ x * φ x) ≤
      ∫⁻ x in U, ENNReal.ofReal (φ x) := by
    refine lintegral_mono fun x => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hψ0 x, hψ1 x, hφ0 x]
  have hφlint : ∫⁻ x in U, ENNReal.ofReal (φ x) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hφint
      ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x _ => hφ0 x))]
    exact ENNReal.ofReal_ne_top
  have hψφint : IntegrableOn (fun x => ψ x * φ x) U volume := by
    refine ⟨(hψmeas.mul hφ).aestronglyMeasurable.restrict, ?_⟩
    have henorm : ∀ x, ‖ψ x * φ x‖ₑ = ENNReal.ofReal (ψ x * φ x) := by
      intro x
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hψ0 x) (hφ0 x))]
    simp only [HasFiniteIntegral, henorm]
    exact lt_of_le_of_lt hfin (lt_of_le_of_ne le_top hφlint)
  have hGint : Integrable (fun omega : PotentialSample d =>
      G omega * ∫ x in U, a omega x * φ x) M.P.toMeasure := by
    have hmeasG : Measurable fun omega : PotentialSample d =>
        G omega * ∫ x in U, a omega x * φ x := by
      refine hG.mul ?_
      have hjoint' : Measurable fun z : PotentialSample d × Vec d =>
          a z.1 z.2 * φ z.2 :=
        (measurable_layerCoefficient_uncurry M S).mul (hφ.comp measurable_snd)
      exact (hjoint'.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict U)).measurable
    refine ⟨hmeasG.aestronglyMeasurable, ?_⟩
    have hnn : ∀ omega : PotentialSample d,
        0 ≤ G omega * ∫ x in U, a omega x * φ x := fun omega =>
      mul_nonneg (hG0 omega)
        (setIntegral_nonneg hU fun x _ => mul_nonneg (ha0 omega x) (hφ0 x))
    have henorm : ∀ omega : PotentialSample d,
        ‖G omega * ∫ x in U, a omega x * φ x‖ₑ =
          ENNReal.ofReal (G omega * ∫ x in U, a omega x * φ x) := by
      intro omega
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hnn omega)]
    simp only [HasFiniteIntegral, henorm, houter, hswap, hinner]
    exact lt_of_le_of_lt hfin (lt_of_le_of_ne le_top hφlint)
  -- both sides are the same `lintegral`
  have hL : ENNReal.ofReal (∫ omega, G omega * (∫ x in U, a omega x * φ x)
      ∂M.P.toMeasure) = ∫⁻ x in U, ENNReal.ofReal (ψ x * φ x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGint
      (Filter.Eventually.of_forall fun omega =>
        mul_nonneg (hG0 omega)
          (setIntegral_nonneg hU fun x _ => mul_nonneg (ha0 omega x) (hφ0 x)))]
    simp only [houter]
    rw [hswap]
    exact lintegral_congr fun x => hinner x
  have hR : ENNReal.ofReal (∫ x in U, ψ x * φ x) =
      ∫⁻ x in U, ENNReal.ofReal (ψ x * φ x) :=
    ofReal_integral_eq_lintegral_ofReal hψφint
      ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x _ =>
        mul_nonneg (hψ0 x) (hφ0 x)))
  have hLnn : 0 ≤ ∫ omega, G omega * (∫ x in U, a omega x * φ x) ∂M.P.toMeasure :=
    integral_nonneg fun omega =>
      mul_nonneg (hG0 omega)
        (setIntegral_nonneg hU fun x _ => mul_nonneg (ha0 omega x) (hφ0 x))
  have hRnn : 0 ≤ ∫ x in U, ψ x * φ x :=
    setIntegral_nonneg hU fun x _ => mul_nonneg (hψ0 x) (hφ0 x)
  have heq : ENNReal.ofReal (∫ omega, G omega * (∫ x in U, a omega x * φ x)
      ∂M.P.toMeasure) = ENNReal.ofReal (∫ x in U, ψ x * φ x) := by
    rw [hL, hR]
  refine ⟨?_, hGint⟩
  calc ∫ omega, G omega * (∫ x in U, a omega x * φ x) ∂M.P.toMeasure
      = (ENNReal.ofReal (∫ omega, G omega * (∫ x in U, a omega x * φ x)
          ∂M.P.toMeasure)).toReal := (ENNReal.toReal_ofReal hLnn).symm
    _ = (ENNReal.ofReal (∫ x in U, ψ x * φ x)).toReal := by rw [heq]
    _ = ∫ x in U, ψ x * φ x := ENNReal.toReal_ofReal hRnn

/-- The spatial integral of a weighted layer product is integrable in the
sample. -/
theorem integrable_setIntegral_layerCoefficient_mul (hφ : Measurable φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (hφint : IntegrableOn φ U volume) :
    Integrable (fun omega : PotentialSample d =>
      ∫ x in U, layerCoefficient M S omega x * φ x) M.P.toMeasure := by
  have h := (integral_mul_setIntegral_layerCoefficient M S
    (G := fun _ => (1 : ℝ)) measurable_const (fun _ => zero_le_one) (fun _ => le_rfl)
    hφ hφ0 hU hUb hφint).2
  refine h.congr (Filter.Eventually.of_forall fun omega => ?_)
  simp only [one_mul]

end Swap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
