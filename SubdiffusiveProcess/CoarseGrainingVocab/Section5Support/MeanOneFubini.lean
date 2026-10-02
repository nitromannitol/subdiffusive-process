import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
import Mathlib.MeasureTheory.Integral.Prod




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The general exchange -/

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A sample-wise continuous field is integrable on every bounded measurable
set. -/
theorem integrableOn_of_continuous {B : Vec d → ℝ} (hB : Continuous B)
    {U : Set (Vec d)} (hUb : Bornology.IsBounded U) :
    IntegrableOn B U volume :=
  (hB.locallyIntegrable.integrableOn_isCompact
    hUb.isCompact_closure).mono_set subset_closure

omit [IsProbabilityMeasure P] in
/-- The pointwise mean-one identity forces pointwise integrability: a
non-integrable function has Bochner integral zero. -/
theorem integrable_of_integral_eq_one {f : Ω → ℝ} (h : ∫ ω, f ω ∂P = 1) :
    Integrable f P := by
  by_contra hcon
  rw [integral_undef hcon] at h
  exact zero_ne_one h

variable {B : Ω → Vec d → ℝ}

/-- The `lintegral` form of the exchange. -/
private theorem lintegral_setLIntegral_ofReal
    (hjoint : Measurable fun z : Ω × Vec d => B z.1 z.2)
    (hB0 : ∀ ω x, 0 ≤ B ω x)
    (hmean : ∀ x, ∫ ω, B ω x ∂P = 1) (U : Set (Vec d)) :
    ∫⁻ ω, (∫⁻ x in U, ENNReal.ofReal (B ω x)) ∂P = volume U := by
  have hmeasProd : AEMeasurable
      (Function.uncurry fun (ω : Ω) (x : Vec d) => ENNReal.ofReal (B ω x))
      (P.prod (volume.restrict U)) :=
    (ENNReal.measurable_ofReal.comp hjoint).aemeasurable
  rw [lintegral_lintegral_swap hmeasProd]
  have hinner : ∀ x : Vec d, ∫⁻ ω, ENNReal.ofReal (B ω x) ∂P = 1 := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_integral_eq_one (hmean x))
      (Filter.Eventually.of_forall fun ω => hB0 ω x), hmean x]
    simp
  simp only [hinner]
  rw [lintegral_one, Measure.restrict_apply_univ]

/-- **The expected volume integral of a mean-one field is the volume.**  This is
the exchange `E[int_U B] = int_U E[B] = |U|` that Step 1 uses to read
`q_* <= 1` off `E[B_0(x)] = 1`, and Step 4 uses again for `A_N^{(R)}`. -/
theorem integral_setIntegral_of_mean_one
    (hjoint : Measurable fun z : Ω × Vec d => B z.1 z.2)
    (hB0 : ∀ ω x, 0 ≤ B ω x) (hcont : ∀ ω, Continuous (B ω))
    (hmean : ∀ x, ∫ ω, B ω x ∂P = 1)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∫ ω, (∫ x in U, B ω x) ∂P = (volume U).toReal ∧
      Integrable (fun ω => ∫ x in U, B ω x) P := by
  have hUtop : volume U ≠ ⊤ := ne_of_lt hUb.measure_lt_top
  have hInnerInt : ∀ ω, IntegrableOn (B ω) U volume := fun ω =>
    integrableOn_of_continuous (hcont ω) hUb
  have hpt : ∀ ω, ENNReal.ofReal (∫ x in U, B ω x) =
      ∫⁻ x in U, ENNReal.ofReal (B ω x) := fun ω =>
    ofReal_integral_eq_lintegral_ofReal (hInnerInt ω)
      (Filter.Eventually.of_forall fun x => hB0 ω x)
  have hswap := lintegral_setLIntegral_ofReal (P := P) hjoint hB0 hmean U
  have hmeasG : Measurable fun ω => ∫ x in U, B ω x := by
    have := (hjoint.stronglyMeasurable).integral_prod_right'
      (ν := volume.restrict U)
    exact this.measurable
  have hnonneg : ∀ ω, 0 ≤ ∫ x in U, B ω x := fun ω =>
    setIntegral_nonneg hU fun x _ => hB0 ω x
  have hlint : ∫⁻ ω, ENNReal.ofReal (∫ x in U, B ω x) ∂P = volume U := by
    simp only [hpt]
    exact hswap
  have hintG : Integrable (fun ω => ∫ x in U, B ω x) P := by
    refine ⟨hmeasG.aestronglyMeasurable, ?_⟩
    have henorm : ∀ ω, ‖∫ x in U, B ω x‖ₑ = ENNReal.ofReal (∫ x in U, B ω x) := by
      intro ω
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
    simp only [HasFiniteIntegral, henorm, hlint]
    exact lt_of_le_of_ne le_top hUtop
  refine ⟨?_, hintG⟩
  have := ofReal_integral_eq_lintegral_ofReal hintG
    (Filter.Eventually.of_forall hnonneg)
  rw [hlint] at this
  have hIntNonneg : 0 ≤ ∫ ω, (∫ x in U, B ω x) ∂P := integral_nonneg hnonneg
  rw [← ENNReal.toReal_ofReal hIntNonneg, this]

end General

/-! ## The GMC fields -/

/-- Joint measurability of a layer product in the sample and the point.  The
route is the one used by `measurable_cutoff_uncurry`. -/
theorem measurable_layerCoefficient_uncurry (M : GMCModel d) (S : Finset ℕ) :
    Measurable fun z : PotentialSample d × Vec d =>
      layerCoefficient M S z.1 z.2 := by
  have hEvalSwap : Measurable
      (Function.uncurry fun x : Vec d => fun g : PotentialField d => g x) :=
    measurable_uncurry_of_continuous_of_measurable
      (ι := Vec d) (α := PotentialField d) (β := ℝ)
      (fun g => g.contDiff_one.continuous)
      (fun x => PotentialField.measurable_eval x)
  have hEval : Measurable fun q : PotentialField d × Vec d => q.1 q.2 :=
    hEvalSwap.comp measurable_swap
  refine Finset.measurable_prod _ fun k _ => ?_
  have hCoordinate : Measurable fun z : PotentialSample d × Vec d =>
      (z.1 k, z.2) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  exact ((hEval.comp hCoordinate).sub measurable_const).exp

/-- Joint measurability of the shell factor `B_k`. -/
theorem measurable_shellFactor_uncurry (M : GMCModel d) (k : ℕ) :
    Measurable fun z : PotentialSample d × Vec d => shellFactor M k z.1 z.2 := by
  have h := measurable_layerCoefficient_uncurry M {k}
  simpa [layerCoefficient] using h

/-- Joint measurability of the sparse coefficient `A_N^{(R)}`. -/
theorem measurable_sparseLayerCoefficient_uncurry (M : GMCModel d) {R : ℕ}
    (hR : 0 < R) (N : ℕ) :
    Measurable fun z : PotentialSample d × Vec d =>
      sparseLayerCoefficient M R N z.1 z.2 := by
  have h := measurable_layerCoefficient_uncurry M (sparseLayerIndices R N)
  simpa [sparseLayerCoefficient_eq_layerCoefficient M hR] using h

/-- **`E[int_U B_k] = |U|`** on every bounded measurable set. -/
theorem integral_setIntegral_layerCoefficient (M : GMCModel d) (S : Finset ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∫ omega, (∫ x in U, layerCoefficient M S omega x) ∂M.P.toMeasure =
      (volume U).toReal :=
  (integral_setIntegral_of_mean_one (measurable_layerCoefficient_uncurry M S)
    (fun omega x => (layerCoefficient_pos M S omega x).le)
    (fun omega => continuous_layerCoefficient M S omega)
    (fun x => integral_layerCoefficient_apply M S x) hU hUb).1

/-- The volume integral of a layer product is integrable in the sample. -/
theorem integrable_setIntegral_layerCoefficient (M : GMCModel d) (S : Finset ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    Integrable (fun omega => ∫ x in U, layerCoefficient M S omega x)
      M.P.toMeasure :=
  (integral_setIntegral_of_mean_one (measurable_layerCoefficient_uncurry M S)
    (fun omega x => (layerCoefficient_pos M S omega x).le)
    (fun omega => continuous_layerCoefficient M S omega)
    (fun x => integral_layerCoefficient_apply M S x) hU hUb).2

/-- **`E[int_U B_0] = |U|`**, the normalization Step 1 reads `q_* <= 1` off. -/
theorem integral_setIntegral_shellFactor (M : GMCModel d) (k : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∫ omega, (∫ x in U, shellFactor M k omega x) ∂M.P.toMeasure =
      (volume U).toReal := by
  have h := integral_setIntegral_layerCoefficient M {k} hU hUb
  simpa [layerCoefficient] using h

/-- The volume integral of `B_k` is integrable in the sample. -/
theorem integrable_setIntegral_shellFactor (M : GMCModel d) (k : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    Integrable (fun omega => ∫ x in U, shellFactor M k omega x) M.P.toMeasure := by
  have h := integrable_setIntegral_layerCoefficient M {k} hU hUb
  simpa [layerCoefficient] using h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
