module

public import SubdiffusiveProcess.ConcentrationScales.EssSupField
public import SubdiffusiveProcess.ConcentrationScales.FieldCells

@[expose] public section

/-!
# Γ₂-moments of cell suprema and a Chernoff–Markov bound for independent products

For a jointly measurable random field `X` whose law is invariant under the translation by the centre of a
cell, the `Γ₂` moment bound on `‖X‖_{L^∞(cube)}` transfers to `‖X‖_{L^∞(cell)}`, and then to the exponential
moments `E ess sup_{cell} exp(λ|X|) ≤ 2 exp(λ²δ²/4)`.  For independent measurable functionals the expectation
of a product factorizes, which gives the Markov bound `P[c < ∏ ρ_i(X_i)] ≤ c⁻¹ B^{#I}`.
-/

namespace SubdiffusiveProcess.ConcentrationScales

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

section Moments

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The cell-restricted `Γ₂` moment bound (`∫⁻ ess sup_{cell} exp((|X|/δ)²) ≤ 2`) from the bound on the centered
cube and the invariance of the law of `X` under the shift by the cell centre. -/
theorem lintegral_essSup_cell_le {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Vec d → ℝ} {δ : ℝ}
    (hXm : Measurable fun p : Ω × Vec d => X p.1 p.2) (i : ℤ) (w : Fin d → ℤ)
    (hstat : μ.map (fun ω x => X ω (x + cellShift d i w)) = μ.map X)
    (hΓ : ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω x|) ^ 2)))
      (volume.restrict (cube d i)) ∂μ ≤ 2) :
    ∫⁻ ω, essSup (fun y => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω y|) ^ 2)))
      (volume.restrict (cell d i w)) ∂μ ≤ 2 := by
  have hG : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp ((δ⁻¹ * |t|) ^ 2)) := by fun_prop
  have hY' : Measurable fun p : Ω × Vec d => X p.1 (p.2 + cellShift d i w) :=
    hXm.comp (measurable_fst.prodMk (measurable_snd.add_const _))
  calc ∫⁻ ω, essSup (fun y => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω y|) ^ 2)))
        (volume.restrict (cell d i w)) ∂μ
      = ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω (x + cellShift d i w)|) ^ 2)))
        (volume.restrict (cube d i)) ∂μ := by
        refine lintegral_congr fun ω => ?_
        exact essSup_cell_eq d i w _
    _ ≤ ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω x|) ^ 2)))
        (volume.restrict (cube d i)) ∂μ :=
        lintegral_essSup_le_of_map_eq (G := fun t : ℝ => ENNReal.ofReal (Real.exp ((δ⁻¹ * |t|) ^ 2)))
          (Y := X) (Y' := fun ω x => X ω (x + cellShift d i w)) hXm hY' hstat hG
    _ ≤ 2 := hΓ

theorem exp_mul_abs_le (lam δ t : ℝ) (hδ : 0 < δ) :
    ENNReal.ofReal (Real.exp (lam * |t|)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) *
        ENNReal.ofReal (Real.exp ((δ⁻¹ * |t|) ^ 2)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have key : lam * |t| = 2 * (lam * δ / 2) * (δ⁻¹ * |t|) := by field_simp
  have hsq : (lam * δ / 2) ^ 2 = lam ^ 2 * δ ^ 2 / 4 := by ring
  nlinarith [sq_nonneg (lam * δ / 2 - δ⁻¹ * |t|)]

/-- The exponential moment of the cell supremum: `E ess sup_{cell} e^{λ|X|} ≤ 2 e^{λ²δ²/4}`. -/
theorem lintegral_essSup_exp_cell_le {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Vec d → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hXm : Measurable fun p : Ω × Vec d => X p.1 p.2) (i : ℤ) (w : Fin d → ℤ)
    (hstat : μ.map (fun ω x => X ω (x + cellShift d i w)) = μ.map X)
    (hΓ : ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω x|) ^ 2)))
      (volume.restrict (cube d i)) ∂μ ≤ 2) (lam : ℝ) :
    ∫⁻ ω, essSup (fun y => ENNReal.ofReal (Real.exp (lam * |X ω y|)))
      (volume.restrict (cell d i w)) ∂μ ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) * 2 := by
  have hM0 := lintegral_essSup_cell_le hXm i w hstat hΓ
  calc ∫⁻ ω, essSup (fun y => ENNReal.ofReal (Real.exp (lam * |X ω y|)))
        (volume.restrict (cell d i w)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) *
        essSup (fun y => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω y|) ^ 2)))
          (volume.restrict (cell d i w)) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.essSup_const_mul]
        exact essSup_mono_ae (Filter.Eventually.of_forall fun y => exp_mul_abs_le lam δ _ hδ)
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) *
        ∫⁻ ω, essSup (fun y => ENNReal.ofReal (Real.exp ((δ⁻¹ * |X ω y|) ^ 2)))
          (volume.restrict (cell d i w)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * δ ^ 2 / 4)) * 2 := by gcongr

/-- Markov bound for a product of independent measurable functionals of the fields `X i`. -/
theorem measure_lt_prod_le {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℤ → Ω → Vec d → ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (I : Finset ℤ)
    (ρ : ℤ → (Vec d → ℝ) → ℝ≥0∞) (hρ : ∀ i, Measurable (ρ i)) (B : ℝ≥0∞)
    (hB : ∀ i ∈ I, ∫⁻ ω, ρ i (X i ω) ∂μ ≤ B) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    μ {ω | c < ∏ i ∈ I, ρ i (X i ω)} ≤ c⁻¹ * B ^ I.card := by
  have hZ : iIndepFun (fun i => ρ i ∘ X i) μ := hind.comp ρ hρ
  have hZm : ∀ i, Measurable (ρ i ∘ X i) := fun i => (hρ i).comp (hXmeas i)
  have hprod := lintegral_prod_eq_prod_lintegral_of_indepFun I (fun i => ρ i ∘ X i) hZ hZm
  have hmeasP : Measurable fun ω => ∏ i ∈ I, ρ i (X i ω) :=
    Finset.measurable_prod I fun i _ => hZm i
  have hmk := mul_meas_ge_le_lintegral₀ (μ := μ) hmeasP.aemeasurable c
  have hint : ∫⁻ ω, ∏ i ∈ I, ρ i (X i ω) ∂μ ≤ B ^ I.card := by
    calc ∫⁻ ω, ∏ i ∈ I, ρ i (X i ω) ∂μ = ∏ i ∈ I, ∫⁻ ω, ρ i (X i ω) ∂μ := hprod
      _ ≤ ∏ _i ∈ I, B := Finset.prod_le_prod' hB
      _ = B ^ I.card := Finset.prod_const B
  have h1 : c * μ {ω | c ≤ ∏ i ∈ I, ρ i (X i ω)} ≤ B ^ I.card := hmk.trans hint
  calc μ {ω | c < ∏ i ∈ I, ρ i (X i ω)} ≤ μ {ω | c ≤ ∏ i ∈ I, ρ i (X i ω)} :=
        measure_mono (Set.setOf_subset_setOf.mpr fun ω h => h.le)
    _ = c⁻¹ * (c * μ {ω | c ≤ ∏ i ∈ I, ρ i (X i ω)}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul]
    _ ≤ c⁻¹ * B ^ I.card := by gcongr

end Moments

end

end SubdiffusiveProcess.ConcentrationScales
