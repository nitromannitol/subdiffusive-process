import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellMomentAggregation
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSolutionLawTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepThermodynamicAggregation




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## Finite stationarity sweeps -/

/-- A normalized finite average of translates of one integrable observable
has exactly the same expectation as the origin observable. -/
theorem normalized_finset_integral_comp_translatePotentialSequence_eq
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (center : ι → Vec d) (s : Finset ι) (hs : s.Nonempty)
    (F : Sample d → ℝ) (hF : Integrable F M.P.toMeasure) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, F (translatePotentialSequence (center i) omega)
          ∂M.P.toMeasure =
      ∫ omega, F omega ∂M.P.toMeasure := by
  have hcell : ∀ i : ι,
      ∫ omega, F (translatePotentialSequence (center i) omega)
          ∂M.P.toMeasure =
        ∫ omega, F omega ∂M.P.toMeasure := by
    intro i
    exact integral_comp_translatePotentialSequence_eq M (center i) F
      hF.aestronglyMeasurable
  simp_rw [hcell]
  have hcard : s.card ≠ 0 := Nat.ne_of_gt hs.card_pos
  simp [hcard]

/-- Square-moment specialization of the finite stationarity sweep. -/
theorem normalized_finset_integral_comp_translatePotentialSequence_sq_eq
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (center : ι → Vec d) (s : Finset ι) (hs : s.Nonempty)
    (F : Sample d → ℝ)
    (hF : Integrable (fun omega ↦ F omega ^ 2) M.P.toMeasure) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, F (translatePotentialSequence (center i) omega) ^ 2
          ∂M.P.toMeasure =
      ∫ omega, F omega ^ 2 ∂M.P.toMeasure := by
  simpa only [Function.comp_apply] using
    normalized_finset_integral_comp_translatePotentialSequence_eq
      M center s hs (fun omega ↦ F omega ^ 2) hF

/-! ## Fourth-moment and ellipticity folds -/

/-- Two separate averaged fourth-moment estimates give the literal combined
`A_z^4 + B_z^4` budget used in the source. -/
theorem normalized_finset_integral_add_four_le_two_mul
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} (s : Finset ι)
    (A B : ι → Omega → ℝ) {E : ℝ}
    (hA4 : ∀ i ∈ s, Integrable (fun omega ↦ A i omega ^ 4) mu)
    (hB4 : ∀ i ∈ s, Integrable (fun omega ↦ B i omega ^ 4) mu)
    (hA : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, A i omega ^ 4 ∂mu ≤ E ^ 4)
    (hB : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, B i omega ^ 4 ∂mu ≤ E ^ 4) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu ≤
      2 * E ^ 4 := by
  have hsplit :
      (∑ i ∈ s, ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu) =
        (∑ i ∈ s, ∫ omega, A i omega ^ 4 ∂mu) +
          ∑ i ∈ s, ∫ omega, B i omega ^ 4 ∂mu := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_add (hA4 i hi) (hB4 i hi)
  calc
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu =
        (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, A i omega ^ 4 ∂mu) +
        (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, B i omega ^ 4 ∂mu) := by
      rw [hsplit]
      ring
    _ ≤ E ^ 4 + E ^ 4 := add_le_add hA hB
    _ = 2 * E ^ 4 := by ring

/-- Stationarity closes the literal averaged `A_z^4 + B_z^4` budget from
the two origin-cell fourth moments.  The cell family may be any finite list
of translates; no independence between cells is used. -/
theorem normalized_finset_integral_translated_add_four_le_two_mul
    {d : ℕ} {ι : Type*} [DecidableEq ι]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (center : ι → Vec d) (s : Finset ι) (hs : s.Nonempty)
    (A B : Sample d → ℝ)
    (hA4 : Integrable (fun omega ↦ A omega ^ 4) M.P.toMeasure)
    (hB4 : Integrable (fun omega ↦ B omega ^ 4) M.P.toMeasure)
    {E : ℝ}
    (hA : ∫ omega, A omega ^ 4 ∂M.P.toMeasure ≤ E ^ 4)
    (hB : ∫ omega, B omega ^ 4 ∂M.P.toMeasure ≤ E ^ 4) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega,
          A (translatePotentialSequence (center i) omega) ^ 4 +
            B (translatePotentialSequence (center i) omega) ^ 4
          ∂M.P.toMeasure ≤
      2 * E ^ 4 := by
  let AT : ι → Sample d → ℝ := fun i omega ↦
    A (translatePotentialSequence (center i) omega)
  let BT : ι → Sample d → ℝ := fun i omega ↦
    B (translatePotentialSequence (center i) omega)
  have hAT4 : ∀ i ∈ s,
      Integrable (fun omega ↦ AT i omega ^ 4) M.P.toMeasure := by
    intro i _hi
    exact (measurePreserving_translatePotentialSequence M (center i))
      |>.integrable_comp_of_integrable hA4
  have hBT4 : ∀ i ∈ s,
      Integrable (fun omega ↦ BT i omega ^ 4) M.P.toMeasure := by
    intro i _hi
    exact (measurePreserving_translatePotentialSequence M (center i))
      |>.integrable_comp_of_integrable hB4
  have hAT : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, AT i omega ^ 4 ∂M.P.toMeasure ≤ E ^ 4 := by
    rw [normalized_finset_integral_comp_translatePotentialSequence_eq
      M center s hs (fun omega ↦ A omega ^ 4) hA4]
    exact hA
  have hBT : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, BT i omega ^ 4 ∂M.P.toMeasure ≤ E ^ 4 := by
    rw [normalized_finset_integral_comp_translatePotentialSequence_eq
      M center s hs (fun omega ↦ B omega ^ 4) hB4]
    exact hB
  simpa only [AT, BT] using
    normalized_finset_integral_add_four_le_two_mul
      s AT BT hAT4 hBT4 hAT hBT

/-- Complete finite-family Holder close.  This is the direct consumer of the
three displayed budgets in Step 2: the ellipticity factor has averaged second
moment at most `L^2`, and the two localization observables have combined
averaged fourth moment at most `2 E^4`. -/
theorem normalized_finset_integral_mul_oneStepCellBesovError_le_six
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (s : Finset ι) (hs : s.Nonempty)
    (Lambda A B : ι → Omega → ℝ)
    (hLambda : ∀ i ∈ s, Measurable (Lambda i))
    (hA : ∀ i ∈ s, Measurable (A i))
    (hB : ∀ i ∈ s, Measurable (B i))
    (hLambda0 : ∀ i ∈ s, 0 ≤ᵐ[mu] Lambda i)
    (hA0 : ∀ i ∈ s, 0 ≤ᵐ[mu] A i)
    (hB0 : ∀ i ∈ s, 0 ≤ᵐ[mu] B i)
    (hLambda2 : ∀ i ∈ s,
      Integrable (fun omega ↦ Lambda i omega ^ 2) mu)
    (hA4 : ∀ i ∈ s, Integrable (fun omega ↦ A i omega ^ 4) mu)
    (hB4 : ∀ i ∈ s, Integrable (fun omega ↦ B i omega ^ 4) mu)
    {L E : ℝ} (hL : 0 ≤ L)
    (hLambdaBudget : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, Lambda i omega ^ 2 ∂mu ≤ L ^ 2)
    (hCellBudget : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu ≤ 2 * E ^ 4) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu ≤
      6 * L * E ^ 2 := by
  let X : ℝ := ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
    ∫ omega, Lambda i omega ^ 2 ∂mu
  let Y : ℝ := ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
    ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu
  have hY0 : 0 ≤ Y := by
    dsimp only [Y]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun omega ↦ by positivity)
  calc
    _ ≤ 3 * Real.sqrt X * Real.sqrt Y := by
      simpa only [X, Y] using
        normalized_finset_integral_mul_oneStepCellBesovError_le
          s hs Lambda A B hLambda hA hB hLambda0 hA0 hB0
            hLambda2 hA4 hB4
    _ ≤ 6 * L * E ^ 2 :=
      three_mul_sqrt_mul_sqrt_le_six_mul_sq hY0 hL
        (by simpa only [X] using hLambdaBudget)
        (by simpa only [Y] using hCellBudget)

/-! ## Mixed-energy finite folds -/

/-- Finite Cauchy--Schwarz after a cellwise mixed-energy estimate.  The
inputs `P` and `O` are the expected principal and oscillatory energies of
each cell. -/
theorem normalized_finset_sum_mixed_le_sqrt_mul_sqrt
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (mixed principal oscillatory : ι → ℝ)
    (hprincipal : ∀ i ∈ s, 0 ≤ principal i)
    (hoscillatory : ∀ i ∈ s, 0 ≤ oscillatory i)
    (hmixed : ∀ i ∈ s, mixed i ≤
      Real.sqrt (principal i) * Real.sqrt (oscillatory i)) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, mixed i ≤
      Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, principal i) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, oscillatory i) := by
  let f : ι → ℝ := fun i ↦ Real.sqrt (principal i)
  let g : ι → ℝ := fun i ↦ Real.sqrt (oscillatory i)
  have hinv : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  have hfirst :
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s, mixed i ≤
        ((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i := by
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi ↦ hmixed i hi) hinv
  have hcs := normalized_finset_sum_mul_le_sqrt_mul_sqrt s hs f g
  have hf : ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, principal i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    exact Real.sq_sqrt (hprincipal i hi)
  have hg : ∑ i ∈ s, g i ^ 2 = ∑ i ∈ s, oscillatory i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [g]
    exact Real.sq_sqrt (hoscillatory i hi)
  exact hfirst.trans (by simpa only [hf, hg] using hcs)

/-- Insert aggregate principal and oscillatory budgets into the preceding
finite Cauchy--Schwarz fold. -/
theorem normalized_finset_sum_mixed_le_of_budgets
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (mixed principal oscillatory : ι → ℝ)
    (hprincipal : ∀ i ∈ s, 0 ≤ principal i)
    (hoscillatory : ∀ i ∈ s, 0 ≤ oscillatory i)
    (hmixed : ∀ i ∈ s, mixed i ≤
      Real.sqrt (principal i) * Real.sqrt (oscillatory i))
    {P O : ℝ}
    (hprincipalBudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, principal i ≤ P)
    (hoscillatoryBudget : ((s.card : ℝ)⁻¹) *
      ∑ i ∈ s, oscillatory i ≤ O) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, mixed i ≤
      Real.sqrt P * Real.sqrt O := by
  calc
    _ ≤ Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, principal i) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, oscillatory i) :=
      normalized_finset_sum_mixed_le_sqrt_mul_sqrt
        s hs mixed principal oscillatory hprincipal hoscillatory hmixed
    _ ≤ Real.sqrt P * Real.sqrt O := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt hprincipalBudget)
        (Real.sqrt_le_sqrt hoscillatoryBudget)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## Thermodynamic passage -/

/-- The complete thermodynamic passage for the oscillatory cell energy.
Every finite volume may have a different surviving interior family; uniform
moment budgets give the source's limiting `6 L E^2` bound after the boundary
layer vanishes. -/
theorem oneStep_limit_le_six_of_finite_cell_moment_budgets
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (cells : ℕ → Finset ι) (hcells : ∀ K, (cells K).Nonempty)
    (Lambda A B : ℕ → ι → Omega → ℝ)
    (energy boundary : ℕ → ℝ) (energyInf : ℝ)
    (henergy : Filter.Tendsto energy Filter.atTop (nhds energyInf))
    (hboundary : Filter.Tendsto boundary Filter.atTop (nhds 0))
    (hfinite : ∀ K,
      energy K ≤
        (((((cells K).card : ℝ)⁻¹) * ∑ i ∈ cells K,
          ∫ omega, Lambda K i omega *
            oneStepCellBesovError (A K i omega) (B K i omega) ∂mu) +
          boundary K))
    (hLambda : ∀ K i, i ∈ cells K → Measurable (Lambda K i))
    (hA : ∀ K i, i ∈ cells K → Measurable (A K i))
    (hB : ∀ K i, i ∈ cells K → Measurable (B K i))
    (hLambda0 : ∀ K i, i ∈ cells K → 0 ≤ᵐ[mu] Lambda K i)
    (hA0 : ∀ K i, i ∈ cells K → 0 ≤ᵐ[mu] A K i)
    (hB0 : ∀ K i, i ∈ cells K → 0 ≤ᵐ[mu] B K i)
    (hLambda2 : ∀ K i, i ∈ cells K →
      Integrable (fun omega ↦ Lambda K i omega ^ 2) mu)
    (hA4 : ∀ K i, i ∈ cells K →
      Integrable (fun omega ↦ A K i omega ^ 4) mu)
    (hB4 : ∀ K i, i ∈ cells K →
      Integrable (fun omega ↦ B K i omega ^ 4) mu)
    {L E : ℝ} (hL : 0 ≤ L)
    (hLambdaBudget : ∀ K,
      ((((cells K).card : ℝ)⁻¹) * ∑ i ∈ cells K,
        ∫ omega, Lambda K i omega ^ 2 ∂mu) ≤ L ^ 2)
    (hCellBudget : ∀ K,
      ((((cells K).card : ℝ)⁻¹) * ∑ i ∈ cells K,
        ∫ omega, A K i omega ^ 4 + B K i omega ^ 4 ∂mu) ≤
          2 * E ^ 4) :
    energyInf ≤ 6 * L * E ^ 2 := by
  let interior : ℕ → ℝ := fun K ↦
    ((((cells K).card : ℝ)⁻¹) * ∑ i ∈ cells K,
      ∫ omega, Lambda K i omega *
        oneStepCellBesovError (A K i omega) (B K i omega) ∂mu)
  apply oneStep_limit_le_of_uniform_interior_bound henergy hboundary
    (fun K ↦ by simpa only [interior] using hfinite K)
  intro K
  exact normalized_finset_integral_mul_oneStepCellBesovError_le_six
    (cells K) (hcells K) (Lambda K) (A K) (B K)
      (hLambda K) (hA K) (hB K) (hLambda0 K) (hA0 K) (hB0 K)
      (hLambda2 K) (hA4 K) (hB4 K) hL
      (hLambdaBudget K) (hCellBudget K)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
