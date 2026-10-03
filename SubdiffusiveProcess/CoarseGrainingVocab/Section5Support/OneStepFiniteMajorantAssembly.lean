module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteComponentBudgets

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## Pointwise elimination of the selected energies -/

/-- Replace a raw principal/mixed/oscillatory cell split by nonnegative
principal and oscillatory majorants.  No measurability is involved: this is
applied separately at each sample before expectation is taken. -/
theorem half_target_le_normalized_finset_majorants_of_raw
    {ι : Type*} [DecidableEq ι]
    (cells : Finset ι) (target : ℝ)
    (rawPrincipal rawMixed rawOscillatory principal oscillatory : ι → ℝ)
    (hrawPrincipal0 : ∀ i ∈ cells, 0 ≤ rawPrincipal i)
    (hrawOscillatory0 : ∀ i ∈ cells, 0 ≤ rawOscillatory i)
    (hprincipal : ∀ i ∈ cells, rawPrincipal i ≤ principal i)
    (hoscillatory : ∀ i ∈ cells, rawOscillatory i ≤ oscillatory i)
    (hmixed : ∀ i ∈ cells,
      |rawMixed i| ≤
        Real.sqrt (rawPrincipal i) * Real.sqrt (rawOscillatory i))
    (hvariational :
      (1 / 2 : ℝ) * target ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * rawPrincipal i + rawMixed i +
            (1 / 2 : ℝ) * rawOscillatory i)) :
    (1 / 2 : ℝ) * target ≤
      ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ((1 / 2 : ℝ) * principal i +
          Real.sqrt (principal i) * Real.sqrt (oscillatory i) +
          (1 / 2 : ℝ) * oscillatory i) := by
  have hcell : ∀ i ∈ cells,
      (1 / 2 : ℝ) * rawPrincipal i + rawMixed i +
          (1 / 2 : ℝ) * rawOscillatory i ≤
        (1 / 2 : ℝ) * principal i +
          Real.sqrt (principal i) * Real.sqrt (oscillatory i) +
          (1 / 2 : ℝ) * oscillatory i := by
    intro i hi
    have hp0 : 0 ≤ principal i := (hrawPrincipal0 i hi).trans (hprincipal i hi)
    have ho0 : 0 ≤ oscillatory i :=
      (hrawOscillatory0 i hi).trans (hoscillatory i hi)
    have hsqrtP : Real.sqrt (rawPrincipal i) ≤ Real.sqrt (principal i) :=
      Real.sqrt_le_sqrt (hprincipal i hi)
    have hsqrtO : Real.sqrt (rawOscillatory i) ≤ Real.sqrt (oscillatory i) :=
      Real.sqrt_le_sqrt (hoscillatory i hi)
    have hproduct :
        Real.sqrt (rawPrincipal i) * Real.sqrt (rawOscillatory i) ≤
          Real.sqrt (principal i) * Real.sqrt (oscillatory i) := by
      exact mul_le_mul hsqrtP hsqrtO (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hmixed' : rawMixed i ≤
        Real.sqrt (principal i) * Real.sqrt (oscillatory i) :=
      (le_abs_self (rawMixed i)).trans ((hmixed i hi).trans hproduct)
    calc
      (1 / 2 : ℝ) * rawPrincipal i + rawMixed i +
          (1 / 2 : ℝ) * rawOscillatory i ≤
        (1 / 2 : ℝ) * principal i + rawMixed i +
          (1 / 2 : ℝ) * oscillatory i := by
            gcongr
            · exact hprincipal i hi
            · exact hoscillatory i hi
      _ ≤ (1 / 2 : ℝ) * principal i +
          Real.sqrt (principal i) * Real.sqrt (oscillatory i) +
          (1 / 2 : ℝ) * oscillatory i := by
            gcongr
  exact hvariational.trans <|
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi ↦ hcell i hi)
      (inv_nonneg.mpr (Nat.cast_nonneg cells.card))

/-- Almost-everywhere form of
`half_target_le_normalized_finset_majorants_of_raw`.  The raw energies may be
arbitrary functions of the sample; in particular, no measurability of the
samplewise selected minimizers is assumed. -/
theorem ae_half_target_le_normalized_finset_majorants_of_raw
    {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω}
    (cells : Finset ι) (target : Ω → ℝ)
    (rawPrincipal rawMixed rawOscillatory principal oscillatory :
      ι → Ω → ℝ)
    (hrawPrincipal0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] rawPrincipal i)
    (hrawOscillatory0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] rawOscillatory i)
    (hprincipal : ∀ i ∈ cells,
      rawPrincipal i ≤ᵐ[μ] principal i)
    (hoscillatory : ∀ i ∈ cells,
      rawOscillatory i ≤ᵐ[μ] oscillatory i)
    (hmixed : ∀ i ∈ cells, ∀ᵐ omega ∂μ,
      |rawMixed i omega| ≤
        Real.sqrt (rawPrincipal i omega) *
          Real.sqrt (rawOscillatory i omega))
    (hvariational : ∀ᵐ omega ∂μ,
      (1 / 2 : ℝ) * target omega ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * rawPrincipal i omega + rawMixed i omega +
            (1 / 2 : ℝ) * rawOscillatory i omega)) :
    ∀ᵐ omega ∂μ,
      (1 / 2 : ℝ) * target omega ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * principal i omega +
            Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega) +
            (1 / 2 : ℝ) * oscillatory i omega) := by
  have hp0 := (Finset.eventually_all cells).2 hrawPrincipal0
  have ho0 := (Finset.eventually_all cells).2 hrawOscillatory0
  have hp := (Finset.eventually_all cells).2 hprincipal
  have ho := (Finset.eventually_all cells).2 hoscillatory
  have hm := (Finset.eventually_all cells).2 hmixed
  filter_upwards [hp0, ho0, hp, ho, hm, hvariational] with
      omega hp0omega ho0omega hpomega hoomega hmomega hvaromega
  exact half_target_le_normalized_finset_majorants_of_raw
    cells (target omega)
      (fun i ↦ rawPrincipal i omega) (fun i ↦ rawMixed i omega)
      (fun i ↦ rawOscillatory i omega) (fun i ↦ principal i omega)
      (fun i ↦ oscillatory i omega)
      hp0omega ho0omega hpomega hoomega hmomega hvaromega

/-! ## Integration of the measurable envelopes -/

/-- Integrate a pointwise finite-cell majorant.  The square-root cross term is
integrable by `L² × L² -> L¹`, derived here only from integrability and
nonnegativity of the two energy envelopes. -/
theorem half_integral_target_le_normalized_finset_majorant_integrals
    {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω}
    (cells : Finset ι) (target : Ω → ℝ)
    (principal oscillatory : ι → Ω → ℝ)
    (htargetInt : Integrable target μ)
    (hprincipalInt : ∀ i ∈ cells, Integrable (principal i) μ)
    (hoscillatoryInt : ∀ i ∈ cells, Integrable (oscillatory i) μ)
    (hprincipal0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] principal i)
    (hoscillatory0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] oscillatory i)
    (hpointwise : ∀ᵐ omega ∂μ,
      (1 / 2 : ℝ) * target omega ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * principal i omega +
            Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega) +
            (1 / 2 : ℝ) * oscillatory i omega)) :
    (1 / 2 : ℝ) * ∫ omega, target omega ∂μ ≤
      (1 / 2 : ℝ) * (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ∫ omega, principal i omega ∂μ) +
      (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ∫ omega, Real.sqrt (principal i omega) *
          Real.sqrt (oscillatory i omega) ∂μ) +
      (1 / 2 : ℝ) * (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ∫ omega, oscillatory i omega ∂μ) := by
  let mixed : ι → Ω → ℝ := fun i omega ↦
    Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega)
  have hmixedInt : ∀ i ∈ cells, Integrable (mixed i) μ := by
    intro i hi
    have hpMem : MemLp (fun omega ↦ Real.sqrt (principal i omega)) 2 μ :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hprincipalInt i hi).aestronglyMeasurable)).2 <|
        (hprincipalInt i hi).congr <| by
          filter_upwards [hprincipal0 i hi] with omega homega
          rw [Real.sq_sqrt homega]
    have hoMem : MemLp (fun omega ↦ Real.sqrt (oscillatory i omega)) 2 μ :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hoscillatoryInt i hi).aestronglyMeasurable)).2 <|
        (hoscillatoryInt i hi).congr <| by
          filter_upwards [hoscillatory0 i hi] with omega homega
          rw [Real.sq_sqrt homega]
    exact hpMem.integrable_mul hoMem
  have hrhsInt : Integrable (fun omega ↦
      ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ((1 / 2 : ℝ) * principal i omega + mixed i omega +
          (1 / 2 : ℝ) * oscillatory i omega)) μ := by
    apply Integrable.const_mul
    exact integrable_finset_sum cells fun i hi ↦
      (((hprincipalInt i hi).const_mul (1 / 2)).add (hmixedInt i hi)).add
        ((hoscillatoryInt i hi).const_mul (1 / 2))
  have hmono :
      ∫ omega, (1 / 2 : ℝ) * target omega ∂μ ≤
        ∫ omega, ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * principal i omega + mixed i omega +
            (1 / 2 : ℝ) * oscillatory i omega) ∂μ := by
    apply integral_mono_ae (htargetInt.const_mul (1 / 2)) hrhsInt
    simpa only [mixed] using! hpointwise
  rw [integral_const_mul] at hmono
  have hrhs :
      ∫ omega, ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * principal i omega + mixed i omega +
            (1 / 2 : ℝ) * oscillatory i omega) ∂μ =
        (1 / 2 : ℝ) * (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ∫ omega, principal i omega ∂μ) +
        (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ∫ omega, mixed i omega ∂μ) +
        (1 / 2 : ℝ) * (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ∫ omega, oscillatory i omega ∂μ) := by
    rw [integral_const_mul, integral_finset_sum]
    · have hterm : ∀ i ∈ cells,
      ∫ omega, ((1 / 2 : ℝ) * principal i omega + mixed i omega +
              (1 / 2 : ℝ) * oscillatory i omega) ∂μ =
            (1 / 2 : ℝ) * ∫ omega, principal i omega ∂μ +
              ∫ omega, mixed i omega ∂μ +
              (1 / 2 : ℝ) * ∫ omega, oscillatory i omega ∂μ := by
        intro i hi
        let fp : Ω → ℝ := fun omega ↦ (1 / 2 : ℝ) * principal i omega
        let fo : Ω → ℝ := fun omega ↦ (1 / 2 : ℝ) * oscillatory i omega
        have hfp : Integrable fp μ := (hprincipalInt i hi).const_mul (1 / 2)
        have hfo : Integrable fo μ := (hoscillatoryInt i hi).const_mul (1 / 2)
        change ∫ omega, ((fp + mixed i) + fo) omega ∂μ = _
        calc
          _ = ∫ omega, (fp + mixed i) omega ∂μ + ∫ omega, fo omega ∂μ :=
            integral_add (hfp.add (hmixedInt i hi)) hfo
          _ = (∫ omega, fp omega ∂μ + ∫ omega, mixed i omega ∂μ) +
              ∫ omega, fo omega ∂μ := by
                have hadd : ∫ omega, (fp + mixed i) omega ∂μ =
                    ∫ omega, fp omega ∂μ + ∫ omega, mixed i omega ∂μ := by
                  simpa only [Pi.add_apply] using
                    (integral_add hfp (hmixedInt i hi))
                rw [hadd]
          _ = _ := by
            dsimp only [fp, fo]
            rw [integral_const_mul, integral_const_mul]
      rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    · intro i hi
      exact (((hprincipalInt i hi).const_mul (1 / 2)).add
        (hmixedInt i hi)).add ((hoscillatoryInt i hi).const_mul (1 / 2))
  rw [hrhs] at hmono
  simpa only [mixed] using hmono



theorem half_integral_target_le_normalized_finset_majorant_integrals_of_raw
    {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω}
    (cells : Finset ι) (target : Ω → ℝ)
    (rawPrincipal rawMixed rawOscillatory principal oscillatory :
      ι → Ω → ℝ)
    (htargetInt : Integrable target μ)
    (hprincipalInt : ∀ i ∈ cells, Integrable (principal i) μ)
    (hoscillatoryInt : ∀ i ∈ cells, Integrable (oscillatory i) μ)
    (hrawPrincipal0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] rawPrincipal i)
    (hrawOscillatory0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] rawOscillatory i)
    (hprincipal0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] principal i)
    (hoscillatory0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] oscillatory i)
    (hprincipal : ∀ i ∈ cells,
      rawPrincipal i ≤ᵐ[μ] principal i)
    (hoscillatory : ∀ i ∈ cells,
      rawOscillatory i ≤ᵐ[μ] oscillatory i)
    (hmixed : ∀ i ∈ cells, ∀ᵐ omega ∂μ,
      |rawMixed i omega| ≤
        Real.sqrt (rawPrincipal i omega) *
          Real.sqrt (rawOscillatory i omega))
    (hvariational : ∀ᵐ omega ∂μ,
      (1 / 2 : ℝ) * target omega ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * rawPrincipal i omega + rawMixed i omega +
            (1 / 2 : ℝ) * rawOscillatory i omega)) :
    (1 / 2 : ℝ) * ∫ omega, target omega ∂μ ≤
      (1 / 2 : ℝ) * (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ∫ omega, principal i omega ∂μ) +
      (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ∫ omega, Real.sqrt (principal i omega) *
          Real.sqrt (oscillatory i omega) ∂μ) +
      (1 / 2 : ℝ) * (((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
        ∫ omega, oscillatory i omega ∂μ) := by
  apply half_integral_target_le_normalized_finset_majorant_integrals
    cells target principal oscillatory htargetInt hprincipalInt
      hoscillatoryInt hprincipal0 hoscillatory0
  exact ae_half_target_le_normalized_finset_majorants_of_raw
    cells target rawPrincipal rawMixed rawOscillatory principal oscillatory
      hrawPrincipal0 hrawOscillatory0 hprincipal hoscillatory hmixed
      hvariational

/-! ## Direct penultimate closures from raw samplewise competitors -/

/-- Primal penultimate inequality with the nonmeasurable selected energies
eliminated before integration. -/
theorem one_step_upper_penultimate_of_ae_finite_majorants
    {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω}
    (cells : Finset ι) (hcells : cells.Nonempty)
    (target : Ω → ℝ) (principal oscillatory : ι → Ω → ℝ)
    (htargetInt : Integrable target μ)
    (hprincipalInt : ∀ i ∈ cells, Integrable (principal i) μ)
    (hoscillatoryInt : ∀ i ∈ cells, Integrable (oscillatory i) μ)
    (hprincipal0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] principal i)
    (hoscillatory0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] oscillatory i)
    (hpointwise : ∀ᵐ omega ∂μ,
      (1 / 2 : ℝ) * target omega ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * principal i omega +
            Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega) +
            (1 / 2 : ℝ) * oscillatory i omega))
    {delta tau h d A P O cell previous : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hO : 0 ≤ O)
    (hcell0 : 0 ≤ cell) (hprevious0 : 0 ≤ previous)
    (hPO : Real.sqrt P * Real.sqrt O ≤ A) (hOLe : O ≤ A)
    (hprincipalBudget : ((cells.card : ℝ)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂μ ≤ P * previous)
    (hprincipalSharp : ((cells.card : ℝ)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂μ ≤
        (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
          A * delta ^ 15 * previous)
    (hoscillatoryBudget : ((cells.card : ℝ)⁻¹) *
      ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂μ ≤
        O * delta ^ 30 * previous) :
    (1 / 2 : ℝ) * ∫ omega, target omega ∂μ ≤
      (1 / 2 - tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cell +
        (4 * A) * delta ^ 15 * previous := by
  let mixed : ι → Ω → ℝ := fun i omega ↦
    Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega)
  have hmixedInt : ∀ i ∈ cells, Integrable (mixed i) μ := by
    intro i hi
    have hpMem : MemLp (fun omega ↦ Real.sqrt (principal i omega)) 2 μ :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hprincipalInt i hi).aestronglyMeasurable)).2 <|
        (hprincipalInt i hi).congr <| by
          filter_upwards [hprincipal0 i hi] with omega homega
          rw [Real.sq_sqrt homega]
    have hoMem : MemLp (fun omega ↦ Real.sqrt (oscillatory i omega)) 2 μ :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hoscillatoryInt i hi).aestronglyMeasurable)).2 <|
        (hoscillatoryInt i hi).congr <| by
          filter_upwards [hoscillatory0 i hi] with omega homega
          rw [Real.sq_sqrt homega]
    exact hpMem.integrable_mul hoMem
  have hvariational :=
    half_integral_target_le_normalized_finset_majorant_integrals
      cells target principal oscillatory htargetInt hprincipalInt
        hoscillatoryInt hprincipal0 hoscillatory0 hpointwise
  apply one_step_upper_penultimate_of_finite_cell_budgets
    cells hcells mixed principal oscillatory hmixedInt hprincipalInt
      hoscillatoryInt hprincipal0 hoscillatory0
      (fun i hi ↦ Filter.Eventually.of_forall fun omega ↦ by
        show |mixed i omega| ≤
          Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega)
        dsimp only [mixed]
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)])
      hdelta0 hdelta1 hA hP hO hcell0 hprevious0 hPO hOLe
      hprincipalBudget hprincipalSharp hoscillatoryBudget
  simpa only [mixed] using hvariational

/-- Dual counterpart of
`one_step_upper_penultimate_of_ae_finite_majorants`. -/
theorem one_step_lower_penultimate_of_ae_finite_majorants
    {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω}
    (cells : Finset ι) (hcells : cells.Nonempty)
    (target : Ω → ℝ) (principal oscillatory : ι → Ω → ℝ)
    (htargetInt : Integrable target μ)
    (hprincipalInt : ∀ i ∈ cells, Integrable (principal i) μ)
    (hoscillatoryInt : ∀ i ∈ cells, Integrable (oscillatory i) μ)
    (hprincipal0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] principal i)
    (hoscillatory0 : ∀ i ∈ cells, 0 ≤ᵐ[μ] oscillatory i)
    (hpointwise : ∀ᵐ omega ∂μ,
      (1 / 2 : ℝ) * target omega ≤
        ((cells.card : ℝ)⁻¹) * ∑ i ∈ cells,
          ((1 / 2 : ℝ) * principal i omega +
            Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega) +
            (1 / 2 : ℝ) * oscillatory i omega))
    {delta tau h d A P O cellStarInv previousInv : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hO : 0 ≤ O)
    (hcell0 : 0 ≤ cellStarInv) (hprevious0 : 0 ≤ previousInv)
    (hPO : Real.sqrt P * Real.sqrt O ≤ A) (hOLe : O ≤ A)
    (hprincipalBudget : ((cells.card : ℝ)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂μ ≤ P * previousInv)
    (hprincipalSharp : ((cells.card : ℝ)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂μ ≤
        (1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv +
          A * delta ^ 15 * previousInv)
    (hoscillatoryBudget : ((cells.card : ℝ)⁻¹) *
      ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂μ ≤
        O * delta ^ 30 * previousInv) :
    (1 / 2 : ℝ) * ∫ omega, target omega ∂μ ≤
      (1 / 2 + tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cellStarInv +
        (4 * A) * delta ^ 15 * previousInv := by
  let mixed : ι → Ω → ℝ := fun i omega ↦
    Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega)
  have hmixedInt : ∀ i ∈ cells, Integrable (mixed i) μ := by
    intro i hi
    have hpMem : MemLp (fun omega ↦ Real.sqrt (principal i omega)) 2 μ :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hprincipalInt i hi).aestronglyMeasurable)).2 <|
        (hprincipalInt i hi).congr <| by
          filter_upwards [hprincipal0 i hi] with omega homega
          rw [Real.sq_sqrt homega]
    have hoMem : MemLp (fun omega ↦ Real.sqrt (oscillatory i omega)) 2 μ :=
      (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (hoscillatoryInt i hi).aestronglyMeasurable)).2 <|
        (hoscillatoryInt i hi).congr <| by
          filter_upwards [hoscillatory0 i hi] with omega homega
          rw [Real.sq_sqrt homega]
    exact hpMem.integrable_mul hoMem
  have hvariational :=
    half_integral_target_le_normalized_finset_majorant_integrals
      cells target principal oscillatory htargetInt hprincipalInt
        hoscillatoryInt hprincipal0 hoscillatory0 hpointwise
  apply one_step_lower_penultimate_of_finite_cell_budgets
    cells hcells mixed principal oscillatory hmixedInt hprincipalInt
      hoscillatoryInt hprincipal0 hoscillatory0
      (fun i hi ↦ Filter.Eventually.of_forall fun omega ↦ by
        show |mixed i omega| ≤
          Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega)
        dsimp only [mixed]
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)])
      hdelta0 hdelta1 hA hP hO hcell0 hprevious0 hPO hOLe
      hprincipalBudget hprincipalSharp hoscillatoryBudget
  simpa only [mixed] using hvariational

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
