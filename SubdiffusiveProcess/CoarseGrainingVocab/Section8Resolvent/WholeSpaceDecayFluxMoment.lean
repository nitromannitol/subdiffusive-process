module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayFluxSum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}



theorem ogammaLE_log_sub_log_of_nat_moment [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} (hZmeas : Measurable Z) (hZone : ∀ omega, 1 ≤ Z omega)
    {p : ℕ} (hp : 0 < p) {K : ℝ} (hK : 1 ≤ K)
    (hZpow : Integrable (fun omega ↦ Z omega ^ p) mu)
    (hmoment : ∫ omega, Z omega ^ p ∂mu ≤ K ^ p) :
    SubdiffusiveProcess.OGammaLE mu 1 (p : ℝ)⁻¹
      (fun omega ↦ Real.log (Z omega) - Real.log K) := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let majorant : Omega → ℝ :=
    fun omega ↦ 1 + (K ^ p)⁻¹ * Z omega ^ p
  have hmajorant : Integrable majorant mu := by
    exact (integrable_const (1 : ℝ)).add (hZpow.const_mul (K ^ p)⁻¹)
  have hpoint : ∀ omega,
      Real.exp ((p : ℝ) *
        max (Real.log (Z omega) - Real.log K) 0) ≤
        majorant omega := by
    intro omega
    have hZpos : 0 < Z omega := lt_of_lt_of_le zero_lt_one (hZone omega)
    have hpowNonneg : 0 ≤ (K ^ p)⁻¹ * Z omega ^ p :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hKpos.le p))
        (pow_nonneg hZpos.le p)
    by_cases hlog : Real.log (Z omega) - Real.log K ≤ 0
    · rw [max_eq_right hlog]
      simp only [mul_zero, Real.exp_zero, majorant]
      exact le_add_of_nonneg_right hpowNonneg
    · have hlogPos : 0 < Real.log (Z omega) - Real.log K :=
        lt_of_not_ge hlog
      rw [max_eq_left hlogPos.le]
      have hexp :
          Real.exp ((p : ℝ) *
              (Real.log (Z omega) - Real.log K)) =
            (K ^ p)⁻¹ * Z omega ^ p := by
        rw [mul_sub, Real.exp_sub, Real.exp_nat_mul,
          Real.exp_nat_mul, Real.exp_log hZpos, Real.exp_log hKpos]
        field_simp
      rw [hexp]
      simp only [majorant]
      linarith
  have hintegrable : Integrable
      (fun omega ↦ Real.exp ((p : ℝ) *
        max (Real.log (Z omega) - Real.log K) 0)) mu := by
    refine Integrable.mono' hmajorant ?_ ?_
    · exact ((measurable_const.mul
        ((hZmeas.log.sub_const (Real.log K)).max measurable_const)).exp).aestronglyMeasurable
    · filter_upwards with omega
      have hmajorantNonneg : 0 ≤ majorant omega := by
        have hpowNonneg : 0 ≤ (K ^ p)⁻¹ * Z omega ^ p :=
          mul_nonneg (inv_nonneg.mpr (pow_nonneg hKpos.le p))
            (pow_nonneg (zero_le_one.trans (hZone omega)) p)
        simp only [majorant]
        linarith
      simpa only [Real.norm_eq_abs, Real.abs_exp,
        abs_of_nonneg hmajorantNonneg] using hpoint omega
  unfold SubdiffusiveProcess.OGammaLE
  simp only [Real.rpow_one, inv_inv]
  refine ⟨hintegrable, ?_⟩
  calc
    (∫ omega, Real.exp ((p : ℝ) *
        max (Real.log (Z omega) - Real.log K) 0) ∂mu) ≤
        ∫ omega, majorant omega ∂mu := by
      exact integral_mono hintegrable hmajorant hpoint
    _ = 1 + (K ^ p)⁻¹ * ∫ omega, Z omega ^ p ∂mu := by
      rw [integral_add (integrable_const (1 : ℝ))
        (hZpow.const_mul (K ^ p)⁻¹), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    _ ≤ 1 + (K ^ p)⁻¹ * K ^ p := by
      gcongr
    _ = 2 := by
      rw [inv_mul_cancel₀ (pow_ne_zero p (ne_of_gt hKpos))]
      norm_num



theorem ogammaLE_log_sub_of_nat_moment [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} (hZmeas : Measurable Z) (hZone : ∀ omega, 1 ≤ Z omega)
    {p : ℕ} (hp : 0 < p) {K C : ℝ} (hK : 1 ≤ K)
    (hlogKC : Real.log K ≤ C)
    (hZpow : Integrable (fun omega ↦ Z omega ^ p) mu)
    (hmoment : ∫ omega, Z omega ^ p ∂mu ≤ K ^ p) :
    SubdiffusiveProcess.OGammaLE mu 1 (p : ℝ)⁻¹
      (fun omega ↦ Real.log (Z omega) - C) := by
  have hbase := ogammaLE_log_sub_log_of_nat_moment
    hZmeas hZone hp hK hZpow hmoment
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hA : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpReal
  have hle : ∀ omega,
      Real.log (Z omega) - C ≤ Real.log (Z omega) - Real.log K := by
    intro omega
    linarith
  have hpoint : ∀ omega,
      Real.exp (((p : ℝ)⁻¹⁻¹ *
          max (Real.log (Z omega) - C) 0) ^ (1 : ℝ)) ≤
        Real.exp (((p : ℝ)⁻¹⁻¹ *
          max (Real.log (Z omega) - Real.log K) 0) ^ (1 : ℝ)) := by
    intro omega
    apply Real.exp_le_exp.mpr
    rw [Real.rpow_one, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left
      (max_le_max (hle omega) le_rfl) (inv_nonneg.mpr hA.le)
  refine ⟨?_, ?_⟩
  · refine hbase.1.mono' ?_ ?_
    · exact (((measurable_const.mul
        ((hZmeas.log.sub_const C).max measurable_const)).pow_const
          (1 : ℝ))).exp.aestronglyMeasurable
    · filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hpoint omega
  · exact (integral_mono_ae (by
        refine hbase.1.mono' ?_ ?_
        · exact (((measurable_const.mul
            ((hZmeas.log.sub_const C).max measurable_const)).pow_const
              (1 : ℝ))).exp.aestronglyMeasurable
        · filter_upwards with omega
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
          exact hpoint omega)
        hbase.1 (Filter.Eventually.of_forall hpoint)).trans hbase.2



theorem ogammaLE_log_sub_of_nat_moment_at_scale [IsProbabilityMeasure mu]
    {Z : Omega → ℝ} (hZmeas : Measurable Z) (hZone : ∀ omega, 1 ≤ Z omega)
    {p : ℕ} (hp : 0 < p) {K C A : ℝ} (hK : 1 ≤ K)
    (hlogKC : Real.log K ≤ C) (hscale : (p : ℝ)⁻¹ ≤ A)
    (hZpow : Integrable (fun omega ↦ Z omega ^ p) mu)
    (hmoment : ∫ omega, Z omega ^ p ∂mu ≤ K ^ p) :
    SubdiffusiveProcess.OGammaLE mu 1 A (fun omega ↦ Real.log (Z omega) - C) := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  exact Section6CutoffRegularity.ogammaLE_mono_scale zero_lt_one
    (inv_pos.mpr hpReal) hscale (hZmeas.log.sub_const C)
    (ogammaLE_log_sub_of_nat_moment
      hZmeas hZone hp hK hlogKC hZpow hmoment)



theorem ogammaLE_log_one_add_sub_of_nat_moment_at_scale
    [IsProbabilityMeasure mu]
    {S : Omega → ℝ} (hSmeas : Measurable S) (hSnonneg : ∀ omega, 0 ≤ S omega)
    {p : ℕ} (hp : 0 < p) {K C A : ℝ} (hK : 1 ≤ K)
    (hlogKC : Real.log K ≤ C) (hscale : (p : ℝ)⁻¹ ≤ A)
    (hSpow : Integrable (fun omega ↦ (1 + S omega) ^ p) mu)
    (hmoment : ∫ omega, (1 + S omega) ^ p ∂mu ≤ K ^ p) :
    SubdiffusiveProcess.OGammaLE mu 1 A (fun omega ↦ Real.log (1 + S omega) - C) := by
  apply ogammaLE_log_sub_of_nat_moment_at_scale
    (measurable_const.add hSmeas) (fun omega ↦ by
      change 1 ≤ 1 + S omega
      linarith only [hSnonneg omega])
    hp hK hlogKC hscale hSpow hmoment



theorem wholeSpaceFluxPartitionFactor_one_le_and_ogammaLE_of_nat_moment
    [IsProbabilityMeasure mu]
    {beta : ℝ} (hbeta : 0 ≤ beta) {shell : ℕ → Omega → ℝ}
    (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hfactorMeas : Measurable (wholeSpaceFluxPartitionFactor beta shell))
    {p : ℕ} (hp : 0 < p) {K C A : ℝ} (hK : 1 ≤ K)
    (hlogKC : Real.log K ≤ C) (hscale : (p : ℝ)⁻¹ ≤ A)
    (hfactorPow : Integrable
      (fun omega ↦ wholeSpaceFluxPartitionFactor beta shell omega ^ p) mu)
    (hmoment : ∫ omega, wholeSpaceFluxPartitionFactor beta shell omega ^ p ∂mu ≤
      K ^ p) :
    (∀ omega, 1 ≤ wholeSpaceFluxPartitionFactor beta shell omega) ∧
      SubdiffusiveProcess.OGammaLE mu 1 A
        (fun omega ↦ Real.log (wholeSpaceFluxPartitionFactor beta shell omega) - C) := by
  have hone : ∀ omega, 1 ≤ wholeSpaceFluxPartitionFactor beta shell omega :=
    one_le_wholeSpaceFluxPartitionFactor hbeta hshell
  exact ⟨hone, ogammaLE_log_sub_of_nat_moment_at_scale
    hfactorMeas hone hp hK hlogKC hscale hfactorPow hmoment⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
