import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszFixedShell




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

omit [MeasurableSpace Omega] in
/-- A random geometric shell bound gives samplewise summability after the
graph contraction.  The existing deterministic comparison is applied after
fixing the sample, so its constant is `amplitude omega`. -/
theorem fluxRowMoment_hsummable_of_geometric_majorant
    {beta D : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j omega, 0 ≤ shell j omega)
    {amplitude : Omega → ℝ}
    (hgrowth : ∀ omega j, shell j omega ≤ amplitude omega * D ^ j) :
    ∀ omega, Summable (fun j ↦ beta ^ j * shell j omega) := by
  intro omega
  exact summable_repairedFluxRowRieszShellMajorant (K := amplitude omega)
    hbeta hD hcontract (fun j ↦ hshell j omega) (fun j ↦ hgrowth omega j)

omit [MeasurableSpace Omega] in
/-- The same random geometric shell bound controls the exact partition factor
by its samplewise geometric majorant. -/
theorem wholeSpaceFluxPartitionFactor_le_random_geometric_majorant
    {beta D : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j omega, 0 ≤ shell j omega)
    {amplitude : Omega → ℝ}
    (hgrowth : ∀ omega j, shell j omega ≤ amplitude omega * D ^ j)
    (omega : Omega) :
    wholeSpaceFluxPartitionFactor beta shell omega ≤
      1 + amplitude omega * (1 - beta * D)⁻¹ := by
  unfold wholeSpaceFluxPartitionFactor
  exact add_le_add_right
    (tsum_repairedFluxRowRieszShellMajorant_le (K := amplitude omega)
      hbeta hD hcontract (fun j ↦ hshell j omega)
      (fun j ↦ hgrowth omega j)) 1

/-- Integrability of a nonnegative pointwise majorant transfers to every
natural power of a measurable nonnegative minorant. -/
theorem integrable_pow_of_nonnegative_le
    {p : ℕ} {F G : Omega → ℝ}
    (hF : Measurable F) (hF0 : ∀ omega, 0 ≤ F omega)
    (hFG : ∀ omega, F omega ≤ G omega)
    (hG : Integrable (fun omega ↦ G omega ^ p) mu) :
    Integrable (fun omega ↦ F omega ^ p) mu := by
  refine hG.mono' (hF.pow_const p).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hF0 omega) p)]
  exact pow_le_pow_left₀ (hF0 omega) (hFG omega) p

/-- **The exact three stochastic-consumer hypotheses from a random geometric
majorant.**  The conclusion is, in order, `hsummable`, `hintegrable`, and
`hmoment` from `fluxRowRieszShellMomentInput_of_measurable_shell`.

All stochastic work is isolated in the last two premises, which concern the
explicit majorant `1 + amplitude * (1 - beta * D)⁻¹`. -/
theorem fluxRowMoment_consumer_hypotheses_of_geometric_majorant
    {beta D : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hmeas : ∀ j, Measurable (shell j))
    {amplitude : Omega → ℝ}
    (hgrowth : ∀ omega j, shell j omega ≤ amplitude omega * D ^ j)
    {p : ℕ} {K : ℝ}
    (hmajorantIntegrable : Integrable (fun omega ↦
      (1 + amplitude omega * (1 - beta * D)⁻¹) ^ p) mu)
    (hmajorantMoment : ∫ omega,
        (1 + amplitude omega * (1 - beta * D)⁻¹) ^ p ∂mu ≤ K ^ p) :
    (∀ omega, Summable (fun j ↦ beta ^ j * shell j omega)) ∧
      Integrable
        (fun omega ↦ wholeSpaceFluxPartitionFactor beta shell omega ^ p) mu ∧
      ∫ omega, wholeSpaceFluxPartitionFactor beta shell omega ^ p ∂mu ≤ K ^ p := by
  have hsummable := fluxRowMoment_hsummable_of_geometric_majorant
    hbeta hD hcontract hshell hgrowth
  have hfactorMeas : Measurable (wholeSpaceFluxPartitionFactor beta shell) :=
    measurable_wholeSpaceFluxPartitionFactor hbeta hshell hsummable hmeas
  have hfactor0 : ∀ omega,
      0 ≤ wholeSpaceFluxPartitionFactor beta shell omega := fun omega ↦
    zero_le_one.trans (one_le_wholeSpaceFluxPartitionFactor hbeta hshell omega)
  have hfactorBound : ∀ omega,
      wholeSpaceFluxPartitionFactor beta shell omega ≤
        1 + amplitude omega * (1 - beta * D)⁻¹ :=
    wholeSpaceFluxPartitionFactor_le_random_geometric_majorant
      hbeta hD hcontract hshell hgrowth
  have hintegrable : Integrable
      (fun omega ↦ wholeSpaceFluxPartitionFactor beta shell omega ^ p) mu :=
    integrable_pow_of_nonnegative_le hfactorMeas hfactor0 hfactorBound
      hmajorantIntegrable
  refine ⟨hsummable, hintegrable, ?_⟩
  exact (integral_mono hintegrable hmajorantIntegrable fun omega ↦
    pow_le_pow_left₀ (hfactor0 omega) (hfactorBound omega) p).trans
      hmajorantMoment

/-- Assembly of the shell moment input once the random geometric amplitude
has the printed high moment.  This theorem supplies the three formerly open
premises of `fluxRowRieszShellMomentInput_of_measurable_shell` literally. -/
theorem fluxRowRieszShellMomentInput_of_geometric_majorant
    {beta D : ℝ} (hbeta : 0 ≤ beta) (hD : 0 ≤ D)
    (hcontract : beta * D < 1)
    {shell : ℕ → Omega → ℝ} (hshell : ∀ j omega, 0 ≤ shell j omega)
    (hmeas : ∀ j, Measurable (shell j))
    {amplitude : Omega → ℝ}
    (hgrowth : ∀ omega j, shell j omega ≤ amplitude omega * D ^ j)
    {p : ℕ} {K C A : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K) (hlogK : Real.log K ≤ C)
    (hA : (p : ℝ)⁻¹ ≤ A)
    (hmajorantIntegrable : Integrable (fun omega ↦
      (1 + amplitude omega * (1 - beta * D)⁻¹) ^ p) mu)
    (hmajorantMoment : ∫ omega,
        (1 + amplitude omega * (1 - beta * D)⁻¹) ^ p ∂mu ≤ K ^ p) :
    FluxRowRieszShellMomentInput mu beta shell p K C A := by
  obtain ⟨hsummable, hintegrable, hmoment⟩ :=
    fluxRowMoment_consumer_hypotheses_of_geometric_majorant
      hbeta hD hcontract hshell hmeas hgrowth
        hmajorantIntegrable hmajorantMoment
  exact fluxRowRieszShellMomentInput_of_measurable_shell hbeta hshell hsummable
    hmeas hp hK hlogK hA hintegrable hmoment

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
