module

public import SubdiffusiveProcess.Probability.SameLawComposition
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper
/-- Transfer convergence in measure through changing same-law environments.
Only the limit must be measurable: the finite error events are controlled by
outer measure, so no extra measurability supplier is needed for the raw arrays. -/
theorem represented_same_law_in_measure {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    {X : ℕ → S → ℝ} {V : S → ℝ} (hV : AEStronglyMeasurable V μ)
    (hXV : TendstoInMeasure μ X atTop V) :
    TendstoInMeasure P (fun n ω => X n (Y n ω)) atTop (fun ω => V (Y0 ω)) := by
  have hterm2 := aux_tendstoInMeasure_comp_const hY hY0 hconv hV
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδtop | hδtop
  · exact Eventually.of_forall (fun n => hδtop ▸ le_top)
  set δ2 := δ / 2 with hδ2_def
  have hδ2pos : 0 < δ2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hδ2sum : δ2 + δ2 ≤ δ := by
    have h2 : (2 : ℝ≥0∞) * (δ / 2) ≤ δ := ENNReal.mul_div_le
    calc δ2 + δ2 = 2 * (δ / 2) := by rw [hδ2_def]; ring
      _ ≤ δ := h2
  set ε2 := ε / 2 with hε2_def
  have hε2pos : 0 < ε2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε2sum : ε2 + ε2 ≤ ε := by
    have h2 : (2 : ℝ≥0∞) * (ε / 2) ≤ ε := ENNReal.mul_div_le
    calc ε2 + ε2 = 2 * (ε / 2) := by rw [hε2_def]; ring
      _ ≤ ε := h2
  have hterm1le : ∀ n, P {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))}
      ≤ μ {s | ε2 ≤ edist (X n s) (V s)} := by
    intro n
    change P ((Y n) ⁻¹' {s | ε2 ≤ edist (X n s) (V s)}) ≤ _
    calc _ ≤ (Measure.map (Y n) P) {s | ε2 ≤ edist (X n s) (V s)} :=
        Measure.le_map_apply (hY n).measurable.aemeasurable _
      _ = _ := by rw [(hY n).map_eq]
  have hE1 : ∀ᶠ n in atTop, P {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))} ≤ δ2 := by
    have h := ENNReal.tendsto_nhds_zero.1 (hXV ε2 hε2pos) δ2 hδ2pos
    filter_upwards [h] with n hn
    exact (hterm1le n).trans hn
  have hE2 : ∀ᶠ n in atTop, P {ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))} ≤ δ2 :=
    ENNReal.tendsto_nhds_zero.1 (hterm2 ε2 hε2pos) δ2 hδ2pos
  filter_upwards [hE1, hE2] with n hE1n hE2n
  have hsub : {ω | ε ≤ edist (X n (Y n ω)) (V (Y0 ω))}
      ⊆ {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))} ∪ {ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have htri : edist (X n (Y n ω)) (V (Y0 ω))
        ≤ edist (X n (Y n ω)) (V (Y n ω)) + edist (V (Y n ω)) (V (Y0 ω)) := edist_triangle _ _ _
    have hlt : edist (X n (Y n ω)) (V (Y0 ω)) < ε2 + ε2 := htri.trans_lt (by gcongr)
    have hle : ε ≤ edist (X n (Y n ω)) (V (Y0 ω)) := hω
    have hcontra : ε < ε := hle.trans_lt (hlt.trans_le hε2sum)
    exact absurd hcontra (lt_irrefl _)
  calc P {ω | ε ≤ edist (X n (Y n ω)) (V (Y0 ω))}
      ≤ P ({ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))} ∪ {ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))}) :=
        measure_mono hsub
    _ ≤ P {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))} + P {ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))} :=
        measure_union_le _ _
    _ ≤ δ2 + δ2 := add_le_add hE1n hE2n
    _ ≤ δ := hδ2sum

end Paper
