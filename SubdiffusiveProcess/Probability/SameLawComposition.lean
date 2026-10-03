module

public import Mathlib

@[expose] public section

/-!
# Same-law composition limits

If `Y n → Y0` almost surely, with all `Y n` and `Y0` pushing a probability measure `P` forward to
the same law `μ`, and `X n → V` in `L¹(μ)` (resp. in `μ`-measure), this file shows that the
composed sequence `X n ∘ Y n` converges to `V ∘ Y0` in `L¹(P)`, in `P`-measure, and (for the
in-measure hypothesis) again in `P`-measure without any integrability assumption on `V`. It does
not address any other mode of convergence (e.g. almost-sure convergence of the composition).
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SubdiffusiveProcess

/-- If `Y n → Y0` almost surely with all `Y n`, `Y0` of the same law `μ`, and `X n → V` in
`L¹(μ)`, then `X n ∘ Y n → V ∘ Y0` in `L¹(P)`. -/
theorem tendsto_eLpNorm_comp_of_sameLaw {Ω S : Type*} [MeasurableSpace Ω] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [TopologicalSpace.PseudoMetrizableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    {X : ℕ → S → ℝ} {V : S → ℝ} (hV : MemLp V 1 μ) (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXV : Tendsto (fun n => eLpNorm (X n - V) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => X n (Y n ω) - V (Y0 ω)) 1 P) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · exact Eventually.of_forall (fun n => hεtop ▸ le_top)
  set ε4 := ε / 4 with hε4_def
  have hε4pos : 0 < ε4 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε4ne : ε4 ≠ 0 := hε4pos.ne'
  have hε4sum : ε4 + ε4 + ε4 + ε4 ≤ ε := by
    have h4 : (4 : ℝ≥0∞) * (ε / 4) ≤ ε := ENNReal.mul_div_le
    calc ε4 + ε4 + ε4 + ε4 = 4 * (ε / 4) := by rw [hε4_def]; ring
      _ ≤ ε := h4
  obtain ⟨g, hg_close, hg_mem⟩ :=
    hV.exists_boundedContinuous_eLpNorm_sub_le (p := (1 : ℝ≥0∞)) ENNReal.one_ne_top hε4ne
  have hg_close' : eLpNorm ((g : S → ℝ) - V) 1 μ ≤ ε4 := by
    rw [eLpNorm_sub_comm]; exact hg_close
  set C : ℝ := ‖g‖ with hC_def
  have hgbound : ∀ x, ‖g x‖ ≤ C := fun x => g.norm_coe_le_norm x
  have hmeas_raw : ∀ n, AEStronglyMeasurable (fun ω => g (Y n ω) - g (Y0 ω)) P := fun n =>
    (hg_mem.aestronglyMeasurable.comp_measurePreserving (hY n)).sub (hg_mem.aestronglyMeasurable.comp_measurePreserving hY0)
  have hbound_pt : ∀ n, ∀ᵐ ω ∂P, ‖g (Y n ω) - g (Y0 ω)‖ ≤ (2 * C : ℝ) := fun n =>
    Eventually.of_forall fun ω => by
      have h1 : ‖g (Y n ω) - g (Y0 ω)‖ ≤ ‖g (Y n ω)‖ + ‖g (Y0 ω)‖ := norm_sub_le _ _
      have h2 : ‖g (Y n ω)‖ + ‖g (Y0 ω)‖ ≤ C + C := add_le_add (hgbound _) (hgbound _)
      calc ‖g (Y n ω) - g (Y0 ω)‖ ≤ C + C := h1.trans h2
        _ = 2 * C := by ring
  have hbound_integrable : Integrable (fun _ : Ω => (2 * C : ℝ)) P := integrable_const _
  have hint_n : ∀ n, Integrable (fun ω => g (Y n ω) - g (Y0 ω)) P := fun n =>
    Integrable.mono' hbound_integrable (hmeas_raw n) (hbound_pt n)
  have hDtendsto :
      Tendsto (fun n => eLpNorm (fun ω => g (Y n ω) - g (Y0 ω)) 1 P) atTop (𝓝 0) := by
    have hmeas : ∀ n, AEStronglyMeasurable (fun ω => ‖g (Y n ω) - g (Y0 ω)‖) P := fun n =>
      (hmeas_raw n).norm
    have hbound : ∀ n, ∀ᵐ ω ∂P,
        ‖(fun ω => ‖g (Y n ω) - g (Y0 ω)‖) ω‖ ≤ (2 * C : ℝ) := fun n =>
      (hbound_pt n).mono fun ω h => by rw [norm_norm]; exact h
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ‖g (Y n ω) - g (Y0 ω)‖) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hconv] with ω hω
      have hg' : Tendsto (fun n => g (Y n ω)) atTop (𝓝 (g (Y0 ω))) :=
        (g.continuous.tendsto (Y0 ω)).comp hω
      have hsub : Tendsto (fun n => g (Y n ω) - g (Y0 ω)) atTop (𝓝 (g (Y0 ω) - g (Y0 ω))) :=
        hg'.sub tendsto_const_nhds
      have hsub0 : Tendsto (fun n => g (Y n ω) - g (Y0 ω)) atTop (𝓝 0) := by
        simpa using hsub
      simpa using hsub0.norm
    have hint := tendsto_integral_of_dominated_convergence (fun _ => (2 * C : ℝ)) hmeas
      hbound_integrable hbound hlim
    simp only [integral_zero] at hint
    have hofReal := ENNReal.tendsto_ofReal hint
    simp only [ENNReal.ofReal_zero] at hofReal
    have heq : ∀ n, eLpNorm (fun ω => g (Y n ω) - g (Y0 ω)) 1 P
        = ENNReal.ofReal (∫ ω, ‖g (Y n ω) - g (Y0 ω)‖ ∂P) := fun n => by
      rw [eLpNorm_one_eq_lintegral_enorm (hmeas_raw n),
        ← ofReal_integral_norm_eq_lintegral_enorm (hint_n n)]
    simp_rw [heq]
    exact hofReal
  have hA : ∀ᶠ n in atTop, eLpNorm (X n - V) 1 μ ≤ ε4 :=
    (ENNReal.tendsto_nhds_zero.1 hXV) ε4 hε4pos
  have hD : ∀ᶠ n in atTop, eLpNorm (fun ω => g (Y n ω) - g (Y0 ω)) 1 P ≤ ε4 :=
    (ENNReal.tendsto_nhds_zero.1 hDtendsto) ε4 hε4pos
  filter_upwards [hA, hD] with n hAn hDn
  have h1 : AEStronglyMeasurable (fun ω => X n (Y n ω) - V (Y n ω)) P := by
    have := ((hX n).sub hV.aestronglyMeasurable).comp_measurePreserving (hY n)
    simpa only [Function.comp_def, Pi.sub_def] using this
  have h2 : AEStronglyMeasurable (fun ω => V (Y n ω) - g (Y n ω)) P := by
    have := (hV.aestronglyMeasurable.sub hg_mem.aestronglyMeasurable).comp_measurePreserving (hY n)
    simpa only [Function.comp_def, Pi.sub_def] using this
  have h3 : AEStronglyMeasurable (fun ω => g (Y n ω) - g (Y0 ω)) P := hmeas_raw n
  have h4 : AEStronglyMeasurable (fun ω => g (Y0 ω) - V (Y0 ω)) P := by
    have := (hg_mem.aestronglyMeasurable.sub hV.aestronglyMeasurable).comp_measurePreserving hY0
    simpa only [Function.comp_def, Pi.sub_def] using this
  have he1 : eLpNorm (fun ω => X n (Y n ω) - V (Y n ω)) 1 P = eLpNorm (X n - V) 1 μ := by
    have := eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞)) ((hX n).sub hV.aestronglyMeasurable) (hY n)
    simpa only [Function.comp_def, Pi.sub_def] using this
  have he2 : eLpNorm (fun ω => V (Y n ω) - g (Y n ω)) 1 P
      = eLpNorm ((V - (g : S → ℝ))) 1 μ := by
    have := eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞)) (hV.aestronglyMeasurable.sub hg_mem.aestronglyMeasurable) (hY n)
    simpa only [Function.comp_def, Pi.sub_def] using this
  have he4 : eLpNorm (fun ω => g (Y0 ω) - V (Y0 ω)) 1 P
      = eLpNorm (((g : S → ℝ) - V)) 1 μ := by
    have := eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞)) (hg_mem.aestronglyMeasurable.sub hV.aestronglyMeasurable) hY0
    simpa only [Function.comp_def, Pi.sub_def] using this
  have he1_le : eLpNorm (fun ω => X n (Y n ω) - V (Y n ω)) 1 P ≤ ε4 := he1 ▸ hAn
  have he2_le : eLpNorm (fun ω => V (Y n ω) - g (Y n ω)) 1 P ≤ ε4 := he2 ▸ hg_close
  have he4_le : eLpNorm (fun ω => g (Y0 ω) - V (Y0 ω)) 1 P ≤ ε4 := he4 ▸ hg_close'
  have hsplit : (fun ω => X n (Y n ω) - V (Y0 ω))
      = (fun ω => (X n (Y n ω) - V (Y n ω))
          + ((V (Y n ω) - g (Y n ω)) + ((g (Y n ω) - g (Y0 ω)) + (g (Y0 ω) - V (Y0 ω))))) := by
    funext ω; ring
  rw [hsplit]
  have step1 := eLpNorm_add_le (μ := P)
    (f := fun ω => X n (Y n ω) - V (Y n ω))
    (g := fun ω => (V (Y n ω) - g (Y n ω)) +
      ((g (Y n ω) - g (Y0 ω)) + (g (Y0 ω) - V (Y0 ω))))
    (le_refl (1 : ℝ≥0∞))
  have step2 := eLpNorm_add_le (μ := P)
    (f := fun ω => V (Y n ω) - g (Y n ω))
    (g := fun ω => (g (Y n ω) - g (Y0 ω)) + (g (Y0 ω) - V (Y0 ω)))
    (le_refl (1 : ℝ≥0∞))
  have step3 := eLpNorm_add_le (μ := P)
    (f := fun ω => g (Y n ω) - g (Y0 ω))
    (g := fun ω => g (Y0 ω) - V (Y0 ω)) (le_refl (1 : ℝ≥0∞))
  calc eLpNorm (fun ω => (X n (Y n ω) - V (Y n ω))
        + ((V (Y n ω) - g (Y n ω)) + ((g (Y n ω) - g (Y0 ω)) + (g (Y0 ω) - V (Y0 ω))))) 1 P
      ≤ eLpNorm (fun ω => X n (Y n ω) - V (Y n ω)) 1 P
        + eLpNorm (fun ω => (V (Y n ω) - g (Y n ω))
          + ((g (Y n ω) - g (Y0 ω)) + (g (Y0 ω) - V (Y0 ω)))) 1 P := step1
    _ ≤ eLpNorm (fun ω => X n (Y n ω) - V (Y n ω)) 1 P
        + (eLpNorm (fun ω => V (Y n ω) - g (Y n ω)) 1 P
          + eLpNorm (fun ω => (g (Y n ω) - g (Y0 ω)) + (g (Y0 ω) - V (Y0 ω))) 1 P) :=
        add_le_add le_rfl step2
    _ ≤ eLpNorm (fun ω => X n (Y n ω) - V (Y n ω)) 1 P
        + (eLpNorm (fun ω => V (Y n ω) - g (Y n ω)) 1 P
          + (eLpNorm (fun ω => g (Y n ω) - g (Y0 ω)) 1 P
            + eLpNorm (fun ω => g (Y0 ω) - V (Y0 ω)) 1 P)) :=
        add_le_add le_rfl (add_le_add le_rfl step3)
    _ ≤ ε4 + (ε4 + (ε4 + ε4)) := add_le_add he1_le (add_le_add he2_le (add_le_add hDn he4_le))
    _ = ε4 + ε4 + ε4 + ε4 := by ring
    _ ≤ ε := hε4sum

/-- In-measure form of `tendsto_eLpNorm_comp_of_sameLaw`. -/
theorem tendstoInMeasure_comp_of_sameLaw {Ω S : Type*} [MeasurableSpace Ω] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [TopologicalSpace.PseudoMetrizableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    {X : ℕ → S → ℝ} {V : S → ℝ} (hV : MemLp V 1 μ) (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXV : Tendsto (fun n => eLpNorm (X n - V) 1 μ) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => X n (Y n ω)) atTop (fun ω => V (Y0 ω)) := by
  have hL1 := tendsto_eLpNorm_comp_of_sameLaw hY hY0 hconv hV hX hXV
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  simpa only [Pi.sub_def] using hL1

/-- Auxiliary: if `Y n → Y0` almost surely with all `Y n`, `Y0` of the same law `μ`, then for any
a.e.-strongly-measurable `V` the composition `V ∘ Y n → V ∘ Y0` in `P`-measure, without any
integrability hypothesis on `V`. -/
theorem aux_tendstoInMeasure_comp_const {Ω S : Type*} [MeasurableSpace Ω] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [TopologicalSpace.PseudoMetrizableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    {V : S → ℝ} (hV : AEStronglyMeasurable V μ) :
    TendstoInMeasure P (fun n ω => V (Y n ω)) atTop (fun ω => V (Y0 ω)) := by
  have hMarkov : ∀ {f : S → ℝ}, AEStronglyMeasurable f μ → ∀ {c : ℝ≥0∞}, c ≠ 0 → c ≠ ⊤ →
      μ {s | c ≤ ‖f s‖ₑ} ≤ c⁻¹ * eLpNorm f 1 μ := by
    intro f hf c hc hctop
    have h := meas_ge_le_mul_pow_eLpNorm_enorm (μ := μ) (p := 1) one_ne_zero ENNReal.one_ne_top
      (f := f) hc (fun h => absurd h hctop)
    simpa using h
  intro ε2 hε2
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδtop | hδtop
  · exact Eventually.of_forall (fun n => hδtop ▸ le_top)
  rcases eq_or_ne ε2 ⊤ with hε2top | hε2top
  · have hempty : ∀ n, {ω : Ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))} = ∅ := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hε2top]
      exact not_le.mpr (edist_lt_top _ _)
    simp only [hempty, measure_empty]
    exact Eventually.of_forall (fun n => zero_le)
  set δ5 := δ / 5 with hδ5_def
  have hδ5pos : 0 < δ5 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hδ5ne : δ5 ≠ 0 := hδ5pos.ne'
  have hδ5sum : δ5 + δ5 + δ5 + δ5 + δ5 ≤ δ := by
    have h5 : (5 : ℝ≥0∞) * (δ / 5) ≤ δ := ENNReal.mul_div_le
    calc δ5 + δ5 + δ5 + δ5 + δ5 = 5 * (δ / 5) := by rw [hδ5_def]; ring
      _ ≤ δ := h5
  set ε5 := ε2 / 5 with hε5_def
  have hε5pos : 0 < ε5 := ENNReal.div_pos hε2.ne' (by norm_num)
  have hε5ne : ε5 ≠ 0 := hε5pos.ne'
  have hε5top : ε5 ≠ ⊤ := by
    rw [hε5_def]; exact (ENNReal.div_lt_top hε2top (by norm_num)).ne
  have hε5sum : ε5 + ε5 + ε5 + ε5 + ε5 ≤ ε2 := by
    have h5 : (5 : ℝ≥0∞) * (ε2 / 5) ≤ ε2 := ENNReal.mul_div_le
    calc ε5 + ε5 + ε5 + ε5 + ε5 = 5 * (ε2 / 5) := by rw [hε5_def]; ring
      _ ≤ ε2 := h5
  -- truncation of V
  set T : ℕ → S → ℝ := fun M s => max (-(M : ℝ)) (min (M : ℝ) (V s)) with hT_def
  have hTmeas : ∀ M, AEStronglyMeasurable (T M) μ := by
    intro M
    have h1 : AEStronglyMeasurable ((fun _ : S => (M : ℝ)) ⊓ V) μ :=
      aestronglyMeasurable_const.inf hV
    have h2 : AEStronglyMeasurable ((fun _ : S => -(M : ℝ)) ⊔ ((fun _ : S => (M : ℝ)) ⊓ V)) μ :=
      aestronglyMeasurable_const.sup h1
    simpa [hT_def, Pi.sup_def, Pi.inf_def] using h2
  have hTbound : ∀ M s, |T M s| ≤ (M : ℝ) := by
    intro M s
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
    have := Nat.cast_nonneg (α := ℝ) M; linarith
  have hTconv : ∀ s, Tendsto (fun M => T M s) atTop (𝓝 (V s)) := by
    intro s
    have hev : ∀ᶠ M in atTop, T M s = V s := by
      rw [eventually_atTop]
      refine ⟨⌈|V s|⌉₊, fun M hM => ?_⟩
      have hM' : |V s| ≤ (M : ℝ) := (Nat.le_ceil |V s|).trans (by exact_mod_cast hM)
      have h1 : (V s) ≤ (M : ℝ) := (le_abs_self _).trans hM'
      have h2 : -(M : ℝ) ≤ V s := by have := neg_abs_le (V s); linarith [hM']
      simp only [hT_def, min_eq_right h1, max_eq_right h2]
    exact Tendsto.congr' (hev.mono fun M h => h.symm) tendsto_const_nhds
  have hTae : TendstoInMeasure μ T atTop V :=
    tendstoInMeasure_of_tendsto_ae hTmeas (Eventually.of_forall hTconv)
  obtain ⟨M, hMspec⟩ := (ENNReal.tendsto_nhds_zero.1 (hTae ε5 hε5pos) δ5 hδ5pos).exists
  set W : S → ℝ := T M with hW_def
  have hWmeas : AEStronglyMeasurable W μ := hTmeas M
  have hWmem : MemLp W 1 μ :=
    MemLp.of_bound hWmeas (M : ℝ) (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hTbound M s)
  have hη_ne : ε5 * δ5 ≠ 0 := mul_ne_zero hε5ne hδ5ne
  obtain ⟨g, hg_close, hg_mem⟩ :=
    hWmem.exists_boundedContinuous_eLpNorm_sub_le (p := (1 : ℝ≥0∞)) ENNReal.one_ne_top hη_ne
  -- static Markov bounds on μ (independent of n)
  have hE2static : μ {s | ε5 ≤ edist (W s) (g s)} ≤ δ5 := by
    have hmark := hMarkov (hWmeas.sub hg_mem.aestronglyMeasurable) hε5ne hε5top
    have heq : {s | ε5 ≤ edist (W s) (g s)} = {s | ε5 ≤ ‖(W - (g : S → ℝ)) s‖ₑ} := by
      ext s; simp [Pi.sub_apply, edist_eq_enorm_sub]
    rw [heq]
    refine hmark.trans ?_
    calc ε5⁻¹ * eLpNorm (W - (g : S → ℝ)) 1 μ ≤ ε5⁻¹ * (ε5 * δ5) := by gcongr
      _ = (ε5⁻¹ * ε5) * δ5 := by ring
      _ = δ5 := by rw [ENNReal.inv_mul_cancel hε5ne hε5top, one_mul]
  have hE4static : μ {s | ε5 ≤ edist (g s) (W s)} ≤ δ5 := by
    have hmark := hMarkov (hg_mem.aestronglyMeasurable.sub hWmeas) hε5ne hε5top
    have heq : {s | ε5 ≤ edist (g s) (W s)} = {s | ε5 ≤ ‖((g : S → ℝ) - W) s‖ₑ} := by
      ext s; simp [Pi.sub_apply, edist_eq_enorm_sub]
    rw [heq]
    refine hmark.trans ?_
    calc ε5⁻¹ * eLpNorm ((g : S → ℝ) - W) 1 μ ≤ ε5⁻¹ * (ε5 * δ5) := by
          gcongr; rw [eLpNorm_sub_comm]; exact hg_close
      _ = (ε5⁻¹ * ε5) * δ5 := by ring
      _ = δ5 := by rw [ENNReal.inv_mul_cancel hε5ne hε5top, one_mul]
  have hE1static : μ {s | ε5 ≤ edist (V s) (W s)} ≤ δ5 := by
    have heq : {s | ε5 ≤ edist (V s) (W s)} = {s | ε5 ≤ edist (W s) (V s)} := by
      ext s; simp [edist_comm]
    rw [heq]; exact hMspec
  have hE5static : μ {s | ε5 ≤ edist (W s) (V s)} ≤ δ5 := hMspec
  -- transport the four static bounds along Yn / Y0 via measure preservation
  have hE1 : ∀ n, P {ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ≤ δ5 := by
    intro n
    have hns : NullMeasurableSet {s : S | ε5 ≤ edist (V s) (W s)} μ :=
      nullMeasurableSet_le aemeasurable_const (hV.edist hWmeas)
    have hpre := (hY n).measure_preimage hns
    have hseteq : (Y n) ⁻¹' {s | ε5 ≤ edist (V s) (W s)}
        = {ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} := rfl
    rw [hseteq] at hpre
    rw [hpre]; exact hE1static
  have hE2 : ∀ n, P {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))} ≤ δ5 := by
    intro n
    have hns : NullMeasurableSet {s : S | ε5 ≤ edist (W s) (g s)} μ :=
      nullMeasurableSet_le aemeasurable_const (hWmeas.edist hg_mem.aestronglyMeasurable)
    have hpre := (hY n).measure_preimage hns
    have hseteq : (Y n) ⁻¹' {s | ε5 ≤ edist (W s) (g s)}
        = {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))} := rfl
    rw [hseteq] at hpre
    rw [hpre]; exact hE2static
  have hE4 : P {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))} ≤ δ5 := by
    have hns : NullMeasurableSet {s : S | ε5 ≤ edist (g s) (W s)} μ :=
      nullMeasurableSet_le aemeasurable_const (hg_mem.aestronglyMeasurable.edist hWmeas)
    have hpre := hY0.measure_preimage hns
    have hseteq : Y0 ⁻¹' {s | ε5 ≤ edist (g s) (W s)}
        = {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))} := rfl
    rw [hseteq] at hpre
    rw [hpre]; exact hE4static
  have hE5 : P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} ≤ δ5 := by
    have hns : NullMeasurableSet {s : S | ε5 ≤ edist (W s) (V s)} μ :=
      nullMeasurableSet_le aemeasurable_const (hWmeas.edist hV)
    have hpre := hY0.measure_preimage hns
    have hseteq : Y0 ⁻¹' {s | ε5 ≤ edist (W s) (V s)}
        = {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := rfl
    rw [hseteq] at hpre
    rw [hpre]; exact hE5static
  -- dynamic term: g ∘ Y n → g ∘ Y0 in P-measure
  have hgP : TendstoInMeasure P (fun n ω => g (Y n ω)) atTop (fun ω => g (Y0 ω)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      have := hg_mem.aestronglyMeasurable.comp_measurePreserving (hY n)
      simpa only [Function.comp_def, Pi.sub_def] using this
    · filter_upwards [hconv] with ω hω
      exact (g.continuous.tendsto (Y0 ω)).comp hω
  have hE3 : ∀ᶠ n in atTop, P {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} ≤ δ5 :=
    (ENNReal.tendsto_nhds_zero.1 (hgP ε5 hε5pos)) δ5 hδ5pos
  filter_upwards [hE3] with n hE3n
  have hsub : {ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))}
      ⊆ {ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ∪ {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
        ∪ {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} ∪ {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))}
        ∪ {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_le] at hcon
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcon
    have htri : edist (V (Y n ω)) (V (Y0 ω)) ≤
        edist (V (Y n ω)) (W (Y n ω)) + edist (W (Y n ω)) (g (Y n ω))
          + edist (g (Y n ω)) (g (Y0 ω)) + edist (g (Y0 ω)) (W (Y0 ω))
          + edist (W (Y0 ω)) (V (Y0 ω)) := by
      calc edist (V (Y n ω)) (V (Y0 ω))
          ≤ edist (V (Y n ω)) (W (Y n ω)) + edist (W (Y n ω)) (V (Y0 ω)) := edist_triangle _ _ _
        _ ≤ edist (V (Y n ω)) (W (Y n ω))
              + (edist (W (Y n ω)) (g (Y n ω)) + edist (g (Y n ω)) (V (Y0 ω))) := by
            gcongr; exact edist_triangle _ _ _
        _ ≤ edist (V (Y n ω)) (W (Y n ω))
              + (edist (W (Y n ω)) (g (Y n ω))
                + (edist (g (Y n ω)) (g (Y0 ω)) + edist (g (Y0 ω)) (V (Y0 ω)))) := by
            gcongr; exact edist_triangle _ _ _
        _ ≤ edist (V (Y n ω)) (W (Y n ω))
              + (edist (W (Y n ω)) (g (Y n ω))
                + (edist (g (Y n ω)) (g (Y0 ω))
                  + (edist (g (Y0 ω)) (W (Y0 ω)) + edist (W (Y0 ω)) (V (Y0 ω))))) := by
            gcongr; exact edist_triangle _ _ _
        _ = edist (V (Y n ω)) (W (Y n ω)) + edist (W (Y n ω)) (g (Y n ω))
              + edist (g (Y n ω)) (g (Y0 ω)) + edist (g (Y0 ω)) (W (Y0 ω))
              + edist (W (Y0 ω)) (V (Y0 ω)) := by ring
    have hlt : edist (V (Y n ω)) (V (Y0 ω)) < ε5 + ε5 + ε5 + ε5 + ε5 := by
      calc edist (V (Y n ω)) (V (Y0 ω))
          ≤ edist (V (Y n ω)) (W (Y n ω)) + edist (W (Y n ω)) (g (Y n ω))
              + edist (g (Y n ω)) (g (Y0 ω)) + edist (g (Y0 ω)) (W (Y0 ω))
              + edist (W (Y0 ω)) (V (Y0 ω)) := htri
        _ < ε5 + ε5 + ε5 + ε5 + ε5 := by gcongr
    have hle : ε2 ≤ edist (V (Y n ω)) (V (Y0 ω)) := hω
    have : ε2 < ε2 := hle.trans_lt (hlt.trans_le hε5sum)
    exact absurd this (lt_irrefl _)
  calc P {ω | ε2 ≤ edist (V (Y n ω)) (V (Y0 ω))}
      ≤ P ({ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ∪ {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
            ∪ {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} ∪ {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))}
            ∪ {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))}) := measure_mono hsub
    _ ≤ P {ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} + P {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
          + P {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} + P {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))}
          + P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := by
        calc P ({ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ∪ {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
                ∪ {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} ∪ {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))}
                ∪ {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))})
            ≤ P ({ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ∪ {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
                ∪ {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} ∪ {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))})
                + P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := measure_union_le _ _
          _ ≤ (P ({ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ∪ {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
                ∪ {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))})
                + P {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))})
                + P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := by
              gcongr; exact measure_union_le _ _
          _ ≤ ((P ({ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} ∪ {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))})
                + P {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))})
                + P {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))})
                + P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := by
              gcongr; exact measure_union_le _ _
          _ ≤ (((P {ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} + P {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))})
                + P {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))})
                + P {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))})
                + P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := by
              gcongr; exact measure_union_le _ _
          _ = P {ω | ε5 ≤ edist (V (Y n ω)) (W (Y n ω))} + P {ω | ε5 ≤ edist (W (Y n ω)) (g (Y n ω))}
                + P {ω | ε5 ≤ edist (g (Y n ω)) (g (Y0 ω))} + P {ω | ε5 ≤ edist (g (Y0 ω)) (W (Y0 ω))}
                + P {ω | ε5 ≤ edist (W (Y0 ω)) (V (Y0 ω))} := by ring
    _ ≤ δ5 + δ5 + δ5 + δ5 + δ5 :=
        add_le_add (add_le_add (add_le_add (add_le_add (hE1 n) (hE2 n)) hE3n) hE4) hE5
    _ ≤ δ := hδ5sum

/-- In-measure same-law composition: if `X n → V` in `μ`-measure (`V` a.e.-strongly measurable),
`Y n → Y0` almost surely and all have law `μ`, then `X n ∘ Y n → V ∘ Y0` in `P`-measure. -/
theorem tendstoInMeasure_comp_of_sameLaw_of_tendstoInMeasure {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → S} {Y0 : Ω → S} (hY : ∀ n, MeasurePreserving (Y n) P μ)
    (hY0 : MeasurePreserving Y0 P μ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω)))
    {X : ℕ → S → ℝ} {V : S → ℝ} (hV : AEStronglyMeasurable V μ)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) (hXV : TendstoInMeasure μ X atTop V) :
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
  have hterm1eq : ∀ n, P {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))}
      = μ {s | ε2 ≤ edist (X n s) (V s)} := by
    intro n
    have hns : NullMeasurableSet {s : S | ε2 ≤ edist (X n s) (V s)} μ :=
      nullMeasurableSet_le aemeasurable_const ((hX n).edist hV)
    have hpre := (hY n).measure_preimage hns
    have hseteq : (Y n) ⁻¹' {s | ε2 ≤ edist (X n s) (V s)}
        = {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))} := rfl
    rw [hseteq] at hpre
    exact hpre
  have hE1 : ∀ᶠ n in atTop, P {ω | ε2 ≤ edist (X n (Y n ω)) (V (Y n ω))} ≤ δ2 := by
    have h := ENNReal.tendsto_nhds_zero.1 (hXV ε2 hε2pos) δ2 hδ2pos
    filter_upwards [h] with n hn
    rw [hterm1eq n]; exact hn
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

end SubdiffusiveProcess
