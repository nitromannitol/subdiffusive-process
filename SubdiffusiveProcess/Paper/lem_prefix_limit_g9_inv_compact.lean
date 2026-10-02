import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open Metric

noncomputable section
namespace Paper

/-- A sequence of indices into an `L¹`-relatively compact family has a further subsequence along
which the family converges almost everywhere. -/
theorem aux_lem_prefix_limit_g9_inv_compact_ae_subseq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : ℕ → Ω → ℝ) (hVmem : ∀ n, MemLp (V n) 1 μ)
    (hcompact : IsCompact (closure (Set.range (fun n => (hVmem n).toLp (V n)))))
    (M : ℕ → ℕ) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ L : Ω → ℝ, AEStronglyMeasurable L μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun j => V (M (ρ j)) ω) atTop (𝓝 (L ω)) := by
  have hmemclosure : ∀ j, (hVmem (M j)).toLp (V (M j)) ∈
      closure (Set.range (fun n => (hVmem n).toLp (V n))) :=
    fun j => subset_closure ⟨M j, rfl⟩
  obtain ⟨a, -, ρ, hρmono, hρtendsto⟩ := hcompact.tendsto_subseq hmemclosure
  have htendstoInMeasure :
      TendstoInMeasure μ (fun j => ((hVmem (M (ρ j))).toLp (V (M (ρ j))) : Ω → ℝ)) atTop
        (a : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hρtendsto
  obtain ⟨σ, hσmono, hσae⟩ := htendstoInMeasure.exists_seq_tendsto_ae
  refine ⟨ρ ∘ σ, hρmono.comp hσmono, (a : Ω → ℝ), Lp.aestronglyMeasurable a, ?_⟩
  have hcong : ∀ j, ((hVmem (M (ρ (σ j)))).toLp (V (M (ρ (σ j)))) : Ω → ℝ) =ᵐ[μ]
      V (M (ρ (σ j))) := fun j => (hVmem (M (ρ (σ j)))).coeFn_toLp
  have hcongall : ∀ᵐ ω ∂μ, ∀ j,
      ((hVmem (M (ρ (σ j)))).toLp (V (M (ρ (σ j)))) : Ω → ℝ) ω = V (M (ρ (σ j))) ω :=
    ae_all_iff.mpr hcong
  filter_upwards [hσae, hcongall] with ω hω hcongω
  exact hω.congr (fun j => hcongω j)

/-- Uniform integrability at exponent `1` from a uniform bound at an exponent `q > 1` on a
probability space. -/
theorem aux_lem_prefix_limit_g9_inv_compact_unifIntegrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (q : ℝ) (hq : 1 < q) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ B) :
    UnifIntegrable f 1 μ := by
  set g : ℕ → Ω → ℝ := fun n => (hf n).choose with hgdef
  have hgmeas : ∀ n, StronglyMeasurable (g n) := fun n => (hf n).choose_spec.1
  have hgeq : ∀ n, f n =ᵐ[μ] g n := fun n => (hf n).choose_spec.2
  have hq0 : 0 < q := by linarith
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  set b : ℝ := B.toReal with hbdef
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hb1pos : (0:ℝ) < b + 1 := by linarith
  have hBb1 : B ≤ ENNReal.ofReal (b + 1) := by
    have hBeq : B = ENNReal.ofReal b := (ENNReal.ofReal_toReal hB).symm
    rw [hBeq]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hgbound : ∀ n, eLpNorm (g n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (b + 1) :=
    fun n => (le_of_eq (eLpNorm_congr_ae (hgeq n)).symm).trans ((hbound n).trans hBb1)
  set e : ℝ := 1 - 1 / q with hedef
  have he0 : 0 < e := by rw [hedef, sub_pos]; exact (div_lt_one hq0).mpr hq
  have hUnifg : UnifIntegrable g 1 μ := by
    apply unifIntegrable_of' (le_refl 1) (by simp) hgmeas
    intro ε hε
    set C0 : ℝ := ((b + 1) ^ q / ε) ^ (1 / (q - 1)) with hC0def
    have hC0pos : 0 < C0 :=
      Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hb1pos q) hε) _
    set C0nn : ℝ≥0 := ⟨C0, hC0pos.le⟩ with hC0nndef
    have hC0nnpos : 0 < C0nn := hC0pos
    refine ⟨C0nn, hC0nnpos, fun n => ?_⟩
    set S : Set Ω := {x | C0nn ≤ ‖g n x‖₊} with hSdef
    have hSm : MeasurableSet S :=
      measurableSet_le measurable_const (hgmeas n).nnnorm.measurable
    have hSeq : S = {x | (C0nn : ℝ≥0∞) ≤ ‖g n x‖ₑ} := by
      ext x; exact ENNReal.coe_le_coe.symm
    have hstep1 : eLpNorm (S.indicator (g n)) 1 μ
        ≤ eLpNorm (g n) (ENNReal.ofReal q) μ * (μ S) ^ e := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hSm]
      have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict S) hqE
        (hgmeas n).aestronglyMeasurable
      have hexp : (1:ℝ) / 1 - 1 / q = e := by rw [hedef]; norm_num
      simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal hq0.le, Measure.restrict_apply_univ,
        hexp] at hH
      calc eLpNorm (g n) 1 (μ.restrict S)
          ≤ eLpNorm (g n) (ENNReal.ofReal q) (μ.restrict S) * (μ S) ^ e := hH
        _ ≤ eLpNorm (g n) (ENNReal.ofReal q) μ * (μ S) ^ e := by
            gcongr
            exact Measure.restrict_le_self
    have hstep2 : μ S ≤ ENNReal.ofReal (b + 1) ^ q / (C0nn : ℝ≥0∞) ^ q := by
      rw [hSeq]
      have hq0' : ENNReal.ofReal q ≠ 0 := by simpa using hq0
      have hmk := mul_meas_ge_le_pow_eLpNorm' μ hq0' ENNReal.ofReal_ne_top
        (hgmeas n).aestronglyMeasurable (C0nn : ℝ≥0∞)
      rw [ENNReal.toReal_ofReal hq0.le] at hmk
      have hCq_pos : (0:ℝ≥0∞) < (C0nn : ℝ≥0∞) ^ q :=
        ENNReal.rpow_pos (ENNReal.coe_pos.mpr hC0nnpos) ENNReal.coe_ne_top
      rw [ENNReal.le_div_iff_mul_le (Or.inl hCq_pos.ne') (Or.inl
        (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.coe_ne_top)), mul_comm]
      exact hmk.trans (ENNReal.rpow_le_rpow (hgbound n) hq0.le)
    have hCqreal : C0 ^ (q - 1) = (b + 1) ^ q / ε := by
      rw [hC0def, ← Real.rpow_mul (by positivity), one_div,
        inv_mul_cancel₀ (show (q - 1) ≠ 0 by linarith), Real.rpow_one]
    have hfinal : ENNReal.ofReal (b + 1) *
        (ENNReal.ofReal (b + 1) ^ q / (C0nn : ℝ≥0∞) ^ q) ^ e =
        ENNReal.ofReal ε := by
      have hC0E : (C0nn : ℝ≥0∞) = ENNReal.ofReal C0 :=
        (ENNReal.ofReal_eq_coe_nnreal hC0pos.le).symm
      rw [hC0E, ENNReal.ofReal_rpow_of_pos hb1pos, ENNReal.ofReal_rpow_of_pos hC0pos,
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hC0pos q),
        ENNReal.ofReal_rpow_of_pos (div_pos (Real.rpow_pos_of_pos hb1pos q)
          (Real.rpow_pos_of_pos hC0pos q)), ← ENNReal.ofReal_mul hb1pos.le]
      congr 1
      have hqe : q * e = q - 1 := by rw [hedef]; field_simp
      rw [Real.div_rpow (Real.rpow_nonneg hb1pos.le q) (Real.rpow_nonneg hC0pos.le q),
        ← Real.rpow_mul hb1pos.le, ← Real.rpow_mul hC0pos.le, hqe, hCqreal,
        Real.rpow_sub hb1pos q 1, Real.rpow_one]
      field_simp
    calc eLpNorm (S.indicator (g n)) 1 μ
        ≤ eLpNorm (g n) (ENNReal.ofReal q) μ * (μ S) ^ e := hstep1
      _ ≤ ENNReal.ofReal (b + 1) *
          (ENNReal.ofReal (b + 1) ^ q / (C0nn : ℝ≥0∞) ^ q) ^ e :=
          mul_le_mul' (hgbound n) (ENNReal.rpow_le_rpow hstep2 he0.le)
      _ = ENNReal.ofReal ε := hfinal
  exact hUnifg.ae_eq (fun n => (hgeq n).symm)

/-- The almost-everywhere limit of a positive sequence whose inverses have uniformly bounded
integrals is almost everywhere positive (Fatou: at a zero of the limit the inverses blow up). -/
theorem aux_lem_prefix_limit_g9_inv_compact_limit_pos
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (L : Ω → ℝ)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hpos : ∀ j, ∀ᵐ ω ∂μ, 0 < Y j ω)
    (hmeas : ∀ j, AEMeasurable (fun ω => ‖(Y j ω)⁻¹‖ₑ) μ)
    (hbound : ∀ j, ∫⁻ ω, ‖(Y j ω)⁻¹‖ₑ ∂μ ≤ B)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun j => Y j ω) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂μ, 0 < L ω := by
  set f : ℕ → Ω → ℝ≥0∞ := fun j ω => ‖(Y j ω)⁻¹‖ₑ with hf
  set g : ℕ → Ω → ℝ≥0∞ := fun j => (hmeas j).mk (f j) with hg
  have hgm : ∀ j, Measurable (g j) := fun j => (hmeas j).measurable_mk
  have hfg : ∀ᵐ ω ∂μ, ∀ j, f j ω = g j ω := ae_all_iff.2 (fun j => (hmeas j).ae_eq_mk)
  have hint : ∫⁻ ω, liminf (fun j => g j ω) atTop ∂μ ≤ B := by
    calc ∫⁻ ω, liminf (fun j => g j ω) atTop ∂μ
        ≤ liminf (fun j => ∫⁻ ω, g j ω ∂μ) atTop := lintegral_liminf_le hgm
      _ ≤ B := by
          apply liminf_le_of_frequently_le'
          refine Frequently.of_forall (fun j => ?_)
          rw [← lintegral_congr_ae (hmeas j).ae_eq_mk]
          exact hbound j
  have hfin : ∀ᵐ ω ∂μ, liminf (fun j => g j ω) atTop < ⊤ :=
    ae_lt_top (Measurable.liminf hgm) (ne_top_of_le_ne_top hB hint)
  have hposall : ∀ᵐ ω ∂μ, ∀ j, 0 < Y j ω := ae_all_iff.2 hpos
  filter_upwards [hfin, hfg, hposall, hconv] with ω hω hfgω hpω hcω
  have hL0 : 0 ≤ L ω := ge_of_tendsto hcω (Eventually.of_forall (fun j => (hpω j).le))
  rcases hL0.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hcω
    have h1 : Tendsto (fun j => Y j ω) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hcω, Eventually.of_forall hpω⟩
    have h2 : Tendsto (fun j => f j ω) atTop (𝓝 ⊤) := by
      have habs : Tendsto (fun j => |(Y j ω)⁻¹|) atTop atTop :=
        tendsto_abs_atTop_atTop.comp (tendsto_inv_nhdsGT_zero.comp h1)
      have := ENNReal.tendsto_ofReal_atTop.comp habs
      simpa [hf, Real.enorm_eq_ofReal_abs, Function.comp_def] using this
    have h3 : Tendsto (fun j => g j ω) atTop (𝓝 ⊤) := Tendsto.congr hfgω h2
    rw [h3.liminf_eq] at hω
    exact lt_irrefl _ hω



theorem lem_prefix_limit_g9_inv_compact
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (q B : ℝ) (hq : 1 < q)
    (hpos : ∀ N, ∀ᵐ ω ∂μ, 0 < X N ω)
    (hcomp : ∃ hm : ∀ N, MemLp (X N) 1 μ,
      IsCompact (closure (Set.range fun N => (hm N).toLp (X N))))
    (hinv : ∀ N, MemLp (fun ω => (X N ω)⁻¹) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun ω => (X N ω)⁻¹) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    ∃ hm : ∀ N, MemLp (fun ω => (X N ω)⁻¹) 1 μ,
      IsCompact (closure (Set.range fun N => (hm N).toLp (fun ω => (X N ω)⁻¹))) := by
  obtain ⟨hXmem, hXcomp⟩ := hcomp
  have h1q : (1:ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  set Bq : ℝ≥0∞ := ENNReal.ofReal B with hBqdef
  have hBq : Bq ≠ ⊤ := ENNReal.ofReal_ne_top
  have hImeas : ∀ N, AEStronglyMeasurable (fun ω => (X N ω)⁻¹) μ :=
    fun N => (hinv N).1.aestronglyMeasurable
  have hIbound1 : ∀ N, eLpNorm (fun ω => (X N ω)⁻¹) 1 μ ≤ Bq := fun N =>
    (eLpNorm_le_eLpNorm_of_exponent_le h1q (hImeas N)).trans (hinv N).2
  have hImem : ∀ N, MemLp (fun ω => (X N ω)⁻¹) 1 μ :=
    fun N => ⟨hImeas N, lt_of_le_of_lt (hIbound1 N) hBq.lt_top⟩
  refine ⟨hImem, ?_⟩
  set F : ℕ → Lp ℝ 1 μ := fun N => (hImem N).toLp (fun ω => (X N ω)⁻¹) with hFdef
  apply IsSeqCompact.isCompact
  intro z hz
  have hdense : ∀ j : ℕ, ∃ Nj : ℕ, dist (z j) (F Nj) < 1 / ((j:ℝ) + 1) := by
    intro j
    have hpos' : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
    obtain ⟨y, hyS, hy⟩ := Metric.mem_closure_iff.mp (hz j) (1 / ((j:ℝ) + 1)) hpos'
    obtain ⟨Nj, rfl⟩ := hyS
    exact ⟨Nj, hy⟩
  choose Nseq hNseq using hdense
  obtain ⟨ρ, hρmono, L, hLmeas, hLconv⟩ :=
    aux_lem_prefix_limit_g9_inv_compact_ae_subseq μ X hXmem hXcomp Nseq
  set M' : ℕ → ℕ := fun j => Nseq (ρ j) with hM'def
  have hLpos : ∀ᵐ ω ∂μ, 0 < L ω :=
    aux_lem_prefix_limit_g9_inv_compact_limit_pos μ (fun j => X (M' j)) L Bq hBq
      (fun j => hpos (M' j)) (fun j => (hImeas (M' j)).enorm)
      (fun j => by
        rw [← eLpNorm_one_eq_lintegral_enorm]
        exact hIbound1 (M' j)) hLconv
  set Ψ : Ω → ℝ := fun ω => (L ω)⁻¹ with hΨdef
  have hΨconv : ∀ᵐ ω ∂μ, Tendsto (fun j => (X (M' j) ω)⁻¹) atTop (𝓝 (Ψ ω)) := by
    filter_upwards [hLconv, hLpos] with ω hω hp
    exact hω.inv₀ hp.ne'
  have hΨmeas : AEStronglyMeasurable Ψ μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => hImeas (M' j)) hΨconv
  have hΨbound : eLpNorm Ψ 1 μ ≤ Bq :=
    Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
      (Filter.Eventually.of_forall (fun j => hIbound1 (M' j)))
      (fun j => hImeas (M' j)) hΨconv
  have hΨmem : MemLp Ψ 1 μ := ⟨hΨmeas, lt_of_le_of_lt hΨbound hBq.lt_top⟩
  have htim : TendstoInMeasure μ (fun j ω => (X (M' j) ω)⁻¹) atTop Ψ :=
    tendstoInMeasure_of_tendsto_ae (fun j => hImeas (M' j)) hΨconv
  have hunif : UnifIntegrable (fun j ω => (X (M' j) ω)⁻¹) 1 μ :=
    aux_lem_prefix_limit_g9_inv_compact_unifIntegrable μ (fun j ω => (X (M' j) ω)⁻¹)
      (fun j => hImeas (M' j)) q hq Bq hBq (fun j => (hinv (M' j)).2)
  have hL1conv : Tendsto (fun j => eLpNorm
      ((fun ω => (X (M' j) ω)⁻¹) - Ψ) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure (le_refl 1) (by simp) (fun j => hImeas (M' j))
      hΨmem hunif htim
  have hFtendsto : Tendsto (fun j => F (M' j)) atTop (𝓝 (hΨmem.toLp Ψ)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j => fun ω => (X (M' j) ω)⁻¹)
      (fun j => hImem (M' j)) Ψ hΨmem).mpr hL1conv
  have hz'tendsto : Tendsto (fun j => dist (z (ρ j)) (F (M' j))) atTop (𝓝 0) := by
    have hb : ∀ j, dist (z (ρ j)) (F (M' j)) < 1 / ((ρ j : ℝ) + 1) := fun j => hNseq (ρ j)
    have h0 : Tendsto (fun j => 1 / ((ρ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hρmono.tendsto_atTop
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (hb j).le) h0
  have hzconv : Tendsto (fun j => z (ρ j)) atTop (𝓝 (hΨmem.toLp Ψ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 : Tendsto (fun j => dist (F (M' j)) (hΨmem.toLp Ψ)) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hFtendsto
    have h3 : Tendsto (fun j => dist (z (ρ j)) (F (M' j)) + dist (F (M' j)) (hΨmem.toLp Ψ))
        atTop (𝓝 0) := by simpa using hz'tendsto.add h2
    exact squeeze_zero (fun j => dist_nonneg) (fun j => dist_triangle _ _ _) h3
  refine ⟨hΨmem.toLp Ψ,
    mem_closure_iff_seq_limit.mpr ⟨fun j => F (M' j), fun j => ⟨M' j, rfl⟩, hFtendsto⟩,
    ρ, hρmono, hzconv⟩

end Paper
