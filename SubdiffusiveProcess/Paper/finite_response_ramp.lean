module

public import SubdiffusiveProcess.Lane3.BandFiltration
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper

theorem aux_finite_response_ramp_unifIntegrable_of_eLpNorm_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*}
    {f : ι → Ω → ℝ} {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p < q) (hq : q ≠ ∞) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : ∀ i, eLpNorm (f i) q μ ≤ K) : UnifIntegrable f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpt : p ≠ ∞ := (hpq.trans_le le_top).ne
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpqr : p.toReal < q.toReal := (ENNReal.toReal_lt_toReal hpt hq).mpr hpq
  have hr : 0 < 1 / p.toReal - 1 / q.toReal :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hpr hpqr)
  have hlim : Tendsto (fun d : ℝ => K * (ENNReal.ofReal d) ^
      (1 / p.toReal - 1 / q.toReal)) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, Function.comp_apply, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos hr, mul_zero] using
      (((ENNReal.continuous_const_mul hK).comp
        ((ENNReal.continuous_rpow_const
          (y := 1 / p.toReal - 1 / q.toReal)).comp ENNReal.continuous_ofReal)).tendsto 0)
  refine unifIntegrable_iff'.mpr ?_
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst ε
    exact ⟨1, zero_lt_one, fun _ _ _ _ => le_top⟩
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp
    (hlim.eventually_lt_const (ENNReal.ofReal_pos.mpr hεr))
  refine ⟨ENNReal.ofReal (δ / 2), ENNReal.ofReal_pos.mpr (by linarith),
    fun i s hs hμs => ?_⟩
  calc
    eLpNorm (f i) p (μ.restrict s) ≤ eLpNorm (f i) q (μ.restrict s) *
        (μ.restrict s) univ ^ (1 / p.toReal - 1 / q.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le (hf i).restrict
    _ ≤ K * (ENNReal.ofReal (δ / 2)) ^
        (1 / p.toReal - 1 / q.toReal) := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hb i))
        (ENNReal.rpow_le_rpow hμs hr.le)
    _ ≤ ENNReal.ofReal ε.toReal := (hδbound (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (show 0 < δ / 2 by linarith)]
      linarith)).le
    _ = ε := ENNReal.ofReal_toReal hεtop

theorem aux_finite_response_ramp_tendsto_eLpNorm
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p < q) (hq : q ≠ ∞) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ n, eLpNorm (f n) q μ ≤ K)
    (hconv : TendstoInMeasure μ f atTop g) :
    MemLp g q μ ∧ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have hgb : eLpNorm g q μ ≤ K :=
    eLpNorm_le_of_tendstoInMeasure (p := q) (Filter.Eventually.of_forall hb) hconv hf
  have hgq : MemLp g q μ := by
    simpa only [MemLp, eLpNorm, ite_eq_left hg] using
      (hgb.trans_lt (lt_top_iff_ne_top.mpr hK))
  refine ⟨hgq, tendsto_Lp_finite_of_tendstoInMeasure hp (hpq.trans_le le_top).ne hf
    (hgq.mono_exponent hpq.le)
    (aux_finite_response_ramp_unifIntegrable_of_eLpNorm_bound hp hpq hq hK hf hb) hconv⟩

theorem aux_finite_response_ramp_band_condExp_le
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (H : ℕ) {f : ((j : ℤ) → Y j) → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) (hf : Integrable f (Measure.infinitePi laws)) :
    eLpNorm ((Measure.infinitePi laws)[f | bandSigma Y H]) p
        (Measure.infinitePi laws) ≤ eLpNorm f p (Measure.infinitePi laws) := by
  classical
  let e : ((j : ℤ) → Y j) ≃ᵐ
      ((j : bandSet H) → Y j) × ((j : {j : ℤ // j ∉ bandSet H}) → Y j) :=
    MeasurableEquiv.piEquivPiSubtypeProd Y (fun j => j ∈ bandSet H)
  let μ : Measure (((j : ℤ) → Y j)) := Measure.infinitePi laws
  let ν : Measure (((j : bandSet H) → Y j) ×
      ((j : {j : ℤ // j ∉ bandSet H}) → Y j)) :=
    (Measure.infinitePi (fun j : bandSet H => laws j.1)).prod
      (Measure.infinitePi (fun j : {j : ℤ // j ∉ bandSet H} => laws j.1))
  have he : MeasurePreserving e μ ν := by
    exact SubdiffusiveProcess.measurePreserving_infinitePi_split laws (fun j => j ∈ bandSet H)
  have hband_eq : bandSigma Y H =
      (inferInstance : MeasurableSpace ((j : bandSet H) → Y j)).comap
        (fun ω => (e ω).1) := by
    rw [bandSigma_eq_comap]
    congr 1
  have hce : μ[f | bandSigma Y H] =ᵐ[μ]
      (ν[f ∘ e.symm | (inferInstance : MeasurableSpace ((j : bandSet H) → Y j)).comap Prod.fst]) ∘ e := by
    rw [hband_eq]
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
      (SubdiffusiveProcess.condExp_comp_measurableEquiv e he measurable_fst.comap_le
        (f := f ∘ e.symm) ((he.symm e).integrable_comp_of_integrable hf))
  rw [eLpNorm_congr_ae hce]
  calc
    eLpNorm ((ν[f ∘ e.symm |
        (inferInstance : MeasurableSpace ((j : bandSet H) → Y j)).comap Prod.fst]) ∘ e) p μ =
        eLpNorm (ν[f ∘ e.symm |
          (inferInstance : MeasurableSpace ((j : bandSet H) → Y j)).comap Prod.fst]) p ν := by
      exact eLpNorm_comp_measurePreserving
        (stronglyMeasurable_condExp.mono measurable_fst.comap_le).aestronglyMeasurable he
    _ ≤ eLpNorm (f ∘ e.symm) p ν :=
      SubdiffusiveProcess.condExp_prod_fst_eLpNorm_le hp hpt
        ((he.symm e).integrable_comp_of_integrable hf)
    _ = eLpNorm f p μ := by
      exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (he.symm e)

theorem aux_finite_response_ramp_sum_eLpNorm_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type*} [Fintype I] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : I → Ω → ℝ} (hf : ∀ i, AEStronglyMeasurable[mΩ] (f i) μ) :
    eLpNorm (fun ω => ∑ i : I, f i ω) p μ ≤
      ∑ i : I, eLpNorm (f i) p μ := by
  calc
    eLpNorm (fun ω => ∑ i : I, f i ω) p μ =
        eLpNorm (∑ i : I, f i) p μ := by
      congr 1
      funext ω
      simp
    _ ≤ ∑ i : I, eLpNorm (f i) p μ := by
      simpa using (eLpNorm_sum_le (s := (Finset.univ : Finset I)) hp)

theorem aux_finite_response_ramp_ramp_band_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type*} [Fintype I] [Nonempty I] [Inhabited I]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {p B : ℝ≥0∞} (eta : ℝ) (hp : 1 ≤ p) (heta : 0 < eta)
    {u v : I → Ω → ℝ}
    (hu : ∀ i, AEStronglyMeasurable[mΩ] (u i) μ)
    (hv : ∀ i, StronglyMeasurable[m] (v i))
    (huint : ∀ i, Integrable (u i) μ)
    (hvint : ∀ i, Integrable (v i) μ)
    (hcontr : ∀ z : Ω → ℝ, Integrable z μ →
      eLpNorm (μ[z | m]) p μ ≤ eLpNorm z p μ)
    (hbound : ∀ i, eLpNorm (u i - v i) p μ ≤ B) :
  (let U : Ω → ℝ := fun ω =>
      min 1 ((Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => |u i ω - u default ω|)) / eta)
     let V : Ω → ℝ := fun ω =>
      min 1 ((Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => |v i ω - v default ω|)) / eta)
     eLpNorm (fun ω => U ω - (μ[U | m]) ω) p μ ≤
       4 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta) := by
  classical
  dsimp only
  let S : (I → Ω → ℝ) → Ω → ℝ := fun w ω =>
    Finset.univ.sup' Finset.univ_nonempty (fun i : I => |w i ω - w default ω|)
  let U : Ω → ℝ := fun ω => min 1 (S u ω / eta)
  let V : Ω → ℝ := fun ω => min 1 (S v ω / eta)
  have hu_term : ∀ i, AEStronglyMeasurable[mΩ] (fun ω => |u i ω - u default ω|) μ := by
    intro i
    exact continuous_abs.comp_aestronglyMeasurable ((hu i).sub (hu default))
  have hv_term : ∀ i, StronglyMeasurable[m] (fun ω => |v i ω - v default ω|) := by
    intro i
    exact continuous_abs.comp_stronglyMeasurable ((hv i).sub (hv default))
  have huS : AEStronglyMeasurable[mΩ] (S u) μ := by
    have h : AEStronglyMeasurable[mΩ]
        (Finset.univ.sup' Finset.univ_nonempty
          (fun i : I => fun ω => |u i ω - u default ω|)) μ := by
      refine Finset.sup'_induction (p := fun z : Ω → ℝ => AEStronglyMeasurable[mΩ] z μ)
        (s := (Finset.univ : Finset I))
        Finset.univ_nonempty (fun i : I => fun ω => |u i ω - u default ω|) ?_ ?_
      · intro a ha b hb
        exact continuous_max.comp_aestronglyMeasurable (ha.prodMk hb)
      · intro i hi
        exact hu_term i
    have hfun : (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => |u i ω - u default ω|)) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun i : I => fun ω => |u i ω - u default ω|) := by
      funext ω
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i : I => fun ω => |u i ω - u default ω|) ω).symm
    rw [show S u = (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => |u i ω - u default ω|)) by rfl, hfun]
    exact h
  have hvS : StronglyMeasurable[m] (S v) := by
    have h : StronglyMeasurable[m]
        (Finset.univ.sup' Finset.univ_nonempty
          (fun i : I => fun ω => |v i ω - v default ω|)) := by
      refine Finset.sup'_induction (p := fun z : Ω → ℝ => StronglyMeasurable[m] z)
        (s := (Finset.univ : Finset I))
        Finset.univ_nonempty (fun i : I => fun ω => |v i ω - v default ω|) ?_ ?_
      · intro a ha b hb
        exact continuous_max.comp_stronglyMeasurable (ha.prodMk hb)
      · intro i hi
        exact hv_term i
    have hfun : (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => |v i ω - v default ω|)) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun i : I => fun ω => |v i ω - v default ω|) := by
      funext ω
      exact (Finset.sup'_apply Finset.univ_nonempty
        (fun i : I => fun ω => |v i ω - v default ω|) ω).symm
    rw [show S v = (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => |v i ω - v default ω|)) by rfl, hfun]
    exact h
  have huU : AEStronglyMeasurable[mΩ] U μ := by
    have hdiv : AEStronglyMeasurable[mΩ] (fun ω => S u ω / eta) μ :=
      (continuous_id.div_const eta).comp_aestronglyMeasurable huS
    simpa only [U] using
      (continuous_min.comp_aestronglyMeasurable
        (aestronglyMeasurable_const.prodMk hdiv))
  have hvV : StronglyMeasurable[m] V := by
    have hdiv : StronglyMeasurable[m] (fun ω => S v ω / eta) :=
      (continuous_id.div_const eta).comp_stronglyMeasurable hvS
    simpa only [V] using
      (continuous_min.comp_stronglyMeasurable
        (stronglyMeasurable_const.prodMk hdiv))
  have huU_bdd : ∀ᵐ ω ∂μ, ‖U ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    have hnonneg : 0 ≤ S u ω / eta := by
      apply div_nonneg
      · have hIci : ∀ a : ℝ, a ∈ Set.Ici (0 : ℝ) → ∀ b : ℝ,
            b ∈ Set.Ici (0 : ℝ) →
            max a b ∈ Set.Ici (0 : ℝ) := by
          intro a ha b hb
          change 0 ≤ max a b
          exact le_max_of_le_left (show (0 : ℝ) ≤ a from ha)
        exact Finset.sup'_mem (Set.Ici (0 : ℝ)) hIci
          _ Finset.univ_nonempty (fun i : I => |u i ω - u default ω|)
          (fun i hi => show 0 ≤ |u i ω - u default ω| from abs_nonneg _)
      · exact le_of_lt heta
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) hnonneg)]
    exact min_le_left _ _
  have hvV_bdd : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    have hnonneg : 0 ≤ S v ω / eta := by
      apply div_nonneg
      · have hIci : ∀ a : ℝ, a ∈ Set.Ici (0 : ℝ) → ∀ b : ℝ,
            b ∈ Set.Ici (0 : ℝ) →
            max a b ∈ Set.Ici (0 : ℝ) := by
          intro a ha b hb
          change 0 ≤ max a b
          exact le_max_of_le_left (show (0 : ℝ) ≤ a from ha)
        exact Finset.sup'_mem (Set.Ici (0 : ℝ)) hIci
          _ Finset.univ_nonempty (fun i : I => |v i ω - v default ω|)
          (fun i hi => show 0 ≤ |v i ω - v default ω| from abs_nonneg _)
      · exact le_of_lt heta
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) hnonneg)]
    exact min_le_left _ _
  have huU' : AEStronglyMeasurable[mΩ] U μ := huU
  have hvV' : StronglyMeasurable[mΩ] V :=
    StronglyMeasurable.mono hvV hm
  have hUint : Integrable U μ := Integrable.of_bound huU' 1 huU_bdd
  have hVint : Integrable V μ :=
    Integrable.of_bound hvV'.aestronglyMeasurable 1 hvV_bdd
  let d : I → Ω → ℝ := fun i ω =>
    (u i ω - v i ω) - (u default ω - v default ω)
  have hdiff_absmeas : ∀ i, AEStronglyMeasurable[mΩ] (fun ω =>
      |d i ω|) μ := by
    intro i
    simpa only [d, Pi.sub_apply] using
      (continuous_abs.comp_aestronglyMeasurable
        (((huint i).aestronglyMeasurable.sub (hvint i).aestronglyMeasurable).sub
          ((huint default).aestronglyMeasurable.sub (hvint default).aestronglyMeasurable)))
  have hdiff_norm_eq : ∀ i, eLpNorm (fun ω =>
      |d i ω|) p μ =
      eLpNorm ((u i - v i) - (u default - v default)) p μ := by
    intro i
    simpa only [d, Pi.sub_apply, Real.norm_eq_abs] using
      (eLpNorm_norm ((u i - v i) - (u default - v default))
        (((huint i).aestronglyMeasurable.sub (hvint i).aestronglyMeasurable).sub
          ((huint default).aestronglyMeasurable.sub (hvint default).aestronglyMeasurable)))
  have hdiff_bound :
      eLpNorm (U - V) p μ ≤
        2 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta := by
    have hpoint : ∀ ω, ‖(U - V) ω‖ ≤
        (1 / eta) * ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)| := by
      intro ω
      have hsuv : |S u ω - S v ω| ≤
          ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)| := by
        have hleft : S u ω ≤ S v ω +
            ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)| := by
          apply Finset.sup'_le Finset.univ_nonempty
          intro i hi
          have hiabs : |u i ω - u default ω| ≤
              |v i ω - v default ω| +
                |(u i ω - v i ω) - (u default ω - v default ω)| := by
            have hdiff : (u i ω - v i ω) - (u default ω - v default ω) =
                (u i ω - u default ω) - (v i ω - v default ω) := by ring
            calc
              |u i ω - u default ω| ≤
                  |v i ω - v default ω| +
                    |(u i ω - u default ω) - (v i ω - v default ω)| := by
                linarith [abs_sub_abs_le_abs_sub
                  (u i ω - u default ω) (v i ω - v default ω)]
              _ = |v i ω - v default ω| +
                    |(u i ω - v i ω) - (u default ω - v default ω)| := by rw [hdiff]
          have hsum := Finset.single_le_sum (s := (Finset.univ : Finset I))
            (fun k hk => abs_nonneg ((u k ω - v k ω) - (u default ω - v default ω))) hi
          exact hiabs.trans (add_le_add
            (Finset.le_sup' (fun k : I => |v k ω - v default ω|) hi) (by simpa using hsum))
        have hright : S v ω ≤ S u ω +
            ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)| := by
          apply Finset.sup'_le Finset.univ_nonempty
          intro i hi
          have hiabs : |v i ω - v default ω| ≤
              |u i ω - u default ω| +
                |(u i ω - v i ω) - (u default ω - v default ω)| := by
            have hdiff : (v i ω - v default ω) - (u i ω - u default ω) =
                -((u i ω - v i ω) - (u default ω - v default ω)) := by ring
            calc
              |v i ω - v default ω| ≤
                  |u i ω - u default ω| +
                    |(v i ω - v default ω) - (u i ω - u default ω)| := by
                linarith [abs_sub_abs_le_abs_sub
                  (v i ω - v default ω) (u i ω - u default ω)]
              _ = |u i ω - u default ω| +
                    |(u i ω - v i ω) - (u default ω - v default ω)| := by
                rw [hdiff, abs_neg]
          have hsum := Finset.single_le_sum (s := (Finset.univ : Finset I))
            (fun k hk => abs_nonneg ((u k ω - v k ω) - (u default ω - v default ω))) hi
          exact hiabs.trans (add_le_add
            (Finset.le_sup' (fun k : I => |u k ω - u default ω|) hi) (by simpa using hsum))
        rw [abs_le]
        constructor <;> linarith
      have hmin := abs_min_sub_min_le_max (1 : ℝ) (S u ω / eta)
        1 (S v ω / eta)
      have hmin' : |U ω - V ω| ≤
          (1 / eta) * ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)| := by
        calc
          |U ω - V ω| ≤ max |(1 : ℝ) - 1| |S u ω / eta - S v ω / eta| := by
            exact hmin
          _ = |S u ω - S v ω| / eta := by
            rw [div_sub_div_same, abs_div, abs_of_pos heta]
            simp only [sub_self, abs_zero]
            exact max_eq_right (show (0 : ℝ) ≤ |S u ω - S v ω| / eta from
              div_nonneg (abs_nonneg _) (le_of_lt heta))
          _ ≤ (∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)|) / eta :=
            div_le_div_of_nonneg_right hsuv (le_of_lt heta)
          _ = (1 / eta) * ∑ i : I,
              |(u i ω - v i ω) - (u default ω - v default ω)| := by
            field_simp [ne_of_gt heta]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hmin'
    have hmono : eLpNorm (U - V) p μ ≤
        eLpNorm (fun ω => (1 / eta) *
          ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)|) p μ := by
      apply eLpNorm_mono_ae (huU'.sub hvV'.aestronglyMeasurable)
      filter_upwards [] with ω
      have hnonneg : 0 ≤ (1 / eta) * ∑ i : I,
          |(u i ω - v i ω) - (u default ω - v default ω)| :=
        mul_nonneg (by positivity) (Finset.sum_nonneg (fun i hi => abs_nonneg _))
      calc
        ‖(U - V) ω‖ ≤ (1 / eta) * ∑ i : I,
            |(u i ω - v i ω) - (u default ω - v default ω)| := hpoint ω
        _ = ‖(1 / eta) * ∑ i : I,
            |(u i ω - v i ω) - (u default ω - v default ω)|‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      eLpNorm (U - V) p μ ≤
          eLpNorm (fun ω => (1 / eta) *
            ∑ i : I, |(u i ω - v i ω) - (u default ω - v default ω)|) p μ := hmono
      _ = eLpNorm ((1 / eta) • (fun ω => ∑ i : I,
            |(u i ω - v i ω) - (u default ω - v default ω)|)) p μ := by
        congr 1
      _ = (ENNReal.ofReal (1 / eta)) *
          eLpNorm (fun ω => ∑ i : I,
            |(u i ω - v i ω) - (u default ω - v default ω)|) p μ := by
        rw [eLpNorm_const_smul]
        rw [← ofReal_norm_eq_enorm]
        congr 1
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr heta)]
      _ ≤ (ENNReal.ofReal (1 / eta)) *
          (∑ i : I, eLpNorm (fun ω =>
            |(u i ω - v i ω) - (u default ω - v default ω)|) p μ) := by
        have hsum' : eLpNorm (fun ω => ∑ i : I, |d i ω|) p μ ≤
            ∑ i : I, eLpNorm (fun ω => |d i ω|) p μ := by
          exact aux_finite_response_ramp_sum_eLpNorm_le (mΩ := mΩ) hp hdiff_absmeas
        have hsum : eLpNorm (fun ω => ∑ i : I,
              |(u i ω - v i ω) - (u default ω - v default ω)|) p μ ≤
            ∑ i : I, eLpNorm (fun ω =>
              |(u i ω - v i ω) - (u default ω - v default ω)|) p μ := by
          simpa only [d] using hsum'
        exact mul_le_mul_right hsum _
      _ ≤ (ENNReal.ofReal (1 / eta)) *
          ((Finset.univ : Finset I).sum (fun _ => B + B)) := by
        have hsum : (Finset.univ : Finset I).sum
              (fun i => eLpNorm (fun ω => |d i ω|) p μ) ≤
            (Finset.univ : Finset I).sum (fun _ => B + B) := by
          refine Finset.sum_le_sum (s := (Finset.univ : Finset I)) ?_
          intro i hi
          rw [hdiff_norm_eq i]
          have hle := eLpNorm_sub_le (μ := μ) (f := u i - v i)
            (g := u default - v default) hp
          exact hle.trans (add_le_add (hbound i) (hbound default))
        exact mul_le_mul_right hsum _
      _ = 2 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul, mul_add, ENNReal.ofReal_natCast]
        rw [show (1 / eta : ℝ) = eta⁻¹ by ring, ENNReal.ofReal_inv_of_pos heta]
        rw [ENNReal.div_eq_inv_mul]
        ring
  have hceV : μ[V | m] =ᵐ[μ] V := by
    exact Filter.Eventually.of_forall (fun ω =>
      congrFun (condExp_of_stronglyMeasurable (m := m) hm hvV hVint) ω)
  have hce_sub := condExp_sub hUint hVint m
  have herror :
      (fun ω => U ω - (μ[U | m]) ω) =ᵐ[μ]
        (U - V) - μ[U - V | m] := by
    filter_upwards [hceV, hce_sub] with ω hV hsub
    have hsub' : (μ[U - V | m]) ω =
        (μ[U | m]) ω - (μ[V | m]) ω := by
      simpa only [Pi.sub_apply] using hsub
    simp only [Pi.sub_apply]
    rw [hsub', hV]
    ring
  have hfinal : eLpNorm (fun ω => U ω - (μ[U | m]) ω) p μ ≤
      4 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta := by
    rw [eLpNorm_congr_ae herror]
    have hUV : AEStronglyMeasurable[mΩ] (U - V) μ :=
      huU'.sub hvV'.aestronglyMeasurable
    calc
      eLpNorm ((U - V) - μ[U - V | m]) p μ ≤
          eLpNorm (U - V) p μ + eLpNorm (μ[U - V | m]) p μ :=
        eLpNorm_sub_le hp
      _ ≤ eLpNorm (U - V) p μ + eLpNorm (U - V) p μ :=
        add_le_add le_rfl (hcontr (U - V) (hUint.sub hVint))
      _ ≤ 4 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta := by
        calc
          _ ≤ (2 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta) +
              (2 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta) :=
            add_le_add hdiff_bound hdiff_bound
          _ = 4 * (Fintype.card I : ℝ≥0∞) * B / ENNReal.ofReal eta := by
            calc
              _ = (ENNReal.ofReal eta)⁻¹ *
                  (B * ((Fintype.card I : ℝ≥0∞) * 4)) := by
                simp only [ENNReal.div_eq_inv_mul]
                ring
              _ = 4 * (Fintype.card I : ℝ≥0∞) * B /
                  ENNReal.ofReal eta := by
                rw [ENNReal.div_eq_inv_mul]
                ac_rfl
  simpa only [U, V, S, Finset.sup'_apply] using hfinal

theorem aux_finite_response_ramp_option_sup
    {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun i : Option I => match i with
          | none => 0
          | some j => f j) =
      Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i hi
    cases i with
    | none =>
        exact (Finset.sup'_mem (Set.Ici (0 : ℝ))
          (fun a ha b hb => by
            change 0 ≤ max a b
            exact le_max_of_le_left (show (0 : ℝ) ≤ a from ha))
          _ Finset.univ_nonempty f (fun j hj => hf j))
    | some j => exact Finset.le_sup' f (by simp)
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i hi
    exact Finset.le_sup' (fun j : Option I => match j with
      | none => 0
      | some k => f k) (Finset.mem_univ (some i))

theorem aux_finite_response_ramp_scale
    {I : Type*} [Fintype I] (eta c s : ℝ) (heta : 0 < eta)
    (hc : 0 ≤ c) (hs : 0 ≤ s) :
    4 * (Fintype.card (Option I) : ℝ≥0∞) *
        (2 * ENNReal.ofReal (c * s)) / ENNReal.ofReal eta =
      ENNReal.ofReal
        ((8 * ((Fintype.card I : ℝ) + 1) * c / eta) * s) := by
  have hcard : (Fintype.card (Option I) : ℝ≥0∞) =
      ENNReal.ofReal ((Fintype.card I : ℝ) + 1) := by
    norm_num [Fintype.card_option, ENNReal.ofReal_add]
  rw [hcard]
  rw [show 2 * ENNReal.ofReal (c * s) = ENNReal.ofReal (2 * (c * s)) by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num]
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * ((Fintype.card I : ℝ) + 1) * c / eta)]
  rw [ENNReal.ofReal_div_of_pos heta]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c)]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * ((Fintype.card I : ℝ) + 1))]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  rw [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (Fintype.card I : ℝ)) (by norm_num)]
  rw [ENNReal.ofReal_natCast]
  simp only [ENNReal.div_eq_inv_mul]
  norm_num
  ring



theorem finite_response_ramp
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (T : Type) [Fintype T] [Nonempty T]
    (p q a Cmom Cband : ℝ)
    (hp : 1 ≤ p) (hpq : p < q) (ha : 0 < a)
    (hCmom : 0 < Cmom) (hCband : 0 < Cband)
    (R : T → ℕ → ((j : ℤ) → Y j) → ℝ)
    (Rlim : T → ((j : ℤ) → Y j) → ℝ)
    (hmeas : ∀ t m, AEStronglyMeasurable (R t m) (Measure.infinitePi laws))
    (hlimmeas : ∀ t, AEStronglyMeasurable (Rlim t) (Measure.infinitePi laws))
    (hmem : ∀ t m, MemLp (R t m) (ENNReal.ofReal q) (Measure.infinitePi laws))
    (hmom : ∀ t m, eLpNorm (R t m) (ENNReal.ofReal q) (Measure.infinitePi laws)
      ≤ ENNReal.ofReal Cmom)
    (hconv : ∀ t, TendstoInMeasure (Measure.infinitePi laws) (R t) atTop (Rlim t))
    (hband : ∀ t m (H : ℕ),
      eLpNorm (fun omega => R t m omega -
        ((Measure.infinitePi laws)[R t m | bandSigma Y H]) omega)
        (ENNReal.ofReal p) (Measure.infinitePi laws)
        ≤ ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ)))) :
    (∀ t, MemLp (Rlim t) (ENNReal.ofReal q) (Measure.infinitePi laws) ∧
      eLpNorm (Rlim t) (ENNReal.ofReal q) (Measure.infinitePi laws)
        ≤ ENNReal.ofReal Cmom ∧
      ∀ H : ℕ, eLpNorm (fun omega => Rlim t omega -
        ((Measure.infinitePi laws)[Rlim t | bandSigma Y H]) omega)
        (ENNReal.ofReal p) (Measure.infinitePi laws)
        ≤ ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ)))) ∧
    (∀ eta : ℝ, 0 < eta → ∃ Cstar : ℝ, 0 < Cstar ∧
      (let Rext : Option ℕ → T → ((j : ℤ) → Y j) → ℝ :=
        fun i t => match i with
          | none => Rlim t
          | some m => R t m
       let X : Option ℕ → Option ℕ → ((j : ℤ) → Y j) → ℝ :=
        fun i j omega => min 1
          ((Finset.univ.sup' Finset.univ_nonempty
            (fun t : T => |Rext i t omega - Rext j t omega|)) / eta)
       (∀ i j omega, X i j omega ∈ Set.Icc (0 : ℝ) 1) ∧
       (∀ i j, AEStronglyMeasurable (X i j) (Measure.infinitePi laws)) ∧
       (∀ i j (H : ℕ), eLpNorm (fun omega => X i j omega -
         ((Measure.infinitePi laws)[X i j | bandSigma Y H]) omega)
         (ENNReal.ofReal p) (Measure.infinitePi laws)
         ≤ ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-a * (H : ℝ)))) ∧
      (∀ eps : ℝ, 0 < eps → ∃ m0 : ℕ, ∀ i j : Option ℕ,
         (∀ n, i = some n → m0 ≤ n) →
         (∀ n, j = some n → m0 ≤ n) →
         ∫ omega, X i j omega ∂(Measure.infinitePi laws) < eps))) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_trans hp0 hpq
  have hpE1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp)
  have hpEqE : ENNReal.ofReal p < ENNReal.ofReal q :=
    (ENNReal.ofReal_lt_ofReal_iff hq0).mpr hpq
  have hqE1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ q by linarith))
  have hqEtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hCtop : ENNReal.ofReal Cmom ≠ ∞ := ENNReal.ofReal_ne_top
  have hlim : ∀ t, MemLp (Rlim t) (ENNReal.ofReal q) (Measure.infinitePi laws) ∧
      Tendsto (fun m => eLpNorm (fun omega => R t m omega - Rlim t omega)
        (ENNReal.ofReal p) (Measure.infinitePi laws)) atTop (𝓝 0) := by
    intro t
    exact aux_finite_response_ramp_tendsto_eLpNorm hpE1 hpEqE hqEtop hCtop
      (fun m => hmeas t m) (hlimmeas t) (fun m => hmom t m) (hconv t)
  have hone : ∀ t, Tendsto
      (fun m => eLpNorm (fun omega => R t m omega - Rlim t omega) 1
        (Measure.infinitePi laws)) atTop (𝓝 0) := by
    intro t
    have hq1 : (1 : ℝ≥0∞) < ENNReal.ofReal q := by
      simpa using (ENNReal.ofReal_lt_ofReal_iff hq0).mpr (show (1 : ℝ) < q by linarith)
    exact (aux_finite_response_ramp_tendsto_eLpNorm (p := (1 : ℝ≥0∞))
      (q := ENNReal.ofReal q) le_rfl hq1 hqEtop hCtop
      (fun m => hmeas t m) (hlimmeas t) (fun m => hmom t m) (hconv t)).2
  have hlim_band : ∀ t H, eLpNorm (fun omega => Rlim t omega -
      ((Measure.infinitePi laws)[Rlim t | bandSigma Y H]) omega)
      (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
      ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))) := by
    intro t H
    have hRint : ∀ m, Integrable (R t m) (Measure.infinitePi laws) := by
      intro m
      exact (hmem t m).integrable hqE1
    have hLint : Integrable (Rlim t) (Measure.infinitePi laws) :=
      (hlim t).1.integrable hqE1
    have hce_meas : ∀ m, AEStronglyMeasurable
        ((Measure.infinitePi laws)[R t m | bandSigma Y H]) (Measure.infinitePi laws) := by
      intro m
      exact (stronglyMeasurable_condExp (μ := Measure.infinitePi laws)
        (m := bandSigma Y H) (f := R t m)).mono (bandSigma_le H) |>.aestronglyMeasurable
    have hce_lim_meas : AEStronglyMeasurable
        ((Measure.infinitePi laws)[Rlim t | bandSigma Y H]) (Measure.infinitePi laws) :=
      (stronglyMeasurable_condExp (μ := Measure.infinitePi laws)
        (m := bandSigma Y H) (f := Rlim t)).mono (bandSigma_le H) |>.aestronglyMeasurable
    have hce_diff : Tendsto (fun m => eLpNorm
        ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
          (Measure.infinitePi laws)[Rlim t | bandSigma Y H]) 1
          (Measure.infinitePi laws)) atTop (𝓝 0) := by
      have hle : ∀ m, eLpNorm
          ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
            (Measure.infinitePi laws)[Rlim t | bandSigma Y H]) 1
              (Measure.infinitePi laws) ≤
          eLpNorm (fun omega => R t m omega - Rlim t omega) 1
            (Measure.infinitePi laws) := by
        intro m
        calc
          eLpNorm ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
              (Measure.infinitePi laws)[Rlim t | bandSigma Y H]) 1
                (Measure.infinitePi laws) =
              eLpNorm ((Measure.infinitePi laws)[(fun omega =>
                R t m omega - Rlim t omega) | bandSigma Y H]) 1
                  (Measure.infinitePi laws) := by
            exact eLpNorm_congr_ae
              (condExp_sub (hRint m) hLint (bandSigma Y H)).symm
          _ ≤ eLpNorm (fun omega => R t m omega - Rlim t omega) 1
                (Measure.infinitePi laws) :=
            eLpNorm_one_condExp_le_eLpNorm _
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
        (hone t) (Filter.Eventually.of_forall (fun _ => zero_le))
        (Filter.Eventually.of_forall hle)
    have hdiff : Tendsto (fun m => eLpNorm
        (fun omega => (R t m omega -
            (Measure.infinitePi laws)[R t m | bandSigma Y H] omega) -
          (Rlim t omega -
            (Measure.infinitePi laws)[Rlim t | bandSigma Y H] omega)) 1
          (Measure.infinitePi laws)) atTop (𝓝 0) := by
      have hle : ∀ m, eLpNorm
          (fun omega => (R t m omega -
              (Measure.infinitePi laws)[R t m | bandSigma Y H] omega) -
            (Rlim t omega -
              (Measure.infinitePi laws)[Rlim t | bandSigma Y H] omega)) 1
              (Measure.infinitePi laws) ≤
          eLpNorm (fun omega => R t m omega - Rlim t omega) 1
              (Measure.infinitePi laws) +
            eLpNorm ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
              (Measure.infinitePi laws)[Rlim t | bandSigma Y H]) 1
                (Measure.infinitePi laws) := by
        intro m
        have hm : AEStronglyMeasurable
            (fun omega => R t m omega - Rlim t omega) (Measure.infinitePi laws) :=
          (hmeas t m).sub (hlimmeas t)
        have hc : AEStronglyMeasurable
            ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
              (Measure.infinitePi laws)[Rlim t | bandSigma Y H])
                (Measure.infinitePi laws) :=
          (hce_meas m).sub hce_lim_meas
        calc
          eLpNorm (fun omega => (R t m omega -
                (Measure.infinitePi laws)[R t m | bandSigma Y H] omega) -
              (Rlim t omega -
                (Measure.infinitePi laws)[Rlim t | bandSigma Y H] omega)) 1
                (Measure.infinitePi laws) =
              eLpNorm ((fun omega => R t m omega - Rlim t omega) -
                ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
                  (Measure.infinitePi laws)[Rlim t | bandSigma Y H])) 1
                    (Measure.infinitePi laws) := by
            congr 1
            funext omega
            simp only [Pi.sub_apply]
            ring
          _ ≤ eLpNorm (fun omega => R t m omega - Rlim t omega) 1
                (Measure.infinitePi laws) +
              eLpNorm ((Measure.infinitePi laws)[R t m | bandSigma Y H] -
                (Measure.infinitePi laws)[Rlim t | bandSigma Y H]) 1
                  (Measure.infinitePi laws) :=
            eLpNorm_sub_le le_rfl
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
        (by simpa using (hone t).add hce_diff)
          (Filter.Eventually.of_forall (fun _ => zero_le))
        (Filter.Eventually.of_forall hle)
    have hmeasure : TendstoInMeasure (Measure.infinitePi laws)
        (fun m omega => R t m omega -
          (Measure.infinitePi laws)[R t m | bandSigma Y H] omega)
        atTop (fun omega => Rlim t omega -
          (Measure.infinitePi laws)[Rlim t | bandSigma Y H] omega) :=
      tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) one_ne_zero
        hdiff
    have hbound : eLpNorm (fun omega => Rlim t omega -
          (Measure.infinitePi laws)[Rlim t | bandSigma Y H] omega)
        (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
          ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))) :=
      eLpNorm_le_of_tendstoInMeasure (p := ENNReal.ofReal p)
        (Filter.Eventually.of_forall (fun m => hband t m H)) hmeasure
        (fun m => (hmeas t m).sub (hce_meas m))
    exact hbound
  constructor
  · intro t
    refine ⟨(hlim t).1, ?_, ?_⟩
    · exact eLpNorm_le_of_tendstoInMeasure (p := ENNReal.ofReal q)
        (Filter.Eventually.of_forall (fun m => hmom t m)) (hconv t) (fun m => hmeas t m)
    · intro H
      exact hlim_band t H
  · intro eta heta
    letI : Inhabited T := ⟨Classical.choice (inferInstance : Nonempty T)⟩
    let Rext : Option ℕ → T → ((j : ℤ) → Y j) → ℝ :=
      fun i t => match i with
        | none => Rlim t
        | some m => R t m
    let X : Option ℕ → Option ℕ → ((j : ℤ) → Y j) → ℝ :=
      fun i j omega => min 1
        ((Finset.univ.sup' Finset.univ_nonempty
          (fun t : T => |Rext i t omega - Rext j t omega|)) / eta)
    let Cstar : ℝ :=
      8 * ((Fintype.card T : ℝ) + 1) * Cband / eta
    refine ⟨Cstar, ?_, ?_⟩
    · dsimp [Cstar]
      positivity
    · dsimp only
      constructor
      · intro i j omega
        have hsup : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun t : T => |Rext i t omega - Rext j t omega|) := by
          have hIci : ∀ a : ℝ, a ∈ Set.Ici (0 : ℝ) → ∀ b : ℝ,
              b ∈ Set.Ici (0 : ℝ) → max a b ∈ Set.Ici (0 : ℝ) := by
            intro a ha b hb
            change 0 ≤ max a b
            exact le_max_of_le_left (show (0 : ℝ) ≤ a from ha)
          exact Finset.sup'_mem (Set.Ici (0 : ℝ)) hIci _
            Finset.univ_nonempty (fun t : T => |Rext i t omega - Rext j t omega|)
            (fun t ht => show 0 ≤ |Rext i t omega - Rext j t omega| from
              abs_nonneg _)
        constructor
        · exact le_min (by norm_num)
            (div_nonneg hsup (le_of_lt heta))
        · exact min_le_left _ _
      · constructor
        · intro i j
          have hRext : ∀ k t, AEStronglyMeasurable (Rext k t)
              (Measure.infinitePi laws) := by
            intro k t
            cases k with
            | none => exact hlimmeas t
            | some m => exact hmeas t m
          have hterm : ∀ t : T, AEStronglyMeasurable
            (fun omega => |Rext i t omega - Rext j t omega|)
              (Measure.infinitePi laws) := by
            intro t
            exact continuous_abs.comp_aestronglyMeasurable
              ((hRext i t).sub (hRext j t))
          have hsup : AEStronglyMeasurable
            (fun omega => Finset.univ.sup' Finset.univ_nonempty
              (fun t : T => |Rext i t omega - Rext j t omega|))
              (Measure.infinitePi laws) := by
            have h : AEStronglyMeasurable
                (Finset.univ.sup' Finset.univ_nonempty
                  (fun t : T => fun omega => |Rext i t omega - Rext j t omega|))
                (Measure.infinitePi laws) := by
              refine Finset.sup'_induction (p := fun z : ((k : ℤ) → Y k) → ℝ =>
                AEStronglyMeasurable z (Measure.infinitePi laws))
                (s := (Finset.univ : Finset T)) Finset.univ_nonempty
                (fun t : T => fun omega => |Rext i t omega - Rext j t omega|) ?_ ?_
              · intro a ha b hb
                exact continuous_max.comp_aestronglyMeasurable (ha.prodMk hb)
              · intro t ht
                exact hterm t
            have hfun : (fun omega => Finset.univ.sup' Finset.univ_nonempty
                (fun t : T => |Rext i t omega - Rext j t omega|)) =
                Finset.univ.sup' Finset.univ_nonempty
                  (fun t : T => fun omega => |Rext i t omega - Rext j t omega|) := by
              funext omega
              exact (Finset.sup'_apply Finset.univ_nonempty
                (fun t : T => fun omega => |Rext i t omega - Rext j t omega|) omega).symm
            rw [hfun]
            exact h
          have hdiv : AEStronglyMeasurable
            (fun omega => (Finset.univ.sup' Finset.univ_nonempty
              (fun t : T => |Rext i t omega - Rext j t omega|)) / eta)
              (Measure.infinitePi laws) :=
            (continuous_id.div_const eta).comp_aestronglyMeasurable hsup
          exact continuous_min.comp_aestronglyMeasurable
            (aestronglyMeasurable_const.prodMk hdiv)
        · constructor
          · intro i j H
            let ν : Measure ((k : ℤ) → Y k) := Measure.infinitePi laws
            let u : Option T → ((k : ℤ) → Y k) → ℝ := fun k => match k with
              | none => 0
              | some t => Rext i t - Rext j t
            let v : Option T → ((k : ℤ) → Y k) → ℝ := fun k =>
              ν[u k | bandSigma Y H]
            have hRext : ∀ k t, AEStronglyMeasurable (Rext k t) ν := by
              intro k t
              cases k with
              | none => exact hlimmeas t
              | some n => exact hmeas t n
            have hRint : ∀ k t, Integrable (Rext k t) ν := by
              intro k t
              cases k with
              | none => exact (hlim t).1.integrable hqE1
              | some n => exact (hmem t n).integrable hqE1
            have hu : ∀ k, AEStronglyMeasurable (u k) ν := by
              intro k
              cases k with
              | none => simpa [u] using (aestronglyMeasurable_zero :
                  AEStronglyMeasurable (fun _ : ((k : ℤ) → Y k) => (0 : ℝ)) ν)
              | some t =>
                  simpa [u] using
                    ((hRext i t).sub (hRext j t))
            have huint : ∀ k, Integrable (u k) ν := by
              intro k
              cases k with
              | none => exact integrable_zero _ _ ν
              | some t => simpa [u] using (hRint i t).sub (hRint j t)
            have hv : ∀ k, StronglyMeasurable[bandSigma Y H] (v k) := by
              intro k
              exact stronglyMeasurable_condExp
            have hvint : ∀ k, Integrable (v k) ν := by
              intro k
              exact integrable_condExp
            have hcontr : ∀ z : ((k : ℤ) → Y k) → ℝ, Integrable z ν →
                eLpNorm (ν[z | bandSigma Y H]) (ENNReal.ofReal p) ν ≤
                  eLpNorm z (ENNReal.ofReal p) ν := by
              intro z hz
              exact aux_finite_response_ramp_band_condExp_le Y laws H hpE1
                ENNReal.ofReal_ne_top hz
            have hbound : ∀ k, eLpNorm (u k - v k) (ENNReal.ofReal p) ν ≤
                2 * ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))) := by
              intro k
              cases k with
              | none => simp [u, v, ν]
              | some t =>
                  have hi : eLpNorm (Rext i t - ν[Rext i t | bandSigma Y H])
                      (ENNReal.ofReal p) ν ≤
                      ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))) := by
                    cases i with
                    | none => simpa [Rext, ν, Pi.sub_def, Pi.sub_apply] using hlim_band t H
                    | some n => simpa [Rext, ν, Pi.sub_def, Pi.sub_apply] using hband t n H
                  have hj : eLpNorm (Rext j t - ν[Rext j t | bandSigma Y H])
                      (ENNReal.ofReal p) ν ≤
                      ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))) := by
                    cases j with
                    | none => simpa [Rext, ν, Pi.sub_def, Pi.sub_apply] using hlim_band t H
                    | some n => simpa [Rext, ν, Pi.sub_def, Pi.sub_apply] using hband t n H
                  have heq : u (some t) - v (some t) =ᵐ[ν]
                      (Rext i t - ν[Rext i t | bandSigma Y H]) -
                        (Rext j t - ν[Rext j t | bandSigma Y H]) := by
                    have hce := condExp_sub (hRint i t) (hRint j t) (bandSigma Y H)
                    filter_upwards [hce] with x hx
                    simp only [u, v, Pi.sub_apply] at hx ⊢
                    rw [hx]
                    ring
                  rw [eLpNorm_congr_ae heq]
                  calc
                    eLpNorm ((Rext i t - ν[Rext i t | bandSigma Y H]) -
                        (Rext j t - ν[Rext j t | bandSigma Y H])) (ENNReal.ofReal p) ν ≤
                        eLpNorm (Rext i t - ν[Rext i t | bandSigma Y H]) (ENNReal.ofReal p) ν +
                          eLpNorm (Rext j t - ν[Rext j t | bandSigma Y H]) (ENNReal.ofReal p) ν :=
                      eLpNorm_sub_le hpE1
                    _ ≤ 2 * ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))) :=
                      by simpa [two_mul] using add_le_add hi hj
            have hmain := aux_finite_response_ramp_ramp_band_le
              (μ := ν) (I := Option T) (p := ENNReal.ofReal p)
              (B := 2 * ENNReal.ofReal (Cband * (3 : ℝ) ^ (-a * (H : ℝ))))
              (u := u) (v := v) (m := bandSigma Y H) (hm := bandSigma_le H)
              eta hpE1 heta
              hu hv huint hvint hcontr hbound
            have hU : (fun omega => min 1
                ((Finset.univ.sup' Finset.univ_nonempty
                  (fun k : Option T => |u k omega - u default omega|)) / eta)) =
                X i j := by
              funext omega
              rw [show (default : Option T) = none by rfl]
              have hfun : (fun k : Option T => |u k omega - u none omega|) =
                  (fun k : Option T => match k with
                    | none => 0
                    | some t => |Rext i t omega - Rext j t omega|) := by
                funext k
                cases k <;> simp [u]
              have hs := aux_finite_response_ramp_option_sup
                (I := T) (fun t : T => |Rext i t omega - Rext j t omega|)
                (fun t => abs_nonneg (Rext i t omega - Rext j t omega))
              rw [hfun]
              dsimp only [X]
              convert congrArg (fun z : ℝ => min 1 (z / eta)) hs using 1 <;>
                congr 2 <;> (funext k; cases k <;> rfl)
            rw [hU] at hmain
            have hscale := aux_finite_response_ramp_scale
              (I := T) eta Cband ((3 : ℝ) ^ (-a * (H : ℝ))) heta
              (le_of_lt hCband) (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
            simpa [ν, Cstar] using hmain.trans_eq hscale
          · intro eps heps
            have hcard : 0 < (Fintype.card T : ℝ) := by
              exact_mod_cast Fintype.card_pos
            let δ : ℝ := eps * eta / (4 * (Fintype.card T : ℝ))
            have hδ : 0 < δ := by
              dsimp [δ]
              positivity
            have hsmall : ∀ t : T, ∀ᶠ m in atTop,
                eLpNorm (fun omega => R t m omega - Rlim t omega) 1
                  (Measure.infinitePi laws) < ENNReal.ofReal δ := by
              intro t
              exact (hone t).eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)
            have hsmall_all : ∀ᶠ m in atTop, ∀ t : T,
                eLpNorm (fun omega => R t m omega - Rlim t omega) 1
                  (Measure.infinitePi laws) < ENNReal.ofReal δ :=
              Filter.eventually_all.mpr hsmall
            obtain ⟨m0, hm0⟩ := Filter.Eventually.exists_forall_of_atTop hsmall_all
            have hRext_int : ∀ (i : Option ℕ) (t : T),
                Integrable (Rext i t) (Measure.infinitePi laws) := by
              intro i t
              cases i with
              | none => exact (hlim t).1.integrable hqE1
              | some m => exact (hmem t m).integrable hqE1
            have hdiff_int : ∀ (i : Option ℕ) (t : T),
                Integrable (fun omega => Rext i t omega - Rlim t omega)
                  (Measure.infinitePi laws) := by
              intro i t
              exact (hRext_int i t).sub ((hlim t).1.integrable hqE1)
            let D : Option ℕ → T → ((j : ℤ) → Y j) → ℝ := fun i t omega =>
              |Rext i t omega - Rlim t omega|
            have hD_int : ∀ (i : Option ℕ) (t : T),
                Integrable (D i t) (Measure.infinitePi laws) := by
              intro i t
              simpa only [D, Real.norm_eq_abs] using (hdiff_int i t).norm
            have hD_eq : ∀ (i : Option ℕ) (t : T),
                ENNReal.ofReal (∫ omega, D i t omega ∂(Measure.infinitePi laws)) =
                  eLpNorm (fun omega => Rext i t omega - Rlim t omega) 1
                    (Measure.infinitePi laws) := by
              intro i t
              simpa only [D, Real.norm_eq_abs,
                eLpNorm_one_eq_lintegral_enorm (hdiff_int i t).aestronglyMeasurable] using
                (ofReal_integral_norm_eq_lintegral_enorm (hdiff_int i t))
            have hD_small : ∀ (n : ℕ) (t : T), m0 ≤ n →
                ∫ omega, D (some n) t omega ∂(Measure.infinitePi laws) < δ := by
              intro n t hn
              apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
              rw [hD_eq (some n) t]
              simpa [Rext] using hm0 n hn t
            have hD_none : ∀ t : T,
                ∫ omega, D none t omega ∂(Measure.infinitePi laws) = 0 := by
              intro t
              simp [D, Rext]
            have hsumD : ∀ (i : Option ℕ),
                (∀ n, i = some n → m0 ≤ n) →
                (∑ t : T, ∫ omega, D i t omega ∂(Measure.infinitePi laws)) <
                  (Fintype.card T : ℝ) * δ := by
              intro i hi
              cases i with
              | none =>
                  calc
                    (∑ t : T, ∫ omega, D none t omega ∂(Measure.infinitePi laws)) = 0 := by
                      simp [hD_none]
                    _ < (Fintype.card T : ℝ) * δ := by positivity
              | some n =>
                  have hterm : ∀ t : T,
                      ∫ omega, D (some n) t omega ∂(Measure.infinitePi laws) < δ :=
                    fun t => hD_small n t (hi n rfl)
                  calc
                    (∑ t : T, ∫ omega, D (some n) t omega ∂(Measure.infinitePi laws)) <
                        ∑ t : T, δ := by
                      exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
                        (fun t _ => hterm t)
                    _ = (Fintype.card T : ℝ) * δ := by
                      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have hXmeas : ∀ i j, AEStronglyMeasurable (X i j)
                (Measure.infinitePi laws) := by
              intro i j
              have hRext : ∀ k t, AEStronglyMeasurable (Rext k t)
                  (Measure.infinitePi laws) := by
                intro k t
                cases k with
                | none => exact hlimmeas t
                | some m => exact hmeas t m
              have hterm : ∀ t : T, AEStronglyMeasurable
                  (fun omega => |Rext i t omega - Rext j t omega|)
                  (Measure.infinitePi laws) := by
                intro t
                exact continuous_abs.comp_aestronglyMeasurable
                  ((hRext i t).sub (hRext j t))
              have hsup : AEStronglyMeasurable
                  (fun omega => Finset.univ.sup' Finset.univ_nonempty
                    (fun t : T => |Rext i t omega - Rext j t omega|))
                  (Measure.infinitePi laws) := by
                have h : AEStronglyMeasurable
                    (Finset.univ.sup' Finset.univ_nonempty
                      (fun t : T => fun omega =>
                        |Rext i t omega - Rext j t omega|))
                    (Measure.infinitePi laws) := by
                  refine Finset.sup'_induction
                    (p := fun z : ((k : ℤ) → Y k) → ℝ =>
                      AEStronglyMeasurable z (Measure.infinitePi laws))
                    (s := (Finset.univ : Finset T)) Finset.univ_nonempty
                    (fun t : T => fun omega =>
                      |Rext i t omega - Rext j t omega|) ?_ ?_
                  · intro a ha b hb
                    exact continuous_max.comp_aestronglyMeasurable (ha.prodMk hb)
                  · intro t ht
                    exact hterm t
                have hfun : (fun omega => Finset.univ.sup' Finset.univ_nonempty
                    (fun t : T => |Rext i t omega - Rext j t omega|)) =
                    Finset.univ.sup' Finset.univ_nonempty
                      (fun t : T => fun omega =>
                        |Rext i t omega - Rext j t omega|) := by
                  funext omega
                  exact (Finset.sup'_apply Finset.univ_nonempty
                    (fun t : T => fun omega =>
                      |Rext i t omega - Rext j t omega|) omega).symm
                rw [hfun]
                exact h
              have hdiv : AEStronglyMeasurable
                  (fun omega => (Finset.univ.sup' Finset.univ_nonempty
                    (fun t : T => |Rext i t omega - Rext j t omega|)) / eta)
                  (Measure.infinitePi laws) :=
                (continuous_id.div_const eta).comp_aestronglyMeasurable hsup
              exact continuous_min.comp_aestronglyMeasurable
                (aestronglyMeasurable_const.prodMk hdiv)
            have hX_bdd : ∀ i j, ∀ᵐ omega ∂(Measure.infinitePi laws),
                ‖X i j omega‖ ≤ (1 : ℝ) := by
              intro i j
              filter_upwards [] with omega
              have hsup : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
                  (fun t : T => |Rext i t omega - Rext j t omega|) := by
                have hIci : ∀ a : ℝ, a ∈ Set.Ici (0 : ℝ) → ∀ b : ℝ,
                    b ∈ Set.Ici (0 : ℝ) → max a b ∈ Set.Ici (0 : ℝ) := by
                  intro a ha b hb
                  change 0 ≤ max a b
                  exact le_max_of_le_left (show (0 : ℝ) ≤ a from ha)
                exact Finset.sup'_mem (Set.Ici (0 : ℝ)) hIci _
                  Finset.univ_nonempty (fun t : T =>
                    |Rext i t omega - Rext j t omega|)
                  (fun t ht => show 0 ≤ |Rext i t omega - Rext j t omega| from
                    abs_nonneg _)
              have hnon : 0 ≤ (Finset.univ.sup' Finset.univ_nonempty
                  (fun t : T => |Rext i t omega - Rext j t omega|)) / eta :=
                div_nonneg hsup (le_of_lt heta)
              rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) hnon)]
              exact min_le_left _ _
            have hXint : ∀ i j, Integrable (X i j) (Measure.infinitePi laws) := by
              intro i j
              exact Integrable.of_bound (hXmeas i j) 1 (hX_bdd i j)
            have hsup_le : ∀ i j omega,
                Finset.univ.sup' Finset.univ_nonempty
                    (fun t : T => |Rext i t omega - Rext j t omega|) ≤
                  ∑ t : T, (D i t omega + D j t omega) := by
              intro i j omega
              apply Finset.sup'_le Finset.univ_nonempty
              intro t ht
              have habs : |Rext i t omega - Rext j t omega| ≤
                  D i t omega + D j t omega := by
                have htriangle := abs_sub_le (Rext i t omega - Rlim t omega)
                  0 (Rext j t omega - Rlim t omega)
                have heq : (Rext i t omega - Rlim t omega) -
                    (Rext j t omega - Rlim t omega) =
                    Rext i t omega - Rext j t omega := by ring
                rw [heq] at htriangle
                simpa [D, abs_sub_comm] using htriangle
              exact habs.trans (by
                have hsum := Finset.single_le_sum
                  (f := fun k : T => D i k omega + D j k omega)
                  (s := (Finset.univ : Finset T))
                  (fun k hk => by
                    dsimp [D]
                    positivity) ht
                simpa using hsum)
            refine ⟨m0, ?_⟩
            intro i j hi hj
            have hsum_int : Integrable
                (fun omega => ∑ t : T, (D i t omega + D j t omega))
                (Measure.infinitePi laws) := by
              simpa only [Finset.sum_apply, Pi.add_def, Pi.add_apply] using
                (integrable_finset_sum (μ := Measure.infinitePi laws)
                  (s := (Finset.univ : Finset T)) (fun t ht =>
                    (hD_int i t).add (hD_int j t)))
            have hGint : Integrable
                (fun omega => (1 / eta) *
                  ∑ t : T, (D i t omega + D j t omega))
                (Measure.infinitePi laws) := hsum_int.const_mul (1 / eta)
            have hXle : ∀ omega, X i j omega ≤
                (1 / eta) * ∑ t : T, (D i t omega + D j t omega) := by
              intro omega
              calc
                X i j omega ≤
                    (Finset.univ.sup' Finset.univ_nonempty
                      (fun t : T => |Rext i t omega - Rext j t omega|)) / eta :=
                  min_le_right _ _
                _ ≤ (∑ t : T, (D i t omega + D j t omega)) / eta :=
                  div_le_div_of_nonneg_right (hsup_le i j omega) (le_of_lt heta)
                _ = (1 / eta) * ∑ t : T, (D i t omega + D j t omega) := by ring
            have hIneq : (∫ omega, X i j omega ∂(Measure.infinitePi laws)) ≤
                (1 / eta) * ∑ t : T,
                  (∫ omega, D i t omega ∂(Measure.infinitePi laws) +
                    ∫ omega, D j t omega ∂(Measure.infinitePi laws)) := by
              calc
                (∫ omega, X i j omega ∂(Measure.infinitePi laws)) ≤
                    ∫ omega, (1 / eta) *
                      ∑ t : T, (D i t omega + D j t omega)
                        ∂(Measure.infinitePi laws) :=
                  integral_mono_ae (hXint i j) hGint
                    (Filter.Eventually.of_forall hXle)
                _ = (1 / eta) * ∑ t : T,
                    (∫ omega, D i t omega ∂(Measure.infinitePi laws) +
                      ∫ omega, D j t omega ∂(Measure.infinitePi laws)) := by
                  rw [integral_const_mul]
                  congr 1
                  calc
                    (∫ omega, ∑ t : T, (D i t omega + D j t omega)
                        ∂(Measure.infinitePi laws)) =
                        ∫ omega, ∑ t ∈ (Finset.univ : Finset T),
                          (D i t omega + D j t omega)
                            ∂(Measure.infinitePi laws) := by rfl
                    _ = ∑ t ∈ (Finset.univ : Finset T),
                        ∫ omega, (D i t omega + D j t omega)
                          ∂(Measure.infinitePi laws) :=
                      integral_finset_sum (Finset.univ : Finset T)
                        (fun t ht => (hD_int i t).add (hD_int j t))
                    _ = ∑ t : T,
                        (∫ omega, D i t omega ∂(Measure.infinitePi laws) +
                          ∫ omega, D j t omega ∂(Measure.infinitePi laws)) := by
                      apply Finset.sum_congr rfl
                      intro t ht
                      exact integral_add (hD_int i t) (hD_int j t)
            have hsum_total : ∑ t : T,
                  (∫ omega, D i t omega ∂(Measure.infinitePi laws) +
                    ∫ omega, D j t omega ∂(Measure.infinitePi laws)) <
                2 * (Fintype.card T : ℝ) * δ := by
              calc
                _ = (∑ t : T, ∫ omega, D i t omega ∂(Measure.infinitePi laws)) +
                    ∑ t : T, ∫ omega, D j t omega ∂(Measure.infinitePi laws) := by
                  rw [Finset.sum_add_distrib]
                _ < (Fintype.card T : ℝ) * δ +
                    (Fintype.card T : ℝ) * δ :=
                  add_lt_add (hsumD i hi) (hsumD j hj)
                _ = 2 * (Fintype.card T : ℝ) * δ := by ring
            calc
              (∫ omega, X i j omega ∂(Measure.infinitePi laws)) <
                  (1 / eta) * (2 * (Fintype.card T : ℝ) * δ) :=
                lt_of_le_of_lt hIneq
                  (mul_lt_mul_of_pos_left hsum_total (by positivity))
              _ = eps / 2 := by
                dsimp [δ]
                field_simp [ne_of_gt heta, ne_of_gt hcard]
                ring
              _ < eps := by linarith

end Paper
