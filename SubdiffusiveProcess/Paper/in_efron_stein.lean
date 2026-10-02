import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Paper

noncomputable section



theorem aux_in_efron_stein_map_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    Measure.map (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2)
        ((Measure.pi μ).prod (μ i)) = Measure.pi μ := by
  classical
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (measurable_update' (a := i)) (MeasurableSet.univ_pi hs)]
  have hpre :
      (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
        = (Set.univ.pi (Function.update s i Set.univ)) ×ˢ (s i) := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simp only [Function.update_self]
          exact Set.mem_univ _
        · simp only [Function.update_of_ne hj]
          have hj2 := h j
          simpa only [Function.update_of_ne hj] using hj2
      · have hi2 := h i
        simpa only [Function.update_self] using hi2
    · rintro ⟨hx, hy⟩ j
      rcases eq_or_ne j i with rfl | hj
      · simpa only [Function.update_self] using hy
      · simp only [Function.update_of_ne hj]
        have hxj := hx j
        simpa only [Function.update_of_ne hj] using hxj
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have h1 : (fun j => μ j (Function.update s i Set.univ j))
      = Function.update (fun j => μ j (s j)) i 1 := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [Function.update_self, measure_univ]
    · simp [Function.update_of_ne hj]
  rw [h1, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    Finset.sdiff_singleton_eq_erase, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

theorem aux_in_efron_stein_update_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {f g : (∀ j, α j) → ℝ}
    (hfg : f =ᵐ[Measure.pi μ] g) :
    (fun p : (∀ j, α j) × α i => f (Function.update p.1 i p.2)) =ᵐ[(Measure.pi μ).prod (μ i)]
      (fun p : (∀ j, α j) × α i => g (Function.update p.1 i p.2)) := by
  have hmp : MeasurePreserving
      (fun p : (∀ j, α j) × α i => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) :=
    ⟨measurable_update' (a := i), aux_in_efron_stein_map_update μ i⟩
  simpa only [Function.comp_apply] using hmp.quasiMeasurePreserving.ae_eq hfg

theorem in_efron_stein
    (hBBLM2005 :
      ∀ (p : ℝ), 2 ≤ p → ∃ (Kp : ℝ), 0 < Kp ∧
        ∀ (m : ℕ) (Xi : Fin m → Type) [∀ i, MeasurableSpace (Xi i)]
          (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)],
          let P := Measure.pi mu
          ∀ (F : ((i : Fin m) → Xi i) → ℝ),
            Measurable F → MemLp F (ENNReal.ofReal p) P →
            (eLpNorm (fun x => max (F x - ∫ y, F y ∂P) 0)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal Kp *
                eLpNorm (fun x => Real.sqrt
                  (∑ i : Fin m, ∫ y : Xi i,
                    (max (F x - F (Function.update x i y)) 0) ^ 2 ∂mu i))
                  (ENNReal.ofReal p) P) ∧
            (eLpNorm (fun x => max ((∫ y, F y ∂P) - F x) 0)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal Kp *
                eLpNorm (fun x => Real.sqrt
                  (∑ i : Fin m, ∫ y : Xi i,
                    (max (F (Function.update x i y) - F x) 0) ^ 2 ∂mu i))
                  (ENNReal.ofReal p) P)) :
    ∀ (p : ℝ), 2 ≤ p → ∃ (Cp : ℝ), 0 < Cp ∧
      ∀ (m : ℕ) (Xi : Fin m → Type) [∀ i, MeasurableSpace (Xi i)]
        (mu : (i : Fin m) → Measure (Xi i)) [∀ i, IsProbabilityMeasure (mu i)],
        let P := Measure.pi mu
        (∀ (F : ((i : Fin m) → Xi i) → ℝ),
          AEStronglyMeasurable F P → MemLp F (ENNReal.ofReal p) P →
          eLpNorm (fun x => F x - ∫ y, F y ∂P) (ENNReal.ofReal p) P ≤
            ENNReal.ofReal Cp *
              eLpNorm (fun x => Real.sqrt
                (∑ i : Fin m, ∫ y : Xi i, (F x - F (Function.update x i y)) ^ 2 ∂mu i))
                (ENNReal.ofReal p) P) ∧
        (∀ (Z : Type) [MeasurableSpace Z] (nu : Measure Z) [IsProbabilityMeasure nu]
          (F : Z → ((i : Fin m) → Xi i) → ℝ),
          AEStronglyMeasurable (fun zx : Z × ((i : Fin m) → Xi i) => F zx.1 zx.2)
            (nu.prod P) →
          MemLp (fun zx : Z × ((i : Fin m) → Xi i) => F zx.1 zx.2)
            (ENNReal.ofReal p) (nu.prod P) →
          ∀ᵐ z ∂nu,
            eLpNorm (fun x => F z x - ∫ y, F z y ∂P) (ENNReal.ofReal p) P ≤
              ENNReal.ofReal Cp *
                eLpNorm (fun x => Real.sqrt
                  (∑ i : Fin m, ∫ y : Xi i,
                    (F z x - F z (Function.update x i y)) ^ 2 ∂mu i))
                  (ENNReal.ofReal p) P) := by
  intro p hp
  obtain ⟨K, hK, hKall⟩ := hBBLM2005 p hp
  refine ⟨2 * K, by linarith, ?_⟩
  intro m Xi instXi mu instMu
  dsimp
  have hUncond :
      ∀ (F : ((i : Fin m) → Xi i) → ℝ),
        AEStronglyMeasurable F (Measure.pi mu) →
        MemLp F (ENNReal.ofReal p) (Measure.pi mu) →
        eLpNorm (fun x => F x - ∫ y, F y ∂Measure.pi mu) (ENNReal.ofReal p)
            (Measure.pi mu) ≤
          ENNReal.ofReal (2 * K) *
            eLpNorm (fun x => Real.sqrt
              (∑ i : Fin m, ∫ y : Xi i,
                (F x - F (Function.update x i y)) ^ 2 ∂mu i))
              (ENNReal.ofReal p) (Measure.pi mu) := by
    intro F hF hLp
    let G := hF.mk F
    have hG : Measurable G := hF.measurable_mk
    have hFG : F =ᵐ[Measure.pi mu] G := hF.ae_eq_mk
    have hLpG : MemLp G (ENNReal.ofReal p) (Measure.pi mu) := hLp.ae_eq hFG
    have h := hKall m Xi mu G hG hLpG
    have hp0 : 0 < ENNReal.ofReal p := by
      exact ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_two hp)
    have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    have hG2 : MemLp G (2 : ℝ≥0∞) (Measure.pi mu) :=
      hLpG.mono_exponent (by simpa using ENNReal.ofReal_le_ofReal hp)
    have hfull_int : ∀ i : Fin m, ∀ᵐ x ∂Measure.pi mu,
        Integrable (fun y : Xi i =>
          (G x - G (Function.update x i y)) ^ 2) (mu i) := by
      intro i
      let u : ((∀ j : Fin m, Xi j) × Xi i) → (∀ j : Fin m, Xi j) :=
        fun q => Function.update q.1 i q.2
      have hmp : MeasurePreserving u ((Measure.pi mu).prod (mu i)) (Measure.pi mu) :=
        ⟨measurable_update' (a := i), aux_in_efron_stein_map_update mu i⟩
      have hu : MemLp (fun q : (∀ j : Fin m, Xi j) × Xi i => G (u q))
          (2 : ℝ≥0∞) ((Measure.pi mu).prod (mu i)) := by
        have ht := hG2.comp_measurePreserving hmp
        simpa only [Function.comp_apply] using ht
      have hfst : MemLp (fun q : (∀ j : Fin m, Xi j) × Xi i => G q.1)
          (2 : ℝ≥0∞) ((Measure.pi mu).prod (mu i)) :=
        hG2.comp_fst (mu i)
      have hd : MemLp (fun q : (∀ j : Fin m, Xi j) × Xi i => G (u q) - G q.1)
          (2 : ℝ≥0∞) ((Measure.pi mu).prod (mu i)) := by
        simpa only [u] using hu.sub hfst
      have hdsq := hd.integrable_sq
      have hfa := hdsq.prod_right_ae
      filter_upwards [hfa] with x hx
      convert hx using 1
      funext y
      dsimp [u]
      ring
    have hsum_pos : ∀ᵐ x ∂Measure.pi mu,
        (∑ i : Fin m, ∫ y : Xi i,
          (max (G x - G (Function.update x i y)) 0) ^ 2 ∂mu i) ≤
          ∑ i : Fin m, ∫ y : Xi i,
            (G x - G (Function.update x i y)) ^ 2 ∂mu i := by
      filter_upwards [ae_all_iff.2 hfull_int] with x hx
      apply Finset.sum_le_sum
      intro i hi
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun y => sq_nonneg (max (G x - G (Function.update x i y)) 0))
      · exact hx i
      · exact ae_of_all _ (fun y => by
          have hsq : (max (G x - G (Function.update x i y)) 0) ^ 2 ≤
              (G x - G (Function.update x i y)) ^ 2 := by
            by_cases hxy : 0 ≤ G x - G (Function.update x i y)
            · rw [max_eq_left hxy]
            · rw [max_eq_right (le_of_not_ge hxy)]
              simpa using sq_nonneg (G x - G (Function.update x i y))
          exact hsq)
    have hsum_neg : ∀ᵐ x ∂Measure.pi mu,
        (∑ i : Fin m, ∫ y : Xi i,
          (max (G (Function.update x i y) - G x) 0) ^ 2 ∂mu i) ≤
          ∑ i : Fin m, ∫ y : Xi i,
            (G x - G (Function.update x i y)) ^ 2 ∂mu i := by
      filter_upwards [ae_all_iff.2 hfull_int] with x hx
      apply Finset.sum_le_sum
      intro i hi
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun y => sq_nonneg (max (G (Function.update x i y) - G x) 0))
      · exact hx i
      · exact ae_of_all _ (fun y => by
          have hsq : (max (G (Function.update x i y) - G x) 0) ^ 2 ≤
              (G x - G (Function.update x i y)) ^ 2 := by
            by_cases hxy : 0 ≤ G (Function.update x i y) - G x
            · rw [max_eq_left hxy]
              nlinarith [sq_nonneg (G x - G (Function.update x i y))]
            · rw [max_eq_right (le_of_not_ge hxy)]
              simpa using sq_nonneg (G x - G (Function.update x i y))
          exact hsq)
    have hproxy_pos :
        eLpNorm (fun x => Real.sqrt
          (∑ i : Fin m, ∫ y : Xi i,
            (max (G x - G (Function.update x i y)) 0) ^ 2 ∂mu i))
          (ENNReal.ofReal p) (Measure.pi mu) ≤
        eLpNorm (fun x => Real.sqrt
          (∑ i : Fin m, ∫ y : Xi i,
            (G x - G (Function.update x i y)) ^ 2 ∂mu i))
          (ENNReal.ofReal p) (Measure.pi mu) := by
      apply eLpNorm_mono_enorm_ae
      filter_upwards [hsum_pos] with x hx
      rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hx)
    have hproxy_neg :
        eLpNorm (fun x => Real.sqrt
          (∑ i : Fin m, ∫ y : Xi i,
            (max (G (Function.update x i y) - G x) 0) ^ 2 ∂mu i))
          (ENNReal.ofReal p) (Measure.pi mu) ≤
        eLpNorm (fun x => Real.sqrt
          (∑ i : Fin m, ∫ y : Xi i,
            (G x - G (Function.update x i y)) ^ 2 ∂mu i))
          (ENNReal.ofReal p) (Measure.pi mu) := by
      apply eLpNorm_mono_enorm_ae
      filter_upwards [hsum_neg] with x hx
      rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hx)
    have hpos := h.1.trans (mul_le_mul_right hproxy_pos (ENNReal.ofReal K))
    have hneg := h.2.trans (mul_le_mul_right hproxy_neg (ENNReal.ofReal K))
    have hpos_meas : AEStronglyMeasurable
        (fun x => max (G x - ∫ y, G y ∂Measure.pi mu) 0) (Measure.pi mu) := by
      fun_prop
    have hneg_meas : AEStronglyMeasurable
        (fun x => max ((∫ y, G y ∂Measure.pi mu) - G x) 0) (Measure.pi mu) := by
      fun_prop
    have hp1 : (1 : ℝ) ≤ p := by linarith
    have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa using ENNReal.ofReal_le_ofReal hp1
    have hcenter :
        eLpNorm (fun x => G x - ∫ y, G y ∂Measure.pi mu)
            (ENNReal.ofReal p) (Measure.pi mu) ≤
          eLpNorm (fun x => max (G x - ∫ y, G y ∂Measure.pi mu) 0)
              (ENNReal.ofReal p) (Measure.pi mu) +
            eLpNorm (fun x => max ((∫ y, G y ∂Measure.pi mu) - G x) 0)
              (ENNReal.ofReal p) (Measure.pi mu) := by
      calc
        eLpNorm (fun x => G x - ∫ y, G y ∂Measure.pi mu)
            (ENNReal.ofReal p) (Measure.pi mu) =
          eLpNorm ((fun x => max (G x - ∫ y, G y ∂Measure.pi mu) 0) -
            (fun x => max ((∫ y, G y ∂Measure.pi mu) - G x) 0))
              (ENNReal.ofReal p) (Measure.pi mu) := by
            apply eLpNorm_congr_ae
            exact ae_of_all _ (fun x => by
              have hx : G x - ∫ y, G y ∂Measure.pi mu =
                  max (G x - ∫ y, G y ∂Measure.pi mu) 0 -
                    max ((∫ y, G y ∂Measure.pi mu) - G x) 0 := by
                by_cases hxa : 0 ≤ G x - ∫ y, G y ∂Measure.pi mu
                · rw [max_eq_left hxa, max_eq_right (by linarith)]
                  ring
                · rw [max_eq_right (le_of_not_ge hxa), max_eq_left (by linarith)]
                  ring
              exact hx)
        _ ≤ _ := eLpNorm_sub_le hpos_meas hneg_meas hp1'
    have hGbound :
        eLpNorm (fun x => G x - ∫ y, G y ∂Measure.pi mu)
            (ENNReal.ofReal p) (Measure.pi mu) ≤
          ENNReal.ofReal (2 * K) *
            eLpNorm (fun x => Real.sqrt
              (∑ i : Fin m, ∫ y : Xi i,
                (G x - G (Function.update x i y)) ^ 2 ∂mu i))
              (ENNReal.ofReal p) (Measure.pi mu) := by
      calc
      eLpNorm (fun x => G x - ∫ y, G y ∂Measure.pi mu)
          (ENNReal.ofReal p) (Measure.pi mu) ≤
        ENNReal.ofReal K *
            eLpNorm (fun x => Real.sqrt
              (∑ i : Fin m, ∫ y : Xi i,
                (G x - G (Function.update x i y)) ^ 2 ∂mu i))
              (ENNReal.ofReal p) (Measure.pi mu) +
          ENNReal.ofReal K *
            eLpNorm (fun x => Real.sqrt
              (∑ i : Fin m, ∫ y : Xi i,
                (G x - G (Function.update x i y)) ^ 2 ∂mu i))
              (ENNReal.ofReal p) (Measure.pi mu) :=
        hcenter.trans (add_le_add hpos hneg)
      _ = ENNReal.ofReal (2 * K) *
            eLpNorm (fun x => Real.sqrt
              (∑ i : Fin m, ∫ y : Xi i,
                (G x - G (Function.update x i y)) ^ 2 ∂mu i))
              (ENNReal.ofReal p) (Measure.pi mu) := by
        rw [← two_mul]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num [ENNReal.ofReal_ofNat]
        ring_nf
    have hmean : (∫ y, F y ∂Measure.pi mu) = ∫ y, G y ∂Measure.pi mu :=
      integral_congr_ae hFG
    have hcenter_eq :
        eLpNorm (fun x => F x - ∫ y, F y ∂Measure.pi mu)
            (ENNReal.ofReal p) (Measure.pi mu) =
          eLpNorm (fun x => G x - ∫ y, G y ∂Measure.pi mu)
            (ENNReal.ofReal p) (Measure.pi mu) := by
      apply eLpNorm_congr_ae
      filter_upwards [hFG] with x hx
      rw [hx, hmean]
    have hupdate_all : ∀ᵐ x ∂Measure.pi mu, ∀ i : Fin m, ∀ᵐ y ∂mu i,
        F (Function.update x i y) = G (Function.update x i y) := by
      apply ae_all_iff.2
      intro i
      exact Measure.ae_ae_of_ae_prod (aux_in_efron_stein_update_ae mu i hFG)
    have hproxy_eq :
        eLpNorm (fun x => Real.sqrt
          (∑ i : Fin m, ∫ y : Xi i,
            (F x - F (Function.update x i y)) ^ 2 ∂mu i))
            (ENNReal.ofReal p) (Measure.pi mu) =
          eLpNorm (fun x => Real.sqrt
            (∑ i : Fin m, ∫ y : Xi i,
              (G x - G (Function.update x i y)) ^ 2 ∂mu i))
            (ENNReal.ofReal p) (Measure.pi mu) := by
      apply eLpNorm_congr_ae
      filter_upwards [hFG, hupdate_all] with x hx hxi
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      filter_upwards [hxi i] with y hy
      rw [hx, hy]
    rw [hcenter_eq, hproxy_eq]
    exact hGbound
  constructor
  · exact hUncond
  · intro Z instZ nu instnu F hF hLp
    have hq0 : ENNReal.ofReal p ≠ 0 :=
      (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_two hp)))
    have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    have hFfib : ∀ᵐ z ∂nu, AEStronglyMeasurable (fun x => F z x) (Measure.pi mu) := by
      simpa only using hF.prodMk_left
    have hLpint : Integrable
        (fun zx : Z × ((i : Fin m) → Xi i) =>
          ‖F zx.1 zx.2‖ ^ (ENNReal.ofReal p).toReal) (nu.prod (Measure.pi mu)) :=
      hLp.integrable_norm_rpow hq0 hqtop
    have hLpintfib : ∀ᵐ z ∂nu, Integrable
        (fun x => ‖F z x‖ ^ (ENNReal.ofReal p).toReal) (Measure.pi mu) := by
      simpa only using hLpint.prod_right_ae
    filter_upwards [hFfib, hLpintfib] with z hzF hzI
    apply hUncond (F z) hzF
    refine ⟨hzF, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqtop]
    have hEq :
        (fun x => (‖F z x‖ₑ) ^ (ENNReal.ofReal p).toReal) =
          (fun x => ‖‖F z x‖ ^ (ENNReal.ofReal p).toReal‖ₑ) := by
      funext x
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
          ENNReal.toReal_nonneg]
    rw [hEq]
    exact hzI.hasFiniteIntegral

end

end Paper
