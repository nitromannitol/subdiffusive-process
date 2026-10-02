import SubdiffusiveProcess.Paper.prefix_bad_density_tail
import SubdiffusiveProcess.Paper.prefix_bad_score_zero
import SubdiffusiveProcess.Paper.prefix_tail_score_bridge
import SubdiffusiveProcess.PrefixTailNumerics
import SubdiffusiveProcess.Paper.prefix_accumulated_error_tail

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem prefix_score_window_tail {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) [NeZero d] (s eps lam A : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam) (hA : 0 < A) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
      ∀ (P : Measure Ω) (g : Ω → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
      AEMeasurable g P → Measure.map g P = M.P.toMeasure →
      ∀ (Fsc Psc Rsc Dsc : ℕ → Vec d → Ω → ENNReal)
        (Zsc : ℕ → Vec d → Ω → ℝ) (goodEvt : ℕ → Vec d → Ω → Prop),
      (∀ᵐ om ∂P, primitive_scores d M s eps (g om)
        (fun j z => Fsc j z om) (fun j z => Psc j z om)
        (fun j z => Rsc j z om) (fun j z => Dsc j z om)
        (fun j z => Zsc j z om) (fun j z => goodEvt j z om)) →
      ∀ (n K : ℕ) (z : Vec d) (useD : Bool),
        (P {om | lam * ((K : ℝ) + 1) / 4 <
            ∑ j ∈ Finset.Icc n (n + K),
              if useD then (Dsc j z om).toReal else Zsc j z om} ≤
          ENNReal.ofReal (2 * Real.exp (-(A * ((K : ℝ) + 1))))) ∧
        (P {om | lam * ((K : ℝ) + 1) / 4 <
            ∑ j ∈ Finset.Icc n (n + K),
              if useD then (Dsc j z om).toReal else Zsc j z om} ≤
          ENNReal.ofReal (1 / 2 : ℝ)) := by
  let s0 : ℝ := min s (1 / 2)
  let theta : ℝ := min (lam / 12) 1
  let B : ℝ := max A (Real.log 4)
  have hs0 : s0 ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨lt_min hs.1 (by norm_num), min_le_right _ _⟩
  have hss : s0 ≤ s := min_le_left _ _
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_min (by positivity) (by norm_num), min_le_right _ _⟩
  have hB : 0 < B := hA.trans_le (le_max_left _ _)
  obtain ⟨δZ, hδZ, htZ⟩ := prefix_bad_density_tail d s0 (eps / 2) theta B
    ⟨hs0.1, hs0.2.trans (by norm_num)⟩ ⟨by linarith [heps.1], by linarith [heps.2]⟩
    htheta hB
  obtain ⟨δD, hδD, htD⟩ := prefix_accumulated_error_tail d s0 lam A hs0 hlam hA
  refine ⟨min δZ δD, lt_min hδZ hδD, ?_⟩
  intro M hδ P g hg hlaw Fsc Psc Rsc Dsc Zsc goodEvt hPS n K z useD
  have hW : 0 < (K : ℝ) + 1 := by positivity
  have hW1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  cases useD with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hdom : P {om | lam * ((K : ℝ) + 1) / 4 <
        ∑ j ∈ Finset.Icc n (n + K), Zsc j z om} ≤
        M.P.toMeasure {x | (∑ j ∈ Finset.Icc n (n + K),
          if x ∈ goodEvent M none j z (eps / 2) s0 then (1 : ℝ) else 0) /
            ((K : ℝ) + 1) ≤ 1 - theta} := by
      apply aux_prefix_score_window_tail_map P M.P.toMeasure g hg hlaw
      filter_upwards [hPS] with om hp
      intro hlarge
      have hz : ∀ j, Zsc j z om ≤ 3 * (1 -
          if g om ∈ goodEvent M none j z (eps / 2) s0 then (1 : ℝ) else 0) := by
        intro j
        by_cases hgood : g om ∈ goodEvent M none j z (eps / 2) s0
        · simp only [hgood, ↓reduceIte, sub_self, mul_zero]
          exact (prefix_bad_score_zero M s s0 eps hs0.2 hss (g om)
            _ _ _ _ _ _ hp j z hgood).le
        · simp only [hgood, ↓reduceIte, sub_zero, mul_one]
          obtain ⟨_, _, _, _, _, _, _, _, _, hz, _⟩ := hp
          exact (hz j z).2.2
      have hcard : (Finset.Icc n (n + K)).card = K + 1 := by
        rw [Nat.card_Icc]; omega
      have hsum : (∑ j ∈ Finset.Icc n (n + K), Zsc j z om) ≤
          3 * (((K : ℝ) + 1) - ∑ j ∈ Finset.Icc n (n + K),
            if g om ∈ goodEvent M none j z (eps / 2) s0 then (1 : ℝ) else 0) := by
        calc _ ≤ ∑ j ∈ Finset.Icc n (n + K), 3 * (1 -
              if g om ∈ goodEvent M none j z (eps / 2) s0 then (1 : ℝ) else 0) :=
            Finset.sum_le_sum (fun j _ => hz j)
          _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]; simp [hcard]
      apply (div_le_iff₀ hW).mpr
      have hθ : theta ≤ lam / 12 := min_le_left _ _
      have hm := mul_le_mul_of_nonneg_right hθ hW.le
      change lam * ((K : ℝ) + 1) / 4 < _ at hlarge
      nlinarith
    have htail := hdom.trans (htZ M (hδ.trans (min_le_left _ _)) n K z)
    constructor
    · refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp : Real.exp (-(B * ((K : ℝ) + 1))) ≤
          Real.exp (-(A * ((K : ℝ) + 1))) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right (le_max_left A (Real.log 4)) hW.le
        linarith
      nlinarith [Real.exp_pos (-(A * ((K : ℝ) + 1)))]
    · refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hBW : Real.log 4 ≤ B * ((K : ℝ) + 1) :=
        (le_max_right A (Real.log 4)).trans (le_mul_of_one_le_right hB.le hW1)
      have hh := Real.exp_le_exp.mpr (neg_le_neg hBW)
      have he : Real.exp (-Real.log 4) = (1 / 4 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        norm_num
      rw [he] at hh
      linarith
  | true =>
    simp only [↓reduceIte]
    have hnative : ∀ᵐ x ∂M.P.toMeasure, ∀ j : ℕ,
        (∑' i : ℕ, aux_psf_Dmaj4 j z i x) ≠ ⊤ :=
      ae_all_iff.mpr (fun j => aux_psf_Dmaj4_tsum_ae M j z)
    rw [← hlaw] at hnative
    have hfin := ae_of_ae_map hg hnative
    have hdom : P {om | lam * ((K : ℝ) + 1) / 4 <
        ∑ j ∈ Finset.Icc n (n + K), (Dsc j z om).toReal} ≤
        M.P.toMeasure {x | lam * ((K : ℝ) + 1) / 4 <
          ∑ j ∈ Finset.Icc n (n + K), accumulatedError M none j z s0 x} := by
      apply aux_prefix_score_window_tail_map P M.P.toMeasure g hg hlaw
      filter_upwards [hPS, hfin] with om hp hf
      intro hlarge
      apply lt_of_lt_of_le hlarge
      apply Finset.sum_le_sum
      intro j _
      have hraw : aux_prefix_score_accumulated_error_raw M s0 (g om) j z ≠ ⊤ :=
        aux_psf_Dsc_ne_top M s0 hs0.1 j z (g om) (hf j)
      have hmono := aux_prefix_score_accumulated_error_raw_antitone M hss (g om) j z
      obtain ⟨_, _, _, _, _, _, _, hd, _, _, _⟩ := hp
      have heq : Dsc j z om = aux_prefix_score_accumulated_error_raw M s (g om) j z := hd j z
      rw [heq, ← aux_prefix_score_accumulated_error_raw_eq M s0 (g om) j z hraw]
      exact ENNReal.toReal_mono hraw hmono
    have htail := htD M (hδ.trans (min_le_right _ _)) n (n + K) (by omega) z
    have heq : ((n + K : ℕ) : ℝ) - (n : ℝ) + 1 = (K : ℝ) + 1 := by push_cast; ring
    rw [heq] at htail
    exact ⟨hdom.trans htail.1, hdom.trans htail.2⟩

end Paper
