import SubdiffusiveProcess.Paper.inputs_baseline_response
import SubdiffusiveProcess.Paper.inputs_baseline_block
import SubdiffusiveProcess.Paper.inputs_baseline_anchor
import SubdiffusiveProcess.Paper.inputs_baseline_gradient
import SubdiffusiveProcess.Paper.Foundations.PrefixActualDMeas

open MeasureTheory
open scoped ENNReal BigOperators
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_baseline_native (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (s q : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) :
    ∃ C delta0 : ℝ, 0 < C ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ min 1 delta0 →
        ∀ (k : ℕ) (z : Vec d),
          let score : PotentialSample d → ENNReal := fun omega =>
            (sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)}) +
            (sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
              u = ENNReal.ofReal |shellBlock k j omega x|}}) +
            (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |omega 0 x|}) +
            (∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
          else 0)
          (∀ᵐ omega ∂M.P.toMeasure, score omega ≠ ∞) ∧
          MemLp (fun omega => (score omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun omega => (score omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
            ENNReal.ofReal (C * M.delta ^ (1 / 2 : ℝ)) := by
  obtain ⟨C1, delta1, hC1, hd1, h1⟩ := inputs_baseline_response d hd s q hs hq
  obtain ⟨C2, delta2, hC2, hd2, h2⟩ := inputs_baseline_block d hd s q hs hq
  obtain ⟨C3, delta3, hC3, hd3, h3⟩ := inputs_baseline_anchor d hd s q hs hq
  obtain ⟨C4, delta4, hC4, hd4, h4⟩ := inputs_baseline_gradient d hd s q hs hq
  refine ⟨C1 + C2 + C3 + C4, min (min delta1 delta2) (min delta3 delta4),
    by positivity, by positivity, ?_⟩
  intro M hsmall k z
  have hOne : M.delta ≤ 1 := hsmall.trans (min_le_left _ _)
  have hD : M.delta ≤ min (min delta1 delta2) (min delta3 delta4) :=
    hsmall.trans (min_le_right _ _)
  obtain ⟨hf1, hm1, hn1⟩ := h1 M
    (le_min hOne (hD.trans ((min_le_left _ _).trans (min_le_left _ _)))) k z
  obtain ⟨hf2, hm2, hn2⟩ := h2 M
    (le_min hOne (hD.trans ((min_le_left _ _).trans (min_le_right _ _)))) k z
  obtain ⟨hf3, hm3, hn3⟩ := h3 M
    (le_min hOne (hD.trans ((min_le_right _ _).trans (min_le_left _ _)))) k z
  obtain ⟨hf4, hm4, hn4⟩ := h4 M
    (le_min hOne (hD.trans ((min_le_right _ _).trans (min_le_right _ _)))) k z
  have hp : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq
  have add_terms {f g : PotentialSample d → ENNReal}
      (hf : ∀ᵐ omega ∂M.P.toMeasure, f omega ≠ ∞)
      (hg : ∀ᵐ omega ∂M.P.toMeasure, g omega ≠ ∞)
      (hmf : MemLp (fun omega => (f omega).toReal) (ENNReal.ofReal q) M.P.toMeasure)
      (hmg : MemLp (fun omega => (g omega).toReal) (ENNReal.ofReal q) M.P.toMeasure) :
      (∀ᵐ omega ∂M.P.toMeasure, f omega + g omega ≠ ∞) ∧
      MemLp (fun omega => (f omega + g omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ∧
      eLpNorm (fun omega => (f omega + g omega).toReal) (ENNReal.ofReal q) M.P.toMeasure ≤
        eLpNorm (fun omega => (f omega).toReal) (ENNReal.ofReal q) M.P.toMeasure +
        eLpNorm (fun omega => (g omega).toReal) (ENNReal.ofReal q) M.P.toMeasure := by
    have heq : (fun omega => (f omega + g omega).toReal) =ᵐ[M.P.toMeasure]
        (fun omega => (f omega).toReal + (g omega).toReal) := by
      filter_upwards [hf, hg] with omega hf hg
      exact ENNReal.toReal_add hf hg
    refine ⟨?_, (memLp_congr_ae heq).2 (hmf.add hmg), ?_⟩
    · filter_upwards [hf, hg] with omega hf hg
      exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩
    · rw [eLpNorm_congr_ae heq]
      exact eLpNorm_add_le hmf.aestronglyMeasurable hmg.aestronglyMeasurable hp
  have h12 := add_terms hf1 hf2 hm1 hm2
  have h123 := add_terms h12.1 hf3 h12.2.1 hm3
  have h1234 := add_terms h123.1 hf4 h123.2.1 hm4
  refine ⟨h1234.1, h1234.2.1, ?_⟩
  have hbound := h1234.2.2.trans (add_le_add
    (h123.2.2.trans (add_le_add
      (h12.2.2.trans (add_le_add hn1 hn2)) hn3)) hn4)
  refine hbound.trans_eq ?_
  have hpow : 0 ≤ M.delta ^ (1 / 2 : ℝ) := Real.rpow_nonneg M.shellPrefix.delta_pos.le _
  rw [← ENNReal.ofReal_add (mul_nonneg hC1.le hpow) (mul_nonneg hC2.le hpow),
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg hC3.le hpow),
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg hC4.le hpow)]
  congr 1
  ring

end Paper
