import SubdiffusiveProcess.Paper.l_concentration_rare_intervals
import SubdiffusiveProcess.ConcentrationScales.ExpSequence
import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
import Mathlib

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Paper

open Classical in


theorem p_concentration_for_scales_exp_sequence :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) (δ₀ : ℝ),
        0 < δ₀ → δ₀ ≤ 1 → (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i ω, 0 ≤ X i ω) → (∀ i, SubdiffusiveProcess.OGammaLE μ 2 δ₀ (X i)) →
        ∀ (m₀ : ℤ) (M : ℕ) (θ s : ℝ), 0 < θ → θ ≤ 1 → 0 < s → s ≤ 1 →
          δ₀ ≤ C⁻¹ * Real.sqrt (s * θ) →
          μ {ω | θ ≤ (1 / ((M : ℝ) + 1)) *
              ∑ k ∈ Finset.Icc m₀ (m₀ + (M : ℤ)),
                (if ∃ j : ℕ, ENNReal.ofReal ((1 + s * j) * Real.log 3) <
                    ∑' i : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(i : ℝ)) * X (k + i + j) ω)
                  then (1 : ℝ) else 0)} ≤
            ENNReal.ofReal (Real.exp (-(s * θ / (C * δ₀ ^ 2)) * ((M : ℝ) + 1))) := by
  classical
  obtain ⟨cr, Cr, hcr, hCr, hRare⟩ := l_concentration_rare_intervals.{u, 0}
  obtain ⟨C, hCpos, hC1, hC2, hC3⟩ :=
    SubdiffusiveProcess.ConcentrationScales.exists_seq_constant hcr hCr
  refine ⟨C, hCpos, ?_⟩
  intro Ω _ μ _ X δ hδ hδ1 hXm hind hX0 hO m₀ M θ s hθ hθ1 hs hs1 hsmall
  obtain ⟨hδs, hlamθ, hkey⟩ := SubdiffusiveProcess.ConcentrationScales.seq_smallness hCpos hcr hδ
    hs hθ hθ1 hC1 hC2 hC3 hsmall
  have hlampos : 0 < SubdiffusiveProcess.ConcentrationScales.seqRate * s / δ ^ 2 := by
    have := SubdiffusiveProcess.ConcentrationScales.seqRate_pos
    positivity
  set lam : ℝ := SubdiffusiveProcess.ConcentrationScales.seqRate * s / δ ^ 2 with hlam
  have hl3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  let E : ℤ → ℕ → Set Ω := fun k j => {ω | Real.log 3 / 3 * (1 + s * j) < X (k + j) ω}
  have hEmeas : ∀ (k : ℤ) (j : ℕ),
      MeasurableSet[⨆ i ∈ Set.Icc k (k + (j : ℤ)), MeasurableSpace.comap (X i) inferInstance]
        (E k j) := by
    intro k j
    have h1 : MeasurableSet[MeasurableSpace.comap (X (k + j)) inferInstance] (E k j) :=
      ⟨Set.Ioi (Real.log 3 / 3 * (1 + s * j)), measurableSet_Ioi, rfl⟩
    exact (le_iSup₂ (f := fun i (_ : i ∈ Set.Icc k (k + (j : ℤ))) =>
      MeasurableSpace.comap (X i) inferInstance) (k + j) ⟨by omega, le_rfl⟩) _ h1
  have hEprob : ∀ (k : ℤ) (j : ℕ), μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1)))) := by
    intro k j
    have hu : 0 ≤ Real.log 3 / 3 * (1 + s * j) := by positivity
    refine (SubdiffusiveProcess.ConcentrationScales.measure_lt_le_of_OGammaLE hδ (hO (k + j)) hu).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact SubdiffusiveProcess.ConcentrationScales.seq_single_le j hs hs1 hδ hδs
  have hrare := hRare μ X hind hXm lam hlampos E (Or.inl hEmeas) hEprob θ hθ hθ1 hlamθ m₀ (M + 1)
    (by omega)
  refine (measure_mono ?_).trans (hrare.trans ?_)
  · intro ω hmem
    have hIcc : Finset.Icc m₀ (m₀ + ((M + 1 : ℕ) : ℤ) - 1) = Finset.Icc m₀ (m₀ + (M : ℤ)) := by
      congr 1
      push_cast
      ring
    show θ * (((M + 1 : ℕ) : ℝ)) ≤
      (((Finset.Icc m₀ (m₀ + ((M + 1 : ℕ) : ℤ) - 1)).filter (fun k => ∃ j, ω ∈ E k j)).card : ℝ)
    rw [hIcc]
    have hmem : θ ≤ _ := hmem
    rw [Finset.sum_boole] at hmem
    have hcard := Finset.card_le_card
      (Finset.monotone_filter_right (Finset.Icc m₀ (m₀ + (M : ℤ)))
        (p := fun k : ℤ => ∃ j : ℕ, ENNReal.ofReal ((1 + s * j) * Real.log 3) <
          ∑' i : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(i : ℝ)) * X (k + i + j) ω))
        (q := fun k : ℤ => ∃ j : ℕ, ω ∈ E k j)
        (fun k _ hk => by
          by_contra hne
          push_neg at hne
          obtain ⟨j, hj⟩ := hk
          have hle : ∀ j : ℕ, X (k + j) ω ≤ Real.log 3 / 3 * (1 + s * j) := fun j =>
            not_lt.mp (hne j)
          have h1 := SubdiffusiveProcess.ConcentrationScales.tsum_ofReal_le_of_forall_le
            (fun i => X i ω) hs hs1 k hle j
          have hpos : 0 < (1 + s * j) * Real.log 3 := by positivity
          have h2 : ENNReal.ofReal (3 / 4 * (1 + s * j) * Real.log 3) <
              ENNReal.ofReal ((1 + s * j) * Real.log 3) :=
            (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by nlinarith)
          exact absurd (lt_of_lt_of_le hj h1) (not_lt.mpr h2.le)))
    have hcard' : ((Finset.filter (fun k : ℤ => ∃ j : ℕ, ENNReal.ofReal ((1 + s * j) * Real.log 3) <
          ∑' i : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(i : ℝ)) * X (k + i + j) ω))
          (Finset.Icc m₀ (m₀ + (M : ℤ)))).card : ℝ) ≤
        ((Finset.filter (fun k : ℤ => ∃ j : ℕ, ω ∈ E k j)
          (Finset.Icc m₀ (m₀ + (M : ℤ)))).card : ℝ) := by exact_mod_cast hcard
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)] at hmem
    push_cast
    exact hmem.trans hcard'
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hN : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hN]
    nlinarith [hkey, show 0 ≤ (M : ℝ) + 1 by positivity]

end Paper
