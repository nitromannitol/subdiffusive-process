module

public import SubdiffusiveProcess.Paper.l_concentration_rare_intervals
public import SubdiffusiveProcess.ConcentrationScales.FieldSingleEvent
public import SubdiffusiveProcess.ConcentrationScales.FieldArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Paper

open Classical in


theorem p_concentration_for_scales_exp_field (d : ℕ) {Ω : Type*} [MeasurableSpace Ω] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℤ → Ω → (Vec d → ℝ)) (δ₀ : ℝ),
        0 < δ₀ → δ₀ ≤ 1 → (∀ i, Measurable (fun p : Ω × Vec d => X i p.1 p.2)) →
        iIndepFun X μ →
        (∀ (i : ℤ) (z : Vec d), (∀ a : Fin d, ∃ n : ℤ, z a = (3 : ℝ) ^ i * n) →
          μ.map (fun ω x => X i ω (x + z)) = μ.map (X i)) →
        (∀ i, ∫⁻ ω, essSup (fun x => ENNReal.ofReal (Real.exp ((δ₀⁻¹ * |X i ω x|) ^ 2)))
            (volume.restrict (cube d i)) ∂μ ≤ 2) →
        ∀ (m₀ : ℤ) (M h : ℕ) (θ s : ℝ), 1 ≤ h → 0 < θ → θ ≤ 1 → 0 < s → s ≤ 1 →
          δ₀ ≤ C⁻¹ * s * Real.sqrt (min θ ((h : ℝ)⁻¹)) →
          μ {ω | θ ≤ (1 / ((M : ℝ) + 1)) *
              ∑ k ∈ Finset.Icc m₀ (m₀ + (M : ℤ)),
                (if ∃ j : ℕ, ENNReal.ofReal (3 * (3 : ℝ) ^ (s * j)) <
                    essSup (fun x => ENNReal.ofReal
                      (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |X i ω x|))
                      (volume.restrict (cube d (k + h + j)))
                  then (1 : ℝ) else 0)} ≤
            ENNReal.ofReal (Real.exp (-(s ^ 2 * θ / (C * δ₀ ^ 2)) * ((M : ℝ) + 1))) := by
  classical
  obtain ⟨cr, Cr, hcr, hCr, hRare⟩ := l_concentration_rare_intervals
  obtain ⟨C, hCpos, hC1, hC2, hC3⟩ :=
    SubdiffusiveProcess.ConcentrationScales.exists_field_constant d hcr hCr
  refine ⟨C, hCpos, ?_⟩
  intro μ _ X δ hδ hδ1 hXm hind hstat hΓ m₀ M h θ s h1 hθ hθ1 hs hs1 hsmall
  obtain ⟨hEnt, hlamθ, hkey⟩ := SubdiffusiveProcess.ConcentrationScales.field_smallness d h h1
    hCpos hcr hδ hs hθ hC1 hC2 hC3 hsmall
  have hlampos : 0 < SubdiffusiveProcess.ConcentrationScales.fieldRate * s ^ 2 / δ ^ 2 := by
    have := SubdiffusiveProcess.ConcentrationScales.fieldRate_pos
    positivity
  set lam : ℝ := SubdiffusiveProcess.ConcentrationScales.fieldRate * s ^ 2 / δ ^ 2 with hlam
  have ht : ∀ j : ℕ, 0 < (1 + s * j) * Real.log 3 := fun j =>
    mul_pos (by positivity) (Real.log_pos (by norm_num))
  choose E hEmeas hEae hEprob using fun (k : ℤ) (j : ℕ) =>
    SubdiffusiveProcess.ConcentrationScales.exists_local_event_gaussian hδ hXm hind hstat hΓ k j h
      (ht j)
  have hEprob' : ∀ (k : ℤ) (j : ℕ),
      μ (E k j) ≤ ENNReal.ofReal (Real.exp (-(lam * ((j : ℝ) + 1)))) := by
    intro k j
    refine (hEprob k j).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    exact SubdiffusiveProcess.ConcentrationScales.field_exponent_le d h j h1 hs hs1 hδ hEnt
  have hrare := hRare μ X hind
    (fun i => SubdiffusiveProcess.ConcentrationScales.measurable_field_of_uncurry (hXm i))
    lam hlampos E (Or.inr hEmeas) hEprob' θ hθ hθ1 hlamθ m₀ (M + 1) (by omega)
  have hae : ∀ᵐ ω ∂μ, ∀ (k : ℤ) (j : ℕ),
      ENNReal.ofReal (Real.exp ((1 + s * j) * Real.log 3)) <
        essSup (fun x => ENNReal.ofReal (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |X i ω x|))
          (volume.restrict (cube d (k + h + j))) → ω ∈ E k j := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro j
    exact hEae k j
  refine (measure_mono_ae ?_).trans (hrare.trans ?_)
  · filter_upwards [hae] with ω hω hmem
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
        (p := fun k : ℤ => ∃ j : ℕ, ENNReal.ofReal (3 * (3 : ℝ) ^ (s * j)) <
          essSup (fun x => ENNReal.ofReal
            (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |X i ω x|))
            (volume.restrict (cube d (k + h + j))))
        (q := fun k : ℤ => ∃ j : ℕ, ω ∈ E k j)
        (fun k _ hk => by
          obtain ⟨j, hj⟩ := hk
          rw [SubdiffusiveProcess.ConcentrationScales.three_mul_rpow_eq_exp] at hj
          exact ⟨j, hω k j hj⟩))
    have hcard' : ((Finset.filter (fun k : ℤ => ∃ j : ℕ, ENNReal.ofReal (3 * (3 : ℝ) ^ (s * j)) <
          essSup (fun x => ENNReal.ofReal
            (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |X i ω x|))
            (volume.restrict (cube d (k + h + j)))) (Finset.Icc m₀ (m₀ + (M : ℤ)))).card : ℝ) ≤
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
