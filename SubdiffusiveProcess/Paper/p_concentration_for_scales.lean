import SubdiffusiveProcess.CoarseGrainingVocab.Concentration

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Concentration
open scoped ENNReal NNReal

noncomputable section

namespace Paper

/-- The paper's two-set `r`-dependence of the columns implies mutual independence of the columns
within each residue class modulo `r` (the form consumed by the proof of the Lean concentration theorem). -/
private theorem aux_p_concentration_for_scales_columnsIndep
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℤ → ℤ → Ω → ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hdep : ∀ I J : Set ℤ, (∀ i ∈ I, ∀ j ∈ J, (r : ℝ) ≤ |(i : ℝ) - (j : ℝ)|) →
      Indep (⨆ k : ℤ, ⨆ j ∈ I, MeasurableSpace.comap (X k j) inferInstance)
        (⨆ k : ℤ, ⨆ j ∈ J, MeasurableSpace.comap (X k j) inferInstance) P) :
    ColumnsIndep P X r := by
  intro b
  set f : ℤ → Ω → (ℤ → ℝ) := fun j ω k => X k (j * r + b) ω with hf
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | h0 =>
    intro sets _
    simp
  | step a T hlt ih =>
    intro sets hsets
    have haT : a ∉ T := fun h => lt_irrefl a (hlt a h)
    rw [Finset.set_biInter_insert, Finset.prod_insert haT]
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    let mI : MeasurableSpace Ω :=
      ⨆ k : ℤ, ⨆ j ∈ ({a * (r : ℤ) + b} : Set ℤ), MeasurableSpace.comap (X k j) inferInstance
    let mJ : MeasurableSpace Ω :=
      ⨆ k : ℤ, ⨆ j ∈ ((fun t : ℤ => t * (r : ℤ) + b) '' (T : Set ℤ)),
        MeasurableSpace.comap (X k j) inferInstance
    have hdist : ∀ i ∈ ({a * (r : ℤ) + b} : Set ℤ),
        ∀ j ∈ ((fun t : ℤ => t * (r : ℤ) + b) '' (T : Set ℤ)),
          (r : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
      intro i hi j hj
      rw [Set.mem_singleton_iff] at hi
      obtain ⟨t, ht, rfl⟩ := hj
      subst hi
      have hta : t + 1 ≤ a := hlt t ht
      have hta' : (t : ℝ) + 1 ≤ a := by exact_mod_cast hta
      push_cast
      have : ((a : ℝ) * r + b) - ((t : ℝ) * r + b) = ((a : ℝ) - t) * r := by ring
      rw [this, abs_of_nonneg (by nlinarith)]
      nlinarith
    have hind : Indep mI mJ P := hdep _ _ hdist
    have hfa : @Measurable Ω (ℤ → ℝ) mI inferInstance (f a) := by
      rw [@measurable_pi_iff]
      intro k
      rw [measurable_iff_comap_le]
      exact le_iSup_of_le k (le_iSup₂_of_le (a * (r : ℤ) + b) (Set.mem_singleton _) le_rfl)
    have hft : ∀ t ∈ T, @Measurable Ω (ℤ → ℝ) mJ inferInstance (f t) := by
      intro t ht
      rw [@measurable_pi_iff]
      intro k
      rw [measurable_iff_comap_le]
      exact le_iSup_of_le k (le_iSup₂_of_le (t * (r : ℤ) + b) ⟨t, ht, rfl⟩ le_rfl)
    have hA : MeasurableSet[mI] (f a ⁻¹' sets a) :=
      hfa (hsets a (Finset.mem_insert_self a T))
    have hB : MeasurableSet[mJ] (⋂ t ∈ T, f t ⁻¹' sets t) := by
      refine Finset.measurableSet_biInter T (fun t ht => ?_)
      exact hft t ht (hsets t (Finset.mem_insert_of_mem ht))
    rw [(Indep_iff mI mJ P).1 hind _ _ hA hB]
    rw [ih (fun j hj => hsets j (Finset.mem_insert_of_mem hj))]



theorem p_concentration_for_scales {Ω : Type*} [MeasurableSpace Ω] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure Ω) [IsProbabilityMeasure P] (X : ℤ → ℤ → Ω → ℝ) (p s : ℝ) (r : ℕ),
        1 ≤ p → 1 / p ≤ s → s ≤ 1 → 1 ≤ r →
        (∀ k j, Measurable (X k j)) → (∀ k j ω, 0 ≤ X k j ω) →
        (∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1) →
        (∀ I J : Set ℤ, (∀ i ∈ I, ∀ j ∈ J, (r : ℝ) ≤ |(i : ℝ) - (j : ℝ)|) →
          Indep (⨆ k : ℤ, ⨆ j ∈ I, MeasurableSpace.comap (X k j) inferInstance)
            (⨆ k : ℤ, ⨆ j ∈ J, MeasurableSpace.comap (X k j) inferInstance) P) →
        ∀ (m₀ : ℤ) (m : ℕ) (θ : ℝ), 0 < θ → θ ≤ 1 →
          P {ω | θ < (1 / ((m : ℝ) + 1)) *
              ∑ k ∈ Finset.Icc m₀ (m₀ + (m : ℤ)),
                (if 6 * s⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < ∑' j : ℤ, (3 : ℝ) ^ (-(s * |(k : ℝ) - (j : ℝ)|)) * X k j ω
                  then (1 : ℝ) else 0)} ≤
            ENNReal.ofReal (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))) := by
  refine ⟨Cstar, Cstar_pos, ?_⟩
  intro P _ X p s r hp hsLower hs1 hr hmeas hnn hmom hdep m₀ m θ hθ0 hθ1
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hsLower
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hsp : 1 ≤ s * p := (div_le_iff₀ hp0).1 hsLower
  exact concentration_for_scales_Cstar P X hp hs0 hs1 hsp hr hmeas hnn hmom
    (aux_p_concentration_for_scales_columnsIndep hr hdep) m₀ m θ hθ0 hθ1

end Paper
