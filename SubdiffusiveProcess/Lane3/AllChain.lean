import SubdiffusiveProcess.Lane3.Elementary
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic




open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

theorem all_chain_estimate
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (θ bstar : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hb : 0 < bstar)
    (badCount : (J : ℕ) → (Fin J → Fin n) → Om → ℕ)
    (hle : ∀ J π ω, badCount J π ω ≤ J)
    (hmeasb : ∀ J π, Measurable (badCount J π))
    (hdev : ∀ J : ℕ, 1 ≤ J →
      P {ω | ∃ π : Fin J → Fin n, θ * (J : ℝ) ≤ (badCount J π ω : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ))))) :
    ∃ B : Om → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧
      (∀ᵐ ω ∂P, ∀ (J : ℕ) (π : Fin J → Fin n),
        1 ≤ J → (badCount J π ω : ℝ) ≤ θ * (J : ℝ) + B ω) ∧
      (∀ t : ℝ, 0 ≤ t →
        P {ω | t < B ω} ≤
          ENNReal.ofReal ((1 - Real.exp (-bstar))⁻¹ *
            Real.exp (-(bstar * t / (1 - θ))))) := by
  classical
  have hθ' : 0 < 1 - θ := by linarith
  have hr0 : (0 : ℝ) ≤ Real.exp (-bstar) := (Real.exp_pos _).le
  have hr1 : Real.exp (-bstar) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set E : ℕ → Set Om := fun J =>
    {ω | ∃ π : Fin J → Fin n, θ * (J : ℝ) ≤ (badCount J π ω : ℝ)} with hE
  have hEmeas : ∀ J, MeasurableSet (E J) := by
    intro J
    have hun : E J = ⋃ π : Fin J → Fin n,
        {ω | θ * (J : ℝ) ≤ (badCount J π ω : ℝ)} := by ext ω; simp [hE]
    rw [hun]
    exact MeasurableSet.iUnion fun π =>
      measurableSet_le measurable_const (measurable_from_top.comp (hmeasb J π))
  set g : ℕ → Om → ℝ≥0∞ := fun J =>
    Set.indicator (E J) (fun _ => ENNReal.ofReal ((1 - θ) * (J : ℝ))) with hg
  set Bne : Om → ℝ≥0∞ := fun ω => ⨆ J : ℕ, g J ω with hBne
  set B : Om → ℝ := fun ω => (Bne ω).toReal with hB
  have hBnemeas : Measurable Bne :=
    Measurable.iSup fun J => (measurable_const).indicator (hEmeas J)
  have hBmeas : Measurable B := hBnemeas.ennreal_toReal
  have hBnonneg : ∀ ω, 0 ≤ B ω := fun ω => ENNReal.toReal_nonneg
  have hPE : ∀ J : ℕ, 1 ≤ J → P (E J) ≤ ENNReal.ofReal (Real.exp (-(bstar * (J : ℝ)))) :=
    fun J hJ => hdev J hJ
  have hsum : (∑' J : ℕ, P (E J)) ≠ ⊤ := by
    have hle' : ∀ J : ℕ, P (E J) ≤ ENNReal.ofReal (Real.exp (-bstar) ^ J) := by
      intro J
      rcases Nat.eq_zero_or_pos J with hJ | hJ
      · subst hJ; simpa using prob_le_one
      · refine (hPE J hJ).trans (le_of_eq ?_)
        congr 1
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    have hgeo : (∑' J : ℕ, ENNReal.ofReal (Real.exp (-bstar) ^ J)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun J => pow_nonneg hr0 J)
        (summable_geometric_of_lt_one hr0 hr1)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hgeo (ENNReal.tsum_le_tsum hle')
  have hfin : ∀ᵐ ω ∂P, ∀ᶠ J in atTop, ω ∉ E J := by
    rw [ae_iff]
    have hrw : {ω | ¬ ∀ᶠ J in atTop, ω ∉ E J} = {ω | ∃ᶠ J in atTop, ω ∈ E J} := by
      ext ω
      simp only [Set.mem_setOf_eq, Filter.not_eventually, not_not]
    rw [hrw]
    exact measure_setOf_frequently_eq_zero hsum
  have hBnefin : ∀ᵐ ω ∂P, Bne ω ≠ ⊤ := by
    filter_upwards [hfin] with ω hω
    obtain ⟨J0, hJ0⟩ := eventually_atTop.mp hω
    have hbound : ∀ J : ℕ, g J ω ≤ ENNReal.ofReal ((1 - θ) * (J0 : ℝ)) := by
      intro J
      by_cases hJ : J0 ≤ J
      · rw [hg]; simp [Set.indicator_of_notMem (hJ0 J hJ)]
      · by_cases hmem : ω ∈ E J
        · rw [hg]
          simp only [Set.indicator_of_mem hmem]
          refine ENNReal.ofReal_le_ofReal ?_
          have hJle : (J : ℝ) ≤ (J0 : ℝ) := by
            exact_mod_cast le_of_lt (lt_of_not_ge hJ)
          nlinarith
        · rw [hg]; simp [Set.indicator_of_notMem hmem]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hbound)
  refine ⟨B, hBmeas, hBnonneg, ?_, ?_⟩
  · filter_upwards [hBnefin] with ω hω J π hJ
    by_cases hmem : ω ∈ E J
    · have hgJ : ENNReal.ofReal ((1 - θ) * (J : ℝ)) ≤ Bne ω := by
        refine le_trans (le_of_eq ?_) (le_iSup (fun K : ℕ => g K ω) J)
        rw [hg]; simp [Set.indicator_of_mem hmem]
      have hreal : (1 - θ) * (J : ℝ) ≤ B ω :=
        (ENNReal.ofReal_le_iff_le_toReal hω).mp hgJ
      have hcount : (badCount J π ω : ℝ) ≤ (J : ℝ) := by exact_mod_cast hle J π ω
      nlinarith
    · have hnot : ¬ (θ * (J : ℝ) ≤ (badCount J π ω : ℝ)) := fun hcon => hmem ⟨π, hcon⟩
      linarith [lt_of_not_ge hnot, hBnonneg ω]
  · intro t ht
    set s : ℝ := t / (1 - θ) with hs
    have hs0 : 0 ≤ s := div_nonneg ht hθ'.le
    set J0 : ℕ := ⌊s⌋₊ + 1 with hJ0def
    have hJ0s : s < (J0 : ℝ) := by
      rw [hJ0def]
      exact_mod_cast Nat.lt_floor_add_one s
    have hmemiff : ∀ J : ℕ, s < (J : ℝ) ↔ J0 ≤ J := by
      intro J
      rw [hJ0def, Nat.add_one_le_iff, ← Nat.floor_lt hs0]
    have hsub : {ω | t < B ω} ⊆ (⋃ k : ℕ, E (J0 + k)) ∪ {ω | Bne ω = ⊤} := by
      intro ω hω
      by_cases htop : Bne ω = ⊤
      · exact Or.inr htop
      · left
        have hlt : ENNReal.ofReal t < Bne ω :=
          (ENNReal.ofReal_lt_iff_lt_toReal ht htop).mpr hω
        obtain ⟨J, hJ⟩ := lt_iSup_iff.mp hlt
        have hmem : ω ∈ E J := by
          by_contra hcon
          rw [hg] at hJ
          simp [Set.indicator_of_notMem hcon] at hJ
        have hJval : ENNReal.ofReal t < ENNReal.ofReal ((1 - θ) * (J : ℝ)) := by
          rw [hg] at hJ
          simpa [Set.indicator_of_mem hmem] using hJ
        have hJreal : t < (1 - θ) * (J : ℝ) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp hJval
        have hsJ : s < (J : ℝ) := by
          rw [hs, div_lt_iff₀ hθ']
          linarith
        have hJ0le : J0 ≤ J := (hmemiff J).mp hsJ
        refine Set.mem_iUnion.2 ⟨J - J0, ?_⟩
        rwa [Nat.add_sub_cancel' hJ0le]
    have hnull : P {ω | Bne ω = ⊤} = 0 := by
      have h0 := hBnefin
      rw [ae_iff] at h0
      simpa using h0
    have hsummable : Summable (fun k : ℕ => Real.exp (-bstar * ((J0 : ℝ) + (k : ℝ)))) := by
      have : ∀ k : ℕ, Real.exp (-bstar * ((J0 : ℝ) + (k : ℝ))) =
          Real.exp (-bstar * (J0 : ℝ)) * Real.exp (-bstar) ^ k := by
        intro k
        rw [show -bstar * ((J0 : ℝ) + (k : ℝ)) = -bstar * (J0 : ℝ) + (k : ℝ) * (-bstar) by ring,
          Real.exp_add, Real.exp_nat_mul]
      simpa only [this] using (summable_geometric_of_lt_one hr0 hr1).mul_left _
    calc P {ω | t < B ω}
        ≤ P ((⋃ k : ℕ, E (J0 + k)) ∪ {ω | Bne ω = ⊤}) := measure_mono hsub
      _ ≤ P (⋃ k : ℕ, E (J0 + k)) + P {ω | Bne ω = ⊤} := measure_union_le _ _
      _ = P (⋃ k : ℕ, E (J0 + k)) := by rw [hnull, add_zero]
      _ ≤ ∑' k : ℕ, P (E (J0 + k)) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-bstar * ((J0 : ℝ) + (k : ℝ)))) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          refine (hPE (J0 + k) (by omega)).trans (le_of_eq ?_)
          congr 1
          push_cast
          ring_nf
      _ = ENNReal.ofReal (∑' k : ℕ, Real.exp (-bstar * ((J0 : ℝ) + (k : ℝ)))) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) hsummable]
      _ = ENNReal.ofReal (Real.exp (-bstar * (J0 : ℝ)) * (1 - Real.exp (-bstar))⁻¹) := by
          rw [tsum_exp_neg_shift hb]
      _ ≤ ENNReal.ofReal ((1 - Real.exp (-bstar))⁻¹ * Real.exp (-(bstar * t / (1 - θ)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hinv : 0 < (1 - Real.exp (-bstar))⁻¹ := by
            apply inv_pos.mpr; linarith
          have hexp : Real.exp (-bstar * (J0 : ℝ)) ≤ Real.exp (-(bstar * s)) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          have hseq : (-(bstar * t / (1 - θ))) = -(bstar * s) := by
            rw [hs]; ring
          rw [hseq]
          nlinarith [hexp, hinv, (Real.exp_pos (-(bstar * s))).le]

end Lane3
end SubdiffusiveProcess
