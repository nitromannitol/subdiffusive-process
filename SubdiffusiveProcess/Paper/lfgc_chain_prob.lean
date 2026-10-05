module

public import SubdiffusiveProcess.Paper.lfgc_chain_num

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Probabilities of the chain events

Abstract chain: approximants `Yb h` of `X` with `L^p` error `Cδ 3^{-a h}`, followed by an
endpoint `Z` that is `1/32`-close to `X` outside an event `Obad`.
-/

open MeasureTheory
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The chain values: approximants, then the endpoint. -/
noncomputable def aux_lfgc_chain_prob_chainY (Yb : ℕ → Ω → ℝ) (Z : Ω → ℝ) (ℓs ℓ : ℕ) : Ω → ℝ :=
  if ℓ < ℓs then Yb (ℓ + 1) else Z

theorem aux_lfgc_chain_prob_eLpNorm_sub_approx_le (P : Measure Ω) {X A B : Ω → ℝ} (_hX : AEStronglyMeasurable X P)
    (_hA : AEStronglyMeasurable A P) (_hB : AEStronglyMeasurable B P) {p : ℝ} (hp : 1 ≤ p)
    {ea eb : ℝ} (hea : 0 ≤ ea) (heb : 0 ≤ eb)
    (ha : eLpNorm (fun ω => X ω - A ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal ea)
    (hb : eLpNorm (fun ω => X ω - B ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal eb) :
    eLpNorm (fun ω => A ω - B ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (ea + eb) := by
  have e : (fun ω => A ω - B ω) = fun ω => (X ω - B ω) - (X ω - A ω) := by funext ω; ring
  rw [e, ENNReal.ofReal_add hea heb, add_comm]
  refine (eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hp)).trans ?_
  exact add_le_add hb ha

theorem lfgc_chain_prob (P : Measure Ω) (X Z : Ω → ℝ) (hXm : AEStronglyMeasurable X P)
    (Yb : ℕ → Ω → ℝ) (hYbm : ∀ h, AEStronglyMeasurable (Yb h) P) {a p Cδ : ℝ} (hp : 1 ≤ p)
    (hCδ : 0 ≤ Cδ)
    (herr : ∀ h : ℕ, 1 ≤ h → eLpNorm (fun ω => X ω - Yb h ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cδ * (3 : ℝ) ^ (-(a * (h : ℝ)))))
    (ℓs : ℕ) (hℓs : 1 ≤ ℓs) (Obad : Set Ω) (hZ : ∀ ω ∉ Obad, |Z ω - X ω| ≤ 1 / 32) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    P (chainEvent (aux_lfgc_chain_prob_chainY Yb Z ℓs) (aux_lfgc_chain_num_chainTheta ρ ℓs) 0) ≤
        P {ω | 1 / 32 < X ω} +
          (ENNReal.ofReal (Cδ * (3 : ℝ) ^ (-(a * (1 : ℝ)))) / ENNReal.ofReal (1 / 32)) ^ p ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < ℓs →
      P (chainEvent (aux_lfgc_chain_prob_chainY Yb Z ℓs) (aux_lfgc_chain_num_chainTheta ρ ℓs) ℓ) ≤
        (ENNReal.ofReal (Cδ * (3 : ℝ) ^ (-(a * ((ℓ + 1 : ℕ) : ℝ))) +
            Cδ * (3 : ℝ) ^ (-(a * (ℓ : ℝ)))) /
          ENNReal.ofReal ((1 / 16) * (1 - ρ) * ρ ^ ℓ)) ^ p) ∧
    P (chainEvent (aux_lfgc_chain_prob_chainY Yb Z ℓs) (aux_lfgc_chain_num_chainTheta ρ ℓs) ℓs) ≤
      P Obad + (ENNReal.ofReal (Cδ * (3 : ℝ) ^ (-(a * (ℓs : ℝ)))) / ENNReal.ofReal (1 / 32)) ^ p := by
  have hp0 : 0 < p := by linarith
  have hpos : ∀ x : ℝ, 0 ≤ Cδ * (3 : ℝ) ^ (-(a * x)) := fun x => mul_nonneg hCδ (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · -- base event
    have hY0 : aux_lfgc_chain_prob_chainY Yb Z ℓs 0 = Yb 1 := by simp [aux_lfgc_chain_prob_chainY, show 0 < ℓs by omega]
    have hsub : chainEvent (aux_lfgc_chain_prob_chainY Yb Z ℓs) (aux_lfgc_chain_num_chainTheta ρ ℓs) 0 ⊆
        {ω | 1 / 32 < X ω} ∪ {ω | 1 / 32 < |X ω - Yb 1 ω|} := by
      intro ω hω
      simp only [chainEvent, aux_lfgc_chain_num_chainTheta, ite_true, hY0, Set.mem_ofPred_eq] at hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hno
      have := (abs_le.mp hno.2).1
      linarith [hno.1]
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
    refine (meas_lt_abs_le_eLpNorm P (hXm.sub (hYbm 1)) hp0 (by norm_num)).trans ?_
    gcongr
    change eLpNorm (fun ω => X ω - Yb 1 ω) (ENNReal.ofReal p) P ≤ _
    simpa only [Nat.cast_one, mul_one] using herr 1 le_rfl
  · -- interior increments
    intro ℓ hℓ1 hℓs'
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    have hY1 : aux_lfgc_chain_prob_chainY Yb Z ℓs (ℓ' + 1) = Yb (ℓ' + 2) := by simp [aux_lfgc_chain_prob_chainY, hℓs']
    have hY0 : aux_lfgc_chain_prob_chainY Yb Z ℓs ℓ' = Yb (ℓ' + 1) := by simp [aux_lfgc_chain_prob_chainY, show ℓ' < ℓs by omega]
    have hθ : aux_lfgc_chain_num_chainTheta ρ ℓs (ℓ' + 1) = (1 / 16) * (1 - ρ) * ρ ^ (ℓ' + 1) := by
      simp [aux_lfgc_chain_num_chainTheta, hℓs']
    simp only [chainEvent, hY1, hY0, hθ]
    have hθpos : 0 < (1 / 16) * (1 - ρ) * ρ ^ (ℓ' + 1) := by
      have := pow_pos hρ0 (ℓ' + 1); nlinarith
    refine (meas_lt_abs_le_eLpNorm P ((hYbm _).sub (hYbm _)) hp0 hθpos).trans ?_
    gcongr
    have h1 := herr (ℓ' + 2) (by omega)
    have h0 := herr (ℓ' + 1) (by omega)
    have := aux_lfgc_chain_prob_eLpNorm_sub_approx_le P hXm (hYbm (ℓ' + 2)) (hYbm (ℓ' + 1)) hp (hpos _) (hpos _) h1 h0
    have e2 : ((ℓ' + 1 + 1 : ℕ) : ℝ) = ((ℓ' + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [e2]
    exact this
  · -- the endpoint increment
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓs = ℓ' + 1 := ⟨ℓs - 1, by omega⟩
    have hY1 : aux_lfgc_chain_prob_chainY Yb Z (ℓ' + 1) (ℓ' + 1) = Z := by simp [aux_lfgc_chain_prob_chainY]
    have hY0 : aux_lfgc_chain_prob_chainY Yb Z (ℓ' + 1) ℓ' = Yb (ℓ' + 1) := by simp [aux_lfgc_chain_prob_chainY]
    have hθ : aux_lfgc_chain_num_chainTheta ρ (ℓ' + 1) (ℓ' + 1) = 1 / 16 := by simp [aux_lfgc_chain_num_chainTheta]
    simp only [chainEvent, hY1, hY0, hθ]
    have hsub : {ω | 1 / 16 < |Z ω - Yb (ℓ' + 1) ω|} ⊆
        Obad ∪ {ω | 1 / 32 < |X ω - Yb (ℓ' + 1) ω|} := by
      intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hno hω
      have h1 := hZ ω hno.1
      have h2 := hno.2
      have : |Z ω - Yb (ℓ' + 1) ω| ≤ |Z ω - X ω| + |X ω - Yb (ℓ' + 1) ω| := by
        have := abs_sub_le (Z ω) (X ω) (Yb (ℓ' + 1) ω); linarith
      linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
    refine (meas_lt_abs_le_eLpNorm P (hXm.sub (hYbm _)) hp0 (by norm_num)).trans ?_
    gcongr
    change eLpNorm (fun ω => X ω - Yb (ℓ' + 1) ω) (ENNReal.ofReal p) P ≤ _
    simpa only [Nat.cast_add, Nat.cast_one] using herr (ℓ' + 1) (by omega)

end SubdiffusiveProcess.Paper
