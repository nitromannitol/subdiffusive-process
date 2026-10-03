module

public import SubdiffusiveProcess.Paper.lfgc_single_assemble

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Geometric bookkeeping of the chain thresholds

With `ρ = 3^{-a/2}` the thresholds `1/16, (1/16)(1-ρ)ρ^ℓ (1 ≤ ℓ < ℓ*), 1/16` sum to at most
`3/16`, and `3^{-aℓ} = ρ^{2ℓ}`.
-/

namespace Paper
/-- The chain thresholds. -/
noncomputable def aux_lfgc_chain_num_chainTheta (ρ : ℝ) (ℓs ℓ : ℕ) : ℝ :=
  if ℓ = 0 then 1 / 16 else if ℓ < ℓs then (1 / 16) * (1 - ρ) * ρ ^ ℓ else 1 / 16

theorem lfgc_chain_num {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (ℓs : ℕ) :
    ∑ ℓ ∈ Finset.range (ℓs + 1), aux_lfgc_chain_num_chainTheta ρ ℓs ℓ ≤ 3 / 16 := by
  have hmid : ∀ n : ℕ, ∑ ℓ ∈ Finset.range n, (1 / 16) * (1 - ρ) * ρ ^ ℓ ≤ 1 / 16 := by
    intro n
    have h := geom_sum_mul_neg ρ n
    have hρn : 0 ≤ ρ ^ n := pow_nonneg h0 n
    have e : ∑ ℓ ∈ Finset.range n, (1 / 16) * (1 - ρ) * ρ ^ ℓ =
        (1 / 16) * ((∑ ℓ ∈ Finset.range n, ρ ^ ℓ) * (1 - ρ)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
    rw [e, h]; nlinarith
  have hle : ∀ ℓ ∈ Finset.range (ℓs + 1), aux_lfgc_chain_num_chainTheta ρ ℓs ℓ ≤
      (if ℓ = 0 then 1 / 16 else 0) + (if ℓ = ℓs then 1 / 16 else 0) +
        (1 / 16) * (1 - ρ) * ρ ^ ℓ := by
    intro ℓ hℓ
    have hℓ' := Finset.mem_range.mp hℓ
    have hpos : 0 ≤ (1 / 16) * (1 - ρ) * ρ ^ ℓ := by
      have := pow_nonneg h0 ℓ; nlinarith
    unfold aux_lfgc_chain_num_chainTheta
    by_cases hℓ0 : ℓ = 0
    · simp only [hℓ0, if_true]
      split_ifs <;> linarith
    · by_cases hlt : ℓ < ℓs
      · simp only [hℓ0, if_false, hlt, if_true, show ℓ ≠ ℓs by omega, zero_add]
        exact le_rfl
      · have hEq : ℓ = ℓs := by omega
        subst hEq
        have hne : ℓ ≠ 0 := hℓ0
        simp only [hne, if_false, lt_irrefl, if_true]
        linarith
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range, show 0 < ℓs + 1 by omega, show ℓs < ℓs + 1 by omega, if_true]
  linarith [hmid (ℓs + 1)]

end Paper
