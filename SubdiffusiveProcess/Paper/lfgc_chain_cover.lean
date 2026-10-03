module

public import SubdiffusiveProcess.Paper.lfgc_family_cover

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_chain_cover_nodeWin_mono (k : ℕ) {h h' : ℕ+} (hh : h ≤ h') : aux_lfgc_family_cover_nodeWin d k h ≤ aux_lfgc_family_cover_nodeWin d k h' := by
  unfold aux_lfgc_family_cover_nodeWin
  refine layerWindow_mono ?_
  intro j hj
  have hh' : (h : ℤ) ≤ (h' : ℤ) := by exact_mod_cast hh
  exact ⟨by linarith [hj.1], by linarith [hj.2]⟩

/-- The chain window of index `ℓ`. -/
def aux_lfgc_chain_cover_chainWin (W₀ : ℕ) (hW₀ : 0 < W₀) (ℓ : ℕ) : ℕ+ := ⟨W₀ * (ℓ + 2), by positivity⟩

theorem aux_lfgc_chain_cover_chainWin_mono (W₀ : ℕ) (hW₀ : 0 < W₀) {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ ≤ aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ' := by
  show W₀ * (ℓ + 2) ≤ W₀ * (ℓ' + 2)
  exact Nat.mul_le_mul_left _ (by omega)

theorem lfgc_chain_cover (P : Measure (BilateralField d)) (k W₀ : ℕ) (hW₀ : 0 < W₀) (ℓs : ℕ)
    (Y : ℕ → BilateralField d → ℝ) (θ : ℕ → ℝ) (f : ℕ+ → ℝ≥0∞)
    (hmeas : ∀ ℓ ≤ ℓs, Measurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ)] (Y ℓ))
    (hprob : ∀ ℓ ≤ ℓs, P (chainEvent Y θ ℓ) ≤ f (aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ)) :
    IsTailCover P (aux_lfgc_family_cover_nodeWin d k) (⋃ ℓ ∈ Finset.range (ℓs + 1), chainEvent Y θ ℓ) f := by
  classical
  let A : ℕ → Set (BilateralField d) := fun ℓ => if ℓ ≤ ℓs then chainEvent Y θ ℓ else ∅
  have hEq : (⋃ ℓ ∈ Finset.range (ℓs + 1), chainEvent Y θ ℓ) = ⋃ ℓ, A ℓ := by
    ext omega
    simp only [Set.mem_iUnion, Finset.mem_range, A]
    constructor
    · rintro ⟨ℓ, hℓ, h⟩
      exact ⟨ℓ, by simp only [show ℓ ≤ ℓs by omega, if_true]; exact h⟩
    · rintro ⟨ℓ, h⟩
      by_cases hl : ℓ ≤ ℓs
      · simp only [hl, if_true] at h; exact ⟨ℓ, by omega, h⟩
      · simp only [hl, if_false, Set.mem_empty_iff_false] at h
  rw [hEq]
  have hinj : Function.Injective (aux_lfgc_chain_cover_chainWin W₀ hW₀) := by
    intro a b h
    have := congrArg PNat.val h
    simp only [aux_lfgc_chain_cover_chainWin, PNat.mk_coe] at this
    have := Nat.eq_of_mul_eq_mul_left hW₀ this
    omega
  refine isTailCover_iUnion_injective (P := P) (B := aux_lfgc_family_cover_nodeWin d k) A (aux_lfgc_chain_cover_chainWin W₀ hW₀) hinj
    (fun ℓ => ?_) f (fun ℓ => ?_)
  · by_cases hl : ℓ ≤ ℓs
    · simp only [A, hl, if_true]
      rcases ℓ with _ | ℓ
      · exact measurableSet_lt measurable_const (hmeas 0 hl)
      · have h1 := hmeas (ℓ + 1) hl
        have h0 : Measurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_chain_cover_chainWin W₀ hW₀ (ℓ + 1))] (Y ℓ) :=
          (hmeas ℓ (by omega)).mono (aux_lfgc_chain_cover_nodeWin_mono k (aux_lfgc_chain_cover_chainWin_mono W₀ hW₀ (by omega))) le_rfl
        exact measurableSet_lt measurable_const (continuous_abs.measurable.comp (h1.sub h0))
    · simp only [A, hl, if_false]; exact @MeasurableSet.empty _ (aux_lfgc_family_cover_nodeWin d k (aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ))
  · by_cases hl : ℓ ≤ ℓs
    · simp only [A, hl, if_true]; exact hprob ℓ hl
    · simp only [A, hl, if_false, measure_empty, zero_le]

end Paper
