import SubdiffusiveProcess.Paper.lfgc_single_num

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Assembly of the single-point cover from the chain and the two layer families
-/

open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_single_assemble_ofReal_quarter_add_eighths (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (x / 4) + ENNReal.ofReal (x / 8) + ENNReal.ofReal (x / 8) = ENNReal.ofReal (x / 2) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

theorem lfgc_single_assemble (hd2 : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d)
    (hoff : ∀ i, -3 ≤ offset i ∧ offset i ≤ 0) (m k : ℕ) (z : SpatialCoordinates d)
    {θ₀ ε₁ ε₂ R : ℝ} (hθ₀ : 0 < θ₀) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (htol1 : aux_lfgc_near_tests_tolTransfer ε₁ (θ₀ / 4) ≤ θ₀) (htol2 : aux_lfgc_near_tests_tolTransfer ε₂ (θ₀ / 8) < θ₀ / 4)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Carrier : Set (BilateralField d))
    (hconv : ∀ omega ∈ Carrier, Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hcanon : ∀ omega ∈ Carrier, ∀ (j : ℕ) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
      (aux_lfgc_layer_tail_canonEta 0 omega j : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) y = omega (j : ℤ) y)
    (W₀ : ℕ) (hW₀ : 0 < W₀) (Y : ℕ → BilateralField d → ℝ) (θ : ℕ → ℝ)
    (hθ : ∑ ℓ ∈ Finset.range (m + k + 3 + 1), θ ℓ ≤ 3 / 16)
    (hYend : Y (m + k + 3) = aux_lfgc_root_impl_rootX I M sigma T offset shift (m + k) k z (2 / θ₀)
      (fun omega => infraredPartialSum omega (W₀ * (m + k + 3 + 2) - k)))
    (hYmeas : ∀ ℓ ≤ m + k + 3, Measurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ)] (Y ℓ))
    (hYprob : ∀ ℓ ≤ m + k + 3, (chaosSampleLaw M).toMeasure (chainEvent Y θ ℓ) ≤
      ENNReal.ofReal (Real.exp (-R * ((aux_lfgc_chain_cover_chainWin W₀ hW₀ ℓ : ℕ) : ℝ)) / 4))
    (hC1a : R ≤ (2 * ε₁ * d / 27 / Paper.aux_psf_sigma M) ^ 2)
    (hC1b : 16 * T * 57 ^ d * Real.exp (-(2 * ε₁ * d / 27 / Paper.aux_psf_sigma M) ^ 2) ≤ 1)
    (hC2a : R ≤ (2 * ε₂ * d / 27 / Paper.aux_psf_sigma M) ^ 2)
    (hC2b : 16 * T * 57 ^ d * Real.exp (-(2 * ε₂ * d / 27 / Paper.aux_psf_sigma M) ^ 2) ≤ 1) :
    IsTailCover (chaosSampleLaw M).toMeasure (aux_lfgc_family_cover_nodeWin d k)
      (Carrier ∩ ({omega | ¬ aux_lfgc_root_stat_nearAll I M H sigma T offset shift (m + k) (k : ℤ) z θ₀ omega} ∪
        {omega | ¬ aux_lfgc_root_stat_nearAll I M 0 sigma T offset shift (m + k) (k : ℤ) z θ₀ omega}))
      (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 2)) := by
  have hr27 : ∀ i, (3 : ℝ) ^ (-((k : ℤ) + offset i)) ≤ 27 := by
    intro i
    have h1 : (3 : ℝ) ^ (-((k : ℤ) + offset i)) ≤ (3 : ℝ) ^ (3 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by have := (hoff i).1; omega)
    have h2 : (3 : ℝ) ^ (3 : ℤ) = 27 := by norm_num
    rw [h2] at h1
    exact h1
  have hsub := lfgc_single_cover1 hd2 I M sigma hsigma T offset shift (m + k) (k : ℤ) z hθ₀ hε₁
    hε₂ htol1 htol2 hr27 H (W₀ * (m + k + 3 + 2) - k) (m + k + 3) Y hYend θ hθ Carrier hconv hcanon
  have hchain := lfgc_chain_cover (chaosSampleLaw M).toMeasure k W₀ hW₀ (m + k + 3) Y θ
    (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 4)) hYmeas hYprob
  have hA := lfgc_family_cover M offset shift k z (fun i => (hoff i).1) hε₁ 0 hC1a hC1b
  have hB := lfgc_family_cover M offset shift k z (fun i => (hoff i).1) hε₂
    (W₀ * (m + k + 3 + 2) - k) hC2a hC2b
  refine ((hchain.union hA).union hB).mono ?_ ?_
  · refine hsub.trans ?_
    intro omega homega
    rcases homega with (h | h) | h
    · exact Or.inl (Or.inl h)
    · refine Or.inl (Or.inr ?_)
      simp only [Set.mem_iUnion] at h ⊢
      obtain ⟨i, l, y, hy, hh⟩ := h
      exact ⟨i, l, Nat.zero_le l, y, hy, hh⟩
    · exact Or.inr h
  · intro h
    rw [aux_lfgc_single_assemble_ofReal_quarter_add_eighths _ (Real.exp_pos _).le]

end Paper
