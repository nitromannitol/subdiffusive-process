import SubdiffusiveProcess.Paper.lfgc_p1_index
import SubdiffusiveProcess.Paper.lfgc_chain_cover

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The level window of a prefix sum. -/
def aux_lfgc_p1_approx_p1Pre (N k buffer D e : ℕ) : Finset ℤ :=
  Finset.Icc ((k : ℤ) - (e : ℤ) - (buffer : ℤ)) (min (N : ℤ) ((k : ℤ) - (e : ℤ) + (D : ℤ) + (buffer : ℤ)))

theorem aux_lfgc_p1_approx_card_p1Pre_le (N k buffer D e : ℕ) (hD : 1 ≤ D) :
    ((aux_lfgc_p1_approx_p1Pre N k buffer D e).card : ℝ) ≤ (2 + 2 * buffer) * D := by
  unfold aux_lfgc_p1_approx_p1Pre
  rw [Int.card_Icc]
  have h : (min (N : ℤ) ((k : ℤ) - (e : ℤ) + (D : ℤ) + (buffer : ℤ)) + 1 -
      ((k : ℤ) - (e : ℤ) - (buffer : ℤ))).toNat ≤ D + 2 * buffer + 1 := by omega
  have h' : ((min (N : ℤ) ((k : ℤ) - (e : ℤ) + (D : ℤ) + (buffer : ℤ)) + 1 -
      ((k : ℤ) - (e : ℤ) - (buffer : ℤ))).toNat : ℝ) ≤ D + 2 * buffer + 1 := by exact_mod_cast h
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  nlinarith



def aux_lfgc_p1_approx_p1Wfun (c1 L0 buffer : ℕ) (H : ℕ) : ℕ+ :=
  ⟨c1 * (H + 1) + L0 + buffer + 3, by omega⟩

theorem aux_lfgc_p1_approx_p1Wfun_mono (c1 L0 buffer : ℕ) : Monotone (aux_lfgc_p1_approx_p1Wfun c1 L0 buffer) := by
  intro H H' hH
  show c1 * (H + 1) + L0 + buffer + 3 ≤ c1 * (H' + 1) + L0 + buffer + 3
  have := Nat.mul_le_mul_left c1 (Nat.add_le_add_right hH 1)
  omega

theorem aux_lfgc_p1_approx_p1Wfun_injective (c1 L0 buffer : ℕ) (hc1 : 1 ≤ c1) : Function.Injective (aux_lfgc_p1_approx_p1Wfun c1 L0 buffer) := by
  intro H H' h
  have h' : c1 * (H + 1) + L0 + buffer + 3 = c1 * (H' + 1) + L0 + buffer + 3 := congrArg PNat.val h
  have : c1 * (H + 1) = c1 * (H' + 1) := by omega
  have := Nat.eq_of_mul_eq_mul_left (by omega) this
  omega

/-- The approximant of a prefix sum. -/
noncomputable def aux_lfgc_p1_approx_p1U [NeZero d] (M : GMCModel d) (s eps : ℝ) (m k buffer cL L0 : ℕ) (e : ℕ)
    (w : SpatialCoordinates d) (b : Bool)
    (Y : Bool → ℤ → SpatialCoordinates d → ℕ → BilateralField d → ℝ) (D H : ℕ)
    (omega : BilateralField d) : ℝ :=
  ∑ j ∈ aux_lfgc_p1_approx_p1Pre (m + k) k buffer D e,
    if 0 ≤ ((m + k : ℕ) : ℤ) - j then
      (if H < m then Y b j w H omega else aux_lfgc_sum_trunc_summandTr b M s eps (m + k) j w (cL * H + L0) omega)
    else 0

/-- Window measurability of the approximants. -/
theorem lfgc_p1_approx [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (m k buffer cL L0 width : ℕ) (e : ℕ) (he : e ≤ 3) (w : SpatialCoordinates d) (b : Bool)
    (Y : Bool → ℤ → SpatialCoordinates d → ℕ → BilateralField d → ℝ)
    (hYm : ∀ j h, j ≤ ((m + k : ℕ) : ℤ) → 1 ≤ h →
      StronglyMeasurable[layerWindow C(SpatialCoordinates d, ℝ)
        (Set.Icc (-j - (width * (h + 1) : ℕ)) (-j + (width * (h + 1) : ℕ)))] (Y b j w h))
    (D H : ℕ) (hD : 1 ≤ D) (hDH : D ≤ H) :
    StronglyMeasurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_p1_approx_p1Wfun (width + cL + 1) L0 buffer H)]
      (aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 e w b Y D H) := by
  unfold aux_lfgc_p1_approx_p1U
  have hsum : ∀ (f : ℤ → BilateralField d → ℝ) (S : Finset ℤ),
      (∀ j ∈ S, StronglyMeasurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_p1_approx_p1Wfun (width + cL + 1) L0 buffer H)] (f j)) →
      StronglyMeasurable[aux_lfgc_family_cover_nodeWin d k (aux_lfgc_p1_approx_p1Wfun (width + cL + 1) L0 buffer H)]
        (fun omega => ∑ j ∈ S, f j omega) := by
    intro f S hf
    have h := Finset.stronglyMeasurable_sum S hf
    convert h using 1
    funext omega
    rw [Finset.sum_apply]
  refine hsum _ _ fun j hj => ?_
  have hj' := Finset.mem_Icc.mp hj
  by_cases hN : 0 ≤ ((m + k : ℕ) : ℤ) - j
  · simp only [hN, if_true]
    by_cases hHm : H < m
    · simp only [hHm, if_true]
      refine (hYm j H (by omega) (by omega)).mono ?_
      unfold aux_lfgc_family_cover_nodeWin
      refine layerWindow_mono ?_
      intro t ht
      simp only [Set.mem_Icc] at ht ⊢
      simp only [aux_lfgc_p1_approx_p1Wfun, PNat.mk_coe]
      have hmin := min_le_right ((m + k : ℕ) : ℤ) ((k : ℤ) - (e : ℤ) + (D : ℤ) + (buffer : ℤ))
      push_cast at ht ⊢
      constructor <;> nlinarith
    · simp only [hHm, if_false]
      refine aux_lfgc_sum_trunc_summandTr_window b M s eps heps (m + k) j w (cL * H + L0) _ fun i hi => ?_
      simp only [Set.mem_Icc, aux_lfgc_p1_approx_p1Wfun, PNat.mk_coe]
      have hi' : (i : ℤ) ≤ ((m + k : ℕ) : ℤ) - j + (cL * H + L0 : ℕ) := by
        have := Int.toNat_of_nonneg hN
        omega
      push_cast at hi' ⊢
      constructor <;> nlinarith
  · simp only [hN, if_false]
    exact stronglyMeasurable_const

end Paper
