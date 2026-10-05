module

public import SubdiffusiveProcess.Paper.lfgc_fp_cover

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_fp_main_three_pieces_le {x a b c e : ℝ≥0∞} {K : ℝ≥0∞} (hx : x ≤ a + b + c)
    (ha : K * a ≤ e / 6) (hb : K * b ≤ e / 6) (hc : K * c ≤ e / 6) : K * x ≤ e / 2 := by
  calc K * x ≤ K * (a + b + c) := by gcongr
    _ = K * a + K * b + K * c := by ring
    _ ≤ e / 6 + e / 6 + e / 6 := add_le_add (add_le_add ha hb) hc
    _ = e / 2 := by
        rw [← ENNReal.add_div, ← ENNReal.add_div, show e + e + e = e * 3 by ring,
          show (6 : ℝ≥0∞) = 2 * 3 by norm_num]
        exact ENNReal.mul_div_mul_right e 2 (by norm_num) (by norm_num)

/-- Interval witnesses for the pad-test bank failures. -/
theorem lfgc_fp_main (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (ns : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (m k : ℕ) (y : Fin ns → Vec d),
        IsTailCover (chaosSampleLaw M).toMeasure (aux_lfgc_family_cover_nodeWin d k) (aux_lfgc_fp_cover_fpBad s (m + k) (m + 1) y)
          (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 2)) := by
  obtain ⟨Λ, hΛ1, hnum⟩ := amaj_num hs hR ns d
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set cF := Real.exp (-(s * Real.log 3 / 8)) * (s * Real.log 3 / 8) ^ 2 / 4 with hcF
  have hcF0 : 0 < cF := by positivity
  set cB := s / 96 with hcB
  have hcB0 : 0 < cB := by positivity
  have hns : (0 : ℝ) ≤ ns := Nat.cast_nonneg ns
  set LF := Real.log (6 * (2 * ((ns : ℝ) + 1))) + Real.log (3 * 9 ^ d) + R with hLF
  set LB := Real.log (6 * (2 * 7 ^ d * ((ns : ℝ) + 1))) + Real.log 2 + R with hLB
  have hLF0 : 0 < LF := by
    have h1 : 0 ≤ Real.log (6 * (2 * ((ns : ℝ) + 1))) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log (3 * 9 ^ d) :=
      Real.log_nonneg (by have : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num); linarith)
    linarith
  have hLB0 : 0 < LB := by
    have h7 : (1 : ℝ) ≤ 7 ^ d := one_le_pow₀ (by norm_num)
    have h1 : 0 ≤ Real.log (6 * (2 * 7 ^ d * ((ns : ℝ) + 1))) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  set σ0 := min (min (cF / Real.sqrt LF) (cB / Real.sqrt LB)) (1 / Λ) with hσ0
  have hσ00 : 0 < σ0 := by
    have h1 : 0 < Real.sqrt LF := Real.sqrt_pos.mpr hLF0
    have h2 : 0 < Real.sqrt LB := Real.sqrt_pos.mpr hLB0
    have hΛpos : 0 < Λ := by linarith
    have h3 : 0 < 1 / Λ := by positivity
    exact lt_min (lt_min (div_pos hcF0 h1) (div_pos hcB0 h2)) h3
  refine ⟨σ0 / (1 + d), by positivity, fun M hM m k y => ?_⟩
  have hσ := _root_.SubdiffusiveProcess.Paper.aux_psf_sigma_pos M
  have hσle : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M ≤ σ0 := by
    have : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M = (1 + (d : ℝ)) * M.delta := rfl
    rw [this]
    have h1 : (0 : ℝ) < 1 + d := by positivity
    rw [le_div_iff₀ h1] at hM
    linarith
  have hsmallF : LF ≤ (cF / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2 :=
    aux_lfgc_fp_cover_sq_ge_of_le_div hσ hLF0 (hσle.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsmallB : LB ≤ (cB / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2 :=
    aux_lfgc_fp_cover_sq_ge_of_le_div hσ hLB0 (hσle.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hΛσ : Λ * _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M ≤ 1 := by
    have h1 : _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M ≤ 1 / Λ := hσle.trans (min_le_right _ _)
    have hΛ0 : 0 < Λ := by linarith
    rw [le_div_iff₀ hΛ0] at h1
    linarith
  refine ⟨fun h => aux_lfgc_fp_cover_fpWin s (m + k) (m + 1) y h, aux_lfgc_fp_cover_measurableSet_fpWin s m k y, fun h => ?_,
    aux_lfgc_fp_cover_fpBad_subset _ _ _ y⟩
  have hh : 1 ≤ (h : ℕ) := h.pos
  set e := ENNReal.ofReal (Real.exp (-R * (h : ℝ)))
  have hj : (((h : ℕ) - 1 + 1 : ℕ) : ℝ) = (h : ℝ) := by
    rw [Nat.sub_add_cancel hh]
  have hpiece : ∀ t : Fin ns, ((ns : ℝ≥0∞) + 1) * (chaosSampleLaw M).toMeasure
      (((⋃ i ∈ Finset.Icc (m + 1 - ((h : ℕ) - 1)) (m + 1 + ((h : ℕ) - 1)),
        aux_lfgc_fp_events_bankEv (m + k) i (m + 1 + 1 + ((h : ℕ) - 1)) (y t)
          ((3 : ℝ) ^ (s * (((h : ℕ) - 1 : ℕ) : ℝ) / 8) / (2 * (((h : ℕ) - 1 : ℕ) : ℝ) + 1))) ∪
        aux_lfgc_fp_events_amajEv (m + k) (m + 1) ((h : ℕ) - 1) (y t)
          (6 * (3 : ℝ) ^ (s * (((h : ℕ) - 1 : ℕ) : ℝ) / 8)) ∪
        ⋃ l ∈ Finset.range (h : ℕ),
          aux_lfgc_fp_events_bankEv (m + k) (m + 1 + ((h : ℕ) - 1 - l) + l) (m + 1 + 1 + ((h : ℕ) - 1 - l)) (y t)
            (aux_lfgc_fp_bound2_tB s ((h : ℕ) - 1 - l) l))) ≤ e / 2 := by
    intro t
    have hF := lfgc_fp_bound M s hs ns hsmallF (m + k) (m + 1) ((h : ℕ) - 1) (y t)
    have hA := aux_lfgc_fp_bound_aPiece_prob M s hs ns hΛ1 hnum hΛσ (m + k) (m + 1) ((h : ℕ) - 1) (y t)
    have hB := lfgc_fp_bound2 M s hs hs1 ns hsmallB (m + k) (m + 1) (h : ℕ) hh (y t)
    rw [hj] at hF hA
    have he6 : ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 6) = e / 6 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    rw [he6] at hF hA hB
    refine aux_lfgc_fp_main_three_pieces_le ?_ hF hA hB
    exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  have hK0 : ((ns : ℝ≥0∞) + 1) ≠ 0 := by positivity
  have hKt : ((ns : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  calc (chaosSampleLaw M).toMeasure (aux_lfgc_fp_cover_fpWin s (m + k) (m + 1) y h)
      ≤ ∑ t : Fin ns, (chaosSampleLaw M).toMeasure
          (((⋃ i ∈ Finset.Icc (m + 1 - ((h : ℕ) - 1)) (m + 1 + ((h : ℕ) - 1)),
            aux_lfgc_fp_events_bankEv (m + k) i (m + 1 + 1 + ((h : ℕ) - 1)) (y t)
              ((3 : ℝ) ^ (s * (((h : ℕ) - 1 : ℕ) : ℝ) / 8) /
                (2 * (((h : ℕ) - 1 : ℕ) : ℝ) + 1))) ∪
            aux_lfgc_fp_events_amajEv (m + k) (m + 1) ((h : ℕ) - 1) (y t)
              (6 * (3 : ℝ) ^ (s * (((h : ℕ) - 1 : ℕ) : ℝ) / 8)) ∪
            ⋃ l ∈ Finset.range (h : ℕ),
              aux_lfgc_fp_events_bankEv (m + k) (m + 1 + ((h : ℕ) - 1 - l) + l) (m + 1 + 1 + ((h : ℕ) - 1 - l))
                (y t) (aux_lfgc_fp_bound2_tB s ((h : ℕ) - 1 - l) l))) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : Fin ns, (e / 2) / ((ns : ℝ≥0∞) + 1) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKt), mul_comm]
        exact hpiece t
    _ = (ns : ℝ≥0∞) * ((e / 2) / ((ns : ℝ≥0∞) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ((ns : ℝ≥0∞) + 1) * ((e / 2) / ((ns : ℝ≥0∞) + 1)) := by gcongr; exact le_self_add
    _ = e / 2 := ENNReal.mul_div_cancel hK0 hKt
    _ = ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]

end SubdiffusiveProcess.Paper
