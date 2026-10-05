module

public import SubdiffusiveProcess.Static.HarmonicCutoffGrid

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

section
open MeasureTheory Metric Filter Topology
open scoped ENNReal

set_option autoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Static

variable {d : ℕ}

/-- Decomposition of a ball integral along the open grid cells. -/
lemma aux_hcut_lintegral_ball_cells {h : ℝ} (hh : 0 < h) (Φ : (Fin d → ℝ) → ℝ≥0∞) (x : Fin d → ℝ) (r : ℝ) :
    ∫⁻ z in ball x r, Φ z = ∑' k : Fin d → ℤ, ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φ z := by
  have huniv : (⋃ k : Fin d → ℤ, aux_hcut_cell h k) =ᵐ[volume] (Set.univ : Set (Fin d → ℝ)) := by
    rw [ae_eq_univ]
    have h1 := aux_hcut_ae_mem_cell (d := d) hh
    rw [ae_iff] at h1
    refine measure_mono_null (fun z hz => ?_) h1
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hz
    simpa only [Set.mem_ofPred_eq, not_exists] using hz
  have hae : (ball x r : Set (Fin d → ℝ)) =ᵐ[volume] ⋃ k : Fin d → ℤ, ball x r ∩ aux_hcut_cell h k := by
    rw [← Set.inter_iUnion]
    filter_upwards [huniv] with z hz
    have hzmem : z ∈ ⋃ k : Fin d → ℤ, aux_hcut_cell h k :=
      Eq.mpr (show (z ∈ ⋃ k : Fin d → ℤ, aux_hcut_cell h k) = True from hz) trivial
    simp only [Set.mem_inter_iff, hzmem, and_true]
  rw [Measure.restrict_congr_set hae]
  refine lintegral_iUnion (fun k => measurableSet_ball.inter (aux_hcut_measurableSet_cell h k)) ?_ Φ
  intro k k' hkk
  exact (aux_hcut_cell_disjoint hh hkk).mono Set.inter_subset_right Set.inter_subset_right

/-- Real bound, small balls. -/
lemma aux_hcut_real_small {h Kc r N : ℝ} {d : ℕ} (hd : 1 ≤ d) (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hKc : 0 ≤ Kc)
    (hr : 0 < r) (hN : N ≤ 4 ^ d) (_hN0 : 0 ≤ N) :
    N * (Kc * (2 * r) ^ ((d : ℝ) - 1 / 2)) ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
  have ht : (0 : ℝ) ≤ (d : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h2t : (2 : ℝ) ^ ((d : ℝ) - 1 / 2) ≤ 2 ^ d := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hhm : 1 ≤ h ^ (-(1 / 2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh (by linarith) (by norm_num)
  have hrt : 0 ≤ r ^ ((d : ℝ) - 1 / 2) := Real.rpow_nonneg hr.le _
  rw [Real.mul_rpow (by norm_num) hr.le]
  calc N * (Kc * (2 ^ ((d : ℝ) - 1 / 2) * r ^ ((d : ℝ) - 1 / 2)))
      ≤ 4 ^ d * (Kc * (2 ^ d * r ^ ((d : ℝ) - 1 / 2))) := by gcongr
    _ = 8 ^ d * Kc * 1 * r ^ ((d : ℝ) - 1 / 2) := by
        rw [show (8 : ℝ) ^ d = 4 ^ d * 2 ^ d by rw [← mul_pow]; norm_num]; ring
    _ ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by gcongr

/-- Real bound, large balls. -/
lemma aux_hcut_real_large {h Kc r N : ℝ} {d : ℕ} (_hd : 1 ≤ d) (hh : 0 < h) (hKc : 0 ≤ Kc)
    (hhr : h < r) (hr1 : r ≤ 1) (hN : N * h ^ d ≤ (4 * r) ^ d) (_hN0 : 0 ≤ N) :
    N * (Kc * h ^ ((d : ℝ) - 1 / 2)) ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
  have hr : 0 < r := hh.trans hhr
  have hsplit : h ^ ((d : ℝ) - 1 / 2) = h ^ d * h ^ (-(1 / 2 : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hh, Real.rpow_natCast]
  have hrd : r ^ d ≤ r ^ ((d : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hhm : 0 ≤ h ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hh.le _
  rw [hsplit]
  calc N * (Kc * (h ^ d * h ^ (-(1 / 2 : ℝ)))) = (N * h ^ d) * Kc * h ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ (4 * r) ^ d * Kc * h ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = 4 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ d := by rw [mul_pow]; ring
    _ ≤ 8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2) := by
        have h48 : (4 : ℝ) ^ d ≤ 8 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
        gcongr

/-- **Ball energy of the cellwise interpolant.** -/
lemma aux_hcut_energy_bound (hd : 1 ≤ d) {h Kc : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hKc : 0 ≤ Kc)
    (T : Finset (Fin d → ℤ)) (Φ : (Fin d → ℝ) → ℝ≥0∞) (Φk : (Fin d → ℤ) → (Fin d → ℝ) → ℝ≥0∞)
    (hΦ1 : ∀ k ∈ T, ∀ z ∈ aux_hcut_cell h k, Φ z = Φk k z)
    (hΦ0 : ∀ k ∉ T, ∀ z ∈ aux_hcut_cell h k, Φ z = 0)
    (hgrow : ∀ k ∈ T, ∀ y ∈ aux_hcut_cell h k, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∫⁻ z in ball y ρ ∩ aux_hcut_cell h k, Φk k z ≤ ENNReal.ofReal (Kc * ρ ^ ((d : ℝ) - 1 / 2)))
    (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ z in ball x r, Φ z ≤
      ENNReal.ofReal (8 ^ d * Kc * h ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2)) := by
  classical
  set T' := T.filter (fun k => (aux_hcut_cell h k ∩ ball x r).Nonempty) with hT'
  have hterm0 : ∀ k ∉ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φ z = 0 := by
    intro k hk
    by_cases hkT : k ∈ T
    · have hemp : ball x r ∩ aux_hcut_cell h k = ∅ := by
        rw [Set.inter_comm]
        by_contra hne
        exact hk (Finset.mem_filter.2 ⟨hkT, Set.nonempty_iff_ne_empty.2 hne⟩)
      rw [hemp, Measure.restrict_empty, lintegral_zero_measure]
    · rw [setLIntegral_congr_fun (measurableSet_ball.inter (aux_hcut_measurableSet_cell h k))
        (fun z hz => hΦ0 k hkT z hz.2)]
      simp
  rw [aux_hcut_lintegral_ball_cells hh Φ x r, tsum_eq_sum (s := T') (fun k hk => hterm0 k hk)]
  have hterm1 : ∀ k ∈ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φ z = ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φk k z := by
    intro k hk
    exact setLIntegral_congr_fun (measurableSet_ball.inter (aux_hcut_measurableSet_cell h k))
      (fun z hz => hΦ1 k (Finset.mem_filter.1 hk).1 z hz.2)
  rw [Finset.sum_congr rfl hterm1]
  have hcard := aux_hcut_card_mul_le hh T' hr.le (fun k hk => by
    have := (Finset.mem_filter.1 hk).2; exact this)
  rcases le_or_gt r h with hrh | hrh
  · -- small balls: at most `4^d` cells, each bounded at radius `2r`
    have hb : ∀ k ∈ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φk k z ≤
        ENNReal.ofReal (Kc * (2 * r) ^ ((d : ℝ) - 1 / 2)) := by
      intro k hk
      obtain ⟨hkT, ⟨y, hy1, hy2⟩⟩ := Finset.mem_filter.1 hk
      refine (lintegral_mono_set ?_).trans (hgrow k hkT y hy1 (2 * r) (by positivity) (by linarith))
      intro z ⟨hz1, hz2⟩
      refine ⟨?_, hz2⟩
      rw [mem_ball] at hz1 hy2 ⊢
      calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
        _ < r + r := by rw [dist_comm x y]; exact add_lt_add hz1 hy2
        _ = 2 * r := by ring
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (aux_hcut_real_small hd hh hh1 hKc hr ?_ (by positivity))
    have h4 : (2 * (r + h)) ^ d ≤ (4 * h) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hhd : 0 < h ^ d := by positivity
    have := hcard.trans h4
    rw [mul_pow] at this
    exact le_of_mul_le_mul_right (by linarith) hhd
  · -- large balls: whole-aux_hcut_cell bounds
    have hb : ∀ k ∈ T', ∫⁻ z in ball x r ∩ aux_hcut_cell h k, Φk k z ≤
        ENNReal.ofReal (Kc * h ^ ((d : ℝ) - 1 / 2)) := by
      intro k hk
      obtain ⟨hkT, -⟩ := Finset.mem_filter.1 hk
      have hc : aux_hcut_cc h k ∈ aux_hcut_cell h k := mem_ball_self (half_pos hh)
      refine (lintegral_mono_set ?_).trans (hgrow k hkT (aux_hcut_cc h k) hc h hh (by linarith))
      intro z ⟨_, hz2⟩
      refine ⟨?_, hz2⟩
      exact ball_subset_ball (by linarith) hz2
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (aux_hcut_real_large hd hh hKc hrh hr1 ?_ (by positivity))
    exact hcard.trans (pow_le_pow_left₀ (by positivity) (by linarith) d)

end SubdiffusiveProcess.Static
end
end
