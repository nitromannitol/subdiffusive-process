module

public import SubdiffusiveProcess.CubeTrace.Mollifier
public import SubdiffusiveProcess.Sobolev.HolderBoundaryExtension

@[expose] public section

/-! Mollification converges in every strictly weaker Hölder norm. -/

open Set Filter MeasureTheory SubdiffusiveProcess
open SubdiffusiveProcess.CubeTrace _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology

noncomputable section
namespace SubdiffusiveProcess.Section9

theorem ctMoll_eq_kernel_integral {d : ℕ} (h : ℝ)
    (B : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    ctMoll h B x = ∫ t, ctRhoH h t * B (x - t) := by
  unfold ctMoll ctConv
  rw [← integral_sub_left_eq_self (fun t => ctRhoH h (x - t) * B t) volume x]
  congr 1
  funext t
  congr 2
  abel_nf

/-- A probability mollifier preserves the increment bound of its datum. -/
theorem ctMoll_holder_bound {d : ℕ} [NeZero d] {h K alpha : ℝ}
    (hh : 0 < h) (ha : 0 < alpha)
    {B : SpatialCoordinates d → ℝ}
    (hB : ∀ x y, |B x - B y| ≤ K * ‖x - y‖ ^ alpha)
    (x y : SpatialCoordinates d) :
    |ctMoll h B x - ctMoll h B y| ≤ K * ‖x - y‖ ^ alpha := by
  have hBc : Continuous B := holder_continuous ha hB
  have hkc : Continuous (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]
    exact (ctScale_contDiff ctRho_contDiff).continuous
  have hkcompact : HasCompactSupport (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]
    exact hasCompactSupport_ctScale hh (fun t ht => ctRho_eq_zero_of_le ht)
  have hi : ∀ z, Integrable (fun t => ctRhoH h t * B (z - t)) := by
    intro z
    exact (hkc.mul (hBc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hkcompact.mul_right
  rw [ctMoll_eq_kernel_integral, ctMoll_eq_kernel_integral, ← integral_sub (hi x) (hi y)]
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ t, (ctRhoH h t * B (x - t) - ctRhoH h t * B (y - t))‖ ≤
        ∫ t, ctRhoH h t * (K * ‖x - y‖ ^ alpha) := by
      refine norm_integral_le_of_norm_le ((ctRhoH_integrable hh).mul_const _)
        (Eventually.of_forall fun t => ?_)
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ctRhoH_nonneg hh t)]
      apply mul_le_mul_of_nonneg_left _ (ctRhoH_nonneg hh t)
      have heq : (x - t) - (y - t) = x - y := by abel
      simpa only [heq] using hB (x - t) (y - t)
    _ = K * ‖x - y‖ ^ alpha := by
      rw [integral_mul_const, ctRhoH_integral hh, one_mul]

/-- The mollification error has a small bound at every lower Hölder exponent. -/
theorem ctMoll_error_holder_bound {d : ℕ} [NeZero d] {h K alpha beta : ℝ}
    (hh : 0 < h) (hK : 0 ≤ K) (ha : 0 < alpha) (hb : 0 ≤ beta) (hba : beta < alpha)
    {B : SpatialCoordinates d → ℝ}
    (hB : ∀ x y, |B x - B y| ≤ K * ‖x - y‖ ^ alpha)
    (x y : SpatialCoordinates d) :
    |(ctMoll h B x - B x) - (ctMoll h B y - B y)| ≤
      (2 * K * h ^ (alpha - beta)) * ‖x - y‖ ^ beta := by
  by_cases hxy : x = y
  · subst y
    rw [sub_self, abs_zero]
    positivity
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  by_cases hnh : ‖x - y‖ ≤ h
  · have hi : |(ctMoll h B x - B x) - (ctMoll h B y - B y)| ≤
        2 * K * ‖x - y‖ ^ alpha := by
      calc
        _ = |(ctMoll h B x - ctMoll h B y) - (B x - B y)| := by congr 1; ring
        _ ≤ |ctMoll h B x - ctMoll h B y| + |B x - B y| := abs_sub _ _
        _ ≤ K * ‖x - y‖ ^ alpha + K * ‖x - y‖ ^ alpha :=
          add_le_add (ctMoll_holder_bound hh ha hB x y) (hB x y)
        _ = _ := by ring
    apply hi.trans
    have hp := Real.rpow_le_rpow hn.le hnh (sub_pos.mpr hba).le
    calc
      2 * K * ‖x - y‖ ^ alpha =
          2 * K * (‖x - y‖ ^ (alpha - beta) * ‖x - y‖ ^ beta) := by
        rw [← Real.rpow_add hn]
        congr 2
        ring
      _ ≤ 2 * K * (h ^ (alpha - beta) * ‖x - y‖ ^ beta) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hn.le _)) (by positivity)
      _ = _ := by ring
  · have hi : |(ctMoll h B x - B x) - (ctMoll h B y - B y)| ≤
        2 * K * h ^ alpha := by
      calc
        _ ≤ |ctMoll h B x - B x| + |ctMoll h B y - B y| := abs_sub _ _
        _ ≤ K * h ^ alpha + K * h ^ alpha :=
          add_le_add (ctMoll_sub_le hh hK ha hB x) (ctMoll_sub_le hh hK ha hB y)
        _ = _ := by ring
    apply hi.trans
    have hp := Real.rpow_le_rpow hh.le (le_of_not_ge hnh) hb
    calc
      2 * K * h ^ alpha = 2 * K * h ^ (alpha - beta) * h ^ beta := by
        have heq : h ^ alpha = h ^ (alpha - beta) * h ^ beta := by
          rw [← Real.rpow_add hh]
          congr 1
          ring
        rw [heq]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- Quantitative convergence in the paper's concrete Hölder norm, on any set. -/
theorem ctMoll_error_cAlphaNorm_le {d : ℕ} [NeZero d] {h K alpha beta : ℝ}
    (hh : 0 < h) (hK : 0 ≤ K) (ha : 0 < alpha) (hb : 0 ≤ beta) (hba : beta < alpha)
    {B : SpatialCoordinates d → ℝ}
    (hB : ∀ x y, |B x - B y| ≤ K * ‖x - y‖ ^ alpha)
    (S : Set (SpatialCoordinates d)) :
    IsHolderOn beta S (fun x => ctMoll h B x - B x) ∧
    BddAbove {v : ℝ | ∃ x ∈ S, v = |ctMoll h B x - B x|} ∧
    cAlphaNorm beta S (fun x => ctMoll h B x - B x) ≤
      K * h ^ alpha + 2 * K * h ^ (alpha - beta) := by
  have hhol := isHolderOn_of_dist_holder_bound beta (2 * K * h ^ (alpha - beta)) hb
    (by positivity) S (fun x => ctMoll h B x - B x) (fun x _ y _ => by
      simpa only [dist_eq_norm] using ctMoll_error_holder_bound hh hK ha hb hba hB x y)
  have habs : ∀ v ∈ {v : ℝ | ∃ x ∈ S, v = |ctMoll h B x - B x|}, v ≤ K * h ^ alpha := by
    rintro v ⟨x, _, rfl⟩
    exact ctMoll_sub_le hh hK ha hB x
  refine ⟨hhol.1, ⟨K * h ^ alpha, habs⟩, ?_⟩
  exact add_le_add (Real.sSup_le habs (by positivity)) hhol.2

/-- Mollification enlarges a concentric compact support by at most its radius. -/
theorem ctMoll_tsupport_subset_closedBall {d : ℕ} {h R : ℝ} (hh : 0 < h)
    (z : SpatialCoordinates d) {B : SpatialCoordinates d → ℝ}
    (hs : tsupport B ⊆ Metric.closedBall z R) :
    tsupport (ctMoll h B) ⊆ Metric.closedBall z (R + h) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have hdist : R + h < dist x z := lt_of_not_ge hn
  apply hx
  unfold ctMoll ctConv
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases hBt : B t = 0
  · simp only [hBt, mul_zero, Pi.zero_apply]
  · have htr : dist t z ≤ R := hs (subset_closure hBt)
    have hxt : h ≤ ‖x - t‖ := by
      have htri := dist_triangle x t z
      rw [dist_eq_norm x t] at htri
      linarith only [hdist, htr, htri]
    simp only [ctRhoH_eq_zero_of_le hh hxt, zero_mul, Pi.zero_apply]

/-- Compact support stays in a closed thickening of the original support. -/
theorem ctMoll_tsupport_subset_cthickening {d : ℕ} {h : ℝ} (hh : 0 < h)
    (B : SpatialCoordinates d → ℝ) :
    tsupport (ctMoll h B) ⊆ Metric.cthickening h (tsupport B) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  by_contra hn
  apply hx
  unfold ctMoll ctConv
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases hBt : B t = 0
  · simp only [hBt, mul_zero, Pi.zero_apply]
  · have hxt : h ≤ ‖x - t‖ := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hle
      apply hn
      exact Metric.mem_cthickening_of_dist_le x t h (tsupport B)
        (subset_closure hBt) (by simpa only [dist_eq_norm] using hle)
    simp only [ctRhoH_eq_zero_of_le hh hxt, zero_mul, Pi.zero_apply]

theorem ctMoll_error_cAlphaNorm_tendsto {d : ℕ} [NeZero d] {K alpha beta : ℝ}
    (hK : 0 ≤ K) (ha : 0 < alpha) (hb : 0 ≤ beta) (hba : beta < alpha)
    {B : SpatialCoordinates d → ℝ}
    (hB : ∀ x y, |B x - B y| ≤ K * ‖x - y‖ ^ alpha)
    (hs : ℕ → ℝ) (hp : ∀ n, 0 < hs n) (ht : Tendsto hs atTop (𝓝 0))
    (S : Set (SpatialCoordinates d)) :
    Tendsto (fun n => cAlphaNorm beta S (fun x => ctMoll (hs n) B x - B x))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => K * hs n ^ alpha) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt ha)] using
      ((Real.continuousAt_rpow_const 0 alpha (Or.inr ha.le)).tendsto.comp ht).const_mul K
  have h2 : Tendsto (fun n => 2 * K * hs n ^ (alpha - beta)) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt (sub_pos.mpr hba))] using
      ((Real.continuousAt_rpow_const 0 (alpha - beta) (Or.inr (sub_pos.mpr hba).le)).tendsto.comp ht).const_mul (2 * K)
  apply squeeze_zero (fun n => ?_)
    (fun n => (ctMoll_error_cAlphaNorm_le (hp n) hK ha hb hba hB S).2.2)
    (by simpa using h1.add h2)
  apply add_nonneg _ (holderSeminorm_nonneg _ _ _)
  apply Real.sSup_nonneg
  rintro v ⟨x, _, rfl⟩
  exact abs_nonneg _

theorem ctMoll_tendstoUniformly {d : ℕ} [NeZero d] {K alpha : ℝ}
    (hK : 0 ≤ K) (ha : 0 < alpha)
    {B : SpatialCoordinates d → ℝ}
    (hB : ∀ x y, |B x - B y| ≤ K * ‖x - y‖ ^ alpha)
    (hs : ℕ → ℝ) (hp : ∀ n, 0 < hs n) (ht : Tendsto hs atTop (𝓝 0)) :
    TendstoUniformly (fun n => ctMoll (hs n) B) B atTop := by
  have hlim : Tendsto (fun n => K * hs n ^ alpha) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt ha)] using
      ((Real.continuousAt_rpow_const 0 alpha (Or.inr ha.le)).tendsto.comp ht).const_mul K
  apply Metric.tendstoUniformly_iff.mpr
  intro eps heps
  filter_upwards [hlim.eventually (gt_mem_nhds heps)] with n hn x
  rw [Real.dist_eq, abs_sub_comm]
  exact (ctMoll_sub_le (hp n) hK ha hB x).trans_lt hn

end SubdiffusiveProcess.Section9
