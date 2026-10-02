import SubdiffusiveProcess.Paper.lfgc_root_near

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Oscillation of the infrared tail from single-layer oscillations

`aux_lfgc_infrared_osc_layerOsc j w r ε` is the event that the layer `ω j` oscillates by more than `ε` on the
closed cube of centre `w` and side `r`.  If the infrared partial sums converge to `H ω` and
no layer `n + 1`, `n ≥ L₀`, oscillates by more than `ε / 2^(n+1)` on the cube, then
`H ω - S_{L₀} ω` oscillates by at most `ε` there (`S_L` the anchored partial sum).
Also: each `aux_lfgc_infrared_osc_layerOsc` event is measurable for any layer window containing `j`.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ}

/-- A single layer oscillates by more than `ε` on a closed cube. -/
def aux_lfgc_infrared_osc_layerOsc (j : ℤ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (ε : ℝ) :
    Set (BilateralField d) :=
  {omega | ∃ y ∈ (closedCube w r hr : Set (SpatialCoordinates d)), ε < |omega j y - omega j w|}

theorem aux_lfgc_infrared_osc_sum_geom_half_le (ε : ℝ) (hε : 0 ≤ ε) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, ε / 2 ^ (n + 1) ≤ ε := by
  have h : ∀ b : ℕ, ∑ n ∈ Finset.range b, ε / 2 ^ (n + 1) = ε - ε / 2 ^ b := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        field_simp
        ring
  calc ∑ n ∈ Finset.Ico a b, ε / 2 ^ (n + 1) ≤ ∑ n ∈ Finset.range b, ε / 2 ^ (n + 1) := by
        rcases le_total a b with hab | hab
        · rw [Finset.range_eq_Ico]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (Nat.zero_le a))
            (fun n _ _ => by positivity)
        · rw [Finset.Ico_eq_empty (by omega)]
          simp only [Finset.sum_empty]
          exact Finset.sum_nonneg fun n _ => by positivity
    _ = ε - ε / 2 ^ b := h b
    _ ≤ ε := by
        have : (0 : ℝ) ≤ ε / 2 ^ b := by positivity
        linarith

theorem aux_lfgc_infrared_osc_infraredPartialSum_sub_eval (omega : BilateralField d) (L₀ L : ℕ) (hL : L₀ ≤ L)
    (y w : SpatialCoordinates d) :
    (infraredPartialSum omega L y - infraredPartialSum omega L₀ y) -
        (infraredPartialSum omega L w - infraredPartialSum omega L₀ w) =
      ∑ n ∈ Finset.Ico L₀ L, (omega (Int.ofNat (n + 1)) y - omega (Int.ofNat (n + 1)) w) := by
  unfold infraredPartialSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply]
  rw [← Finset.sum_range_add_sum_Ico _ hL, ← Finset.sum_range_add_sum_Ico _ hL]
  simp only [add_sub_cancel_left]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The infrared tail oscillates little when every tail layer does. -/
theorem lfgc_infrared_osc (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d)
    (hconv : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) (L₀ : ℕ)
    (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 ≤ ε)
    (hlayers : ∀ n, L₀ ≤ n → omega ∉ aux_lfgc_infrared_osc_layerOsc (Int.ofNat (n + 1)) w r hr (ε / 2 ^ (n + 1))) :
    aux_lfgc_root_near_OscLe (fun y => H omega y - infraredPartialSum omega L₀ y) w r hr ε := by
  intro y hy
  have hyc : y ∈ (closedCube w r hr : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube w hr hy
  have hev : ∀ x : SpatialCoordinates d,
      Tendsto (fun L => infraredPartialSum omega L x) atTop (𝓝 (H omega x)) :=
    fun x => ((continuous_eval_const x).tendsto _).comp hconv
  have hlim : Tendsto (fun L => (infraredPartialSum omega L y - infraredPartialSum omega L₀ y) -
      (infraredPartialSum omega L w - infraredPartialSum omega L₀ w)) atTop
      (𝓝 ((H omega y - infraredPartialSum omega L₀ y) - (H omega w - infraredPartialSum omega L₀ w))) :=
    ((hev y).sub tendsto_const_nhds).sub ((hev w).sub tendsto_const_nhds)
  have hbound : ∀ᶠ L in atTop, |(infraredPartialSum omega L y - infraredPartialSum omega L₀ y) -
      (infraredPartialSum omega L w - infraredPartialSum omega L₀ w)| ≤ ε := by
    filter_upwards [eventually_ge_atTop L₀] with L hL
    rw [aux_lfgc_infrared_osc_infraredPartialSum_sub_eval omega L₀ L hL y w]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
      (aux_lfgc_infrared_osc_sum_geom_half_le ε hε L₀ L))
    have hn' := (Finset.mem_Ico.mp hn).1
    have := hlayers n hn'
    simp only [aux_lfgc_infrared_osc_layerOsc, Set.mem_setOf_eq, not_exists, not_and, not_lt] at this
    exact this y hyc
  have := le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hlim) hbound
  simpa [sub_sub_sub_cancel_right] using
    (show |(H omega y - infraredPartialSum omega L₀ y) - (H omega w - infraredPartialSum omega L₀ w)| ≤ ε
      from this)

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The oscillation functional of a layer on a closed cube is continuous. -/
theorem aux_lfgc_infrared_osc_measurableSet_layerOsc (j : ℤ) (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (ε : ℝ) :
    MeasurableSet (aux_lfgc_infrared_osc_layerOsc j w r hr ε) := by
  set K := closedCube w r hr
  let Φ : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    ‖(f - ContinuousMap.const _ (f w)).restrict (K : Set (SpatialCoordinates d))‖
  have hΦ : Continuous Φ := by
    refine continuous_norm.comp ?_
    refine (ContinuousMap.continuous_restrict _).comp ?_
    exact continuous_id.sub (ContinuousMap.continuous_const'.comp (continuous_eval_const w))
  have hset : aux_lfgc_infrared_osc_layerOsc j w r hr ε = (fun omega : BilateralField d => omega j) ⁻¹' {f | ε < Φ f} := by
    ext omega
    simp only [aux_lfgc_infrared_osc_layerOsc, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, hlt⟩
      refine lt_of_lt_of_le hlt ?_
      have := ContinuousMap.norm_coe_le_norm
        ((omega j - ContinuousMap.const _ (omega j w)).restrict (K : Set (SpatialCoordinates d))) ⟨y, hy⟩
      rw [Real.norm_eq_abs] at this
      exact this
    · intro hlt
      by_contra hno
      push_neg at hno
      have hw : w ∈ (K : Set (SpatialCoordinates d)) :=
        Metric.mem_closedBall_self (by positivity)
      have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hno w hw)
      have hle : Φ (omega j) ≤ ε := by
        refine (ContinuousMap.norm_le _ hε0).mpr fun x => ?_
        rw [Real.norm_eq_abs]
        exact hno x.1 x.2
      linarith
  rw [hset]
  exact (measurable_pi_apply j) (hΦ.measurable (measurableSet_lt measurable_const measurable_id))

end Paper
