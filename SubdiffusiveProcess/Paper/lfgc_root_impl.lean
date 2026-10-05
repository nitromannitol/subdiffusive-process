module

public import SubdiffusiveProcess.Paper.lfgc_root_near

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Deterministic implications for the root statistic

With `K = 2/θ₀` and `X_H = aux_lfgc_root_stat_phiStat K (aux_lfgc_root_stat_bandCoords … H …)`:
* failure of `aux_lfgc_root_stat_nearAll H θ₀` forces `X_H ≥ 1/2`;
* failure of `aux_lfgc_root_stat_nearAll H' θ₀` forces `X_H ≥ 1/2` or an oscillation of `H' - H` above `ε₁`;
* `X_H ≥ 1/2` forces `X_{H'} ≥ 1/4` or an oscillation of `H - H'` above `ε₂`;
* small oscillation gives `|X_{H'} - X_H| ≤ K (2(e^ε-1) + √(2(e^ε-1)))`.
The admissible `ε₁, ε₂` are characterised by explicit inequalities on `aux_lfgc_near_tests_tolTransfer`.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_root_near_OscLe.symm {f g : SpatialCoordinates d → ℝ} {w : SpatialCoordinates d} {r : ℝ}
    {hr : 0 < r} {ε : ℝ} (h : aux_lfgc_root_near_OscLe (fun y => f y - g y) w r hr ε) :
    aux_lfgc_root_near_OscLe (fun y => g y - f y) w r hr ε := by
  intro y hy
  have := h y hy
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

theorem aux_lfgc_root_impl_tolTransfer_nonneg (ε θ : ℝ) : 0 ≤ aux_lfgc_near_tests_tolTransfer ε θ :=
  (Real.sqrt_nonneg _).trans (le_max_right _ _)

/-- The slack in the transferred tolerance. -/
noncomputable def aux_lfgc_root_impl_tolSlack (ε : ℝ) : ℝ := 2 * (Real.exp ε - 1) + Real.sqrt (2 * (Real.exp ε - 1))

theorem aux_lfgc_root_impl_tolTransfer_le {ε s : ℝ} (hε : 0 ≤ ε) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    aux_lfgc_near_tests_tolTransfer ε s ≤ s + aux_lfgc_root_impl_tolSlack ε := by
  have he : 0 ≤ Real.exp ε - 1 := by linarith [Real.one_le_exp hε]
  have hsq := Real.sqrt_nonneg (2 * (Real.exp ε - 1))
  unfold aux_lfgc_near_tests_tolTransfer aux_lfgc_root_impl_tolSlack
  refine max_le ?_ ?_
  · nlinarith
  · rw [Real.sqrt_le_left (by positivity)]
    have h2 := Real.sq_sqrt (show 0 ≤ 2 * (Real.exp ε - 1) by positivity)
    have : s ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hs0 hsq]

variable [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
  (sigma : ℝ) (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
  (z : SpatialCoordinates d)

/-- The root statistic for the infrared field `H`. -/
noncomputable def aux_lfgc_root_impl_rootX (K : ℝ) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) : ℝ :=
  aux_lfgc_root_stat_phiStat K (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)

/-- Oscillation of `H' - H` is at most `ε` on every root cube. -/
def aux_lfgc_root_impl_allOscLe (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (ε : ℝ)
    (omega : BilateralField d) : Prop :=
  ∀ i : Fin T, aux_lfgc_root_near_OscLe (fun y => H' omega y - H omega y)
    (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) (by positivity) ε

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
omit [NeZero d] in
theorem aux_lfgc_root_impl_allOscLe.symm
    {d : ℕ} [_portSection1 : NeZero d] (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (n : ℤ) (z : SpatialCoordinates d) {H H' : BilateralField d → C(SpatialCoordinates d, ℝ)} {ε : ℝ}
    {omega : BilateralField d} (h : aux_lfgc_root_impl_allOscLe T offset shift n z H H' ε omega) :
    aux_lfgc_root_impl_allOscLe T offset shift n z H' H ε omega := fun i => (h i).symm

variable {I M sigma T offset shift N n z}

theorem aux_lfgc_root_impl_not_nearAll_imp (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (h : ¬ aux_lfgc_root_stat_nearAll I M H sigma T offset shift N n z θ₀ omega) :
    1 / 2 ≤ aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega := by
  by_contra hlt
  push Not at hlt
  have hK : 0 < 2 / θ₀ := by positivity
  have hn := aux_lfgc_root_stat_norm_selOf_lt_of_phiStat_lt hK (by norm_num) hlt
  apply h
  refine (aux_lfgc_root_near_nearAll_iff_norm I M H sigma hsigma T offset shift N n z hθ₀.le omega).mpr ?_
  refine hn.le.trans ?_
  rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

theorem aux_lfgc_root_impl_not_nearAll_imp' (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) {θ₀ ε₁ : ℝ} (hθ₀ : 0 < θ₀)
    (hε₁ : 0 ≤ ε₁) (htol : aux_lfgc_near_tests_tolTransfer ε₁ (θ₀ / 4) ≤ θ₀)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (h : ¬ aux_lfgc_root_stat_nearAll I M H' sigma T offset shift N n z θ₀ omega) :
    1 / 2 ≤ aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega ∨
      ¬ aux_lfgc_root_impl_allOscLe T offset shift n z H H' ε₁ omega := by
  by_contra hno
  push Not at hno
  obtain ⟨hlt, hosc⟩ := hno
  have hK : 0 < 2 / θ₀ := by positivity
  have hn := aux_lfgc_root_stat_norm_selOf_lt_of_phiStat_lt hK (by norm_num) hlt
  have hnear : aux_lfgc_root_stat_nearAll I M H sigma T offset shift N n z (θ₀ / 4) omega := by
    refine (aux_lfgc_root_near_nearAll_iff_norm I M H sigma hsigma T offset shift N n z (by positivity) omega).mpr ?_
    refine hn.le.trans (le_of_eq ?_)
    field_simp; ring
  have h' := lfgc_root_near I M H H' sigma hsigma T offset shift N n z (by positivity) hε₁ omega
    hosc hnear
  exact h fun i => (h' i).mono htol

theorem aux_lfgc_root_impl_half_le_imp (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) {θ₀ ε₂ : ℝ} (hθ₀ : 0 < θ₀)
    (hε₂ : 0 ≤ ε₂) (htol : aux_lfgc_near_tests_tolTransfer ε₂ (θ₀ / 8) < θ₀ / 4)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (h : 1 / 2 ≤ aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega) :
    1 / 4 ≤ aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H' omega ∨
      ¬ aux_lfgc_root_impl_allOscLe T offset shift n z H' H ε₂ omega := by
  by_contra hno
  push Not at hno
  obtain ⟨hlt, hosc⟩ := hno
  have hK : 0 < 2 / θ₀ := by positivity
  have hn := aux_lfgc_root_stat_norm_selOf_lt_of_phiStat_lt hK (by norm_num) hlt
  have hnear : aux_lfgc_root_stat_nearAll I M H' sigma T offset shift N n z (θ₀ / 8) omega := by
    refine (aux_lfgc_root_near_nearAll_iff_norm I M H' sigma hsigma T offset shift N n z (by positivity) omega).mpr ?_
    refine hn.le.trans (le_of_eq ?_)
    field_simp; ring
  have h' := lfgc_root_near I M H' H sigma hsigma T offset shift N n z (by positivity) hε₂ omega
    hosc hnear
  have hnorm := (aux_lfgc_root_near_nearAll_iff_norm I M H sigma hsigma T offset shift N n z
    (aux_lfgc_root_impl_tolTransfer_nonneg _ _) omega).mp h'
  have hX := aux_lfgc_root_stat_phiStat_le_of_norm_le hK.le hnorm
  have : (2 / θ₀) * aux_lfgc_near_tests_tolTransfer ε₂ (θ₀ / 8) < 1 / 2 := by
    calc (2 / θ₀) * aux_lfgc_near_tests_tolTransfer ε₂ (θ₀ / 8) < (2 / θ₀) * (θ₀ / 4) :=
          mul_lt_mul_of_pos_left htol hK
      _ = 1 / 2 := by field_simp; ring
  unfold aux_lfgc_root_impl_rootX at h
  linarith

theorem lfgc_root_impl (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) {θ₀ ε : ℝ} (hθ₀ : 0 < θ₀)
    (hθ₀2 : θ₀ ≤ 2) (hε : 0 ≤ ε) (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (hosc : aux_lfgc_root_impl_allOscLe T offset shift n z H H' ε omega) :
    aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H' omega ≤
      aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega + (2 / θ₀) * aux_lfgc_root_impl_tolSlack ε := by
  have hK : 0 < 2 / θ₀ := by positivity
  have hslack : 0 ≤ aux_lfgc_root_impl_tolSlack ε := by
    unfold aux_lfgc_root_impl_tolSlack
    have := Real.one_le_exp hε
    have := Real.sqrt_nonneg (2 * (Real.exp ε - 1))
    linarith
  set s := ‖aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)‖
  by_cases hX : 1 ≤ (2 / θ₀) * s
  · have h1 : aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega = 1 := by
      unfold aux_lfgc_root_impl_rootX aux_lfgc_root_stat_phiStat; exact min_eq_left hX
    rw [h1]
    have := aux_lfgc_root_stat_phiStat_le_one (d := d) (2 / θ₀)
      (aux_lfgc_root_stat_bandCoords I M H' sigma sigma T offset shift N n z omega)
    have : 0 ≤ (2 / θ₀) * aux_lfgc_root_impl_tolSlack ε := mul_nonneg hK.le hslack
    unfold aux_lfgc_root_impl_rootX; linarith
  · push Not at hX
    have hs0 : 0 ≤ s := norm_nonneg _
    have hs1 : s ≤ 1 := by
      have h2 : (2 / θ₀) * s = 2 * s / θ₀ := by ring
      rw [h2, div_lt_one hθ₀] at hX
      linarith
    have hnear : aux_lfgc_root_stat_nearAll I M H sigma T offset shift N n z s omega :=
      (aux_lfgc_root_near_nearAll_iff_norm I M H sigma hsigma T offset shift N n z hs0 omega).mpr le_rfl
    have h' := lfgc_root_near I M H H' sigma hsigma T offset shift N n z hs0 hε omega hosc hnear
    have hnorm := (aux_lfgc_root_near_nearAll_iff_norm I M H' sigma hsigma T offset shift N n z
      (aux_lfgc_root_impl_tolTransfer_nonneg _ _) omega).mp h'
    have hX' := aux_lfgc_root_stat_phiStat_le_of_norm_le hK.le hnorm
    have htl := aux_lfgc_root_impl_tolTransfer_le hε hs0 hs1
    have hXH : aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega = (2 / θ₀) * s := by
      unfold aux_lfgc_root_impl_rootX aux_lfgc_root_stat_phiStat; exact min_eq_right hX.le
    unfold aux_lfgc_root_impl_rootX at hXH ⊢
    rw [hXH]
    calc aux_lfgc_root_stat_phiStat (2 / θ₀) (aux_lfgc_root_stat_bandCoords I M H' sigma sigma T offset shift N n z omega)
        ≤ (2 / θ₀) * aux_lfgc_near_tests_tolTransfer ε s := hX'
      _ ≤ (2 / θ₀) * (s + aux_lfgc_root_impl_tolSlack ε) := mul_le_mul_of_nonneg_left htl hK.le
      _ = (2 / θ₀) * s + (2 / θ₀) * aux_lfgc_root_impl_tolSlack ε := by ring

end SubdiffusiveProcess.Paper
