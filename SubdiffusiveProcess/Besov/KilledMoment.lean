module

public import SubdiffusiveProcess.Besov.DetachTheta

@[expose] public section

/-!
# First-moment duality on the unit cube

For `g` integrable on the unit cube `Q`, the first moment `⨍_Q g x_i` is bounded by
`Σ_{m<J} 3^{-(m+1)} theta Q (m+1) g ^{1/2} + 3^{-J}/2 ⨍_Q |g|` (the affine field `x_i`, seen through the block
averages of `g` at all depths).  Used for the mean part of `\eqref{e.CG.Poincare.trace.zero}`.
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

theorem dA_sub {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F G : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => F R - G R) =
      descendantsAverage Q j F - descendantsAverage Q j G := by
  unfold descendantsAverage
  dsimp only
  rw [Finset.sum_sub_distrib, mul_sub]

theorem dA_congr {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F G : TriadicCube d → ℝ)
    (h : ∀ R ∈ descendantsAtDepth Q j, F R = G R) :
    descendantsAverage Q j F = descendantsAverage Q j G := by
  unfold descendantsAverage
  dsimp only
  rw [Finset.sum_congr rfl h]

theorem dA_mono {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F G : TriadicCube d → ℝ)
    (h : ∀ R ∈ descendantsAtDepth Q j, F R ≤ G R) :
    descendantsAverage Q j F ≤ descendantsAverage Q j G := by
  unfold descendantsAverage
  dsimp only
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem abs_dA_le {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    |descendantsAverage Q j F| ≤ descendantsAverage Q j (fun R => |F R|) := by
  unfold descendantsAverage
  dsimp only
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem dA_abs_le_sqrt {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => |F R|) ≤
      Real.sqrt (descendantsAverage Q j (fun R => (F R) ^ 2)) := by
  have hpos : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  apply Real.le_sqrt_of_sq_le
  unfold descendantsAverage
  dsimp only
  have h := sq_sum_le_card_mul_sum_sq (s := descendantsAtDepth Q j) (f := fun R => |F R|)
  simp only [sq_abs] at h
  set n : ℝ := ((descendantsAtDepth Q j).card : ℝ)
  set S := ∑ R ∈ descendantsAtDepth Q j, |F R|
  set T := ∑ R ∈ descendantsAtDepth Q j, (F R) ^ 2
  calc (n⁻¹ * S) ^ 2 = (S ^ 2) / n ^ 2 := by field_simp
    _ ≤ (n * T) / n ^ 2 := by gcongr
    _ = n⁻¹ * T := by field_simp

theorem cubeCenter_originCube_zero {d : ℕ} (i : Fin d) : cubeCenter (originCube d 0) i = 0 := by
  simp [cubeCenter, originCube]

theorem child_center_diff {d : ℕ} {R R' : TriadicCube d} (h : R' ∈ childCubes R) (i : Fin d) :
    |cubeCenter R' i - cubeCenter R i| ≤ cubeScaleFactor R' := by
  obtain ⟨δ, rfl⟩ := mem_childCubes_iff.mp h
  simp only [cubeCenter, cubeScaleFactor]
  have h3 : (3 : ℝ) ^ (R.scale - 1) > 0 := zpow_pos (by norm_num) _
  have hs : (3 : ℝ) ^ R.scale = 3 * (3 : ℝ) ^ (R.scale - 1) := by
    rw [show R.scale = (R.scale - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]
    simp; ring
  have hδ0 : (0 : ℝ) ≤ ((δ i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hδ2 : ((δ i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp (δ i).isLt
  have : ((3 * R.index i + ((δ i : ℕ) : ℤ) - 1 : ℤ) : ℝ) * (3 : ℝ) ^ (R.scale - 1) -
      (R.index i : ℝ) * (3 : ℝ) ^ R.scale = (((δ i : ℕ) : ℝ) - 1) * (3 : ℝ) ^ (R.scale - 1) := by
    rw [hs]; push_cast; ring
  rw [this, abs_mul, abs_of_pos h3]
  have : |((δ i : ℕ) : ℝ) - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  nlinarith

theorem coord_sub_center_le {d : ℕ} {R : TriadicCube d} {x : Vec d} (hx : x ∈ cubeSet R) (i : Fin d) :
    |x i - cubeCenter R i| ≤ cubeScaleFactor R / 2 := by
  have h := hx i
  simp only [cubeCenter] at *
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]


/-- The `i`-th first moment of the block averages of `g` at depth `j`. -/
noncomputable def momAvg {d : ℕ} (g : Vec d → ℝ) (i : Fin d) (j : ℕ) : ℝ :=
  descendantsAverage (originCube d 0) j (fun R => cubeAverage R g * cubeCenter R i)

theorem momAvg_zero {d : ℕ} (g : Vec d → ℝ) (i : Fin d) : momAvg g i 0 = 0 := by
  unfold momAvg descendantsAverage
  simp [cubeCenter_originCube_zero]

theorem momAvg_step {d : ℕ} (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet (originCube d 0)) volume) (i : Fin d) (j : ℕ) :
    |momAvg g i (j + 1) - momAvg g i j| ≤
      ((3 : ℝ) ^ (j + 1))⁻¹ * Real.sqrt (theta (originCube d 0) (j + 1) g) := by
  set Q := originCube d 0 with hQ
  set a : TriadicCube d → ℝ := fun R => cubeAverage R g with ha
  set c : TriadicCube d → ℝ := fun R => cubeCenter R i with hc
  have hstep := descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q j 1
    (fun R => a R * c R)
  have hK : ∀ R ∈ descendantsAtDepth Q j,
      |descendantsAverage R 1 (fun R' => a R' * c R') - a R * c R| ≤
        ((3 : ℝ) ^ (j + 1))⁻¹ * descendantsAverage R 1 (fun R' => |a R'|) := by
    intro R hR
    have hsc : R.scale = -(j : ℤ) := by
      have := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa [hQ, originCube] using this
    have hgR : IntegrableOn g (cubeSet R) volume :=
      hg.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have h1 : a R = descendantsAverage R 1 a :=
      cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn R 1 g hgR
    have h2 : a R * c R = descendantsAverage R 1 (fun R' => a R' * c R) := by
      rw [h1]
      unfold descendantsAverage
      dsimp only
      rw [mul_assoc, Finset.sum_mul]
    have h3 : descendantsAverage R 1 (fun R' => a R' * c R') - a R * c R =
        descendantsAverage R 1 (fun R' => a R' * (c R' - c R)) := by
      rw [h2, ← dA_sub]
      exact dA_congr R 1 _ _ (fun R' _ => by ring)
    rw [h3]
    refine (abs_dA_le R 1 _).trans ?_
    have h4 : descendantsAverage R 1 (fun R' => |a R' * (c R' - c R)|) ≤
        descendantsAverage R 1 (fun R' => ((3 : ℝ) ^ (j + 1))⁻¹ * |a R'|) := by
      apply dA_mono
      intro R' hR'
      rw [descendantsAtDepth_one] at hR'
      have := child_center_diff hR' i
      have hs' : cubeScaleFactor R' = ((3 : ℝ) ^ (j + 1))⁻¹ := by
        have hsR' : R'.scale = R.scale - 1 := child_scale_of_mem_childCubes hR'
        simp only [cubeScaleFactor, hsR', hsc]
        rw [show (-(j : ℤ) - 1) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
      rw [abs_mul, mul_comm]
      rw [hs'] at this
      simp only [hc] at this ⊢
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    exact h4.trans (le_of_eq (descendantsAverage_mul_left R 1 _ _))
  unfold momAvg
  rw [hstep, ← dA_sub]
  refine (abs_dA_le Q j _).trans ?_
  refine (dA_mono Q j _ _ hK).trans ?_
  rw [descendantsAverage_mul_left,
    ← descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q j 1 (fun R => |a R|)]
  exact mul_le_mul_of_nonneg_left (dA_abs_le_sqrt Q (j + 1) a) (by positivity)


theorem cubeAverage_abs_le {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ) :
    |cubeAverage R f| ≤ cubeAverage R (fun x => |f x|) := by
  unfold cubeAverage
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (cubeVolume_pos R).le)]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_integral_le_integral_norm (μ := volume.restrict (cubeSet R)) f)
    (inv_nonneg.mpr (cubeVolume_pos R).le)

theorem cubeAverage_mono_on {d : ℕ} (R : TriadicCube d) (f h : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet R) volume) (hh : IntegrableOn h (cubeSet R) volume)
    (hle : ∀ x ∈ cubeSet R, f x ≤ h x) : cubeAverage R f ≤ cubeAverage R h := by
  unfold cubeAverage
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_on hf hh (measurableSet_cubeSet R) hle) (inv_nonneg.mpr (cubeVolume_pos R).le)

theorem cubeAverage_const_mul {d : ℕ} (R : TriadicCube d) (K : ℝ) (f : Vec d → ℝ) :
    cubeAverage R (fun x => K * f x) = K * cubeAverage R f := by
  unfold cubeAverage
  rw [integral_const_mul]
  ring

theorem cubeAverage_sub {d : ℕ} (R : TriadicCube d) (f h : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet R) volume) (hh : IntegrableOn h (cubeSet R) volume) :
    cubeAverage R (fun x => f x - h x) = cubeAverage R f - cubeAverage R h := by
  unfold cubeAverage
  rw [integral_sub hf hh]
  ring


theorem abs_coord_le_cubeSet {d : ℕ} (x : Vec d) (hx : x ∈ cubeSet (originCube d 0)) (i : Fin d) :
    |x i| ≤ 1 / 2 := by
  have := coord_sub_center_le hx i
  rw [cubeCenter_originCube_zero, sub_zero] at this
  simpa [originCube, cubeScaleFactor] using this

theorem first_moment_close {d : ℕ} (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet (originCube d 0)) volume) (i : Fin d) (J : ℕ) :
    |cubeAverage (originCube d 0) (fun x => g x * x i) - momAvg g i J| ≤
      ((3 : ℝ) ^ J)⁻¹ / 2 * cubeAverage (originCube d 0) (fun x => |g x|) := by
  set Q := originCube d 0 with hQ
  have hM : ∀ᵐ x ∂(volume.restrict (cubeSet Q)), ‖x i‖ ≤ 1 / 2 := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    simpa [Real.norm_eq_abs] using abs_coord_le_cubeSet x hx i
  have hgξ : IntegrableOn (fun x => g x * x i) (cubeSet Q) volume :=
    hg.mul_bdd (continuous_apply i).aestronglyMeasurable hM
  have hI := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q J
    (fun x => g x * x i) hgξ
  have hIabs := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q J
    (fun x => |g x|) hg.abs
  unfold momAvg
  rw [hI, ← dA_sub]
  refine (abs_dA_le Q J _).trans ?_
  have hpt : ∀ R ∈ descendantsAtDepth Q J,
      |cubeAverage R (fun x => g x * x i) - cubeAverage R g * cubeCenter R i| ≤
        ((3 : ℝ) ^ J)⁻¹ / 2 * cubeAverage R (fun x => |g x|) := by
    intro R hR
    have hsc : R.scale = -(J : ℤ) := by
      have := scale_eq_sub_of_mem_descendantsAtDepth hR
      simpa [hQ, originCube] using this
    have hsub := cubeSet_subset_of_mem_descendantsAtDepth hR
    have hgR : IntegrableOn g (cubeSet R) volume := hg.mono_set hsub
    have hgξR : IntegrableOn (fun x => g x * x i) (cubeSet R) volume := hgξ.mono_set hsub
    set c := cubeCenter R i with hc
    have hs : cubeScaleFactor R = ((3 : ℝ) ^ J)⁻¹ := by
      simp only [cubeScaleFactor, hsc]
      rw [zpow_neg, zpow_natCast]
    have h1 : cubeAverage R (fun x => g x * x i) - cubeAverage R g * c =
        cubeAverage R (fun x => g x * x i - c * g x) := by
      rw [cubeAverage_sub R _ _ hgξR (hgR.const_mul c), cubeAverage_const_mul]
      ring
    rw [h1]
    refine (cubeAverage_abs_le R _).trans ?_
    have hint : IntegrableOn (fun x => |g x * x i - c * g x|) (cubeSet R) volume :=
      (hgξR.sub (hgR.const_mul c)).abs
    have hint2 : IntegrableOn (fun x => cubeScaleFactor R / 2 * |g x|) (cubeSet R) volume :=
      hgR.abs.const_mul _
    have h2 := cubeAverage_mono_on R _ (fun x => cubeScaleFactor R / 2 * |g x|) hint hint2 (by
      intro x hx
      have hb := coord_sub_center_le hx i
      rw [show g x * x i - c * g x = g x * (x i - c) by ring, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    rw [cubeAverage_const_mul, hs] at h2
    rw [div_eq_mul_inv]
    exact h2
  refine (dA_mono Q J _ _ hpt).trans ?_
  rw [descendantsAverage_mul_left, ← hIabs]


/-- **First moment bound.** For `g` integrable on the unit cube, the first moment
`⨍_Q g x_i` is bounded by the multiscale sum of the block averages of `g`. -/
theorem first_moment_le {d : ℕ} (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet (originCube d 0)) volume) (i : Fin d) (J : ℕ) :
    |cubeAverage (originCube d 0) (fun x => g x * x i)| ≤
      ∑ m ∈ Finset.range J, ((3 : ℝ) ^ (m + 1))⁻¹ *
        Real.sqrt (theta (originCube d 0) (m + 1) g) +
      ((3 : ℝ) ^ J)⁻¹ / 2 * cubeAverage (originCube d 0) (fun x => |g x|) := by
  have h1 := first_moment_close g hg i J
  have h2 : |momAvg g i J| ≤ ∑ m ∈ Finset.range J, ((3 : ℝ) ^ (m + 1))⁻¹ *
      Real.sqrt (theta (originCube d 0) (m + 1) g) := by
    have htel : momAvg g i J = ∑ m ∈ Finset.range J, (momAvg g i (m + 1) - momAvg g i m) := by
      rw [Finset.sum_range_sub (fun m => momAvg g i m), momAvg_zero, sub_zero]
    rw [htel]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun m _ => momAvg_step g hg i m)
  have h3 : |cubeAverage (originCube d 0) (fun x => g x * x i)| ≤
      |cubeAverage (originCube d 0) (fun x => g x * x i) - momAvg g i J| + |momAvg g i J| := by
    have := abs_add_le (cubeAverage (originCube d 0) (fun x => g x * x i) - momAvg g i J)
      (momAvg g i J)
    simpa using this
  linarith


end

end SubdiffusiveProcess.Besov.Detach
