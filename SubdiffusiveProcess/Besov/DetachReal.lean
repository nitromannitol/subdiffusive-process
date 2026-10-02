import Mathlib

/-!
# Real-variable lemma for the detach inequality

Step 2 of the proof of `\eqref{e.nabla.u.detach}` (`inputs_poincare_detach_interior`): for a nondecreasing
bounded nonnegative sequence `X`, weights `3^{-m}` shifted by `j` are dominated by `2 s` times the sum of
`3^{-s m} X m`, uniformly in `s ∈ (0,1)` and `j`.
-/

namespace SubdiffusiveProcess.Besov.Detach

/-- `1 - 3^{-s} ≤ s log 3`. -/
theorem one_sub_three_rpow_neg_le (s : ℝ) (hs : 0 ≤ s) :
    1 - (3 : ℝ) ^ (-s) ≤ s * Real.log 3 := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have hpow : (3:ℝ) ^ (-s) = Real.exp (Real.log 3 * (-s)) := Real.rpow_def_of_pos h3 (-s)
  have hle : -(s * Real.log 3) + 1 ≤ Real.exp (-(s * Real.log 3)) := Real.add_one_le_exp (-(s * Real.log 3))
  have harg : Real.log 3 * (-s) = -(s * Real.log 3) := by ring
  rw [harg] at hpow
  linarith

/-- Summability of the geometric-weighted bounded sequence `3^{-s m} X m`. -/
theorem summable_weighted (s : ℝ) (hs : 0 < s) (X : ℕ → ℝ) (hX0 : ∀ m, 0 ≤ X m) (G : ℝ)
    (hG : ∀ m, X m ≤ G) :
    Summable (fun m : ℕ => (3 : ℝ) ^ (-s * (m : ℝ)) * X m) := by
  let r : ℝ := (3 : ℝ) ^ (-s)
  have h3nonneg : (0 : ℝ) ≤ 3 := by norm_num
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg h3nonneg (-s)
  have hsneg : -s < 0 := by linarith
  have hr_lt_one : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hsneg
  have hgeom : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have hmaj : Summable (fun m : ℕ => G * r ^ m) := hgeom.mul_left G
  refine Summable.of_nonneg_of_le ?_ ?_ hmaj
  · intro m
    exact mul_nonneg (Real.rpow_nonneg h3nonneg _) (hX0 m)
  · intro m
    have heq : (3 : ℝ) ^ (-s * (m : ℝ)) = r ^ m := by
      rw [Real.rpow_mul h3nonneg, Real.rpow_natCast]
    rw [heq]
    calc r ^ m * X m ≤ r ^ m * G := by
          apply mul_le_mul_of_nonneg_left (hG m)
          exact pow_nonneg hr_nonneg m
      _ = G * r ^ m := by ring

/-- Summability of the shifted `3^{-m}` weighted bounded sequence. -/
theorem summable_shift (j : ℕ) (X : ℕ → ℝ) (hX0 : ∀ m, 0 ≤ X m) (G : ℝ) (hG : ∀ m, X m ≤ G) :
    Summable (fun k : ℕ => ((3 : ℝ) ^ (j + 1 + k))⁻¹ * X (j + 1 + k)) := by
  have hbound : ∀ k : ℕ,
      ((3 : ℝ) ^ (j + 1 + k))⁻¹ * X (j + 1 + k)
        ≤ G * ((3 : ℝ) ^ (j + 1))⁻¹ * (1 / 3 : ℝ) ^ k := by
    intro k
    have hpow : (3 : ℝ) ^ (j + 1 + k) = (3 : ℝ) ^ (j + 1) * (3 : ℝ) ^ k := by
      rw [pow_add]
    have hpowinv : ((3 : ℝ) ^ (j + 1 + k))⁻¹
        = ((3 : ℝ) ^ (j + 1))⁻¹ * ((3 : ℝ) ^ k)⁻¹ := by
      rw [hpow, mul_inv]
    have hk : ((3 : ℝ) ^ k)⁻¹ = (1 / 3 : ℝ) ^ k := by
      rw [one_div, inv_pow]
    calc
      ((3 : ℝ) ^ (j + 1 + k))⁻¹ * X (j + 1 + k)
          = ((3 : ℝ) ^ (j + 1))⁻¹ * ((3 : ℝ) ^ k)⁻¹ * X (j + 1 + k) := by
            rw [hpowinv]
      _ = ((3 : ℝ) ^ (j + 1))⁻¹ * (1 / 3 : ℝ) ^ k * X (j + 1 + k) := by
            rw [hk]
      _ ≤ ((3 : ℝ) ^ (j + 1))⁻¹ * (1 / 3 : ℝ) ^ k * G := by
            exact mul_le_mul_of_nonneg_left (hG (j + 1 + k)) (by positivity)
      _ = G * ((3 : ℝ) ^ (j + 1))⁻¹ * (1 / 3 : ℝ) ^ k := by
            ring
  have hsum : Summable (fun k : ℕ => G * ((3 : ℝ) ^ (j + 1))⁻¹ * (1 / 3 : ℝ) ^ k) := by
    have hg : Summable (fun k : ℕ => (1 / 3 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hmul := hg.mul_left (G * ((3 : ℝ) ^ (j + 1))⁻¹)
    simpa [mul_assoc] using hmul
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (hX0 (j + 1 + k)))
    hbound hsum

/-- Monotone case of the single-term bound: `y_m ≤ (1 - 3^{-s}) * Σ y`. -/
theorem term_le_of_mono (s : ℝ) (hs : 0 < s) (X : ℕ → ℝ) (hX0 : ∀ m, 0 ≤ X m)
    (hmono : ∀ m, X m ≤ X (m + 1)) (G : ℝ) (hG : ∀ m, X m ≤ G) (m : ℕ) :
    (3 : ℝ) ^ (-s * (m : ℝ)) * X m ≤
      (1 - (3 : ℝ) ^ (-s)) * ∑' n : ℕ, (3 : ℝ) ^ (-s * (n : ℝ)) * X n := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  have hr0 : 0 < (3:ℝ)^(-s) := Real.rpow_pos_of_pos h3pos _
  have hr0le : (0:ℝ) ≤ (3:ℝ)^(-s) := le_of_lt hr0
  have hr1 : (3:ℝ)^(-s) < 1 := by
    have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 3)).mpr (by linarith : -s < 0)
    rwa [Real.rpow_zero] at h
  have h1mr : (0:ℝ) < 1 - (3:ℝ)^(-s) := by linarith
  have h1mr_ne : (1:ℝ) - (3:ℝ)^(-s) ≠ 0 := ne_of_gt h1mr
  have hXmono : Monotone X := monotone_nat_of_le_succ hmono
  have hsum : Summable (fun n : ℕ => (3:ℝ)^(-s*(n:ℝ)) * X n) :=
    summable_weighted s hs X hX0 G hG
  have hrpow : ∀ n : ℕ, (3:ℝ)^(-s*((n:ℝ))) = ((3:ℝ)^(-s))^n := by
    intro n
    rw [Real.rpow_mul (le_of_lt h3pos) (-s) (n:ℝ), Real.rpow_natCast]
  have hkey : ∀ k : ℕ,
      ((3:ℝ)^(-s))^k * (((3:ℝ)^(-s))^m * X m) ≤
        (3:ℝ)^(-s*((k+m:ℕ):ℝ)) * X (k+m) := by
    intro k
    have hXle : X m ≤ X (k+m) := hXmono (Nat.le_add_left m k)
    rw [hrpow (k+m), pow_add]
    calc ((3:ℝ)^(-s))^k * (((3:ℝ)^(-s))^m * X m)
        = ((3:ℝ)^(-s))^k * ((3:ℝ)^(-s))^m * X m := by ring
      _ ≤ ((3:ℝ)^(-s))^k * ((3:ℝ)^(-s))^m * X (k+m) :=
          mul_le_mul_of_nonneg_left hXle (by positivity)
  have hsum_f : Summable (fun k : ℕ => ((3:ℝ)^(-s))^k * (((3:ℝ)^(-s))^m * X m)) :=
    (summable_geometric_of_lt_one hr0le hr1).mul_right _
  have hsum_g : Summable (fun k : ℕ => (3:ℝ)^(-s*((k+m:ℕ):ℝ)) * X (k+m)) :=
    (summable_nat_add_iff m).mpr hsum
  have hle1 : ∑' k : ℕ, ((3:ℝ)^(-s))^k * (((3:ℝ)^(-s))^m * X m) ≤
      ∑' k : ℕ, (3:ℝ)^(-s*((k+m:ℕ):ℝ)) * X (k+m) :=
    Summable.tsum_le_tsum hkey hsum_f hsum_g
  have hY := Summable.sum_add_tsum_nat_add m hsum
  have hfin_nonneg : 0 ≤ ∑ i ∈ Finset.range m, (3:ℝ)^(-s*(i:ℝ)) * X i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hX0 i))
  have hle2 : ∑' k : ℕ, (3:ℝ)^(-s*((k+m:ℕ):ℝ)) * X (k+m) ≤
      ∑' n : ℕ, (3:ℝ)^(-s*(n:ℝ)) * X n := by
    linarith
  have hle3 : ∑' k : ℕ, ((3:ℝ)^(-s))^k * (((3:ℝ)^(-s))^m * X m) ≤
      ∑' n : ℕ, (3:ℝ)^(-s*(n:ℝ)) * X n := le_trans hle1 hle2
  have hgeom : ∑' k : ℕ, ((3:ℝ)^(-s))^k = (1 - (3:ℝ)^(-s))⁻¹ :=
    tsum_geometric_of_lt_one hr0le hr1
  have hLHS_eq : ∑' k : ℕ, ((3:ℝ)^(-s))^k * (((3:ℝ)^(-s))^m * X m) =
      (1 - (3:ℝ)^(-s))⁻¹ * (((3:ℝ)^(-s))^m * X m) := by
    rw [tsum_mul_right, hgeom]
  have hle4 : (1 - (3:ℝ)^(-s))⁻¹ * (((3:ℝ)^(-s))^m * X m) ≤
      ∑' n : ℕ, (3:ℝ)^(-s*(n:ℝ)) * X n := hLHS_eq ▸ hle3
  have hmul := mul_le_mul_of_nonneg_left hle4 (le_of_lt h1mr)
  have hfinal : (1 - (3:ℝ)^(-s)) * ((1 - (3:ℝ)^(-s))⁻¹ * (((3:ℝ)^(-s))^m * X m)) =
      ((3:ℝ)^(-s))^m * X m := by
    rw [← mul_assoc, mul_inv_cancel₀ h1mr_ne, one_mul]
  calc (3:ℝ)^(-s*(m:ℝ)) * X m
      = ((3:ℝ)^(-s))^m * X m := by rw [hrpow m]
    _ = (1 - (3:ℝ)^(-s)) * ((1 - (3:ℝ)^(-s))⁻¹ * (((3:ℝ)^(-s))^m * X m)) := hfinal.symm
    _ ≤ (1 - (3:ℝ)^(-s)) * ∑' n : ℕ, (3:ℝ)^(-s*(n:ℝ)) * X n := hmul

/-- Geometric tail: `Σ_{k ≥ 1} 3^{-k/2} ≤ 3/2`. -/
theorem geom_tail_le : ∑' k : ℕ, (3 : ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) ≤ 3 / 2 := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  set r : ℝ := (3:ℝ)^(-(1/2:ℝ)) with hr
  have hr_nonneg : 0 ≤ r := by
    rw [hr]; exact Real.rpow_nonneg (le_of_lt h3pos) _
  have hr_sq : r ^ 2 = 1/3 := by
    have h : r ^ ((2:ℕ):ℝ) = 1/3 := by
      rw [hr, ← Real.rpow_mul (le_of_lt h3pos) (-(1/2:ℝ)) ((2:ℕ):ℝ)]
      rw [show -(1/2:ℝ) * ((2:ℕ):ℝ) = -1 by norm_num, Real.rpow_neg_one]
      norm_num
    rw [Real.rpow_natCast] at h
    exact h
  have hr_le : r ≤ 3/5 := by
    have hprod : (3/5 - r) * (3/5 + r) = 2/75 := by nlinarith [hr_sq]
    have hpos2 : 0 < 3/5 + r := by linarith
    nlinarith [hprod]
  have hr_lt_one : r < 1 := by linarith
  have hgoal : ∑' k : ℕ, (3:ℝ) ^ (-((k + 1 : ℕ) : ℝ) / 2) = r * (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr_nonneg hr_lt_one, ← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [hr]
    rw [show -((k + 1 : ℕ) : ℝ) / 2 = (-(1/2:ℝ)) * ((k + 1 : ℕ) : ℝ) by ring]
    rw [Real.rpow_mul (le_of_lt h3pos), Real.rpow_natCast, pow_succ']
  have hInv : (1 - r)⁻¹ ≤ (5:ℝ)/2 := by
    have h := (inv_le_inv₀ (by linarith : (0:ℝ) < 1 - r) (by norm_num : (0:ℝ) < 2/5)).mpr (by linarith : (2:ℝ)/5 ≤ 1 - r)
    norm_num at h
    exact h
  rw [hgoal]
  have hprod := mul_le_mul hr_le hInv (inv_nonneg.mpr (by linarith : (0:ℝ) ≤ 1 - r)) (by norm_num : (0:ℝ) ≤ 3/5)
  norm_num at hprod
  linarith

/-- Case `s ≥ 1/2` of the real lemma. -/
theorem detach_real_large (s : ℝ) (hs : 1 / 2 ≤ s) (hs1 : s < 1) (X : ℕ → ℝ) (hX0 : ∀ m, 0 ≤ X m)
    (G : ℝ) (hG : ∀ m, X m ≤ G) (j : ℕ) :
    (3 : ℝ) ^ ((j : ℝ) * (1 - s)) * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * X (j + 1 + k) ≤
      2 * s * ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * X m := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  have h3one : (1:ℝ) ≤ 3 := by norm_num
  have hspos : 0 < s := by linarith
  have hs1' : 0 ≤ 1 - s := by linarith
  -- termwise coefficient bound
  have hcoef : ∀ k : ℕ, (3:ℝ)^((j:ℝ)*(1-s)) * ((3:ℝ)^(j+1+k))⁻¹ ≤ (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) := by
    intro k
    have h1 : ((3:ℝ)^(j+1+k))⁻¹ = (3:ℝ)^(-((j+1+k:ℕ):ℝ)) := by
      rw [← Real.rpow_natCast (3:ℝ) (j+1+k)]
      exact (Real.rpow_neg (le_of_lt h3pos) ((j+1+k:ℕ):ℝ)).symm
    have hexp : (j:ℝ)*(1-s) + -((j+1+k:ℕ):ℝ) ≤ -s*((j+1+k:ℕ):ℝ) := by
      have hcast : ((j+1+k:ℕ):ℝ) = (j:ℝ) + 1 + (k:ℝ) := by push_cast; ring
      rw [hcast]
      have hk : (0:ℝ) ≤ (k:ℝ) + 1 := by positivity
      nlinarith [mul_nonneg hs1' hk]
    calc (3:ℝ)^((j:ℝ)*(1-s)) * ((3:ℝ)^(j+1+k))⁻¹
        = (3:ℝ)^((j:ℝ)*(1-s)) * (3:ℝ)^(-((j+1+k:ℕ):ℝ)) := by rw [h1]
      _ = (3:ℝ)^((j:ℝ)*(1-s) + -((j+1+k:ℕ):ℝ)) := (Real.rpow_add h3pos _ _).symm
      _ ≤ (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) := Real.rpow_le_rpow_of_exponent_le h3one hexp
  -- termwise bound with X
  have hterm : ∀ k : ℕ, (3:ℝ)^((j:ℝ)*(1-s)) * (((3:ℝ)^(j+1+k))⁻¹ * X (j+1+k)) ≤ (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k) := by
    intro k
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcoef k) (hX0 (j+1+k))
  -- summability
  have hF : Summable (fun k : ℕ => (3:ℝ)^((j:ℝ)*(1-s)) * (((3:ℝ)^(j+1+k))⁻¹ * X (j+1+k))) :=
    (summable_shift j X hX0 G hG).mul_left _
  have hy : Summable (fun m : ℕ => (3:ℝ)^(-s*(m:ℝ)) * X m) := summable_weighted s hspos X hX0 G hG
  have hg : Summable (fun k : ℕ => (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) := by
    have h := (summable_nat_add_iff (f := fun m : ℕ => (3:ℝ)^(-s*(m:ℝ)) * X m) (j+1)).mpr hy
    simpa [Nat.add_comm] using h
  have hle1 : ∑' k : ℕ, (3:ℝ)^((j:ℝ)*(1-s)) * (((3:ℝ)^(j+1+k))⁻¹ * X (j+1+k)) ≤ ∑' k : ℕ, (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k) :=
    Summable.tsum_le_tsum hterm hF hg
  have hshift : ∑' k : ℕ, (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k) ≤ ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m := by
    have h := Summable.sum_add_tsum_nat_add (f := fun m : ℕ => (3:ℝ)^(-s*(m:ℝ)) * X m) (j+1) hy
    have hfin : 0 ≤ ∑ i ∈ Finset.range (j+1), (3:ℝ)^(-s*(i:ℝ)) * X i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg h3pos.le _) (hX0 i))
    have h2 : ∑' i : ℕ, (3:ℝ)^(-s*((i+(j+1):ℕ):ℝ)) * X (i+(j+1)) ≤ ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m := by linarith
    have heq : (∑' k : ℕ, (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) = ∑' i : ℕ, (3:ℝ)^(-s*((i+(j+1):ℕ):ℝ)) * X (i+(j+1)) := by
      apply tsum_congr
      intro k
      rw [Nat.add_comm (j+1) k]
    rw [heq]
    exact h2
  have hscale : ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m ≤ 2 * s * ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m := by
    have hnn : 0 ≤ ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m :=
      tsum_nonneg (fun m => mul_nonneg (Real.rpow_nonneg h3pos.le _) (hX0 m))
    have h1 : (1:ℝ) ≤ 2*s := by linarith
    nlinarith [hnn, h1]
  calc (3:ℝ)^((j:ℝ)*(1-s)) * ∑' k : ℕ, ((3:ℝ)^(j+1+k))⁻¹ * X (j+1+k)
      = ∑' k : ℕ, (3:ℝ)^((j:ℝ)*(1-s)) * (((3:ℝ)^(j+1+k))⁻¹ * X (j+1+k)) := by rw [tsum_mul_left]
    _ ≤ ∑' k : ℕ, (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k) := hle1
    _ ≤ ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m := hshift
    _ ≤ 2 * s * ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m := hscale

/-- Case `s < 1/2` of the real lemma (uses monotonicity of `X`). -/
theorem detach_real_small (s : ℝ) (hs0 : 0 < s) (hs : s < 1 / 2) (X : ℕ → ℝ) (hX0 : ∀ m, 0 ≤ X m)
    (hmono : ∀ m, X m ≤ X (m + 1)) (G : ℝ) (hG : ∀ m, X m ≤ G) (j : ℕ) :
    (3 : ℝ) ^ ((j : ℝ) * (1 - s)) * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * X (j + 1 + k) ≤
      2 * s * ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * X m := by
  have h3pos : (0:ℝ) < 3 := by norm_num
  have h3le1 : (3:ℝ)^(-s) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 3 by norm_num) (show -s ≤ 0 by linarith)
    simpa using h
  set Y : ℝ := ∑' m : ℕ, (3:ℝ)^(-s*(m:ℝ)) * X m with hYdef
  have hc0 : 0 ≤ 1 - (3:ℝ)^(-s) := by linarith
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    exact tsum_nonneg (fun m => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hX0 m))
  have hcle : 1 - (3:ℝ)^(-s) ≤ s * Real.log 3 := one_sub_three_rpow_neg_le s (le_of_lt hs0)
  have hlog3 : Real.log 3 ≤ 4/3 := by
    have h1 : Real.log 3 = Real.log 2 + Real.log (3/2) := by
      rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : ((3:ℝ)/2) ≠ 0)]
      norm_num
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h3 : Real.log ((3:ℝ)/2) ≤ (3:ℝ)/2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [h1]; linarith
  have hterm_le : ∀ k : ℕ, (3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k) ≤ (1 - (3:ℝ)^(-s)) * Y := by
    intro k
    have h := term_le_of_mono s hs0 X hX0 hmono G hG (j+1+k)
    rwa [← hYdef] at h
  have hterm : ∀ k : ℕ, (3:ℝ)^((j:ℝ)*(1-s)) * (((3:ℝ)^(j+1+k))⁻¹ * X (j+1+k))
      = (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) * ((3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) := by
    intro k
    have hb : ((3:ℝ)^(j+1+k))⁻¹ = (3:ℝ)^(-(((j+1+k:ℕ):ℝ))) := by
      rw [← Real.rpow_natCast (3:ℝ) (j+1+k), ← Real.rpow_neg (le_of_lt h3pos)]
    have hexp : (j:ℝ)*(1-s) + (-(((j+1+k:ℕ):ℝ))) = -(1-s)*((k+1:ℕ):ℝ) + (-s*((j+1+k:ℕ):ℝ)) := by
      push_cast; ring
    rw [hb]
    rw [← mul_assoc, ← Real.rpow_add h3pos, hexp, Real.rpow_add h3pos]
    ring
  rw [← tsum_mul_left]
  simp_rw [hterm]
  set r : ℝ := (3:ℝ)^(-(1/2:ℝ)) with hrdef
  have hrk : ∀ k : ℕ, r^(k+1) = (3:ℝ)^(-(((k+1:ℕ):ℝ))/2) := by
    intro k
    rw [hrdef, ← Real.rpow_natCast ((3:ℝ)^(-(1/2:ℝ))) (k+1),
      ← Real.rpow_mul (le_of_lt h3pos) (-(1/2)) ((k+1:ℕ):ℝ)]
    congr 1
    ring
  have hgeom : Summable (fun k : ℕ => r^k) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs]
    have hpos : (0:ℝ) ≤ r := by rw [hrdef]; exact Real.rpow_nonneg (by norm_num) _
    rw [abs_of_nonneg hpos, hrdef]
    have heq : (3:ℝ)^(-(1/2:ℝ)) = ((3:ℝ)^((1/2:ℝ)))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
    rw [heq]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hgshift : Summable (fun k : ℕ => r^(k+1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => r^n) 1).mpr hgeom
  have hg2 : Summable (fun k : ℕ => (3:ℝ)^(-(((k+1:ℕ):ℝ))/2)) :=
    hgshift.congr (fun k => hrk k)
  let g : ℕ → ℝ := fun k => (3:ℝ)^(-(((k+1:ℕ):ℝ))/2) * ((1 - (3:ℝ)^(-s)) * Y)
  have hsum_g : Summable g := by
    simpa only [g] using hg2.mul_right ((1 - (3:ℝ)^(-s)) * Y)
  have hsum_g_val : ∑' k, g k = (∑' k, (3:ℝ)^(-(((k+1:ℕ):ℝ))/2)) * ((1 - (3:ℝ)^(-s)) * Y) := by
    simp only [g]
    rw [tsum_mul_right]
  have hg_le : ∑' k, g k ≤ (3/2) * ((1 - (3:ℝ)^(-s)) * Y) := by
    rw [hsum_g_val]
    exact mul_le_mul_of_nonneg_right geom_tail_le (mul_nonneg hc0 hY0)
  have hfnn : ∀ k : ℕ, 0 ≤ (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) * ((3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) :=
    fun k => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hX0 _))
  have hf_le_g : ∀ k : ℕ, (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) * ((3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) ≤ g k := by
    intro k
    simp only [g]
    have h1 : (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) ≤ (3:ℝ)^(-(((k+1:ℕ):ℝ))/2) := by
      apply Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 3 by norm_num)
      have hs' : (1:ℝ)/2 ≤ 1 - s := by linarith
      nlinarith [show (0:ℝ) ≤ ((k+1:ℕ):ℝ) by positivity]
    exact mul_le_mul h1 (hterm_le k) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hX0 _)) (Real.rpow_nonneg (by norm_num) _)
  have hsum_f : Summable (fun k : ℕ => (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) * ((3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k))) :=
    Summable.of_nonneg_of_le hfnn hf_le_g hsum_g
  have hcf : ∑' k, (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) * ((3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) ≤ ∑' k, g k :=
    Summable.tsum_le_tsum hf_le_g hsum_f hsum_g
  have htotal : ∑' k, (3:ℝ)^(-(1-s)*((k+1:ℕ):ℝ)) * ((3:ℝ)^(-s*((j+1+k:ℕ):ℝ)) * X (j+1+k)) ≤
      (3/2) * ((1 - (3:ℝ)^(-s)) * Y) := le_trans hcf hg_le
  refine le_trans htotal ?_
  have hlog32 : (3/2:ℝ)*Real.log 3 ≤ 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcle hY0, hlog32,
    mul_nonneg (le_of_lt hs0) hY0, hY0, hc0]

/-- **Real lemma R1.** -/
theorem detach_real (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (X : ℕ → ℝ) (hX0 : ∀ m, 0 ≤ X m)
    (hmono : ∀ m, X m ≤ X (m + 1)) (G : ℝ) (hG : ∀ m, X m ≤ G) (j : ℕ) :
    (3 : ℝ) ^ ((j : ℝ) * (1 - s)) * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * X (j + 1 + k) ≤
      2 * s * ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * X m := by
  by_cases h : 1 / 2 ≤ s
  · exact detach_real_large s h hs1 X hX0 G hG j
  · exact detach_real_small s hs0 (not_le.mp h) X hX0 hmono G hG j

end SubdiffusiveProcess.Besov.Detach
