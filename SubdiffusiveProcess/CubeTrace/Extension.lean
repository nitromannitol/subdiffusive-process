import Mathlib
import SubdiffusiveProcess.CubeTrace.Scale
import SubdiffusiveProcess.CubeTrace.Cutoff
import SubdiffusiveProcess.CubeTrace.Mollifier

/-!
# Cube trace extension: the Whitney-type extension `b = ∑_k θ_k A_k`

`A_k = ρ_{3^{-k}} ⋆ G` is the mollification of a Hölder function `G`; `b(x) = ∑_k θ_k(x) A_k(x)`.
On `{x : 3 < 3^N m(x)}` the sum has only the terms `k ≤ N`.  Since `∑ θ_k = 1` there, `∇b` and
`D²b` can be computed with `A_k - G(x)` in place of `A_k`, which gives
`|b - G| ≲ K m^β`, `|∇b| ≲ K m^{β-1}`, `|D²b| ≲ K m^{β-2}`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The `k`-th mollification radius `3^{-k}`. -/
def ctH (k : ℕ) : ℝ := ((1 : ℝ) / 3) ^ k

/-- The `k`-th mollification `A_k = ρ_{3^{-k}} ⋆ G`. -/
def ctA (k : ℕ) (G : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := ctMoll (ctH k) G

/-- The extension `b = ∑_k θ_k A_k` (a locally finite sum inside the cube). -/
def ctB (z : (Fin d → ℝ)) (G : (Fin d → ℝ) → ℝ) (x : (Fin d → ℝ)) : ℝ :=
  ∑' k : ℕ, ctTheta z k x * ctA k G x

theorem ctH_pos (k : ℕ) : 0 < ctH k := by
  unfold ctH
  positivity

/-- Near `x` the tsum is the finite partial sum. -/
theorem ctB_eventuallyEq [NeZero d] (z : (Fin d → ℝ)) (G : (Fin d → ℝ) → ℝ)
    {x : (Fin d → ℝ)} {N : ℕ} (hN : 3 < (3 : ℝ) ^ N * ctM z x) :
    ctB z G =ᶠ[𝓝 x] fun y => ∑ k ∈ Finset.range (N + 1), ctTheta z k y * ctA k G y := by
  have hev : ∀ᶠ y in 𝓝 x, 3 < (3 : ℝ) ^ N * ctM z y :=
    (continuous_const.mul (continuous_ctM z)).continuousAt.eventually (lt_mem_nhds hN)
  filter_upwards [hev] with y hy
  unfold ctB
  apply tsum_eq_sum
  intro k hk'
  have hNk : N < k := by
    by_contra hle
    exact hk' (Finset.mem_range.2 (by omega))
  rw [ctTheta_eq_zero_of_gt z hNk hy, zero_mul]

theorem ctB_contDiffOn [NeZero d] (z : (Fin d → ℝ)) {G : (Fin d → ℝ) → ℝ}
    (hG : Continuous G) : ContDiffOn ℝ 2 (ctB z G) (ctQ z) := by
  intro x hx
  obtain ⟨N, hN⟩ := exists_N_of_mem hx
  have hsm : ContDiff ℝ 2 (fun y => ∑ k ∈ Finset.range (N + 1), ctTheta z k y * ctA k G y) := by
    apply ContDiff.sum
    intro k _
    have h1 : ContDiff ℝ 2 (ctTheta z k) := (ctTheta_contDiff z k).of_le (by norm_cast)
    have h2 : ContDiff ℝ 2 (ctA k G) :=
      (ctMoll_contDiff (ctH_pos k) hG).of_le (by norm_cast)
    exact h1.mul h2
  have hev := ctB_eventuallyEq z G hN
  exact ((hsm.contDiffAt).congr_of_eventuallyEq hev).contDiffWithinAt

/-- A nonzero `θ_k(y)` forces `y` into the band `3^{-k} ≤ m(y) ≤ 9 · 3^{-k}`. -/
theorem ctTheta_ne_zero_band [NeZero d] {z y : (Fin d → ℝ)} {k : ℕ}
    (h : ctTheta z k y ≠ 0) : ctH k ≤ ctM z y ∧ ctM z y ≤ 9 * ctH k := by
  by_contra hnot
  have hor : ctM z y < ((1 : ℝ) / 3) ^ k ∨ 9 * ((1 : ℝ) / 3) ^ k < ctM z y := by
    unfold ctH at hnot
    by_contra h'
    push_neg at h'
    exact hnot ⟨h'.1, h'.2⟩
  exact h ((ctTheta_eventually_zero z k hor).self_of_nhds)

/-- `∑_{k ≤ N} ∂_j θ_k = 0` near a point where the partial sum of the partition is `1`. -/
theorem sum_ctTheta_fderiv_eq_zero [NeZero d] (z : (Fin d → ℝ)) (N : ℕ)
    {x : (Fin d → ℝ)} (hx : 3 < (3 : ℝ) ^ N * ctM z x) (j : Fin d) :
    ∑ k ∈ Finset.range (N + 1), fderiv ℝ (ctTheta z k) x (Pi.single j 1) = 0 := by
  have hev := sum_ctTheta_eventually_one z N hx
  have hdiff : ∀ k ∈ Finset.range (N + 1), DifferentiableAt ℝ (ctTheta z k) x := fun k _ =>
    ((ctTheta_contDiff z k).differentiable (by simp)).differentiableAt
  have h1 : fderiv ℝ (fun y => ∑ k ∈ Finset.range (N + 1), ctTheta z k y) x = 0 := by
    have hev' : (fun y => ∑ k ∈ Finset.range (N + 1), ctTheta z k y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := hev
    rw [Filter.EventuallyEq.fderiv_eq hev']
    simp
  rw [fderiv_fun_sum hdiff] at h1
  have := congrArg (fun L => L (Pi.single j 1)) h1
  simpa [ContinuousLinearMap.sum_apply] using this

theorem sum_ctTheta_fderiv2_eq_zero [NeZero d] (z : (Fin d → ℝ)) (N : ℕ)
    {x : (Fin d → ℝ)} (hx : 3 < (3 : ℝ) ^ N * ctM z x) (j l : Fin d) :
    ∑ k ∈ Finset.range (N + 1),
      fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) = 0 := by
  classical
  have hev : ∀ᶠ y in 𝓝 x, 3 < (3 : ℝ) ^ N * ctM z y :=
    (continuous_const.mul (continuous_ctM z)).continuousAt.eventually (lt_mem_nhds hx)
  have hzero : ∀ᶠ y in 𝓝 x,
      ∑ k ∈ Finset.range (N + 1), fderiv ℝ (ctTheta z k) y (Pi.single j 1) = 0 := by
    filter_upwards [hev] with y hy
    exact sum_ctTheta_fderiv_eq_zero z N hy j
  have hdiff : ∀ k ∈ Finset.range (N + 1),
      DifferentiableAt ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x := by
    intro k _
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (ctTheta z k)) := (ctTheta_contDiff z k).fderiv_right (by simp)
    exact ((h1.clm_apply contDiff_const).differentiable (by simp)).differentiableAt
  have h1 : fderiv ℝ (fun y => ∑ k ∈ Finset.range (N + 1),
      fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x = 0 := by
    have hev' : (fun y => ∑ k ∈ Finset.range (N + 1), fderiv ℝ (ctTheta z k) y (Pi.single j 1))
        =ᶠ[𝓝 x] fun _ => (0 : ℝ) := hzero
    rw [Filter.EventuallyEq.fderiv_eq hev']
    simp
  rw [fderiv_fun_sum hdiff] at h1
  have := congrArg (fun L => L (Pi.single l 1)) h1
  simpa [ContinuousLinearMap.sum_apply] using this

/-- The first-derivative formula, with `A_k(x) - c` in place of `A_k` for an arbitrary constant. -/
theorem ctB_fderiv_eq [NeZero d] (z : (Fin d → ℝ)) {G : (Fin d → ℝ) → ℝ}
    (hG : Continuous G) {x : (Fin d → ℝ)} {N : ℕ} (hN : 3 < (3 : ℝ) ^ N * ctM z x)
    (c : ℝ) (j : Fin d) :
    fderiv ℝ (ctB z G) x (Pi.single j 1) =
      ∑ k ∈ Finset.range (N + 1),
        (fderiv ℝ (ctTheta z k) x (Pi.single j 1) * (ctA k G x - c) +
          ctTheta z k x * fderiv ℝ (ctA k G) x (Pi.single j 1)) := by
  classical
  have hev := ctB_eventuallyEq z G hN
  have hdθ : ∀ k, DifferentiableAt ℝ (ctTheta z k) x := fun k =>
    ((ctTheta_contDiff z k).differentiable (by simp)).differentiableAt
  have hdA : ∀ k, DifferentiableAt ℝ (ctA k G) x := fun k =>
    ((ctMoll_contDiff (ctH_pos k) hG).differentiable (by simp)).differentiableAt
  rw [Filter.EventuallyEq.fderiv_eq hev]
  rw [fderiv_fun_sum (A := fun k y => ctTheta z k y * ctA k G y) (fun k _ => (hdθ k).mul (hdA k))]
  have hs := sum_ctTheta_fderiv_eq_zero z N hN j
  simp only [ContinuousLinearMap.sum_apply]
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (fderiv ℝ (fun y => ctTheta z k y * ctA k G y) x) (Pi.single j 1) =
        (fderiv ℝ (ctTheta z k) x (Pi.single j 1) * (ctA k G x - c) +
          ctTheta z k x * fderiv ℝ (ctA k G) x (Pi.single j 1)) +
          c * fderiv ℝ (ctTheta z k) x (Pi.single j 1) := by
    intro k _
    have h : HasFDerivAt (fun y => ctTheta z k y * ctA k G y)
        (ctTheta z k x • fderiv ℝ (ctA k G) x + ctA k G x • fderiv ℝ (ctTheta z k) x) x :=
      (hdθ k).hasFDerivAt.mul (hdA k).hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero, add_zero]

/-- Product-rule computation for one term of the second-derivative formula. -/
theorem fderiv_term_eq {g a t b : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (c : ℝ) (v : Fin d → ℝ)
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x) (ht : DifferentiableAt ℝ t x)
    (hb : DifferentiableAt ℝ b x) :
    fderiv ℝ (fun y => g y * (a y - c) + t y * b y) x v =
      fderiv ℝ g x v * (a x - c) + g x * fderiv ℝ a x v + (fderiv ℝ t x v * b x + t x * fderiv ℝ b x v) := by
  have h : HasFDerivAt (fun y => g y * (a y - c) + t y * b y)
      (g x • fderiv ℝ a x + (a x - c) • fderiv ℝ g x + (t x • fderiv ℝ b x + b x • fderiv ℝ t x)) x :=
    (hg.hasFDerivAt.mul (ha.hasFDerivAt.sub_const c)).add (ht.hasFDerivAt.mul hb.hasFDerivAt)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The second-derivative formula (constant `c`). -/
theorem ctB_fderiv2_eq [NeZero d] (z : (Fin d → ℝ)) {G : (Fin d → ℝ) → ℝ}
    (hG : Continuous G) {x : (Fin d → ℝ)} {N : ℕ} (hN : 3 < (3 : ℝ) ^ N * ctM z x)
    (c : ℝ) (j l : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (ctB z G) y (Pi.single j 1)) x (Pi.single l 1) =
      ∑ k ∈ Finset.range (N + 1),
        (fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctA k G x - c) +
          fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctA k G) x (Pi.single l 1) +
          fderiv ℝ (ctTheta z k) x (Pi.single l 1) * fderiv ℝ (ctA k G) x (Pi.single j 1) +
          ctTheta z k x *
            fderiv ℝ (fun y => fderiv ℝ (ctA k G) y (Pi.single j 1)) x (Pi.single l 1)) := by
  classical
  have hev : ∀ᶠ y in 𝓝 x, 3 < (3 : ℝ) ^ N * ctM z y :=
    (continuous_const.mul (continuous_ctM z)).continuousAt.eventually (lt_mem_nhds hN)
  have hS : (fun y => fderiv ℝ (ctB z G) y (Pi.single j 1)) =ᶠ[𝓝 x] fun y =>
      ∑ k ∈ Finset.range (N + 1),
        (fderiv ℝ (ctTheta z k) y (Pi.single j 1) * (ctA k G y - c) +
          ctTheta z k y * fderiv ℝ (ctA k G) y (Pi.single j 1)) := by
    filter_upwards [hev] with y hy
    exact ctB_fderiv_eq z hG hy c j
  rw [Filter.EventuallyEq.fderiv_eq hS]
  have hθ : ∀ k, ContDiff ℝ ∞ (ctTheta z k) := ctTheta_contDiff z
  have hA : ∀ k, ContDiff ℝ ∞ (ctA k G) := fun k => ctMoll_contDiff (ctH_pos k) hG
  have hg : ∀ k, DifferentiableAt ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x := by
    intro k
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (ctTheta z k)) := (hθ k).fderiv_right (by simp)
    exact ((h1.clm_apply contDiff_const).differentiable (by simp)).differentiableAt
  have hb : ∀ k, DifferentiableAt ℝ (fun y => fderiv ℝ (ctA k G) y (Pi.single j 1)) x := by
    intro k
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (ctA k G)) := (hA k).fderiv_right (by simp)
    exact ((h1.clm_apply contDiff_const).differentiable (by simp)).differentiableAt
  have hdθ : ∀ k, DifferentiableAt ℝ (ctTheta z k) x := fun k =>
    ((hθ k).differentiable (by simp)).differentiableAt
  have hdA : ∀ k, DifferentiableAt ℝ (ctA k G) x := fun k =>
    ((hA k).differentiable (by simp)).differentiableAt
  rw [fderiv_fun_sum (A := fun k y => fderiv ℝ (ctTheta z k) y (Pi.single j 1) * (ctA k G y - c) +
      ctTheta z k y * fderiv ℝ (ctA k G) y (Pi.single j 1))
    (fun k _ => ((hg k).mul ((hdA k).sub_const c)).add ((hdθ k).mul (hb k)))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_term_eq c (Pi.single l 1) (hg k) (hdA k) (hdθ k) (hb k)]
  ring

/-- A sum over `k ≤ N` of terms supported in the band `3^{-k} ≤ m ≤ 9 · 3^{-k}` (at most three
values of `k`) is bounded by three times the termwise bound. -/
theorem abs_sum_band_le {m B : ℝ} (hm : 0 < m) (hB : 0 ≤ B) (N : ℕ) (f : ℕ → ℝ)
    (hzero : ∀ k, ¬ (ctH k ≤ m ∧ m ≤ 9 * ctH k) → f k = 0)
    (hbound : ∀ k, ctH k ≤ m ∧ m ≤ 9 * ctH k → |f k| ≤ B) :
    |∑ k ∈ Finset.range (N + 1), f k| ≤ 3 * B := by
  classical
  set band : Finset ℕ := (Finset.range (N + 1)).filter (fun k : ℕ => ctH k ≤ m ∧ m ≤ 9 * ctH k) with hband
  have hsum : ∑ k ∈ Finset.range (N + 1), f k = ∑ k ∈ band, f k := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    apply hzero
    intro hb
    exact hnot (Finset.mem_filter.2 ⟨hk, hb⟩)
  have hcard : band.card ≤ 3 := by
    have := band_card_le hm (N + 1)
    simpa [hband, ctH] using this
  rw [hsum]
  calc |∑ k ∈ band, f k| ≤ ∑ k ∈ band, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ band, B := Finset.sum_le_sum (fun k hk => hbound k (Finset.mem_filter.1 hk).2)
    _ = band.card * B := by simp
    _ ≤ 3 * B := by
        have : (band.card : ℝ) ≤ 3 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right this hB

theorem ctH_mul_three_pow (k : ℕ) : (3 : ℝ) ^ k * ctH k = 1 := by
  unfold ctH
  rw [← mul_pow]
  norm_num

/-- `3^k h_k^β = h_k^{β-1}`. -/
theorem three_pow_mul_ctH_rpow (k : ℕ) (β : ℝ) : (3 : ℝ) ^ k * ctH k ^ β = ctH k ^ (β - 1) := by
  have hh := ctH_pos k
  have h3 : (3 : ℝ) ^ k = (ctH k)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact (by
    have := ctH_mul_three_pow k; linarith))
  rw [h3, Real.rpow_sub_one hh.ne', div_eq_inv_mul]

/-- `9^k h_k^β = h_k^{β-2}`. -/
theorem nine_pow_mul_ctH_rpow (k : ℕ) (β : ℝ) : (9 : ℝ) ^ k * ctH k ^ β = ctH k ^ (β - 2) := by
  have hh := ctH_pos k
  have h3 : (3 : ℝ) ^ k = (ctH k)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact (by
    have := ctH_mul_three_pow k; linarith))
  have h9 : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h9, h3, Real.rpow_sub hh, Real.rpow_two, div_eq_mul_inv, inv_pow, mul_comm]

/-- Power comparisons on the band `m/9 ≤ h ≤ m`. -/
theorem band_rpow_bounds {m h β : ℝ} (hm : 0 < m) (hh : m ≤ 9 * h) (hhm : h ≤ m)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    h ^ β ≤ m ^ β ∧ h ^ (β - 1) ≤ 9 * m ^ (β - 1) ∧ h ^ (β - 2) ≤ 81 * m ^ (β - 2) := by
  have hh0 : 0 < h := by linarith
  have hm9 : 0 < m / 9 := by positivity
  have hmh : m / 9 ≤ h := by linarith
  refine ⟨Real.rpow_le_rpow hh0.le hhm hβ.1.le, ?_, ?_⟩
  · have e1 : β - 1 ≤ 0 := by linarith [hβ.2]
    have key : h ^ (β - 1) ≤ (m / 9) ^ (β - 1) := Real.rpow_le_rpow_of_nonpos hm9 hmh e1
    have e2 : (m / 9) ^ (β - 1) = m ^ (β - 1) * 9 ^ (-(β - 1)) := by
      rw [Real.div_rpow hm.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    have e3 : (9 : ℝ) ^ (-(β - 1)) ≤ 9 := by
      calc (9 : ℝ) ^ (-(β - 1)) ≤ (9 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hβ.1])
        _ = 9 := by norm_num
    have e4 : 0 ≤ m ^ (β - 1) := Real.rpow_nonneg hm.le _
    calc h ^ (β - 1) ≤ (m / 9) ^ (β - 1) := key
      _ = m ^ (β - 1) * 9 ^ (-(β - 1)) := e2
      _ ≤ m ^ (β - 1) * 9 := mul_le_mul_of_nonneg_left e3 e4
      _ = 9 * m ^ (β - 1) := by ring
  · have e1 : β - 2 ≤ 0 := by linarith [hβ.2]
    have key : h ^ (β - 2) ≤ (m / 9) ^ (β - 2) := Real.rpow_le_rpow_of_nonpos hm9 hmh e1
    have e2 : (m / 9) ^ (β - 2) = m ^ (β - 2) * 9 ^ (-(β - 2)) := by
      rw [Real.div_rpow hm.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    have e3 : (9 : ℝ) ^ (-(β - 2)) ≤ 81 := by
      calc (9 : ℝ) ^ (-(β - 2)) ≤ (9 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hβ.1])
        _ = 81 := by norm_num
    have e4 : 0 ≤ m ^ (β - 2) := Real.rpow_nonneg hm.le _
    calc h ^ (β - 2) ≤ (m / 9) ^ (β - 2) := key
      _ = m ^ (β - 2) * 9 ^ (-(β - 2)) := e2
      _ ≤ m ^ (β - 2) * 81 := mul_le_mul_of_nonneg_left e3 e4
      _ = 81 * m ^ (β - 2) := by ring

/-- **The extension bounds.**  With `Cb` depending only on `d` and `β`. -/
theorem ct_extension_bounds [NeZero d] {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (z : (Fin d → ℝ)) (G : (Fin d → ℝ) → ℝ) (K : ℝ),
      0 ≤ K → (∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) →
      (∀ x ∈ ctQ z, |ctB z G x - G x| ≤ Cb * K * ctM z x ^ β) ∧
      (∀ x ∈ ctQ z, ∀ j : Fin d,
        |fderiv ℝ (ctB z G) x (Pi.single j 1)| ≤ Cb * K * ctM z x ^ (β - 1)) ∧
      (∀ x ∈ ctQ z, ∀ j l : Fin d,
        |fderiv ℝ (fun y => fderiv ℝ (ctB z G) y (Pi.single j 1)) x (Pi.single l 1)| ≤
          Cb * K * ctM z x ^ (β - 2)) := by
  classical
  obtain ⟨c1θ, hc1θ0, hc1θ⟩ := ctTheta_fderiv_bound (d := d)
  obtain ⟨c2θ, hc2θ0, hc2θ⟩ := ctTheta_fderiv2_bound (d := d)
  obtain ⟨c1m, hc1m0, hc1m⟩ := ctMoll_fderiv_bound (d := d) hβ.1
  obtain ⟨c2m, hc2m0, hc2m⟩ := ctMoll_fderiv2_bound (d := d) hβ.1
  refine ⟨3 + 27 * (c1θ + c1m) + 243 * (c2θ + 2 * c1θ * c1m + c2m), by positivity, ?_⟩
  intro z G K hK hG
  have hGc : Continuous G := holder_continuous hβ.1 hG
  -- pointwise setup
  have key : ∀ x ∈ ctQ z, ∃ N : ℕ, 3 < (3 : ℝ) ^ N * ctM z x ∧
      (∀ k, ¬ (ctH k ≤ ctM z x ∧ ctM z x ≤ 9 * ctH k) →
        ctTheta z k x = 0 ∧ (∀ j : Fin d, fderiv ℝ (ctTheta z k) x (Pi.single j 1) = 0) ∧
        ∀ j l : Fin d, fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x
          (Pi.single l 1) = 0) := by
    intro x hx
    obtain ⟨N, hN⟩ := exists_N_of_mem hx
    refine ⟨N, hN, ?_⟩
    intro k hk
    have hor : ctM z x < ((1 : ℝ) / 3) ^ k ∨ 9 * ((1 : ℝ) / 3) ^ k < ctM z x := by
      unfold ctH at hk
      by_contra h'
      push_neg at h'
      exact hk ⟨h'.1, h'.2⟩
    have hev := ctTheta_eventually_zero z k hor
    exact ⟨hev.self_of_nhds, fun j => (ctTheta_derivs_zero_of_eventually hev j j).1,
      fun j l => (ctTheta_derivs_zero_of_eventually hev j l).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨N, hN, hout⟩ := key x hx
    have hm := ctM_pos hx
    have hsum1 : ∑ k ∈ Finset.range (N + 1), ctTheta z k x = 1 := by
      rw [sum_ctTheta_range]; exact ctE_eq_one_of_gt z N hN
    have hB : ctB z G x = ∑ k ∈ Finset.range (N + 1), ctTheta z k x * ctA k G x :=
      (ctB_eventuallyEq z G hN).self_of_nhds
    have hdiff : ctB z G x - G x =
        ∑ k ∈ Finset.range (N + 1), ctTheta z k x * (ctA k G x - G x) := by
      rw [hB]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hsum1]
      ring
    rw [hdiff]
    have hKm : 0 ≤ K * ctM z x ^ β := mul_nonneg hK (Real.rpow_nonneg hm.le _)
    have h3 := abs_sum_band_le hm hKm N (fun k => ctTheta z k x * (ctA k G x - G x))
      (fun k hk => by simp only [(hout k hk).1, zero_mul])
      (fun k hk => by
        have hh := ctH_pos k
        have hb := (band_rpow_bounds hm hk.2 hk.1 hβ).1
        have h1 := ctMoll_sub_le hh hK hβ.1 hG x
        have h2 := abs_ctTheta_le_one z x k
        change |ctTheta z k x * (ctMoll (ctH k) G x - G x)| ≤ K * ctM z x ^ β
        rw [abs_mul]
        calc |ctTheta z k x| * |ctMoll (ctH k) G x - G x| ≤ 1 * (K * ctH k ^ β) :=
              mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
          _ ≤ K * ctM z x ^ β := by
              rw [one_mul]; exact mul_le_mul_of_nonneg_left hb hK)
    have hC : 3 * (K * ctM z x ^ β) ≤
        (3 + 27 * (c1θ + c1m) + 243 * (c2θ + 2 * c1θ * c1m + c2m)) * K * ctM z x ^ β := by
      have : 0 ≤ (27 * (c1θ + c1m) + 243 * (c2θ + 2 * c1θ * c1m + c2m)) * (K * ctM z x ^ β) :=
        mul_nonneg (by positivity) hKm
      nlinarith
    exact h3.trans hC
  · intro x hx j
    obtain ⟨N, hN, hout⟩ := key x hx
    have hm := ctM_pos hx
    rw [ctB_fderiv_eq z hGc hN (G x) j]
    have hKm : 0 ≤ K * ctM z x ^ (β - 1) := mul_nonneg hK (Real.rpow_nonneg hm.le _)
    have hB0 : 0 ≤ 9 * (c1θ + c1m) * (K * ctM z x ^ (β - 1)) := by positivity
    have h3 := abs_sum_band_le hm hB0 N
      (fun k => fderiv ℝ (ctTheta z k) x (Pi.single j 1) * (ctA k G x - G x) +
        ctTheta z k x * fderiv ℝ (ctA k G) x (Pi.single j 1))
      (fun k hk => by simp only [(hout k hk).2.1 j, (hout k hk).1, zero_mul, add_zero])
      (fun k hk => by
        have hh := ctH_pos k
        obtain ⟨hb0, hb1, hb2⟩ := band_rpow_bounds hm hk.2 hk.1 hβ
        have hA := ctMoll_sub_le hh hK hβ.1 hG x
        have hd1 := hc1θ z x k j
        have hd2 := hc1m hh hK hG x j
        have hθ := abs_ctTheta_le_one z x k
        change |fderiv ℝ (ctTheta z k) x (Pi.single j 1) * (ctMoll (ctH k) G x - G x) +
          ctTheta z k x * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1)| ≤
            9 * (c1θ + c1m) * (K * ctM z x ^ (β - 1))
        have hnn : 0 ≤ (c1θ + c1m) * K := by positivity
        calc |fderiv ℝ (ctTheta z k) x (Pi.single j 1) * (ctMoll (ctH k) G x - G x) +
              ctTheta z k x * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1)|
            ≤ |fderiv ℝ (ctTheta z k) x (Pi.single j 1)| * |ctMoll (ctH k) G x - G x| +
              |ctTheta z k x| * |fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1)| := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul]
          _ ≤ (c1θ * (3 : ℝ) ^ k) * (K * ctH k ^ β) + 1 * (c1m * K * ctH k ^ (β - 1)) :=
              add_le_add (mul_le_mul hd1 hA (abs_nonneg _) (by positivity))
                (mul_le_mul hθ hd2 (abs_nonneg _) zero_le_one)
          _ = (c1θ + c1m) * K * ctH k ^ (β - 1) := by
              rw [← three_pow_mul_ctH_rpow k β]; ring
          _ ≤ (c1θ + c1m) * K * (9 * ctM z x ^ (β - 1)) :=
              mul_le_mul_of_nonneg_left hb1 hnn
          _ = 9 * (c1θ + c1m) * (K * ctM z x ^ (β - 1)) := by ring)
    have hC : 3 * (9 * (c1θ + c1m) * (K * ctM z x ^ (β - 1))) ≤
        (3 + 27 * (c1θ + c1m) + 243 * (c2θ + 2 * c1θ * c1m + c2m)) * K * ctM z x ^ (β - 1) := by
      have : 0 ≤ (3 + 243 * (c2θ + 2 * c1θ * c1m + c2m)) * (K * ctM z x ^ (β - 1)) :=
        mul_nonneg (by positivity) hKm
      nlinarith
    exact h3.trans hC
  · intro x hx j l
    obtain ⟨N, hN, hout⟩ := key x hx
    have hm := ctM_pos hx
    rw [ctB_fderiv2_eq z hGc hN (G x) j l]
    have hKm : 0 ≤ K * ctM z x ^ (β - 2) := mul_nonneg hK (Real.rpow_nonneg hm.le _)
    have hB0 : 0 ≤ 81 * (c2θ + 2 * c1θ * c1m + c2m) * (K * ctM z x ^ (β - 2)) := by positivity
    have h3 := abs_sum_band_le hm hB0 N
      (fun k => fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctA k G x - G x) +
          fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctA k G) x (Pi.single l 1) +
          fderiv ℝ (ctTheta z k) x (Pi.single l 1) * fderiv ℝ (ctA k G) x (Pi.single j 1) +
          ctTheta z k x *
            fderiv ℝ (fun y => fderiv ℝ (ctA k G) y (Pi.single j 1)) x (Pi.single l 1))
      (fun k hk => by
        simp only [(hout k hk).2.2 j l, (hout k hk).2.1 j, (hout k hk).2.1 l, (hout k hk).1,
          zero_mul, add_zero])
      (fun k hk => by
        have hh := ctH_pos k
        obtain ⟨hb0, hb1, hb2⟩ := band_rpow_bounds hm hk.2 hk.1 hβ
        have hA := ctMoll_sub_le hh hK hβ.1 hG x
        have hd1j := hc1θ z x k j
        have hd1l := hc1θ z x k l
        have hd2 := hc2θ z x k j l
        have hm1j := hc1m hh hK hG x j
        have hm1l := hc1m hh hK hG x l
        have hm2 := hc2m hh hK hG x j l
        have hθ := abs_ctTheta_le_one z x k
        change |fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctMoll (ctH k) G x - G x) +
          fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single l 1) +
          fderiv ℝ (ctTheta z k) x (Pi.single l 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1) +
          ctTheta z k x *
            fderiv ℝ (fun y => fderiv ℝ (ctMoll (ctH k) G) y (Pi.single j 1)) x (Pi.single l 1)| ≤
            81 * (c2θ + 2 * c1θ * c1m + c2m) * (K * ctM z x ^ (β - 2))
        have e9 := nine_pow_mul_ctH_rpow k β
        have e3 := three_pow_mul_ctH_rpow k (β - 1)
        have e3' : (3 : ℝ) ^ k * ctH k ^ (β - 1) = ctH k ^ (β - 2) := by
          rw [e3]; congr 1; ring
        have hp : 0 ≤ (3 : ℝ) ^ k := by positivity
        have hp9 : 0 ≤ (9 : ℝ) ^ k := by positivity
        have hHK : 0 ≤ K * ctH k ^ β := mul_nonneg hK (Real.rpow_nonneg hh.le _)
        have hHK1 : 0 ≤ K * ctH k ^ (β - 1) := mul_nonneg hK (Real.rpow_nonneg hh.le _)
        have t1 : |fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctMoll (ctH k) G x - G x)| ≤ c2θ * K * ctH k ^ (β - 2) := by
          rw [abs_mul]
          calc _ ≤ (c2θ * (9 : ℝ) ^ k) * (K * ctH k ^ β) :=
                mul_le_mul hd2 hA (abs_nonneg _) (by positivity)
            _ = c2θ * K * ctH k ^ (β - 2) := by rw [← e9]; ring
        have t2 : |fderiv ℝ (ctTheta z k) x (Pi.single j 1) *
            fderiv ℝ (ctMoll (ctH k) G) x (Pi.single l 1)| ≤ c1θ * c1m * K * ctH k ^ (β - 2) := by
          rw [abs_mul]
          calc _ ≤ (c1θ * (3 : ℝ) ^ k) * (c1m * K * ctH k ^ (β - 1)) :=
                mul_le_mul hd1j hm1l (abs_nonneg _) (by positivity)
            _ = c1θ * c1m * K * ctH k ^ (β - 2) := by rw [← e3']; ring
        have t3 : |fderiv ℝ (ctTheta z k) x (Pi.single l 1) *
            fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1)| ≤ c1θ * c1m * K * ctH k ^ (β - 2) := by
          rw [abs_mul]
          calc _ ≤ (c1θ * (3 : ℝ) ^ k) * (c1m * K * ctH k ^ (β - 1)) :=
                mul_le_mul hd1l hm1j (abs_nonneg _) (by positivity)
            _ = c1θ * c1m * K * ctH k ^ (β - 2) := by rw [← e3']; ring
        have t4 : |ctTheta z k x *
            fderiv ℝ (fun y => fderiv ℝ (ctMoll (ctH k) G) y (Pi.single j 1)) x (Pi.single l 1)| ≤
              c2m * K * ctH k ^ (β - 2) := by
          rw [abs_mul]
          calc _ ≤ 1 * (c2m * K * ctH k ^ (β - 2)) :=
                mul_le_mul hθ hm2 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        have hsum : |fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctMoll (ctH k) G x - G x) +
          fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single l 1) +
          fderiv ℝ (ctTheta z k) x (Pi.single l 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1) +
          ctTheta z k x *
            fderiv ℝ (fun y => fderiv ℝ (ctMoll (ctH k) G) y (Pi.single j 1)) x (Pi.single l 1)| ≤
            (c2θ + 2 * c1θ * c1m + c2m) * K * ctH k ^ (β - 2) := by
          have := abs_add_le (fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctMoll (ctH k) G x - G x) +
          fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single l 1) +
          fderiv ℝ (ctTheta z k) x (Pi.single l 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1))
            (ctTheta z k x *
            fderiv ℝ (fun y => fderiv ℝ (ctMoll (ctH k) G) y (Pi.single j 1)) x (Pi.single l 1))
          have h2 := abs_add_le (fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctMoll (ctH k) G x - G x) +
          fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single l 1))
            (fderiv ℝ (ctTheta z k) x (Pi.single l 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single j 1))
          have h1 := abs_add_le (fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) *
            (ctMoll (ctH k) G x - G x))
            (fderiv ℝ (ctTheta z k) x (Pi.single j 1) * fderiv ℝ (ctMoll (ctH k) G) x (Pi.single l 1))
          nlinarith
        have hnn : 0 ≤ (c2θ + 2 * c1θ * c1m + c2m) * K := by positivity
        calc _ ≤ (c2θ + 2 * c1θ * c1m + c2m) * K * ctH k ^ (β - 2) := hsum
          _ ≤ (c2θ + 2 * c1θ * c1m + c2m) * K * (81 * ctM z x ^ (β - 2)) :=
              mul_le_mul_of_nonneg_left hb2 hnn
          _ = 81 * (c2θ + 2 * c1θ * c1m + c2m) * (K * ctM z x ^ (β - 2)) := by ring)
    have hC : 3 * (81 * (c2θ + 2 * c1θ * c1m + c2m) * (K * ctM z x ^ (β - 2))) ≤
        (3 + 27 * (c1θ + c1m) + 243 * (c2θ + 2 * c1θ * c1m + c2m)) * K * ctM z x ^ (β - 2) := by
      have : 0 ≤ (3 + 27 * (c1θ + c1m)) * (K * ctM z x ^ (β - 2)) :=
        mul_nonneg (by positivity) hKm
      nlinarith
    exact h3.trans hC

end SubdiffusiveProcess.CubeTrace
