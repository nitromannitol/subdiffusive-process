module

public import Mathlib
public import SubdiffusiveProcess.CubeTrace.Scale

@[expose] public section

/-!
# Cube trace extension: smooth scale cutoffs

`τ(s) = smoothTransition((s-1)/2)` vanishes for `s ≤ 1` and equals `1` for `s ≥ 3`.  The product
`E_n(x) = ∏_i τ(3^n u_i(x))` is a smooth (on all of `ℝ^d`) cutoff which is `0` where some
`u_i < 3^{-n}` and `1` where all `u_i > 3 · 3^{-n}`; `θ_k = E_k - E_{k-1}` (`θ_0 = E_0`) form a
locally finite partition of unity of the open cube supported in the bands
`3^{-k} ≤ m ≤ 9 · 3^{-k}`.  Because each factor depends on one coordinate, the derivative bounds
are elementary and do not involve second derivatives of `m`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The smooth step: `0` on `s ≤ 1`, `1` on `s ≥ 3`. -/
def ctTau (s : ℝ) : ℝ := Real.smoothTransition ((s - 1) / 2)

theorem ctTau_contDiff : ContDiff ℝ ∞ ctTau := by
  unfold ctTau
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem ctTau_eq_zero_of_le {s : ℝ} (h : s ≤ 1) : ctTau s = 0 := by
  unfold ctTau
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem ctTau_eq_one_of_ge {s : ℝ} (h : 3 ≤ s) : ctTau s = 1 := by
  unfold ctTau
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem ctTau_nonneg (s : ℝ) : 0 ≤ ctTau s := by
  unfold ctTau
  exact Real.smoothTransition.nonneg _

theorem ctTau_le_one (s : ℝ) : ctTau s ≤ 1 := by
  unfold ctTau
  exact Real.smoothTransition.le_one _

/-- `τ'` vanishes outside `(1,3)`, and so does `τ''`. -/
theorem ctTau_deriv_support {s : ℝ} (h : s ≤ 1 ∨ 3 ≤ s) :
    deriv ctTau s = 0 ∧ deriv (deriv ctTau) s = 0 := by
  have hτ := ctTau_contDiff
  have hd1 : ContDiff ℝ ∞ (deriv ctTau) := (contDiff_infty_iff_deriv.1 hτ).2
  have hc1 : Continuous (deriv ctTau) := hd1.continuous
  have hc2 : Continuous (deriv (deriv ctTau)) := (contDiff_infty_iff_deriv.1 hd1).2.continuous
  have hleft : ∀ s < 1, deriv ctTau s = 0 ∧ deriv (deriv ctTau) s = 0 := by
    intro s hs
    have hev : ctTau =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with u hu
      exact ctTau_eq_zero_of_le (le_of_lt hu)
    have h1 : deriv ctTau s = 0 := by rw [Filter.EventuallyEq.deriv_eq hev]; simp
    have hev2 : deriv ctTau =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with u hu
      have hev' : ctTau =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        exact ctTau_eq_zero_of_le (le_of_lt hv)
      rw [Filter.EventuallyEq.deriv_eq hev']; simp
    have h2 : deriv (deriv ctTau) s = 0 := by rw [Filter.EventuallyEq.deriv_eq hev2]; simp
    exact ⟨h1, h2⟩
  have hright : ∀ s > 3, deriv ctTau s = 0 ∧ deriv (deriv ctTau) s = 0 := by
    intro s hs
    have hev : ctTau =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with u hu
      exact ctTau_eq_one_of_ge (le_of_lt hu)
    have h1 : deriv ctTau s = 0 := by rw [Filter.EventuallyEq.deriv_eq hev]; simp
    have hev2 : deriv ctTau =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hs] with u hu
      have hev' : ctTau =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact ctTau_eq_one_of_ge (le_of_lt hv)
      rw [Filter.EventuallyEq.deriv_eq hev']; simp
    have h2 : deriv (deriv ctTau) s = 0 := by rw [Filter.EventuallyEq.deriv_eq hev2]; simp
    exact ⟨h1, h2⟩
  have cl1 : ∀ g : ℝ → ℝ, Continuous g → (∀ s < 1, g s = 0) → ∀ s ≤ 1, g s = 0 := by
    intro g hg hz s hs
    have hsub : Iio (1 : ℝ) ⊆ {s | g s = 0} := fun s hs => hz s hs
    have := closure_minimal hsub (isClosed_eq hg continuous_const)
    rw [closure_Iio] at this
    exact this hs
  have cl3 : ∀ g : ℝ → ℝ, Continuous g → (∀ s > 3, g s = 0) → ∀ s ≥ 3, g s = 0 := by
    intro g hg hz s hs
    have hsub : Ioi (3 : ℝ) ⊆ {s | g s = 0} := fun s hs => hz s hs
    have := closure_minimal hsub (isClosed_eq hg continuous_const)
    rw [closure_Ioi] at this
    exact this hs
  rcases h with h | h
  · exact ⟨cl1 _ hc1 (fun s hs => (hleft s hs).1) s h, cl1 _ hc2 (fun s hs => (hleft s hs).2) s h⟩
  · exact ⟨cl3 _ hc1 (fun s hs => (hright s hs).1) s h, cl3 _ hc2 (fun s hs => (hright s hs).2) s h⟩

/-- `τ'` and `τ''` are bounded (compactly supported continuous functions). -/
theorem ctTau_deriv_bounds :
    ∃ T1 T2 : ℝ, 0 ≤ T1 ∧ 0 ≤ T2 ∧ (∀ s, |deriv ctTau s| ≤ T1) ∧
      (∀ s, |deriv (deriv ctTau) s| ≤ T2) := by
  have hτ := ctTau_contDiff
  have hd1 : ContDiff ℝ ∞ (deriv ctTau) := (contDiff_infty_iff_deriv.1 hτ).2
  have hc1 : Continuous (deriv ctTau) := hd1.continuous
  have hc2 : Continuous (deriv (deriv ctTau)) := (contDiff_infty_iff_deriv.1 hd1).2.continuous
  have hs1 : HasCompactSupport (deriv ctTau) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 3))
    intro s hs
    simp only [mem_Icc, not_and_or, not_le] at hs
    exact (ctTau_deriv_support (by rcases hs with h | h <;> [left; right] <;> linarith)).1
  have hs2 : HasCompactSupport (deriv (deriv ctTau)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 3))
    intro s hs
    simp only [mem_Icc, not_and_or, not_le] at hs
    exact (ctTau_deriv_support (by rcases hs with h | h <;> [left; right] <;> linarith)).2
  obtain ⟨C1, hC1⟩ := hc1.bounded_above_of_compact_support hs1
  obtain ⟨C2, hC2⟩ := hc2.bounded_above_of_compact_support hs2
  refine ⟨max C1 0, max C2 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro s
    have := hC1 s
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · intro s
    have := hC2 s
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- `E_n(x) = ∏_i τ(3^n u_i(x))`. -/
def ctE (z : (Fin d → ℝ)) (n : ℕ) (x : (Fin d → ℝ)) : ℝ :=
  ∏ i, ctTau ((3 : ℝ) ^ n * ctU z x i)

/-- The one-variable factor of `E_n`: `φ_{n,i}(t) = τ(3^n (1/4 - (t - z_i)^2))`. -/
def ctPhi (z : (Fin d → ℝ)) (n : ℕ) (i : Fin d) (t : ℝ) : ℝ :=
  ctTau ((3 : ℝ) ^ n * (1 / 4 - (t - z i) ^ 2))

theorem ctE_eq_prod_phi (z : (Fin d → ℝ)) (n : ℕ) (x : (Fin d → ℝ)) :
    ctE z n x = ∏ i, ctPhi z n i (x i) := by
  rfl

theorem ctPhi_contDiff (z : (Fin d → ℝ)) (n : ℕ) (i : Fin d) :
    ContDiff ℝ ∞ (ctPhi z n i) := by
  unfold ctPhi
  exact ctTau_contDiff.comp (by fun_prop)

/-- One-variable bounds: `0 ≤ φ ≤ 1`, `|φ'| ≤ c 3^n`, `|φ''| ≤ c 9^n`. -/
theorem ctPhi_bounds :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (z : (Fin d → ℝ)) (n : ℕ) (i : Fin d) (t : ℝ),
      0 ≤ ctPhi z n i t ∧ ctPhi z n i t ≤ 1 ∧ |deriv (ctPhi z n i) t| ≤ c * (3 : ℝ) ^ n ∧
        |deriv (deriv (ctPhi z n i)) t| ≤ c * (9 : ℝ) ^ n := by
  obtain ⟨T1, T2, hT10, hT20, hT1, hT2⟩ := ctTau_deriv_bounds
  refine ⟨T1 + T2 + 2 * T1, by positivity, ?_⟩
  intro z n i t
  have ha0 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have ha1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h39 : (3 : ℝ) ^ n ≤ (9 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h99 : (9 : ℝ) ^ n = (3 : ℝ) ^ n * (3 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  let u : ℝ → ℝ := fun t => (3 : ℝ) ^ n * (1 / 4 - (t - z i) ^ 2)
  have hu : ∀ t, HasDerivAt u ((3 : ℝ) ^ n * (-2 * (t - z i))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s - z i) 1 t := (hasDerivAt_id t).sub_const (z i)
    have h2 := (h1.pow 2).const_sub (1 / 4 : ℝ)
    have h3 := h2.const_mul ((3 : ℝ) ^ n)
    convert h3 using 1
    simp
  have hτ1 : Differentiable ℝ ctTau := ctTau_contDiff.differentiable (by simp)
  have hτ2 : Differentiable ℝ (deriv ctTau) :=
    (contDiff_infty_iff_deriv.1 (contDiff_infty_iff_deriv.1 ctTau_contDiff).2).1
  have hφ : ∀ s, HasDerivAt (ctPhi z n i) (deriv ctTau (u s) * ((3 : ℝ) ^ n * (-2 * (s - z i)))) s :=
    fun s => (hτ1 (u s)).hasDerivAt.comp s (hu s)
  have hdφ : deriv (ctPhi z n i) = fun s => deriv ctTau (u s) * ((3 : ℝ) ^ n * (-2 * (s - z i))) :=
    funext fun s => (hφ s).deriv
  have hφ2 : HasDerivAt (deriv (ctPhi z n i))
      (deriv (deriv ctTau) (u t) * ((3 : ℝ) ^ n * (-2 * (t - z i))) * ((3 : ℝ) ^ n * (-2 * (t - z i))) +
        deriv ctTau (u t) * ((3 : ℝ) ^ n * (-2))) t := by
    rw [hdφ]
    have h1 : HasDerivAt (fun s => deriv ctTau (u s))
        (deriv (deriv ctTau) (u t) * ((3 : ℝ) ^ n * (-2 * (t - z i)))) t :=
      (hτ2 (u t)).hasDerivAt.comp t (hu t)
    have h2 : HasDerivAt (fun s : ℝ => (3 : ℝ) ^ n * (-2 * (s - z i))) ((3 : ℝ) ^ n * (-2)) t := by
      have := (((hasDerivAt_id t).sub_const (z i)).const_mul (-2 : ℝ)).const_mul ((3 : ℝ) ^ n)
      simpa only [id_eq, mul_one] using this
    exact h1.mul h2
  -- support facts
  have hw : ∀ s, 1 < u s → (2 * (s - z i)) ^ 2 ≤ 1 := by
    intro s hs
    have hpos : 0 < 1 / 4 - (s - z i) ^ 2 := by
      by_contra hneg
      push Not at hneg
      have : u s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0.le hneg
      linarith
    nlinarith
  have k1 : ∀ s, |deriv ctTau (u s)| * |2 * (s - z i)| ≤ T1 := by
    intro s
    by_cases h0 : deriv ctTau (u s) = 0
    · rw [h0]; simp; exact hT10
    · have hs : 1 < u s := by
        by_contra hnot
        exact h0 (ctTau_deriv_support (Or.inl (not_lt.1 hnot))).1
      have hb := hw s hs
      have : |2 * (s - z i)| ≤ 1 := by
        have := abs_le_of_sq_le_sq' (by nlinarith [sq_abs (2 * (s - z i))] : |2 * (s - z i)| ^ 2 ≤ 1 ^ 2) (by norm_num)
        exact abs_le.2 ⟨by linarith [abs_nonneg (2 * (s - z i)), neg_abs_le (2 * (s - z i))], by
          nlinarith [abs_nonneg (2 * (s - z i)), sq_abs (2 * (s - z i))]⟩
      calc |deriv ctTau (u s)| * |2 * (s - z i)| ≤ T1 * 1 :=
            mul_le_mul (hT1 _) this (abs_nonneg _) hT10
        _ = T1 := mul_one _
  have k2 : ∀ s, |deriv (deriv ctTau) (u s)| * (2 * (s - z i)) ^ 2 ≤ T2 := by
    intro s
    by_cases h0 : deriv (deriv ctTau) (u s) = 0
    · rw [h0]; simp; exact hT20
    · have hs : 1 < u s := by
        by_contra hnot
        exact h0 (ctTau_deriv_support (Or.inl (not_lt.1 hnot))).2
      calc |deriv (deriv ctTau) (u s)| * (2 * (s - z i)) ^ 2 ≤ T2 * 1 :=
            mul_le_mul (hT2 _) (hw s hs) (sq_nonneg _) hT20
        _ = T2 := mul_one _
  refine ⟨ctTau_nonneg _, ctTau_le_one _, ?_, ?_⟩
  · rw [hdφ]
    show |deriv ctTau (u t) * ((3 : ℝ) ^ n * (-2 * (t - z i)))| ≤ _
    have e : |deriv ctTau (u t) * ((3 : ℝ) ^ n * (-2 * (t - z i)))| =
        (3 : ℝ) ^ n * (|deriv ctTau (u t)| * |2 * (t - z i)|) := by
      have hneg : (-2 * (t - z i)) = -(2 * (t - z i)) := by ring
      rw [hneg, abs_mul, abs_mul, abs_neg, abs_of_pos ha0]
      ring
    rw [e]
    calc (3 : ℝ) ^ n * (|deriv ctTau (u t)| * |2 * (t - z i)|) ≤ (3 : ℝ) ^ n * T1 :=
          mul_le_mul_of_nonneg_left (k1 t) ha0.le
      _ ≤ (T1 + T2 + 2 * T1) * (3 : ℝ) ^ n := by nlinarith
  · rw [hφ2.deriv]
    have e : deriv (deriv ctTau) (u t) * ((3 : ℝ) ^ n * (-2 * (t - z i))) * ((3 : ℝ) ^ n * (-2 * (t - z i))) +
        deriv ctTau (u t) * ((3 : ℝ) ^ n * (-2)) =
        (9 : ℝ) ^ n * (deriv (deriv ctTau) (u t) * (2 * (t - z i)) ^ 2) -
          2 * (3 : ℝ) ^ n * deriv ctTau (u t) := by
      rw [h99]; ring
    rw [e]
    have b1 : |(9 : ℝ) ^ n * (deriv (deriv ctTau) (u t) * (2 * (t - z i)) ^ 2)| ≤ (9 : ℝ) ^ n * T2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (9 : ℝ) ^ n), abs_mul, abs_of_nonneg (sq_nonneg (2 * (t - z i)))]
      exact mul_le_mul_of_nonneg_left (k2 t) (by positivity)
    have b2 : |2 * (3 : ℝ) ^ n * deriv ctTau (u t)| ≤ (9 : ℝ) ^ n * (2 * T1) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (3 : ℝ) ^ n)]
      have := hT1 (u t)
      nlinarith
    calc |(9 : ℝ) ^ n * (deriv (deriv ctTau) (u t) * (2 * (t - z i)) ^ 2) -
          2 * (3 : ℝ) ^ n * deriv ctTau (u t)|
        ≤ |(9 : ℝ) ^ n * (deriv (deriv ctTau) (u t) * (2 * (t - z i)) ^ 2)| +
          |2 * (3 : ℝ) ^ n * deriv ctTau (u t)| := abs_sub _ _
      _ ≤ (9 : ℝ) ^ n * T2 + (9 : ℝ) ^ n * (2 * T1) := add_le_add b1 b2
      _ = (T1 + T2 + 2 * T1) * (9 : ℝ) ^ n - T1 * (9 : ℝ) ^ n := by ring
      _ ≤ (T1 + T2 + 2 * T1) * (9 : ℝ) ^ n := by
          have : 0 ≤ T1 * (9 : ℝ) ^ n := by positivity
          linarith

theorem hasFDerivAt_prod_coord {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (s : Finset (Fin d)) (x : Fin d → ℝ) :
    HasFDerivAt (fun y : Fin d → ℝ => ∏ i ∈ s, f i (y i))
      (∑ i ∈ s, (∏ k ∈ s.erase i, f k (x k)) •
        (deriv (f i) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)) x := by
  classical
  have h : ∀ i ∈ s, HasFDerivAt (fun y : Fin d → ℝ => f i (y i))
      (deriv (f i) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
    intro i _
    have hd : HasDerivAt (f i) (deriv (f i) (x i)) (x i) :=
      (((hf i).differentiable (by simp)) (x i)).hasDerivAt
    exact hd.comp_hasFDerivAt x (hasFDerivAt_apply i x)
  exact HasFDerivAt.finsetProd (u := s) (g := fun i (y : Fin d → ℝ) => f i (y i)) h

theorem fderiv_prod_coord_finset {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (s : Finset (Fin d)) (x : Fin d → ℝ) (j : Fin d) :
    fderiv ℝ (fun y : Fin d → ℝ => ∏ i ∈ s, f i (y i)) x (Pi.single j 1) =
      if j ∈ s then deriv (f j) (x j) * ∏ i ∈ s.erase j, f i (x i) else 0 := by
  classical
  rw [(hasFDerivAt_prod_coord hf s x).fderiv]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · simp; ring
    · intro i _ hij; simp [hij]
    · intro h; exact absurd hj h
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    have : i ≠ j := fun h => hj (h ▸ hi)
    simp [this]

theorem hasFDerivAt_coord_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (x : Fin d → ℝ) (i : Fin d) :
    HasFDerivAt (fun y : Fin d → ℝ => g (y i))
      (deriv g (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
  have hd : HasDerivAt g (deriv g (x i)) (x i) := (((hg.differentiable (by simp)) (x i)).hasDerivAt)
  exact hd.comp_hasFDerivAt x (hasFDerivAt_apply i x)

/-- Partial derivative of a function of one coordinate. -/
theorem fderiv_coord_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (x : Fin d → ℝ) (i j : Fin d) :
    fderiv ℝ (fun y : Fin d → ℝ => g (y i)) x (Pi.single j 1) =
      if j = i then deriv g (x i) else 0 := by
  classical
  have := fderiv_prod_coord_finset (f := fun _ : Fin d => g) (fun _ => hg) {i} x j
  simp only [Finset.prod_singleton, Finset.mem_singleton] at this
  rw [this]
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- Directional derivative of a coordinate product. -/
theorem fderiv_prod_coord {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : (Fin d → ℝ)) (j : Fin d) :
    fderiv ℝ (fun y : (Fin d → ℝ) => ∏ i, f i (y i)) x (Pi.single j 1) =
      deriv (f j) (x j) * ∏ i ∈ Finset.univ.erase j, f i (x i) := by
  rw [fderiv_prod_coord_finset hf Finset.univ x j, ite_eq_left (Finset.mem_univ j)]

/-- Second directional derivative of a coordinate product, same direction. -/
theorem fderiv2_prod_coord_eq {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : (Fin d → ℝ)) (j : Fin d) :
    fderiv ℝ (fun w => fderiv ℝ (fun y : (Fin d → ℝ) => ∏ i, f i (y i)) w (Pi.single j 1))
        x (Pi.single j 1) =
      deriv (deriv (f j)) (x j) * ∏ i ∈ Finset.univ.erase j, f i (x i) := by
  classical
  have hF : (fun w : Fin d → ℝ => fderiv ℝ (fun y : Fin d → ℝ => ∏ i, f i (y i)) w (Pi.single j 1)) =
      fun w => deriv (f j) (w j) * ∏ i ∈ Finset.univ.erase j, f i (w i) := by
    funext w; exact fderiv_prod_coord hf w j
  rw [hF]
  have hdf : ContDiff ℝ ∞ (deriv (f j)) := by
    have := (hf j).iterate_deriv 1
    simpa using this
  have hda : DifferentiableAt ℝ (fun w : Fin d → ℝ => deriv (f j) (w j)) x :=
    (hasFDerivAt_coord_comp hdf x j).differentiableAt
  have hdb : DifferentiableAt ℝ (fun w : Fin d → ℝ => ∏ i ∈ Finset.univ.erase j, f i (w i)) x :=
    (hasFDerivAt_prod_coord hf _ x).differentiableAt
  have hm := hda.hasFDerivAt.mul hdb.hasFDerivAt
  have hmm : HasFDerivAt (fun w : Fin d → ℝ => deriv (f j) (w j) * ∏ i ∈ Finset.univ.erase j, f i (w i))
      ((deriv (f j) (x j)) • fderiv ℝ (fun w : Fin d → ℝ => ∏ i ∈ Finset.univ.erase j, f i (w i)) x +
        (∏ i ∈ Finset.univ.erase j, f i (x i)) •
          fderiv ℝ (fun w : Fin d → ℝ => deriv (f j) (w j)) x) x := hm
  rw [hmm.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_prod_coord_finset hf (Finset.univ.erase j) x j, fderiv_coord_comp hdf x j j]
  simp [mul_comm]

/-- Second directional derivative of a coordinate product, different directions. -/
theorem fderiv2_prod_coord_ne {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : (Fin d → ℝ)) {j l : Fin d} (hlj : l ≠ j) :
    fderiv ℝ (fun w => fderiv ℝ (fun y : (Fin d → ℝ) => ∏ i, f i (y i)) w (Pi.single j 1))
        x (Pi.single l 1) =
      deriv (f j) (x j) * (deriv (f l) (x l) *
        ∏ i ∈ (Finset.univ.erase j).erase l, f i (x i)) := by
  classical
  have hF : (fun w : Fin d → ℝ => fderiv ℝ (fun y : Fin d → ℝ => ∏ i, f i (y i)) w (Pi.single j 1)) =
      fun w => deriv (f j) (w j) * ∏ i ∈ Finset.univ.erase j, f i (w i) := by
    funext w; exact fderiv_prod_coord hf w j
  rw [hF]
  have hdf : ContDiff ℝ ∞ (deriv (f j)) := by
    have := (hf j).iterate_deriv 1
    simpa using this
  have hda : DifferentiableAt ℝ (fun w : Fin d → ℝ => deriv (f j) (w j)) x :=
    (hasFDerivAt_coord_comp hdf x j).differentiableAt
  have hdb : DifferentiableAt ℝ (fun w : Fin d → ℝ => ∏ i ∈ Finset.univ.erase j, f i (w i)) x :=
    (hasFDerivAt_prod_coord hf _ x).differentiableAt
  have hm := hda.hasFDerivAt.mul hdb.hasFDerivAt
  have hmm : HasFDerivAt (fun w : Fin d → ℝ => deriv (f j) (w j) * ∏ i ∈ Finset.univ.erase j, f i (w i))
      ((deriv (f j) (x j)) • fderiv ℝ (fun w : Fin d → ℝ => ∏ i ∈ Finset.univ.erase j, f i (w i)) x +
        (∏ i ∈ Finset.univ.erase j, f i (x i)) •
          fderiv ℝ (fun w : Fin d → ℝ => deriv (f j) (w j)) x) x := hm
  rw [hmm.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_prod_coord_finset hf (Finset.univ.erase j) x l, fderiv_coord_comp hdf x j l]
  have hl : l ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hlj, Finset.mem_univ l⟩
  simp [hl, hlj]

/-- The partition pieces `θ_0 = E_0`, `θ_{k+1} = E_{k+1} - E_k`. -/
def ctTheta (z : (Fin d → ℝ)) : ℕ → (Fin d → ℝ) → ℝ
  | 0 => ctE z 0
  | k + 1 => fun x => ctE z (k + 1) x - ctE z k x

theorem ctE_contDiff (z : (Fin d → ℝ)) (n : ℕ) : ContDiff ℝ ∞ (ctE z n) := by
  have h : ctE z n = fun x => ∏ i, ctPhi z n i (x i) := funext (ctE_eq_prod_phi z n)
  rw [h]
  exact contDiff_prod (fun i _ => (ctPhi_contDiff z n i).comp (contDiff_apply ℝ ℝ i))

theorem ctTheta_contDiff (z : (Fin d → ℝ)) (k : ℕ) : ContDiff ℝ ∞ (ctTheta z k) := by
  cases k with
  | zero => exact ctE_contDiff z 0
  | succ k => exact (ctE_contDiff z (k + 1)).sub (ctE_contDiff z k)

theorem ctE_nonneg (z x : (Fin d → ℝ)) (n : ℕ) : 0 ≤ ctE z n x := by
  unfold ctE
  exact Finset.prod_nonneg (fun i _ => ctTau_nonneg _)

theorem ctE_le_one (z x : (Fin d → ℝ)) (n : ℕ) : ctE z n x ≤ 1 := by
  unfold ctE
  exact Finset.prod_le_one₀ (fun i _ => ctTau_nonneg _) (fun i _ => ctTau_le_one _)

theorem abs_ctTheta_le_one (z x : (Fin d → ℝ)) (k : ℕ) : |ctTheta z k x| ≤ 1 := by
  cases k with
  | zero =>
    have h0 := ctE_nonneg z x 0
    have h1 := ctE_le_one z x 0
    simp only [ctTheta]
    rw [abs_le]
    constructor <;> linarith
  | succ k =>
    have h0 := ctE_nonneg z x (k + 1)
    have h1 := ctE_le_one z x (k + 1)
    have h2 := ctE_nonneg z x k
    have h3 := ctE_le_one z x k
    simp only [ctTheta]
    rw [abs_le]
    constructor <;> linarith

/-- Telescoping: `∑_{k ≤ N} θ_k = E_N`. -/
theorem sum_ctTheta_range (z x : (Fin d → ℝ)) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), ctTheta z k x = ctE z N x := by
  induction N with
  | zero => simp [ctTheta]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [ctTheta]
    ring

/-- `E_n = 1` near `x` once `3 < 3^n m(x)`. -/
theorem ctE_eventually_one [NeZero d] (z : (Fin d → ℝ)) (n : ℕ) {x : (Fin d → ℝ)}
    (hx : 3 < (3 : ℝ) ^ n * ctM z x) : ∀ᶠ y in 𝓝 x, ctE z n y = 1 := by
  have hc : Continuous fun y => (3 : ℝ) ^ n * ctM z y := continuous_const.mul (continuous_ctM z)
  have h : ∀ᶠ y in 𝓝 x, 3 < (3 : ℝ) ^ n * ctM z y := hc.continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [h] with y hy
  unfold ctE
  apply Finset.prod_eq_one
  intro i _
  apply ctTau_eq_one_of_ge
  have h1 := ctM_le_ctU z y i
  have h2 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  nlinarith

/-- `E_n = 0` near `x` once `3^n m(x) < 1`. -/
theorem ctE_eventually_zero [NeZero d] (z : (Fin d → ℝ)) (n : ℕ) {x : (Fin d → ℝ)}
    (hx : (3 : ℝ) ^ n * ctM z x < 1) : ∀ᶠ y in 𝓝 x, ctE z n y = 0 := by
  have hc : Continuous fun y => (3 : ℝ) ^ n * ctM z y := continuous_const.mul (continuous_ctM z)
  have h : ∀ᶠ y in 𝓝 x, (3 : ℝ) ^ n * ctM z y < 1 := hc.continuousAt.eventually (gt_mem_nhds hx)
  filter_upwards [h] with y hy
  unfold ctE
  obtain ⟨i, hi⟩ := exists_ctM_eq (z := z) (x := y)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply ctTau_eq_zero_of_le
  rw [← hi]
  exact hy.le

/-- Pointwise: `E_n(x) = 1` once `3 < 3^n m(x)`. -/
theorem ctE_eq_one_of_gt [NeZero d] (z : (Fin d → ℝ)) (n : ℕ) {x : (Fin d → ℝ)}
    (hx : 3 < (3 : ℝ) ^ n * ctM z x) : ctE z n x = 1 := by
  unfold ctE
  apply Finset.prod_eq_one
  intro i _
  apply ctTau_eq_one_of_ge
  have h1 := ctM_le_ctU z x i
  have h2 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  nlinarith

/-- Pointwise: `θ_k(x) = 0` for `k > N` once `3 < 3^N m(x)`. -/
theorem ctTheta_eq_zero_of_gt [NeZero d] (z : (Fin d → ℝ)) {N k : ℕ} (hk : N < k)
    {x : (Fin d → ℝ)} (hx : 3 < (3 : ℝ) ^ N * ctM z x) : ctTheta z k x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hm : 0 < ctM z x := by
    by_contra hneg
    push Not at hneg
    have : (3 : ℝ) ^ N * ctM z x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have h1 : 3 < (3 : ℝ) ^ j * ctM z x := by
    have : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have h2 : 3 < (3 : ℝ) ^ (j + 1) * ctM z x := by
    have : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  simp only [ctTheta, ctE_eq_one_of_gt z j h1, ctE_eq_one_of_gt z (j + 1) h2, sub_self]

/-- `θ_k` vanishes near `x` when `x` is outside the band `3^{-k} ≤ m ≤ 9 · 3^{-k}`. -/
theorem ctTheta_eventually_zero [NeZero d] (z : (Fin d → ℝ)) (k : ℕ)
    {x : (Fin d → ℝ)}
    (hx : ctM z x < ((1 : ℝ) / 3) ^ k ∨ 9 * ((1 : ℝ) / 3) ^ k < ctM z x) :
    ∀ᶠ y in 𝓝 x, ctTheta z k y = 0 := by
  cases k with
  | zero =>
    rcases hx with hx | hx
    · have h0 : (3 : ℝ) ^ 0 * ctM z x < 1 := by simpa using hx
      filter_upwards [ctE_eventually_zero z 0 h0] with y hy
      simpa [ctTheta] using hy
    · exfalso
      have := ctM_le_quarter z x
      simp at hx
      linarith
  | succ j =>
    have hpow : (3 : ℝ) ^ (j + 1) * (1 / 3) ^ (j + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (j + 1) := by positivity
    have hsplit : (3 : ℝ) ^ (j + 1) * ctM z x = 3 * ((3 : ℝ) ^ j * ctM z x) := by ring
    rcases hx with hx | hx
    · have h1 : (3 : ℝ) ^ (j + 1) * ctM z x < 1 := by
        calc (3 : ℝ) ^ (j + 1) * ctM z x < (3 : ℝ) ^ (j + 1) * (1 / 3) ^ (j + 1) :=
              mul_lt_mul_of_pos_left hx hpos
          _ = 1 := hpow
      have h2 : (3 : ℝ) ^ j * ctM z x < 1 := by linarith
      filter_upwards [ctE_eventually_zero z (j + 1) h1, ctE_eventually_zero z j h2] with y hy1 hy2
      simp only [ctTheta, hy1, hy2, sub_self]
    · have h9' : 9 < (3 : ℝ) ^ (j + 1) * ctM z x := by
        have : (3 : ℝ) ^ (j + 1) * (9 * (1 / 3) ^ (j + 1)) < (3 : ℝ) ^ (j + 1) * ctM z x :=
          mul_lt_mul_of_pos_left hx hpos
        have h9 : (3 : ℝ) ^ (j + 1) * (9 * (1 / 3) ^ (j + 1)) = 9 := by
          rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (j + 1)) 9, mul_assoc, hpow]; norm_num
        linarith
      have h1 : 3 < (3 : ℝ) ^ (j + 1) * ctM z x := by linarith
      have h2 : 3 < (3 : ℝ) ^ j * ctM z x := by linarith
      filter_upwards [ctE_eventually_one z (j + 1) h1, ctE_eventually_one z j h2] with y hy1 hy2
      simp only [ctTheta, hy1, hy2, sub_self]

/-- For `k > N` the pieces vanish near `x` once `3 < 3^N m(x)`. -/
theorem ctTheta_eventually_zero_of_gt [NeZero d] (z : (Fin d → ℝ)) {N k : ℕ}
    (hk : N < k) {x : (Fin d → ℝ)} (hx : 3 < (3 : ℝ) ^ N * ctM z x) :
    ∀ᶠ y in 𝓝 x, ctTheta z k y = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hm : 0 < ctM z x := by
    by_contra hneg
    push Not at hneg
    have : (3 : ℝ) ^ N * ctM z x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have h1 : 3 < (3 : ℝ) ^ j * ctM z x := by
    have : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have h2 : 3 < (3 : ℝ) ^ (j + 1) * ctM z x := by
    have : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  filter_upwards [ctE_eventually_one z j h1, ctE_eventually_one z (j + 1) h2] with y hy1 hy2
  simp only [ctTheta, hy1, hy2, sub_self]

/-- Near `x`, the partial sum of the partition of unity is `1` once `3 < 3^N m(x)`. -/
theorem sum_ctTheta_eventually_one [NeZero d] (z : (Fin d → ℝ)) (N : ℕ)
    {x : (Fin d → ℝ)} (hx : 3 < (3 : ℝ) ^ N * ctM z x) :
    ∀ᶠ y in 𝓝 x, ∑ k ∈ Finset.range (N + 1), ctTheta z k y = 1 := by
  filter_upwards [ctE_eventually_one z N hx] with y hy
  rw [sum_ctTheta_range, hy]

/-- Every point of the cube has some `N` with `3 < 3^N m(x)`. -/
theorem exists_N_of_mem [NeZero d] {z x : (Fin d → ℝ)} (hx : x ∈ ctQ z) :
    ∃ N : ℕ, 3 < (3 : ℝ) ^ N * ctM z x := by
  have hm := ctM_pos hx
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (3 / ctM z x) (by norm_num : (1 : ℝ) < 3)
  refine ⟨N, ?_⟩
  rw [div_lt_iff₀ hm] at hN
  linarith

/-- The number of `k` whose band `3^{-k} ≤ m ≤ 9 · 3^{-k}` contains a given `m > 0` is at most `3`. -/
theorem band_card_le {m : ℝ} (hm : 0 < m) (N : ℕ) :
    ((Finset.range N).filter (fun k : ℕ =>
      ((1 : ℝ) / 3) ^ k ≤ m ∧ m ≤ 9 * ((1 : ℝ) / 3) ^ k)).card ≤ 3 := by
  set S := (Finset.range N).filter (fun k : ℕ =>
      ((1 : ℝ) / 3) ^ k ≤ m ∧ m ≤ 9 * ((1 : ℝ) / 3) ^ k) with hS
  have hdiam : ∀ a ∈ S, ∀ b ∈ S, b ≤ a + 2 := by
    intro a ha b hb
    rw [hS, Finset.mem_filter] at ha hb
    by_contra hlt
    push Not at hlt
    have h1 : ((1 : ℝ) / 3) ^ b ≤ ((1 : ℝ) / 3) ^ (a + 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : ((1 : ℝ) / 3) ^ (a + 3) = ((1 : ℝ) / 3) ^ a * ((1 : ℝ) / 27) := by
      rw [pow_add]; norm_num
    have hp : (0 : ℝ) < ((1 : ℝ) / 3) ^ a := by positivity
    have h3 := ha.2.1
    have h4 := ha.2.2
    have h5 := hb.2.1
    have h6 := hb.2.2
    nlinarith
  by_cases hne : S.Nonempty
  · set a := S.min' hne with ha
    have hsub : S ⊆ Finset.Icc a (a + 2) := by
      intro k hk
      rw [Finset.mem_Icc]
      exact ⟨S.min'_le k hk, hdiam a (S.min'_mem hne) k hk⟩
    calc S.card ≤ (Finset.Icc a (a + 2)).card := Finset.card_le_card hsub
      _ = 3 := by rw [Nat.card_Icc]; omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-- First derivative of `E_n`: bounded by `c1 · 3^n` everywhere. -/
theorem ctE_fderiv_bound :
    ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ (z x : (Fin d → ℝ)) (n : ℕ) (j : Fin d),
      |fderiv ℝ (ctE z n) x (Pi.single j 1)| ≤ c1 * (3 : ℝ) ^ n := by
  obtain ⟨c, hc0, hc⟩ := ctPhi_bounds (d := d)
  refine ⟨c, hc0, ?_⟩
  intro z x n j
  have hE : ctE z n = fun y : Fin d → ℝ => ∏ i, ctPhi z n i (y i) := funext (ctE_eq_prod_phi z n)
  rw [hE, fderiv_prod_coord (fun i => ctPhi_contDiff z n i) x j, abs_mul]
  have hprod0 : 0 ≤ ∏ i ∈ Finset.univ.erase j, ctPhi z n i (x i) :=
    Finset.prod_nonneg (fun i _ => (hc z n i (x i)).1)
  have hprod1 : ∏ i ∈ Finset.univ.erase j, ctPhi z n i (x i) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hc z n i (x i)).1) (fun i _ => (hc z n i (x i)).2.1)
  rw [abs_of_nonneg hprod0]
  calc |deriv (ctPhi z n j) (x j)| * ∏ i ∈ Finset.univ.erase j, ctPhi z n i (x i)
      ≤ (c * (3 : ℝ) ^ n) * 1 :=
        mul_le_mul (hc z n j (x j)).2.2.1 hprod1 hprod0 (by positivity)
    _ = c * (3 : ℝ) ^ n := mul_one _

/-- Second derivative of `E_n`: bounded by `c2 · 9^n` everywhere. -/
theorem ctE_fderiv2_bound :
    ∃ c2 : ℝ, 0 ≤ c2 ∧ ∀ (z x : (Fin d → ℝ)) (n : ℕ) (j l : Fin d),
      |fderiv ℝ (fun y => fderiv ℝ (ctE z n) y (Pi.single j 1)) x (Pi.single l 1)| ≤
        c2 * (9 : ℝ) ^ n := by
  obtain ⟨c, hc0, hc⟩ := ctPhi_bounds (d := d)
  refine ⟨c + c * c, by positivity, ?_⟩
  intro z x n j l
  have hE : ctE z n = fun y : Fin d → ℝ => ∏ i, ctPhi z n i (y i) := funext (ctE_eq_prod_phi z n)
  have hcd := fun i => ctPhi_contDiff z n i
  rw [hE]
  by_cases hlj : l = j
  · subst hlj
    rw [fderiv2_prod_coord_eq hcd x l, abs_mul]
    have hprod0 : 0 ≤ ∏ i ∈ Finset.univ.erase l, ctPhi z n i (x i) :=
      Finset.prod_nonneg (fun i _ => (hc z n i (x i)).1)
    have hprod1 : ∏ i ∈ Finset.univ.erase l, ctPhi z n i (x i) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => (hc z n i (x i)).1) (fun i _ => (hc z n i (x i)).2.1)
    rw [abs_of_nonneg hprod0]
    calc |deriv (deriv (ctPhi z n l)) (x l)| * ∏ i ∈ Finset.univ.erase l, ctPhi z n i (x i)
        ≤ (c * (9 : ℝ) ^ n) * 1 :=
          mul_le_mul (hc z n l (x l)).2.2.2 hprod1 hprod0 (by positivity)
      _ = c * (9 : ℝ) ^ n := mul_one _
      _ ≤ (c + c * c) * (9 : ℝ) ^ n := by
          have : 0 ≤ c * c * (9 : ℝ) ^ n := by positivity
          nlinarith
  · rw [fderiv2_prod_coord_ne hcd x hlj, abs_mul, abs_mul]
    have hprod0 : 0 ≤ ∏ i ∈ (Finset.univ.erase j).erase l, ctPhi z n i (x i) :=
      Finset.prod_nonneg (fun i _ => (hc z n i (x i)).1)
    have hprod1 : ∏ i ∈ (Finset.univ.erase j).erase l, ctPhi z n i (x i) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => (hc z n i (x i)).1) (fun i _ => (hc z n i (x i)).2.1)
    rw [abs_of_nonneg hprod0]
    have h1 := (hc z n j (x j)).2.2.1
    have h2 := (hc z n l (x l)).2.2.1
    calc |deriv (ctPhi z n j) (x j)| * (|deriv (ctPhi z n l) (x l)| *
          ∏ i ∈ (Finset.univ.erase j).erase l, ctPhi z n i (x i))
        ≤ (c * (3 : ℝ) ^ n) * ((c * (3 : ℝ) ^ n) * 1) :=
          mul_le_mul h1 (mul_le_mul h2 hprod1 hprod0 (by positivity)) (by positivity)
            (by positivity)
      _ = c * c * (9 : ℝ) ^ n := by
          have : (9 : ℝ) ^ n = (3 : ℝ) ^ n * (3 : ℝ) ^ n := by
            rw [← mul_pow]; norm_num
          rw [this]; ring
      _ ≤ (c + c * c) * (9 : ℝ) ^ n := by
          have : 0 ≤ c * (9 : ℝ) ^ n := by positivity
          nlinarith

/-- First derivative of `θ_k`: bounded by `c1 · 3^k` everywhere. -/
theorem ctTheta_fderiv_bound :
    ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ (z x : (Fin d → ℝ)) (k : ℕ) (j : Fin d),
      |fderiv ℝ (ctTheta z k) x (Pi.single j 1)| ≤ c1 * (3 : ℝ) ^ k := by
  obtain ⟨c1, hc10, hc1⟩ := ctE_fderiv_bound (d := d)
  refine ⟨2 * c1, by positivity, ?_⟩
  intro z x k j
  have hdE : ∀ n, DifferentiableAt ℝ (ctE z n) x := fun n =>
    ((ctE_contDiff z n).differentiable (by simp)).differentiableAt
  cases k with
  | zero =>
    have := hc1 z x 0 j
    simp only [ctTheta]
    calc |fderiv ℝ (ctE z 0) x (Pi.single j 1)| ≤ c1 * (3 : ℝ) ^ 0 := this
      _ ≤ 2 * c1 * (3 : ℝ) ^ 0 := by nlinarith
  | succ k =>
    have h1 := hc1 z x (k + 1) j
    have h2 := hc1 z x k j
    have hfd : fderiv ℝ (ctTheta z (k + 1)) x = fderiv ℝ (ctE z (k + 1)) x - fderiv ℝ (ctE z k) x := by
      have : ctTheta z (k + 1) = fun y => ctE z (k + 1) y - ctE z k y := rfl
      rw [this]
      exact fderiv_sub (hdE (k + 1)) (hdE k)
    rw [hfd, sub_apply]
    have hp : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc |fderiv ℝ (ctE z (k + 1)) x (Pi.single j 1) - fderiv ℝ (ctE z k) x (Pi.single j 1)|
        ≤ |fderiv ℝ (ctE z (k + 1)) x (Pi.single j 1)| + |fderiv ℝ (ctE z k) x (Pi.single j 1)| :=
          abs_sub _ _
      _ ≤ c1 * (3 : ℝ) ^ (k + 1) + c1 * (3 : ℝ) ^ k := add_le_add h1 h2
      _ ≤ 2 * c1 * (3 : ℝ) ^ (k + 1) := by nlinarith

/-- Second derivative of `θ_k`: bounded by `c2 · 9^k` everywhere. -/
theorem ctTheta_fderiv2_bound :
    ∃ c2 : ℝ, 0 ≤ c2 ∧ ∀ (z x : (Fin d → ℝ)) (k : ℕ) (j l : Fin d),
      |fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1)| ≤
        c2 * (9 : ℝ) ^ k := by
  obtain ⟨c2, hc20, hc2⟩ := ctE_fderiv2_bound (d := d)
  refine ⟨2 * c2, by positivity, ?_⟩
  intro z x k j l
  have hdE1 : ∀ n, DifferentiableAt ℝ (fun y => fderiv ℝ (ctE z n) y (Pi.single j 1)) x := by
    intro n
    have h1 : ContDiff ℝ ∞ (fderiv ℝ (ctE z n)) := (ctE_contDiff z n).fderiv_right (by simp)
    exact ((h1.clm_apply contDiff_const).differentiable (by simp)).differentiableAt
  cases k with
  | zero =>
    have := hc2 z x 0 j l
    simp only [ctTheta]
    calc _ ≤ c2 * (9 : ℝ) ^ 0 := this
      _ ≤ 2 * c2 * (9 : ℝ) ^ 0 := by nlinarith
  | succ k =>
    have h1 := hc2 z x (k + 1) j l
    have h2 := hc2 z x k j l
    have hfun : (fun y => fderiv ℝ (ctTheta z (k + 1)) y (Pi.single j 1)) =
        fun y => fderiv ℝ (ctE z (k + 1)) y (Pi.single j 1) - fderiv ℝ (ctE z k) y (Pi.single j 1) := by
      funext y
      have hdE : ∀ n, DifferentiableAt ℝ (ctE z n) y := fun n =>
        ((ctE_contDiff z n).differentiable (by simp)).differentiableAt
      have : ctTheta z (k + 1) = fun y => ctE z (k + 1) y - ctE z k y := rfl
      have h' : HasFDerivAt (fun y => ctE z (k + 1) y - ctE z k y)
          (fderiv ℝ (ctE z (k + 1)) y - fderiv ℝ (ctE z k) y) y :=
        (hdE (k + 1)).hasFDerivAt.sub (hdE k).hasFDerivAt
      rw [this, h'.fderiv, sub_apply]
    have h'' : HasFDerivAt (fun y => fderiv ℝ (ctE z (k + 1)) y (Pi.single j 1) -
        fderiv ℝ (ctE z k) y (Pi.single j 1))
        (fderiv ℝ (fun y => fderiv ℝ (ctE z (k + 1)) y (Pi.single j 1)) x -
          fderiv ℝ (fun y => fderiv ℝ (ctE z k) y (Pi.single j 1)) x) x :=
      (hdE1 (k + 1)).hasFDerivAt.sub (hdE1 k).hasFDerivAt
    rw [hfun, h''.fderiv, sub_apply]
    have hp : (9 : ℝ) ^ k ≤ (9 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc _ ≤ |fderiv ℝ (fun y => fderiv ℝ (ctE z (k + 1)) y (Pi.single j 1)) x (Pi.single l 1)| +
          |fderiv ℝ (fun y => fderiv ℝ (ctE z k) y (Pi.single j 1)) x (Pi.single l 1)| := abs_sub _ _
      _ ≤ c2 * (9 : ℝ) ^ (k + 1) + c2 * (9 : ℝ) ^ k := add_le_add h1 h2
      _ ≤ 2 * c2 * (9 : ℝ) ^ (k + 1) := by nlinarith

/-- Where `θ_k` vanishes nearby, so do its first and second partial derivatives. -/
theorem ctTheta_derivs_zero_of_eventually {z : (Fin d → ℝ)} {k : ℕ}
    {x : (Fin d → ℝ)} (h : ∀ᶠ y in 𝓝 x, ctTheta z k y = 0) (j l : Fin d) :
    fderiv ℝ (ctTheta z k) x (Pi.single j 1) = 0 ∧
      fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x (Pi.single l 1) = 0 := by
  have h1 : fderiv ℝ (ctTheta z k) x = 0 := by
    have : fderiv ℝ (ctTheta z k) x = fderiv ℝ (fun _ : (Fin d → ℝ) => (0 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq h
    rw [this]; simp
  refine ⟨by rw [h1]; rfl, ?_⟩
  have h2 : ∀ᶠ y in 𝓝 x, fderiv ℝ (ctTheta z k) y (Pi.single j 1) = 0 := by
    filter_upwards [h.eventually_nhds] with y hy
    have : fderiv ℝ (ctTheta z k) y = fderiv ℝ (fun _ : (Fin d → ℝ) => (0 : ℝ)) y :=
      Filter.EventuallyEq.fderiv_eq hy
    rw [this]; simp
  have : fderiv ℝ (fun y => fderiv ℝ (ctTheta z k) y (Pi.single j 1)) x =
      fderiv ℝ (fun _ : (Fin d → ℝ) => (0 : ℝ)) x := Filter.EventuallyEq.fderiv_eq h2
  rw [this]; simp

end SubdiffusiveProcess.CubeTrace
