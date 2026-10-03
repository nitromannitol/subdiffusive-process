module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section




set_option autoImplicit false

open Filter Finset MeasureTheory

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

/-! ## The dyadic grid on `[0, T]` -/

/-- The `k`-th point of the `n`-th dyadic subdivision of `[0, T]`, frozen at `T` for `k ≥ 2ⁿ`.
The freezing is what makes `dyadicTime T n` monotone on all of `ℕ`. -/
def dyadicTime (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := ((min k (2 ^ n) : ℕ) : ℝ≥0) / ((2 ^ n : ℕ) : ℝ≥0) * T

theorem dyadicTime_coe (T : ℝ≥0) (n k : ℕ) :
    ((dyadicTime T n k : ℝ≥0) : ℝ) = ((min k (2 ^ n) : ℕ) : ℝ) / (2 ^ n : ℝ) * (T : ℝ) := by
  simp [dyadicTime]

theorem monotone_dyadicTime (T : ℝ≥0) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro k k' hkk
  simp only [dyadicTime]
  gcongr

theorem dyadicTime_le (T : ℝ≥0) (n k : ℕ) : dyadicTime T n k ≤ T := by
  have h : ((min k (2 ^ n) : ℕ) : ℝ≥0) / ((2 ^ n : ℕ) : ℝ≥0) ≤ 1 :=
    (div_le_one (by positivity)).2 (by exact_mod_cast min_le_right k (2 ^ n))
  calc dyadicTime T n k ≤ 1 * T := by
        simp only [dyadicTime]
        gcongr
    _ = T := one_mul T

@[simp] theorem dyadicTime_last (T : ℝ≥0) (n : ℕ) : dyadicTime T n (2 ^ n) = T := by
  simp [dyadicTime]

/-- **The grids are nested**: every point of the `n`-th subdivision is a point of the
`(n+1)`-st. -/
theorem dyadicTime_succ_two_mul (T : ℝ≥0) (n k : ℕ) :
    dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  have hpow : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hmin : min (2 * k) (2 ^ (n + 1)) = 2 * min k (2 ^ n) := by omega
  simp only [dyadicTime, hmin]
  congr 1
  rw [div_eq_div_iff (by positivity) (by positivity)]
  push_cast
  ring

/-- Every point of `[0, T]` is within `T / 2ⁿ` of a point of the `n`-th dyadic subdivision. -/
theorem exists_dyadicTime_close (T : ℝ≥0) (n : ℕ) {t : ℝ≥0} (ht : t ≤ T) :
    ∃ k : ℕ, k ≤ 2 ^ n ∧ |((dyadicTime T n k : ℝ≥0) : ℝ) - (t : ℝ)| ≤ (T : ℝ) / 2 ^ n := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rcases eq_or_lt_of_le (show 0 ≤ T from zero_le) with hT | hT
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have ht0 : t = 0 := le_antisymm (hT ▸ ht) zero_le
    simp [dyadicTime_coe, ht0, ← hT]
  · have hT' : (0 : ℝ) < (T : ℝ) := hT
    set x : ℝ := (t : ℝ) * 2 ^ n / (T : ℝ) with hx
    have hx0 : 0 ≤ x := by positivity
    have hxle : x ≤ (2 : ℝ) ^ n := by
      rw [hx, div_le_iff₀ hT']
      have : (t : ℝ) ≤ (T : ℝ) := ht
      nlinarith
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have hlt_floor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hkle : ⌊x⌋₊ ≤ 2 ^ n := by
      have hx2 : x ≤ ((2 ^ n : ℕ) : ℝ) := by push_cast; exact hxle
      have h := Nat.floor_le_floor hx2
      rwa [Nat.floor_natCast] at h
    refine ⟨⌊x⌋₊, hkle, ?_⟩
    have hmin : min ⌊x⌋₊ (2 ^ n) = ⌊x⌋₊ := min_eq_left hkle
    have hk1 : (⌊x⌋₊ : ℝ) * (T : ℝ) ≤ (t : ℝ) * 2 ^ n := by
      have := mul_le_mul_of_nonneg_right hfloor_le hT'.le
      rwa [hx, div_mul_cancel₀ _ (ne_of_gt hT')] at this
    have hk2 : (t : ℝ) * 2 ^ n < ((⌊x⌋₊ : ℝ) + 1) * (T : ℝ) := by
      have := mul_lt_mul_of_pos_right hlt_floor hT'
      rwa [hx, div_mul_cancel₀ _ (ne_of_gt hT')] at this
    have habs : |(⌊x⌋₊ : ℝ) * (T : ℝ) - (t : ℝ) * 2 ^ n| ≤ (T : ℝ) := by
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    have hrw : ((dyadicTime T n ⌊x⌋₊ : ℝ≥0) : ℝ) - (t : ℝ)
        = ((⌊x⌋₊ : ℝ) * (T : ℝ) - (t : ℝ) * 2 ^ n) / 2 ^ n := by
      rw [dyadicTime_coe, hmin]
      field_simp
    rw [hrw, abs_div, abs_of_pos h2n]
    gcongr

/-! ## The finite maxima and their limit -/

/-- The maximum of `F` over the `n`-th dyadic subdivision of `[0, T]`. -/
def dyadicGridSup (F : ℝ≥0 → ℝ≥0∞) (T : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one fun k => F (dyadicTime T n k)

/-- **The finite maxima increase**, because the dyadic grids are nested.  This is what licenses
monotone convergence under the integral. -/
theorem monotone_dyadicGridSup (F : ℝ≥0 → ℝ≥0∞) (T : ℝ≥0) : Monotone (dyadicGridSup F T) := by
  refine monotone_nat_of_le_succ fun n => ?_
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hk' : k ≤ 2 ^ n := by simpa [Nat.lt_succ_iff] using hk
  have hmem : 2 * k ∈ Finset.range (2 ^ (n + 1) + 1) := by
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    omega
  calc F (dyadicTime T n k) = F (dyadicTime T (n + 1) (2 * k)) := by
        rw [dyadicTime_succ_two_mul]
    _ ≤ dyadicGridSup F T (n + 1) :=
        Finset.le_sup' (fun k => F (dyadicTime T (n + 1) k)) hmem

/-- **Grids to the continuous supremum.**  For a continuous `F`, the supremum over `[0, T]` is at
most the supremum of the dyadic maxima.  No constant is lost. -/
theorem iSup_le_dyadicGridSup {T : ℝ≥0} {F : ℝ≥0 → ℝ≥0∞} (hF : Continuous F) :
    (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F t) ≤ ⨆ n : ℕ, dyadicGridSup F T n := by
  refine iSup_le fun t => iSup_le fun ht => ?_
  choose k hkle hk using fun n => exists_dyadicTime_close T n ht
  set s : ℕ → ℝ≥0 := fun n => dyadicTime T n (k n) with hs
  have hzero : Tendsto (fun n : ℕ => (T : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    have := h.const_mul (T : ℝ)
    simpa [div_pow, div_eq_mul_inv] using this
  have hst : Tendsto s atTop (𝓝 t) := by
    rw [← NNReal.tendsto_coe, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hzero
    rw [Real.dist_eq]
    exact hk n
  have hlim : Tendsto (fun n => F (s n)) atTop (𝓝 (F t)) := (hF.tendsto t).comp hst
  refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  refine le_trans ?_ (le_iSup (fun n : ℕ => dyadicGridSup F T n) n)
  exact Finset.le_sup' (fun j => F (dyadicTime T n j))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hkle n)

/-- The two facts, packaged with monotone convergence: the continuous supremum integrates to at
most the limit of the grid integrals. -/
theorem lintegral_iSup_le_dyadicGridSup {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    {T : ℝ≥0} {F : Ω → ℝ≥0 → ℝ≥0∞} (hcont : ∀ ω, Continuous (F ω))
    (hmeas : ∀ n : ℕ, Measurable fun ω => dyadicGridSup (F ω) T n) :
    ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F ω t) ∂P
      ≤ ⨆ n : ℕ, ∫⁻ ω, dyadicGridSup (F ω) T n ∂P := by
  calc ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F ω t) ∂P
      ≤ ∫⁻ ω, ⨆ n : ℕ, dyadicGridSup (F ω) T n ∂P :=
        lintegral_mono fun ω => iSup_le_dyadicGridSup (hcont ω)
    _ = ⨆ n : ℕ, ∫⁻ ω, dyadicGridSup (F ω) T n ∂P :=
        lintegral_iSup hmeas (fun _ _ h ω => monotone_dyadicGridSup (F ω) T h)

/-! ## Matching the two shapes of "maximum of squares" -/

/-- The grid inequality produces `ofReal ((maxₖ |xₖ|)²)`; the target has `maxₖ ofReal (xₖ²)`.
They agree. -/
theorem ofReal_sq_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (x : ι → ℝ) :
    ENNReal.ofReal ((s.sup' hs fun i => |x i|) ^ 2)
      = s.sup' hs fun i => ENNReal.ofReal (x i ^ 2) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup' hs fun i => |x i|
    rw [hieq, sq_abs]
    exact Finset.le_sup' (fun i => ENNReal.ofReal (x i ^ 2)) hi
  · refine Finset.sup'_le _ _ fun i hi => ENNReal.ofReal_le_ofReal ?_
    have h1 : |x i| ≤ s.sup' hs fun i => |x i| := Finset.le_sup' (fun i => |x i|) hi
    have h0 : (0 : ℝ) ≤ |x i| := abs_nonneg _
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ ≤ (s.sup' hs fun i => |x i|) ^ 2 := by nlinarith

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
